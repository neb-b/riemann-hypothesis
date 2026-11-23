module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0003

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.CycSecP
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.CycP

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ}

def gen (ε : Fin m → Bool) (k : Bool × Fin n × Fin n) : PX m n := Qb ε k.1 k.2.1 k.2.2

def Mon (ε : Fin m → Bool) (d : ℕ) : Submodule ℂ (PX m n) :=
  Submodule.span ℂ {M | ∃ l : List (Bool × Fin n × Fin n), l.length ≤ d ∧ M = (l.map (gen ε)).prod}

theorem mon_mono (ε : Fin m → Bool) {d d' : ℕ} (h : d ≤ d') : Mon (n := n) ε d ≤ Mon ε d' :=
  Submodule.span_mono fun _ ⟨l, hl, e⟩ => ⟨l, hl.trans h, e⟩

theorem gen_mul_mon (ε : Fin m → Bool) (d : ℕ) (k : Bool × Fin n × Fin n) {M : PX m n} (hM : M ∈ Mon ε d) :
    gen ε k * M ∈ Mon ε (d + 1) := by
  induction hM using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    exact Submodule.subset_span ⟨k :: l, by simp; omega, by simp⟩
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul a x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

theorem mon_mul (ε : Fin m → Bool) {d d' : ℕ} {a b : PX m n} (ha : a ∈ Mon ε d) (hb : b ∈ Mon ε d') :
    a * b ∈ Mon ε (d + d') := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    induction hb using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l', hl', rfl⟩ := hy
      exact Submodule.subset_span ⟨l ++ l', by simp; omega, by simp⟩
    | zero => simp
    | add u v _ _ hu hv => rw [mul_add]; exact add_mem hu hv
    | smul c u _ hu => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hu
  | zero => simp
  | add u v _ _ hu hv => rw [add_mul]; exact add_mem hu hv
  | smul c u _ hu => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hu

theorem adjoin_le (ε : Fin m → Bool) {R : PX m n}
    (hR : R ∈ Algebra.adjoin ℂ (Set.range fun k : Bool × Fin n × Fin n => (Qb ε k.1 k.2.1 k.2.2 : PX m n))) :
    ∃ d, R ∈ Mon ε d := by
  induction hR using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact ⟨1, Submodule.subset_span ⟨[k], by simp, by simp [gen]⟩⟩
  | algebraMap r =>
    refine ⟨0, ?_⟩
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[], by simp, by simp⟩)
  | add x y _ _ hx hy =>
    obtain ⟨d, hd⟩ := hx
    obtain ⟨d', hd'⟩ := hy
    exact ⟨max d d', add_mem (mon_mono ε (le_max_left _ _) hd) (mon_mono ε (le_max_right _ _) hd')⟩
  | mul x y _ _ hx hy =>
    obtain ⟨d, hd⟩ := hx
    obtain ⟨d', hd'⟩ := hy
    exact ⟨d + d', mon_mul ε hd hd'⟩

theorem dsum_apply {ι : Type*} (s : Finset ι) (D : ι → Derivation ℂ (PX m n) (PX m n)) (x : PX m n) :
    (∑ i ∈ s, D i) x = ∑ i ∈ s, D i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_apply, ih]

def eulD (H : Matrix (Fin n) (Fin n) ℂ) : Derivation ℂ (PX m n) (PX m n) :=
  ∑ a : Fin m, ∑ j : Fin n, ((∑ i, X (a, i, false) * C (H i j)) • pderiv (a, j, false) +
    (∑ i, X (a, i, true) * C (star (H i j))) • pderiv (a, j, true))

theorem eulH_eq (H : Matrix (Fin n) (Fin n) ℂ) (R : PX m n) : eulH H R = eulD H R := by
  simp [eulH, eulD, smul_eq_mul]

theorem eulD_X_false (H : Matrix (Fin n) (Fin n) ℂ) (a : Fin m) (j : Fin n) :
    eulD H (X (a, j, false) : PX m n) = ∑ i, X (a, i, false) * C (H i j) := by
  simp [eulD, pderiv_X, Pi.single_apply, ite_and, Finset.sum_ite_eq]

theorem eulD_X_true (H : Matrix (Fin n) (Fin n) ℂ) (a : Fin m) (j : Fin n) :
    eulD H (X (a, j, true) : PX m n) = ∑ i, X (a, i, true) * C (star (H i j)) := by
  simp [eulD, pderiv_X, Pi.single_apply, ite_and, Finset.sum_ite_eq]

theorem eulH_gen (ε : Fin m → Bool) (H : Matrix (Fin n) (Fin n) ℂ) (k : Bool × Fin n × Fin n) :
    eulH H (gen ε k) ∈ Mon ε 1 := by
  have : eulH H (gen ε k) = ∑ l, C (H l k.2.2) * gen ε (k.1, k.2.1, l) + ∑ l, C (star (H l k.2.1)) * gen ε (k.1, l, k.2.2) := by
    obtain ⟨b, i, j⟩ := k
    rw [eulH_eq]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [gen, Qb, map_sum, Derivation.leibniz, smul_eq_mul, eulD_X_false, eulD_X_true, Finset.mul_sum]
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => by ring
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => by ring
  rw [this]
  refine add_mem (Submodule.sum_mem _ fun l _ => ?_) (Submodule.sum_mem _ fun l _ => ?_)
  · rw [← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[(k.1, k.2.1, l)], by simp, by simp⟩)
  · rw [← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[(k.1, l, k.2.2)], by simp, by simp⟩)

theorem eulH_mon (ε : Fin m → Bool) (H : Matrix (Fin n) (Fin n) ℂ) (d : ℕ) {M : PX m n} (hM : M ∈ Mon ε d) :
    eulH H M ∈ Mon ε d := by
  rw [eulH_eq]
  induction hM using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    induction l generalizing d with
    | nil => simp
    | cons k l ih =>
      simp only [List.map_cons, List.prod_cons, Derivation.leibniz, smul_eq_mul]
      simp only [List.length_cons] at hl
      have hd : l.length + 1 ≤ d := hl
      refine add_mem ?_ ?_
      · exact mon_mono ε hd (gen_mul_mon ε l.length k (ih l.length le_rfl))
      · have h1 := eulH_gen ε H k
        rw [eulH_eq] at h1
        have h2 : (l.map (gen ε)).prod ∈ Mon ε l.length := Submodule.subset_span ⟨l, le_rfl, rfl⟩
        rw [mul_comm ((l.map (gen ε)).prod)]
        exact mon_mono ε (by omega) (mon_mul ε h1 h2)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [(eulD H).map_smul]; exact Submodule.smul_mem _ _ hx

end PositivityTheory.Rg.Sw.AbsSt.CycP
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DerivativeVacuumDilations
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

theorem cnt_add (ε : Fin m → Bool) : cnt ε true + cnt ε false = m := by
  unfold cnt
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m))) (fun a => ε a = true)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  have h2 : (Finset.univ.filter fun a => ε a = false) = Finset.univ.filter fun a => ¬ ε a = true := by
    ext a; simp
  rw [h2]
  exact h

theorem bS_herm (X : Fin n → ℝ) (h : ℝ) {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) : (bS X h b).IsHermitian := by
  have hD : (diagonal (fun j => (Real.exp (-(h * X j)) : ℂ)))ᴴ = diagonal (fun j => (Real.exp (-(h * X j)) : ℂ)) := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext j
    exact Complex.conj_ofReal _
  unfold bS Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hD, hb.eq, Matrix.mul_assoc]

theorem derivative_vacuum_of_parts (hG : GaussPart) (hH : GroupPart) : DerivativeVacuumDilations := by
  intro m n ε c t p q e sL ρ hL X a hA y r
  obtain ⟨hadd, ha0, hup, hcont, hupmul, hdec, hconj, hcellinv, hdense, hF0⟩ := hH n X a hA
  obtain ⟨C, hC0, hcell⟩ := hL.cell
  have hpq : p + q = m := by
    rcases hL.sign with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
    · exact cnt_add ε
    · rw [add_comm]; exact cnt_add ε
  have hneg : ∀ h : ℝ, a (-h) * a h = 1 := by
    intro h; rw [← hadd, neg_add_cancel, ha0]

  have L1 : ∀ (Q : PX m n) (y : GR n), (mR y).toBlocks₂₁.det ≠ 0 →
      HasDerivAt (fun h => sL Q (y * a h)) (sL (dil c X Q) y) 0 := by
    intro Q y hy
    obtain ⟨y₁, g, b, hy₁, hb, hg, rfl⟩ := hdec y hy
    have hfun : (fun h => sL Q (y₁ * g * a h)) = fun h => (F0 p q e y₁ * C) *
        (Complex.exp (-((h * ((m : ℝ) * ∑ j, X j) : ℝ) : ℂ)) * secN ε c t Q (bS X h b)) := by
      funext h
      have e1 : y₁ * g * a h = (y₁ * a (-h)) * (a h * g * a h) := by
        calc y₁ * g * a h = y₁ * (a (-h) * a h) * g * a h := by rw [hneg, mul_one]
          _ = _ := by group
      have e2 : F0 p q e (y₁ * a (-h)) = F0 p q e y₁ * F0 p q e (a (-h)) := by
        rw [← hL.vac, hL.law 1 _ _ hy₁, hL.vac]
      have e3 : F0 p q e (a (-h)) = Complex.exp (-((h * ((m : ℝ) * ∑ j, X j) : ℝ) : ℂ)) := by
        rw [hF0, hpq]
      rw [e1, hL.law Q _ _ (hupmul y₁ hy₁ (-h)), e2, e3, hcell Q _ _ (bS_herm X h hb) (hconj g b hg h)]
      ring
    rw [hfun]
    have hv : sL (dil c X Q) (y₁ * g) = (F0 p q e y₁ * C) * secN ε c t (dil c X Q) b := by
      rw [hL.law _ _ _ hy₁, hcell _ _ _ hb hg]; ring
    rw [hv]
    exact (hG m n ε c t hL.cpos X b hb Q).const_mul _

  have L2 : ∀ (Q : PX m n) (y : GR n), (mR y).toBlocks₂₁.det ≠ 0 → ∀ s,
      HasDerivAt (fun h => sL Q (y * a h)) (sL (dil c X Q) (y * a s)) s := by
    intro Q y hy s
    have h0 := L1 Q (y * a s) (hcellinv y hy s)
    have h0' : HasDerivAt (fun h => sL Q (y * a s * a h)) (sL (dil c X Q) (y * a s)) (s - s) := by
      rw [sub_self]; exact h0
    have h1 := HasDerivAt.comp_sub_const s s h0'
    have hf : (fun x => sL Q (y * a x)) = fun x => sL Q (y * a s * a (x - s)) := by
      funext x
      rw [mul_assoc, ← hadd, add_sub_cancel]
    rw [hf]
    exact h1
  have hjc : ∀ (Q : PX m n), Continuous (fun z : GR n × ℝ => sL Q (z.1 * a z.2)) := fun Q =>
    (hL.cont Q).comp (continuous_fst.mul (hcont.comp continuous_snd))

  have L3 : ∀ (Q : PX m n) (s : ℝ) (y : GR n),
      sL Q (y * a s) - sL Q y = ∫ u in (0 : ℝ)..s, sL (dil c X Q) (y * a u) := by
    intro Q s
    have hc1 : Continuous fun y : GR n => sL Q (y * a s) - sL Q y :=
      ((hL.cont Q).comp (continuous_id.mul continuous_const)).sub (hL.cont Q)
    have hc2 : Continuous fun y : GR n => ∫ u in (0 : ℝ)..s, sL (dil c X Q) (y * a u) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (hjc (dil c X Q)) continuous_const
    intro y0
    refine congrFun (Continuous.ext_on hdense hc1 hc2 ?_) y0
    intro y hy
    show sL Q (y * a s) - sL Q y = ∫ u in (0 : ℝ)..s, sL (dil c X Q) (y * a u)
    have hd : ∀ x ∈ Set.uIcc (0 : ℝ) s, HasDerivAt (fun h => sL Q (y * a h)) (sL (dil c X Q) (y * a x)) x :=
      fun x _ => L2 Q y hy x
    have hint : IntervalIntegrable (fun u => sL (dil c X Q) (y * a u)) volume 0 s :=
      ((hL.cont (dil c X Q)).comp (continuous_const.mul hcont)).intervalIntegrable 0 s
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint, ha0, mul_one]
  have L4 : ∀ (Q : PX m n) (y : GR n) (s : ℝ),
      HasDerivAt (fun h => sL Q (y * a h)) (sL (dil c X Q) (y * a s)) s := by
    intro Q y s
    have hgc : Continuous fun u => sL (dil c X Q) (y * a u) := (hL.cont _).comp (continuous_const.mul hcont)
    have h1 := (hgc.integral_hasStrictDerivAt 0 s).hasDerivAt
    have h2 := h1.const_add (sL Q y)
    have hf : (fun h => sL Q (y * a h)) = fun x => sL Q y + ∫ u in (0 : ℝ)..x, sL (dil c X Q) (y * a u) := by
      funext x
      rw [← L3 Q x y]; ring
    rw [hf]
    exact h2
  have L5 : ∀ k : ℕ, iteratedDeriv k (fun s => F0 p q e (y * a s)) = fun s => sL ((dil c X ^ k) 1) (y * a s) := by
    intro k
    induction k with
    | zero => funext s; simp [hL.vac]
    | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      funext s
      rw [(L4 _ y s).deriv, pow_succ', Module.End.mul_apply]
  refine ⟨?_, ?_⟩
  · rw [L5 r]
    have := L4 ((dil c X ^ r) 1) y 0
    rw [ha0, mul_one, ← Module.End.mul_apply, ← pow_succ'] at this
    exact this
  · rw [L5 r]
    show sL ((dil c X ^ r) 1) (y * a 0) = _
    rw [ha0, mul_one]

end PositivityTheory.Rg.Sw.AbsSt.DF
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FlatEq
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

def FlatEq : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
    (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ → ∀ (Q Q' : PX m n),
    (∀ k : GR n, InK (mR k) → sL Q k = sL Q' k) → ∀ y, sL Q y = sL Q' y

def Basis : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
    (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ → ∀ [MeasurableSpace (KR n)] [BorelSpace (KR n)],
    ∀ W : Submodule ℂ (PX m n), FiniteDimensional ℂ W → (∀ k : GR n, InK (mR k) → ∀ Q ∈ W, ρ k Q ∈ W) →
    ∀ (ν : Measure (KR n)) (κ : KR n → ℂ), IsFiniteMeasure ν → Continuous κ →
      (∀ Q ∈ W, ∀ y : GR n, ∫ k, κ k * sL Q (y * (k : GR n)) ∂ν = sL Q y) →
      (∀ (w : ℂ) (f : GR n → ℂ), Continuous f →
          (∀ (y g : GR n), (mR y).toBlocks₂₁ = 0 → f (y * g) = (hLoc y : ℂ) ^ w * F0 p q e y * f g) →
          ∃ Q ∈ W, ∀ y : GR n, ∫ k, κ k * f (y * (k : GR n)) ∂ν = (hLoc y : ℂ) ^ w * sL Q y) →
      ∀ P ∈ W, ∃ (N : ℕ) (yy : Fin N → GR n) (QQ : Fin N → PX m n) (cc : Fin N → ℂ) (M : ℂ → Matrix (Fin N) (Fin N) ℂ),
        (∀ j, QQ j ∈ W) ∧ (∀ y, sL P y = ∑ j, cc j * sL (QQ j) y) ∧ M 0 = 1 ∧ (∀ i j, Differentiable ℂ fun w => M w i j) ∧
        (∀ i, ∀ y', ∫ k, κ k * F0 p q e (y' * (k : GR n) * yy i) ∂ν = sL (QQ i) y') ∧
        ∀ (w : ℂ) (i : Fin N) (y' : GR n), ∫ k, κ k * ((hLoc (y' * (k : GR n) * yy i) : ℂ) ^ w * F0 p q e (y' * (k : GR n) * yy i)) ∂ν =
          (hLoc y' : ℂ) ^ w * ∑ j, M w i j * sL (QQ j) y'

end PositivityTheory.Rg.Sw.AbsSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.IsEmbeddingEmbK
section
noncomputable section

open Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem inK_entry_le (M : M2 n) (hM : InK M) (i j : Fin n ⊕ Fin n) : ‖M i j‖ ≤ 1 := by
  exact entry_norm_bound_of_unitary (Matrix.mem_unitaryGroup_iff'.2 hM.2) i j

theorem isCompact_inK : IsCompact {M : M2 n | InK M} := by
  have hB : IsCompact (Set.pi univ fun _ : Fin n ⊕ Fin n => Set.pi univ fun _ : Fin n ⊕ Fin n =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hB.of_isClosed_subset ?_ ?_
  · have c1 : Continuous fun M : M2 n => Mᴴ * JJ n * M :=
      (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id
    have c2 : Continuous fun M : M2 n => Mᴴ * M := continuous_id.matrix_conjTranspose.matrix_mul continuous_id
    exact (isClosed_eq c1 continuous_const).inter (isClosed_eq c2 continuous_const)
  · intro M hM
    simp only [Set.mem_pi, Set.mem_univ, forall_const, Metric.mem_closedBall, dist_zero_right]
    intro i j
    exact inK_entry_le M hM i j

def embK (k : KR n) : M2 n × (M2 n)ᵐᵒᵖ := Units.embedProduct (M2 n) (k : GR n).1

theorem isEmbedding_embK : Topology.IsEmbedding (embK (n := n)) :=
  Units.isEmbedding_embedProduct.comp (Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal)

theorem range_embK : Set.range (embK (n := n)) = (fun M : M2 n => (M, MulOpposite.op Mᴴ)) '' {M | InK M} := by
  ext ⟨A, B⟩
  constructor
  · rintro ⟨k, hk⟩
    have hK : InK (mR (k : GR n)) := k.2
    have hinv : ((((k : GR n) : GL (Fin n ⊕ Fin n) ℂ)⁻¹ : GL (Fin n ⊕ Fin n) ℂ) : M2 n) =
        (mR (k : GR n))ᴴ :=
      Units.inv_eq_of_mul_eq_one_left hK.2
    refine ⟨mR (k : GR n), hK, ?_⟩
    rw [← hk]
    simp only [embK, Units.embedProduct_apply, hinv]
    rfl
  · rintro ⟨M, hM, hMAB⟩
    have hM' : M * Mᴴ = 1 := mul_eq_one_comm.1 hM.2
    let u : GL (Fin n ⊕ Fin n) ℂ := ⟨M, Mᴴ, hM', hM.2⟩
    let g : GR n := ⟨u, hM.1⟩
    have hg : g ∈ KR n := hM
    refine ⟨⟨g, hg⟩, ?_⟩
    rw [← hMAB]
    rfl

theorem isCompact_KR : IsCompact (univ : Set (KR n)) := by
  rw [isEmbedding_embK.isCompact_iff, Set.image_univ, range_embK]
  exact isCompact_inK.image (continuous_id.prodMk (MulOpposite.continuous_op.comp continuous_id.matrix_conjTranspose))

end PositivityTheory.Rg.Sw.AbsSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ProjSt
section
noncomputable section

open MeasureTheory Matrix Set

namespace PositivityTheory.Rg.Sw.AbsSt.Proj

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

def kM {n : ℕ} (a b : Matrix (Fin n) (Fin n) ℂ) : M2 n :=
  fromBlocks ((1 / 2 : ℂ) • (a + b)) ((Complex.I / 2) • (a - b)) (-((Complex.I / 2) • (a - b))) ((1 / 2 : ℂ) • (a + b))

def KIso : Prop := ∀ n : ℕ,
  (∀ a b : Matrix (Fin n) (Fin n) ℂ, a ∈ unitaryGroup (Fin n) ℂ → b ∈ unitaryGroup (Fin n) ℂ →
      ∃ k : GR n, k ∈ KR n ∧ mR k = kM a b) ∧
  (∀ a b a' b' : Matrix (Fin n) (Fin n) ℂ, kM a b * kM a' b' = kM (a * a') (b * b')) ∧ kM (1 : Matrix (Fin n) (Fin n) ℂ) 1 = 1 ∧
  (∀ a b : Matrix (Fin n) (Fin n) ℂ, u1 (kM a b) = a ∧ u2 (kM a b) = b) ∧
  (∀ a : Matrix (Fin n) (Fin n) ℂ, (kM a a).toBlocks₂₁ = 0) ∧
  ∀ k : GR n, k ∈ KR n → u1 (mR k) ∈ unitaryGroup (Fin n) ℂ ∧ u2 (mR k) ∈ unitaryGroup (Fin n) ℂ ∧
    mR k = kM (u1 (mR k)) (u2 (mR k))

def RepKer : Prop := ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [T2Space H]
  [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsHaarMeasure] (V : Submodule ℂ (H → ℂ)), FiniteDimensional ℂ V →
    (∀ φ ∈ V, Continuous φ) → (∀ φ ∈ V, ∀ a : H, (fun x => φ (a * x)) ∈ V) →
    ∃ κ : H → ℂ, Continuous κ ∧ (∀ f : H → ℂ, Continuous f → (fun x => ∫ v, κ v * f (x * v) ∂μ) ∈ V) ∧
      ∀ φ ∈ V, ∀ x, ∫ v, κ v * φ (x * v) ∂μ = φ x

end PositivityTheory.Rg.Sw.AbsSt.Proj
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecDerSt
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def NDer : Prop := ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
  (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ → ∀ (R : PX m n) (H : Matrix (Fin n) (Fin n) ℂ),
    H.IsHermitian → ∀ f : ℝ → GR n, (∀ σ : ℝ, mR (f σ) = nU ((σ : ℂ) • H)) → ∀ g : GR n,
      (mR g).toBlocks₂₁.det ≠ 0 → ∀ s : ℝ, HasDerivAt (fun σ : ℝ => sL R (g * f σ)) (sL (DN ε t H R) (g * f s)) s

def MDer : Prop := ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
  (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ → ∀ (R : PX m n) (H : Matrix (Fin n) (Fin n) ℂ),
    H.IsHermitian → ∀ f : ℝ → GR n,
      (∀ σ : ℝ, mR (f σ) = fromBlocks (NormedSpace.exp ((σ : ℂ) • H)) 0 0 (NormedSpace.exp (-((σ : ℂ) • H)))) →
      ∀ g : GR n, (mR g).toBlocks₂₁.det ≠ 0 → ∀ s : ℝ,
        HasDerivAt (fun σ : ℝ => sL R (g * f σ)) (sL (DM ε c H R) (g * f s)) s

end PositivityTheory.Rg.Sw.AbsSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ThSphC
section
noncomputable section

open Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

theorem anNhd_iter {f : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V) (hf : DifferentiableOn ℂ f V) (r : ℕ) :
    AnalyticOnNhd ℂ (iteratedDeriv r f) V := by
  rw [iteratedDeriv_eq_iterate]
  exact (hf.analyticOnNhd hV).iterated_deriv r

theorem real_iter (f : ℂ → ℂ) (V : Set ℂ) (hV : IsOpen V) (hR : ∀ s : ℝ, (s : ℂ) ∈ V)
    (hf : DifferentiableOn ℂ f V) (r : ℕ) :
    iteratedDeriv r (fun t : ℝ => f t) = fun s : ℝ => iteratedDeriv r f s := by
  induction r with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext s
    rw [iteratedDeriv_succ]
    have hd : DifferentiableAt ℂ (iteratedDeriv n f) (s : ℂ) :=
      ((anNhd_iter hV hf n) s (hR s)).differentiableAt
    exact hd.hasDerivAt.comp_ofReal.deriv

theorem helpC : HelpC := by
  refine ⟨fun f V hV hR hf r s => congrFun (real_iter f V hV hR hf r) s, ?_⟩
  intro f V hV hR hf h0 s
  have hA := hf.analyticOnNhd hV
  have h0V : (0 : ℂ) ∈ V := by simpa using hR 0
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV 0 h0V
  have hloc : f =ᶠ[𝓝 (0 : ℂ)] 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hε] with z hz
    rw [← Complex.taylorSeries_eq_on_ball' hz (hf.mono hball)]
    simp [h0]
  have hpre : IsPreconnected (Set.range ((↑) : ℝ → ℂ)) :=
    (isConnected_range Complex.continuous_ofReal).isPreconnected
  have hsub := hpre.subset_connectedComponentIn (x := (0 : ℂ)) ⟨0, by simp⟩
    (by rintro _ ⟨t, rfl⟩; exact hR t)
  have hEq := (hA.mono (connectedComponentIn_subset V 0)).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_connectedComponentIn (mem_connectedComponentIn h0V) hloc
  simpa using hEq (hsub ⟨s, rfl⟩)

end PositivityTheory.Rg.Sw.AbsSt
end
end

