module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.Bundle0004

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.AdjoinFirstOperatorsPreservesFamily
section
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC.Core

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

theorem pderiv_eq_zero_of_supported {S : Set (Fin m × Fin n × Bool)} {g : PX m n} (hg : g ∈ supported ℂ S)
    {k : Fin m × Fin n × Bool} (hk : k ∉ S) : pderiv k g = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro h
  exact hk ((mem_supported.mp hg) h)

theorem pderiv_mem_supported {S : Set (Fin m × Fin n × Bool)} {g : PX m n} (hg : g ∈ supported ℂ S)
    (k : Fin m × Fin n × Bool) : pderiv k g ∈ supported ℂ S := by
  rw [supported_eq_adjoin_X] at hg
  induction hg using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, -, rfl⟩ := hx
    rw [pderiv_X]
    rcases eq_or_ne i k with rfl | h
    · simp only [Pi.single_eq_same]; exact Subalgebra.one_mem _
    · rw [Pi.single_eq_of_ne h]; exact Subalgebra.zero_mem _
  | algebraMap r => simp [Subalgebra.zero_mem]
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Subalgebra.add_mem _ hx hy
  | mul x y hx' hy' hx hy =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    have hx'' : x ∈ supported ℂ S := by rw [supported_eq_adjoin_X]; exact hx'
    have hy'' : y ∈ supported ℂ S := by rw [supported_eq_adjoin_X]; exact hy'
    exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ hx'' hy) (Subalgebra.mul_mem _ hy'' hx)

theorem mem_F1_iff_supported (ε : Fin m → Bool) (f : PX m n) : f ∈ F1 ε ↔ f ∈ supported ℂ {k | inF1 ε k} := Iff.rfl

theorem variable_mem_first_family (ε : Fin m → Bool) {k : Fin m × Fin n × Bool} (hk : inF1 ε k) : (X k : PX m n) ∈ F1 ε :=
  (mem_F1_iff_supported ε _).2 (X_mem_supported.2 hk)

theorem compact_operator_mul_second_family (ε : Fin m → Bool) (i j : Fin n) (f g : PX m n) (hg : g ∈ F2 ε) :
    KopL ε i j (f * g) = KopL ε i j f * g := by
  have h0 : ∀ k : Fin m × Fin n × Bool, inF1 ε k → pderiv k g = 0 := fun k hk =>
    pderiv_eq_zero_of_supported hg (by simpa using hk)
  have hK : ∀ h : PX m n, KopL ε i j h = ∑ a ∈ Finset.univ.filter (fun a => ε a = true), X (a, i, false) * pderiv (a, j, false) h -
      ∑ a ∈ Finset.univ.filter (fun a => ε a = false), X (a, j, true) * pderiv (a, i, true) h := by
    intro h; simp [KopL, LinearMap.sum_apply]
  rw [hK, hK]
  simp only [Derivation.leibniz, smul_eq_mul]
  have e1 : ∀ a ∈ Finset.univ.filter (fun a => ε a = true),
      X (a, i, false) * (f * pderiv (a, j, false) g + g * pderiv (a, j, false) f) =
        X (a, i, false) * pderiv (a, j, false) f * g := by
    intro a ha
    rw [h0 (a, j, false) (by simp [inF1, (Finset.mem_filter.mp ha).2])]; ring
  have e2 : ∀ a ∈ Finset.univ.filter (fun a => ε a = false),
      X (a, j, true) * (f * pderiv (a, i, true) g + g * pderiv (a, i, true) f) =
        X (a, j, true) * pderiv (a, i, true) f * g := by
    intro a ha
    rw [h0 (a, i, true) (by simp [inF1, (Finset.mem_filter.mp ha).2])]; ring
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, ← Finset.sum_mul, ← Finset.sum_mul, sub_mul]

theorem compact_algebra_mul_second_family (ε : Fin m → Bool) (w : Module.End ℂ (PX m n)) (hw : w ∈ kAlg ε) (f g : PX m n) (hg : g ∈ F2 ε) :
    w (f * g) = w f * g := by
  induction hw using Algebra.adjoin_induction generalizing f with
  | mem x hx =>
    obtain ⟨ij, rfl⟩ := hx
    exact compact_operator_mul_second_family ε ij.1 ij.2 f g hg
  | algebraMap r => simp [Algebra.algebraMap_eq_smul_one, smul_mul_assoc]
  | add x y _ _ hx hy => simp [hx, hy, add_mul]
  | mul x y _ _ hx hy => simp only [Module.End.mul_apply, hy, hx]

theorem first_operator_preserves_first_family (ε : Fin m → Bool) (c : ℝ) (a b : Fin m) (f : PX m n) (hf : f ∈ F1 ε) : D1 ε c a b f ∈ F1 ε := by
  have hp : ∀ k (g : PX m n), g ∈ F1 ε → pderiv k g ∈ F1 ε := fun k g hg => pderiv_mem_supported hg k
  have hm : ∀ g h : PX m n, g ∈ F1 ε → h ∈ F1 ε → g * h ∈ F1 ε := fun g h hg hh => Subalgebra.mul_mem _ hg hh
  unfold D1
  split_ifs with h1 h2 h2
  · refine Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ => hm _ _ (variable_mem_first_family ε ?_) (hp _ _ hf))
    simp [inF1, h2]
  · refine Submodule.sum_mem _ fun i _ => hm _ _ (variable_mem_first_family ε ?_) (hp _ _ hf)
    simp [inF1, ← h1]; simpa using h2
  · refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
      hm _ _ (hm _ _ (variable_mem_first_family ε ?_) (variable_mem_first_family ε ?_)) hf)
    · simp [inF1, h2]
    · simp [inF1]; cases hb : ε b <;> simp_all
  · refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => hp _ _ (hp _ _ hf))

theorem adjoin_first_operators_preserves_family (ε : Fin m → Bool) (c : ℝ) (B : Module.End ℂ (PX m n)) (hBF : ∀ f ∈ F1 ε, B f ∈ F1 ε)
    (hB : ∀ a b, ∀ f ∈ F1 ε, B (D1 ε c a b f) = D1 ε c a b (B f)) (w : Module.End ℂ (PX m n))
    (hw : w ∈ Algebra.adjoin ℂ (Set.range fun ab : Fin m × Fin m => firstFamilyOperatorEnd (n := n) ε c ab.1 ab.2)) :
    (∀ f ∈ F1 ε, w f ∈ F1 ε) ∧ ∀ f ∈ F1 ε, B (w f) = w (B f) := by
  induction hw using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨ab, rfl⟩ := hx
    exact ⟨fun f hf => first_operator_preserves_first_family ε c ab.1 ab.2 f hf, fun f hf => hB ab.1 ab.2 f hf⟩
  | algebraMap r =>
    refine ⟨fun f hf => by simpa [Algebra.algebraMap_eq_smul_one] using Submodule.smul_mem _ r hf, fun f _ => ?_⟩
    simp [Algebra.algebraMap_eq_smul_one]
  | add x y _ _ hx hy =>
    exact ⟨fun f hf => by simpa using Submodule.add_mem _ (hx.1 f hf) (hy.1 f hf),
      fun f hf => by simp [hx.2 f hf, hy.2 f hf]⟩
  | mul x y _ _ hx hy =>
    exact ⟨fun f hf => hx.1 _ (hy.1 f hf), fun f hf => by
      simp only [Module.End.mul_apply]; rw [hx.2 _ (hy.1 f hf), hy.2 f hf]⟩

end PositivityTheory.Rg.Sw.LC.Core
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.DiagApply
section
noncomputable section

namespace PositivityTheory.Rg.Sw.LC

namespace CoreA

variable {V : Type} [AddCommGroup V] [Module ℂ V] {φ : V → V → ℂ}

theorem adj_closed (h : PosH φ) {ι : Type} (T : ι → Module.End ℂ V)
    (hT : ∀ i, ∃ j, ∀ v w, φ (T i v) w = φ v (T j w)) :
    ∀ s ∈ Algebra.adjoin ℂ (Set.range T), ∃ s' ∈ Algebra.adjoin ℂ (Set.range T), ∀ v w, φ (s v) w = φ v (s' w) := by
  intro s hs
  induction hs using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, hj⟩ := hT i
    exact ⟨T j, Algebra.subset_adjoin ⟨j, rfl⟩, hj⟩
  | algebraMap r =>
    refine ⟨algebraMap ℂ _ (star r), Subalgebra.algebraMap_mem _ _, fun v w => ?_⟩
    simp only [Module.algebraMap_end_apply]
    rw [h.smul_left, h.smul]
  | add x y _ _ hx hy =>
    obtain ⟨x', hx', hx''⟩ := hx
    obtain ⟨y', hy', hy''⟩ := hy
    refine ⟨x' + y', add_mem hx' hy', fun v w => ?_⟩
    simp only [LinearMap.add_apply]
    rw [h.add_left, hx'', hy'', h.add]
  | mul x y _ _ hx hy =>
    obtain ⟨x', hx', hx''⟩ := hx
    obtain ⟨y', hy', hy''⟩ := hy
    refine ⟨y' * x', mul_mem hy' hx', fun v w => ?_⟩
    simp only [Module.End.mul_apply]
    rw [hx'', hy'']

theorem orbit [FiniteDimensional ℂ V] (h : PosH φ) {ι : Type} (T : ι → Module.End ℂ V)
    (hT : ∀ i, ∃ j, ∀ v w, φ (T i v) w = φ v (T j w)) (x : Module.End ℂ V)
    (hx : ∀ t : Module.End ℂ V, (∀ i, t * T i = T i * t) → x * t = t * x) (v : V) :
    ∃ s ∈ Algebra.adjoin ℂ (Set.range T), x v = s v := by
  classical
  set S := Algebra.adjoin ℂ (Set.range T) with hS
  let M : Submodule ℂ V := (Subalgebra.toSubmodule S).map (LinearMap.applyₗ v)
  have hM : ∀ y, y ∈ M ↔ ∃ s ∈ S, s v = y := by
    intro y
    simp [M, Submodule.mem_map]
  have hMinv : ∀ s ∈ S, ∀ y ∈ M, s y ∈ M := by
    intro s hs y hy
    obtain ⟨t, ht, rfl⟩ := (hM y).1 hy
    exact (hM _).2 ⟨s * t, mul_mem hs ht, rfl⟩
  have hNinv : ∀ s ∈ S, ∀ u ∈ h.perp M, s u ∈ h.perp M := by
    intro s hs u hu m hm
    obtain ⟨s', hs', hs''⟩ := adj_closed h T hT s hs
    rw [h.herm (s u) m, hs'' u m, h.herm (s' m) u, star_star, hu _ (hMinv s' hs' m hm)]
  have hc : IsCompl M (h.perp M) := IsCompl.of_eq (h.inf_perp M) (h.sup_perp M)
  let P : Module.End ℂ V := M.subtype ∘ₗ Submodule.projectionOnto M (h.perp M) hc
  have hPdec : ∀ m ∈ M, ∀ u ∈ h.perp M, P (m + u) = m := by
    intro m hm u hu
    have e1 : Submodule.projectionOnto M (h.perp M) hc m = ⟨m, hm⟩ :=
      Submodule.projectionOnto_apply_left hc ⟨m, hm⟩
    have e2 : Submodule.projectionOnto M (h.perp M) hc u = 0 :=
      Submodule.projectionOnto_apply_right hc ⟨u, hu⟩
    simp only [P, LinearMap.comp_apply, map_add (f := _), e1, e2]
    simp
  have hdec : ∀ y : V, ∃ m ∈ M, ∃ u ∈ h.perp M, y = m + u := by
    intro y
    have hy : y ∈ M ⊔ h.perp M := by rw [h.sup_perp]; trivial
    obtain ⟨m, hm, u, hu, e⟩ := Submodule.mem_sup.1 hy
    exact ⟨m, hm, u, hu, e.symm⟩
  have hPT : ∀ i, P * T i = T i * P := by
    intro i
    have hTi : T i ∈ S := Algebra.subset_adjoin ⟨i, rfl⟩
    refine LinearMap.ext fun y => ?_
    obtain ⟨m, hm, u, hu, rfl⟩ := hdec y
    simp only [Module.End.mul_apply]
    rw [map_add (T i), hPdec _ (hMinv _ hTi m hm) _ (hNinv _ hTi u hu), hPdec m hm u hu]
  have hxP := hx P hPT
  have hvM : v ∈ M := (hM v).2 ⟨1, Subalgebra.one_mem S, rfl⟩
  have hPv : P v = v := by simpa using hPdec v hvM 0 (Submodule.zero_mem _)
  have hxv : x v = P (x v) := by
    rw [← Module.End.mul_apply, ← hxP, Module.End.mul_apply, hPv]
  have hmem : P (x v) ∈ M := by
    simp only [P, LinearMap.comp_apply, Submodule.subtype_apply]
    exact Submodule.coe_mem _
  obtain ⟨s, hs, hsv⟩ := (hM _).1 hmem
  exact ⟨s, hs, by rw [hxv, ← hsv]⟩

def diag (d : ℕ) : Module.End ℂ V →ₐ[ℂ] Module.End ℂ (Fin d → V) where
  toFun f := LinearMap.pi fun k => f ∘ₗ LinearMap.proj k
  map_one' := LinearMap.ext fun w => funext fun k => by simp
  map_mul' f g := LinearMap.ext fun w => funext fun k => by simp
  map_zero' := LinearMap.ext fun w => funext fun k => by simp
  map_add' f g := LinearMap.ext fun w => funext fun k => by simp
  commutes' r := LinearMap.ext fun w => funext fun k => by simp

theorem diag_apply (d : ℕ) (f : Module.End ℂ V) (w : Fin d → V) (k : Fin d) : diag d f w k = f (w k) := by
  simp [diag]

def amp (φ : V → V → ℂ) (d : ℕ) (v w : Fin d → V) : ℂ := ∑ k, φ (v k) (w k)

theorem amp_posH (h : PosH φ) (d : ℕ) : PosH (amp φ d) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v w₁ w₂
    simp only [amp, Pi.add_apply, h.add, Finset.sum_add_distrib]
  · intro v w r
    simp only [amp, Pi.smul_apply, h.smul, Finset.mul_sum]
  · intro v w
    simp only [amp, star_sum, ← h.herm]
  · intro v hv
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hv
    simp only [amp, Complex.re_sum]
    calc 0 < (φ (v k) (v k)).re := h.pos _ hk
      _ ≤ ∑ l, (φ (v l) (v l)).re :=
        Finset.single_le_sum (f := fun l => (φ (v l) (v l)).re) (fun l _ => h.re_nonneg _) (Finset.mem_univ k)

end CoreA

open CoreA in
theorem bicomm : Bicomm := by
  intro V _ _ _ φ hadd hsmul hherm hpos ι T hT x hx
  classical
  have h : PosH φ := ⟨hadd, hsmul, hherm, hpos⟩
  set d := Module.finrank ℂ V
  let e := Module.finBasis ℂ V
  let T' : ι → Module.End ℂ (Fin d → V) := fun i => diag d (T i)
  have hT' : ∀ i, ∃ j, ∀ v w, amp φ d (T' i v) w = amp φ d v (T' j w) := by
    intro i
    obtain ⟨j, hj⟩ := hT i
    exact ⟨j, fun v w => by simp only [amp, T', diag_apply, hj]⟩
  have hx' : ∀ t : Module.End ℂ (Fin d → V), (∀ i, t * T' i = T' i * t) → diag d x * t = t * diag d x := by
    intro t ht
    let tt : Fin d → Fin d → Module.End ℂ V := fun k l => LinearMap.proj k ∘ₗ t ∘ₗ LinearMap.single ℂ (fun _ => V) l
    have htt : ∀ k l, x * tt k l = tt k l * x := by
      intro k l
      apply hx
      intro i
      refine LinearMap.ext fun u => ?_
      have hs : (Pi.single l (T i u) : Fin d → V) = T' i (Pi.single l u) := by
        funext l'
        simp only [T', diag_apply]
        by_cases hl : l' = l
        · subst hl; simp
        · simp [Pi.single_apply, hl]
      have := LinearMap.congr_fun (ht i) (Pi.single l u)
      simp only [Module.End.mul_apply] at this
      simp only [Module.End.mul_apply, tt, LinearMap.comp_apply, LinearMap.coe_single, LinearMap.coe_proj,
        Function.eval, hs, this]
      simp [T', diag_apply]
    have hsum : ∀ w : Fin d → V, ∀ k, t w k = ∑ l, tt k l (w l) := by
      intro w k
      conv_lhs => rw [← Finset.univ_sum_single w]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [tt, map_sum]
    refine LinearMap.ext fun w => funext fun k => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Module.End.mul_apply, diag_apply, hsum, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    exact LinearMap.congr_fun (htt k l) (w l)
  obtain ⟨s', hs', hs'E⟩ := orbit (amp_posH h d) T' hT' (diag d x) hx' (fun k => e k)
  have hmap : Algebra.adjoin ℂ (Set.range T') = (Algebra.adjoin ℂ (Set.range T)).map (diag d) := by
    rw [AlgHom.map_adjoin, ← Set.range_comp]
    rfl
  rw [hmap] at hs'
  obtain ⟨s, hs, rfl⟩ := Subalgebra.mem_map.1 hs'
  have hxs : x = s := by
    refine e.ext fun k => ?_
    have := congrFun hs'E k
    simpa [diag_apply] using this
  rw [hxs]
  exact hs

end PositivityTheory.Rg.Sw.LC
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.FirstFamilySymbolMulVariablePow
section
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ} {ε : Fin m → Bool}

def Good (ε : Fin m → Bool) (d : ℕ) (r : Sym m n) : Prop := SymbolInFirstFamily ε r ∧ EtaLt r d

theorem good_zero (d : ℕ) : Good ε d (0 : Sym m n) := by
  constructor <;> intro t ht <;> simp at ht

theorem good_add {d : ℕ} {r₁ r₂ : Sym m n} (h₁ : Good ε d r₁) (h₂ : Good ε d r₂) : Good ε d (r₁ + r₂) := by
  classical
  constructor
  · intro t ht k hk
    rcases Finset.mem_union.1 (MvPolynomial.support_add ht) with h | h
    · exact h₁.1 t h k hk
    · exact h₂.1 t h k hk
  · intro t ht
    rcases Finset.mem_union.1 (MvPolynomial.support_add ht) with h | h
    · exact h₁.2 t h
    · exact h₂.2 t h

theorem good_smul {d : ℕ} {r : Sym m n} (a : ℂ) (h : Good ε d r) : Good ε d (a • r) :=
  ⟨fun t ht => h.1 t (MvPolynomial.support_smul ht), fun t ht => h.2 t (MvPolynomial.support_smul ht)⟩

theorem good_sum {ι : Type*} (S : Finset ι) {d : ℕ} (r : ι → Sym m n) (h : ∀ i ∈ S, Good ε d (r i)) :
    Good ε d (∑ i ∈ S, r i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using good_zero d
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    exact good_add (h a (Finset.mem_insert_self a S)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem mem_support_mul_monomial {p : Sym m n} {s t' : Ix m n ⊕ Ix m n →₀ ℕ} {a : ℂ}
    (h : t' ∈ (p * monomial s a).support) : ∃ t ∈ p.support, t' = t + s := by
  rw [MvPolynomial.mem_support_iff, coeff_mul_monomial'] at h
  split_ifs at h with hs
  · refine ⟨t' - s, ?_, (tsub_add_cancel_of_le hs).symm⟩
    rw [MvPolynomial.mem_support_iff]
    intro h0; rw [h0, zero_mul] at h; exact h rfl
  · exact absurd rfl h

theorem good_mul_monomial {d e : ℕ} {r : Sym m n} (h : Good ε d r) (s : Ix m n ⊕ Ix m n →₀ ℕ)
    (hs : ∀ k, (s (Sum.inl k) ≠ 0 ∨ s (Sum.inr k) ≠ 0) → inF1 ε k) (he : (∑ k, s (Sum.inr k)) ≤ e) :
    Good ε (d + e) (r * monomial s 1) := by
  constructor
  · intro t' ht' k hk
    obtain ⟨t, ht, rfl⟩ := mem_support_mul_monomial ht'
    simp only [Finsupp.add_apply, ne_eq, Nat.add_eq_zero_iff, not_and_or] at hk
    by_cases h1 : t (Sum.inl k) ≠ 0 ∨ t (Sum.inr k) ≠ 0
    · exact h.1 t ht k h1
    · push_neg at h1
      apply hs k
      rcases hk with hk | hk
      · rcases hk with hk | hk
        · exact absurd h1.1 hk
        · exact Or.inl hk
      · rcases hk with hk | hk
        · exact absurd h1.2 hk
        · exact Or.inr hk
  · intro t' ht'
    obtain ⟨t, ht, rfl⟩ := mem_support_mul_monomial ht'
    simp only [Finsupp.add_apply, Finset.sum_add_distrib]
    exact add_lt_add_of_lt_of_le (h.2 t ht) he

theorem mem_support_pderiv {u : Sym m n} {i : Ix m n ⊕ Ix m n} {t' : Ix m n ⊕ Ix m n →₀ ℕ}
    (h : t' ∈ (pderiv i u).support) : ∃ t ∈ u.support, t i ≠ 0 ∧ t = t' + Finsupp.single i 1 := by
  classical
  have hu : pderiv i u = ∑ t ∈ u.support, monomial (t - Finsupp.single i 1) (AddMonoidAlgebra.coeff u t * (t i : ℂ)) := by
    conv_lhs => rw [u.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [pderiv_monomial]
  rw [MvPolynomial.mem_support_iff, hu, coeff_sum] at h
  obtain ⟨t, ht, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [coeff_monomial] at hne
  split_ifs at hne with heq
  · have hti : t i ≠ 0 := by
      intro h0; rw [h0] at hne; simp at hne
    refine ⟨t, ht, hti, ?_⟩
    rw [← heq, tsub_add_cancel_of_le]
    rw [Finsupp.single_le_iff]; omega
  · exact absurd rfl hne

theorem good_pderiv {d : ℕ} {u : Sym m n} (hu : SymbolInFirstFamily ε u) (hue : EtaLe u d) (k : Ix m n) :
    Good ε d (pderiv (Sum.inr k) u) := by
  constructor
  · intro t' ht' j hj
    obtain ⟨t, ht, -, rfl⟩ := mem_support_pderiv ht'
    apply hu _ ht j
    simp only [Finsupp.add_apply, ne_eq] at hj ⊢
    omega
  · intro t' ht'
    obtain ⟨t, ht, hti, rfl⟩ := mem_support_pderiv ht'
    have h1 := hue _ ht
    have h3 : ∑ j, t' (Sum.inr j) + 1 ≤ d := by
      simpa [Finsupp.add_apply, Finset.sum_add_distrib, Finsupp.single_apply] using h1
    omega

theorem good_le {d : ℕ} {r : Sym m n} (h : Good ε d r) : EtaLe r d := fun t ht => (h.2 t ht).le

theorem first_family_symbol_mul_variable_pow {u : Sym m n} (hu : SymbolInFirstFamily ε u) {a : Ix m n} (ha : inF1 ε a) (b : ℕ) :
    SymbolInFirstFamily ε (u * X (Sum.inl a) ^ b) ∧ ∀ d, EtaLe u d → EtaLe (u * X (Sum.inl a) ^ b) d := by
  have hs : ∀ k, ((Finsupp.single (Sum.inl a) b : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inl k) ≠ 0 ∨
      (Finsupp.single (Sum.inl a) b : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k) ≠ 0) → inF1 ε k := by
    intro k hk
    simp only [Finsupp.single_apply, Sum.inl.injEq, reduceCtorEq, if_false, ne_eq, not_true, or_false] at hk
    split_ifs at hk with h
    · subst h; exact ha
    · exact absurd rfl hk
  have h0 : (∑ k, (Finsupp.single (Sum.inl a) b : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k)) ≤ 0 := by
    simp [Finsupp.single_apply]
  rw [X_pow_eq_monomial]
  refine ⟨?_, fun d hd => ?_⟩
  · intro t ht k hk
    obtain ⟨t0, ht0, rfl⟩ := mem_support_mul_monomial ht
    simp only [Finsupp.add_apply, ne_eq, Nat.add_eq_zero_iff, not_and_or] at hk
    by_cases h1 : t0 (Sum.inl k) ≠ 0 ∨ t0 (Sum.inr k) ≠ 0
    · exact hu t0 ht0 k h1
    · push_neg at h1
      apply hs k
      rcases hk with hk | hk
      · rcases hk with hk | hk
        · exact absurd h1.1 hk
        · exact Or.inl hk
      · rcases hk with hk | hk
        · exact absurd h1.2 hk
        · exact Or.inr hk
  · intro t ht
    obtain ⟨t0, ht0, rfl⟩ := mem_support_mul_monomial ht
    simp only [Finsupp.add_apply, Finset.sum_add_distrib]
    calc _ ≤ d + 0 := add_le_add (hd t0 ht0) h0
      _ = d := add_zero d

end PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.PartialDerivQuadraticPairing
section
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC.NullS

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

abbrev QA (ε : Fin m → Bool) : Subalgebra ℂ (PX m n) :=
  Algebra.adjoin ℂ (Set.range fun ij : Fin n × Fin n => (Qp ε ij.1 ij.2 : PX m n))

theorem sgn_mul_self (ε : Fin m → Bool) (a : Fin m) : sgn ε a * sgn ε a = 1 := by
  unfold sgn; split_ifs <;> norm_num

theorem Qp_eq (ε : Fin m → Bool) (i j : Fin n) :
    Qp ε i j = ∑ a, C (sgn ε a) * (X (a, i, true) * X (a, j, false)) := by
  unfold Qp Qb
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  unfold sgn; cases ε a <;> simp

theorem Qp_mem (ε : Fin m → Bool) (i j : Fin n) : (Qp ε i j : PX m n) ∈ QA ε :=
  Algebra.subset_adjoin ⟨(i, j), rfl⟩

theorem pd_Qp_f (ε : Fin m → Bool) (a : Fin m) (i k l : Fin n) :
    pderiv (a, i, false) (Qp ε k l : PX m n) = if l = i then C (sgn ε a) * X (a, k, true) else 0 := by
  rw [Qp_eq]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply]
  by_cases h : l = i <;> simp [h]

theorem partial_deriv_quadratic_pairing (ε : Fin m → Bool) (a : Fin m) (j k l : Fin n) :
    pderiv (a, j, true) (Qp ε k l : PX m n) = if k = j then C (sgn ε a) * X (a, l, false) else 0 := by
  rw [Qp_eq]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply]
  by_cases h : k = j <;> simp [h]

end PositivityTheory.Rg.Sw.LC.NullS
end
end

