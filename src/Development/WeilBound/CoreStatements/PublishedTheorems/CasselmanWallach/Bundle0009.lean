module

public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CasimirNonnegativeSymmetric
section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

namespace PositivityTheory.CW.SeminormApproximation

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)} {E : Type} [AddCommGroup E] [Module ℂ E]

theorem sup_bound {p : ℕ → Seminorm ℂ E} {T : H →ₗ[ℂ] E} (hT : SobBdOn ε σ (Sm ε σ) p T) (s : Finset ℕ) :
    ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧
      ∀ x, Sm ε σ x → s.sup p (T x) ≤ C * sobNorm σ S x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · refine ⟨[], 0, fun l hl => by simp at hl, le_refl _, fun x _ => ?_⟩
    simp [Seminorm.bot_eq_zero]
  · intro i s _ ih
    obtain ⟨S, C, hS, hC, h⟩ := ih
    obtain ⟨S', C', hS', h'⟩ := hT i
    refine ⟨S' ++ S, |C'| + C, words_append hS' hS, by positivity, fun x hx => ?_⟩
    rw [Finset.sup_insert, Seminorm.sup_apply, sobNorm_append]
    have e1 := h x hx
    have e2 := h' x hx
    have a := sobNorm_nonneg σ S x
    have b := sobNorm_nonneg σ S' x
    have c1 := mul_nonneg (abs_nonneg C') a
    have c2 := mul_nonneg hC b
    have c3 := mul_nonneg hC a
    have c4 := mul_nonneg (abs_nonneg C') b
    have c5 := mul_le_mul_of_nonneg_right (le_abs_self C') b
    refine max_le ?_ ?_
    · nlinarith
    · nlinarith

theorem q_bound {p : ℕ → Seminorm ℂ E} [TopologicalSpace E] (hp : WithSeminorms p) {T : H →ₗ[ℂ] E}
    (hT : SobBdOn ε σ (Sm ε σ) p T) (Q : Seminorm ℂ E) (hQ : Continuous Q) :
    ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧
      ∀ x, Sm ε σ x → Q (T x) ≤ C * sobNorm σ S x := by
  obtain ⟨s, C', -, hle⟩ := Seminorm.bound_of_continuous hp Q hQ
  obtain ⟨S, C, hS, hC, h⟩ := sup_bound hT s
  refine ⟨S, C' * C, hS, mul_nonneg (NNReal.coe_nonneg C') hC, fun x hx => ?_⟩
  have h1 : Q (T x) ≤ (C' • s.sup p) (T x) := hle (T x)
  rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul] at h1
  calc Q (T x) ≤ C' * s.sup p (T x) := h1
    _ ≤ C' * (C * sobNorm σ S x) := mul_le_mul_of_nonneg_left (h x hx) (NNReal.coe_nonneg C')
    _ = _ := by ring

theorem approx (hD : Dens ε σ) {p : ℕ → Seminorm ℂ E} [TopologicalSpace E] (hp : WithSeminorms p)
    {T : H →ₗ[ℂ] E} (hT : SobBdOn ε σ (Sm ε σ) p T) (Q : Seminorm ℂ E) (hQ : Continuous Q) (l : List (Mx n))
    (hl : ∀ X ∈ l, X ∈ lieSet ε) (y : H) (hy : Sm ε σ y) (δ : ℝ) (hδ : 0 < δ) :
    ∃ v, IsKFin ε σ v ∧ Q (T (y - v)) ≤ δ ∧ ‖y - v‖ ≤ δ ∧ ‖Dw σ l (y - v)‖ ≤ δ := by
  obtain ⟨S, C, hS, hC, h⟩ := q_bound hp hT Q hQ
  have hW : Words (lieSet ε) (S ++ [l, []]) := by
    intro m hm X hX
    rcases List.mem_append.1 hm with hm | hm
    · exact hS m hm X hX
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · exact hl X hX
      · simp at hX
  have hC1 : 0 < C + 1 := by linarith
  obtain ⟨v, hv, hlt⟩ := hD.2.2 y hy (S ++ [l, []]) hW (δ / (C + 1)) (div_pos hδ hC1)
  have hsm : Sm ε σ (y - v) := sm_iff.2 ((smooth (Jm ε) σ).sub_mem (sm_iff.1 hy) (sm_iff.1 (hD.1 v hv)))
  have e : sobNorm σ (S ++ [l, []]) (y - v) = sobNorm σ S (y - v) + (‖Dw σ l (y - v)‖ + ‖y - v‖) := by
    rw [sobNorm_append]
    congr 1
    simp [sobNorm]
  rw [e] at hlt
  have a := sobNorm_nonneg σ S (y - v)
  have n1 := norm_nonneg (Dw σ l (y - v))
  have n2 := norm_nonneg (y - v)
  have hρ : δ / (C + 1) ≤ δ := div_le_self hδ.le (by linarith)
  have hCρ : C * (δ / (C + 1)) ≤ δ := by
    have : (C + 1) * (δ / (C + 1)) = δ := by field_simp
    nlinarith [div_pos hδ hC1]
  refine ⟨v, hv, ?_, by linarith, by linarith⟩
  calc Q (T (y - v)) ≤ C * sobNorm σ S (y - v) := h _ hsm
    _ ≤ C * (δ / (C + 1)) := mul_le_mul_of_nonneg_left (by linarith) hC
    _ ≤ δ := hCρ

end PositivityTheory.CW.SeminormApproximation

namespace PositivityTheory.CW

open SeminormApproximation in
theorem e2d : SobolevBoundedPairing := by
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ hD T hT Q hQ l η C hl
  have hp := hπ.withSeminorms
  refine ⟨fun h y hy => ?_, fun h y hy => ?_⟩
  · refine le_of_forall_pos_le_add fun e he => ?_
    have hK : 0 < |C| + ‖η‖ + 1 := by positivity
    obtain ⟨v, hv, h1, h2, -⟩ := approx hD hp hT Q hQ l hl y hy (e / (|C| + ‖η‖ + 1)) (div_pos he hK)
    have hv' := h v hv
    have i1 : ‖⟪η, y⟫_ℂ‖ ≤ ‖⟪η, v⟫_ℂ‖ + ‖η‖ * ‖y - v‖ := by
      have : ⟪η, y⟫_ℂ = ⟪η, v⟫_ℂ + ⟪η, y - v⟫_ℂ := by rw [inner_sub_right]; ring
      rw [this]
      exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_inner_le_norm _ _))
    have i2 : |Q (T v) - Q (T y)| ≤ Q (T (y - v)) := by
      rw [show T (y - v) = T y - T v from map_sub T y v, abs_sub_comm]
      exact abs_sub_map_le_sub Q (T y) (T v)
    have i3 : C * (Q (T v) - Q (T y)) ≤ |C| * Q (T (y - v)) := by
      have := le_abs_self (C * (Q (T v) - Q (T y)))
      rw [abs_mul] at this
      exact this.trans (mul_le_mul_of_nonneg_left i2 (abs_nonneg C))
    have i4 : C * Q (T v) = C * Q (T y) + C * (Q (T v) - Q (T y)) := by ring
    have i5 : |C| * Q (T (y - v)) + ‖η‖ * ‖y - v‖ ≤ e := by
      calc |C| * Q (T (y - v)) + ‖η‖ * ‖y - v‖
          ≤ |C| * (e / (|C| + ‖η‖ + 1)) + ‖η‖ * (e / (|C| + ‖η‖ + 1)) :=
            add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg C)) (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
        _ = (|C| + ‖η‖) * (e / (|C| + ‖η‖ + 1)) := by ring
        _ ≤ (|C| + ‖η‖ + 1) * (e / (|C| + ‖η‖ + 1)) :=
            mul_le_mul_of_nonneg_right (by linarith) (div_pos he hK).le
        _ = e := by field_simp
    linarith
  · refine le_of_forall_pos_le_add fun e he => ?_
    obtain ⟨v, hv, h1, -, h3⟩ := approx hD hp hT Q hQ l hl y hy (e / 2) (by positivity)
    have hv' := h v hv
    have hsm : Sm ε σ (y - v) := sm_iff.2 ((smooth (Jm ε) σ).sub_mem (sm_iff.1 hy) (sm_iff.1 (hD.1 v hv)))
    have hsplit : Dw σ l y = Dw σ l (y - v) + Dw σ l v := by
      have := Dw_add hU hl hsm (hD.1 v hv)
      rwa [sub_add_cancel] at this
    have i1 : ‖Dw σ l y‖ ≤ ‖Dw σ l (y - v)‖ + ‖Dw σ l v‖ := by
      rw [hsplit]; exact norm_add_le _ _
    have i2 : Q (T v) ≤ Q (T y) + Q (T (y - v)) := by
      have := map_sub_le_add Q (T y) (T (y - v))
      have e2 : T y - T (y - v) = T v := by rw [map_sub T y v, sub_sub_cancel]
      rwa [e2] at this
    linarith

end PositivityTheory.CW

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.DerivativeContinuity
section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open ReciprocityTheory.ChartRestriction.DS (actM casimirK)

namespace PositivityTheory.CW.WeightedRepresentationMul

variable {n : ℕ}

theorem actM_add {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (X Y : Mx n) :
    actM E (X + Y) = actM E X + actM E Y := by
  simp [actM, add_smul, Finset.sum_add_distrib]

theorem actM_smul {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (c : ℂ)
    (X : Mx n) : actM E (c • X) = c • actM E X := by
  simp [actM, smul_smul, Finset.smul_sum]

theorem actM_single {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (a b : Fin n) :
    actM E (Matrix.single a b (1 : ℂ)) = E a b := by
  unfold actM
  rw [Finset.sum_eq_single a (fun a' _ h => Finset.sum_eq_zero fun b' _ => by
    simp [Ne.symm h]) (by simp)]
  rw [Finset.sum_eq_single b (fun b' _ h => by simp [Ne.symm h]) (by simp)]
  simp

variable {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

def WRep (ε : Fin n → Bool) (σ : Mx n → (H →L[ℂ] H)) (u : Module.End ℂ (kfin ε σ)) : Prop :=
  ∃ L : List (ℂ × List (Mx n)), (∀ p ∈ L, ∀ X ∈ p.2, X ∈ lieSet ε) ∧
    ∀ v : kfin ε σ, ((u v : kfin ε σ) : H) = (L.map fun p => p.1 • Dw σ p.2 (v : H)).sum

theorem wrep_one : WRep ε σ 1 :=
  ⟨[(1, [])], by simp, fun v => by simp⟩

theorem wrep_zero : WRep ε σ 0 :=
  ⟨[], by simp, fun v => by simp⟩

theorem wrep_add {u w : Module.End ℂ (kfin ε σ)} (hu : WRep ε σ u) (hw : WRep ε σ w) : WRep ε σ (u + w) := by
  obtain ⟨L, hL, hLv⟩ := hu
  obtain ⟨L', hL', hLv'⟩ := hw
  refine ⟨L ++ L', fun p hp => (List.mem_append.1 hp).elim (hL p) (hL' p), fun v => ?_⟩
  rw [LinearMap.add_apply, Submodule.coe_add, hLv, hLv', List.map_append, List.sum_append]

theorem wrep_mul_E (hU : IsURepOn (UJset ε) σ) (hD : Dens ε σ) {E : Fin n → Fin n → Module.End ℂ (kfin ε σ)}
    (hE : KDer ε σ E) {u : Module.End ℂ (kfin ε σ)} (hu : WRep ε σ u) (a b : Fin n) : WRep ε σ (u * E a b) := by
  obtain ⟨L, hL, hLv⟩ := hu
  set Z : Mx n := Matrix.single a b 1
  obtain ⟨h1, h2, h3, -⟩ := Formalism.REAL.complex_parts_mem_lie_algebra_holds n ε Z
  set X1 := Formalism.REAL.cpart1 ε Z
  set X2 := Formalism.REAL.cpart2 ε Z
  have hX1 : X1 ∈ lieSet ε := h1
  have hX2 : X2 ∈ lieSet ε := h2
  have hEab : ∀ v : kfin ε σ, ((E a b v : kfin ε σ) : H) = dRep σ X1 v + Complex.I • dRep σ X2 v := by
    intro v
    have e : E a b = actM E X1 + Complex.I • actM E X2 := by
      rw [← actM_single E a b, ← actM_smul, ← actM_add]
      exact congrArg (actM E) h3
    rw [e, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul, hE X1 hX1 v,
      hE X2 hX2 v]
  let f : ℂ × List (Mx n) → List (ℂ × List (Mx n)) := fun p => [(p.1, p.2 ++ [X1]), (p.1 * Complex.I, p.2 ++ [X2])]
  refine ⟨L.flatMap f, ?_, fun v => ?_⟩
  · intro q hq X hX
    obtain ⟨p, hp, hq⟩ := List.mem_flatMap.1 hq
    simp only [f, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · rcases List.mem_append.1 hX with h | h
      · exact hL p hp X h
      · simp only [List.mem_singleton] at h; rw [h]; exact hX1
    · rcases List.mem_append.1 hX with h | h
      · exact hL p hp X h
      · simp only [List.mem_singleton] at h; rw [h]; exact hX2
  · have hv := v.2
    have hs1 : Sm ε σ (dRep σ X1 v) := hD.1 _ (hD.2.1 _ hv X1 hX1)
    have hs2 : Sm ε σ (dRep σ X2 v) := hD.1 _ (hD.2.1 _ hv X2 hX2)
    have hs2' : Sm ε σ (Complex.I • dRep σ X2 v) := hD.1 _ ((kfin ε σ).smul_mem Complex.I (hD.2.1 _ hv X2 hX2))
    have key : ∀ p ∈ L, p.1 • Dw σ p.2 ((E a b v : kfin ε σ) : H) =
        ((f p).map fun q => q.1 • Dw σ q.2 (v : H)).sum := by
      intro p hp
      have hl := hL p hp
      rw [hEab, Dw_add hU hl hs1 hs2', Dw_smul hU hl _ hs2]
      simp only [f, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Dw_append]
      rw [smul_add, smul_smul]
      rfl
    rw [Module.End.mul_apply, hLv]
    clear hLv
    induction L with
    | nil => simp
    | cons p L ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
        key p List.mem_cons_self, ih (fun q hq => hL q (List.mem_cons_of_mem _ hq))
          (fun q hq => key q (List.mem_cons_of_mem _ hq))]

theorem wrep_sum {ι : Type} (s : Finset ι) (g : ι → Module.End ℂ (kfin ε σ)) (h : ∀ i ∈ s, WRep ε σ (g i)) :
    WRep ε σ (∑ i ∈ s, g i) :=
  Finset.sum_induction g (WRep ε σ) (fun _ _ => wrep_add) wrep_zero h

theorem wrep_mul_cas (hU : IsURepOn (UJset ε) σ) (hD : Dens ε σ) {E : Fin n → Fin n → Module.End ℂ (kfin ε σ)}
    (hE : KDer ε σ E) {u : Module.End ℂ (kfin ε σ)} (hu : WRep ε σ u) : WRep ε σ (u * casimirK ε E) := by
  unfold casimirK
  rw [Finset.mul_sum]
  refine wrep_sum _ _ fun a _ => ?_
  rw [Finset.mul_sum]
  refine wrep_sum _ _ fun b _ => ?_
  rw [← mul_assoc]
  exact wrep_mul_E hU hD hE (wrep_mul_E hU hD hE hu a b) b a

theorem norm_sum_le (S : List (List (Mx n))) (w : H) :
    ∀ L : List (ℂ × List (Mx n)), (∀ p ∈ L, p.2 ∈ S) →
      ‖(L.map fun p => p.1 • Dw σ p.2 w).sum‖ ≤ (L.map fun p => ‖p.1‖).sum * sobNorm σ S w
  | [], _ => by simp
  | p :: L, h => by
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, add_mul]
    refine (norm_add_le _ _).trans (add_le_add ?_ (norm_sum_le S w L fun q hq => h q (List.mem_cons_of_mem _ hq)))
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (norm_Dw_le_sobNorm σ (h p List.mem_cons_self) w) (norm_nonneg _)

end PositivityTheory.CW.WeightedRepresentationMul

namespace PositivityTheory.CW

open WeightedRepresentationMul

theorem c4 : C4 := by
  intro n ε H _ _ _ σ hU _ hD E hE m
  have hrep : WRep ε σ ((1 + casimirK ε E) ^ m) := by
    induction m with
    | zero => simpa using (wrep_one : WRep ε σ 1)
    | succ m ih =>
      rw [pow_succ, mul_add, mul_one]
      exact wrep_add ih (wrep_mul_cas hU hD hE ih)
  obtain ⟨L, hL, hLv⟩ := hrep
  refine ⟨L.map Prod.snd, (L.map fun p => ‖p.1‖).sum, ?_, List.sum_nonneg fun x hx => ?_, fun v => ?_⟩
  · intro l hl X hX
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hl
    exact hL p hp X hX
  · obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
    exact norm_nonneg _
  · have e : ‖((1 + casimirK ε E) ^ m) v‖ = ‖((((1 + casimirK ε E) ^ m) v : kfin ε σ) : H)‖ := rfl
    rw [e, hLv]
    exact norm_sum_le _ _ L fun p hp => List.mem_map.2 ⟨p, hp, rfl⟩

end PositivityTheory.CW

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.E3D
section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped InnerProductSpace

namespace PositivityTheory.CW

theorem e3d : SobolevNormDomination := by
  intro he2 n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ hD T hT hd q hq hq1 S hS
  let Dop : List (Mx n) → (E →L[ℂ] E) := fun l =>
    l.foldr (fun X f => (dπ X).comp f) (ContinuousLinearMap.id ℂ E)
  have key : ∀ l : List (Mx n), (∀ X ∈ l, X ∈ lieSet ε) → ∀ v, IsKFin ε σ v →
      IsKFin ε σ (Dw σ l v) ∧ T (Dw σ l v) = Dop l (T v) := by
    intro l
    induction l with
    | nil => intro _ v hv; exact ⟨hv, rfl⟩
    | cons X l ih =>
      intro hl v hv
      obtain ⟨h1, h2⟩ := ih (fun Y hY => hl Y (List.mem_cons_of_mem _ hY)) v hv
      refine ⟨hD.2.1 _ h1 X (hl X List.mem_cons_self), ?_⟩
      show T (dRep σ X (Dw σ l v)) = dπ X (Dop l (T v))
      rw [hd X (hl X List.mem_cons_self) _ h1, h2]
  have hcont : ∀ l, Continuous (q.comp (Dop l : E →ₗ[ℂ] E)) := fun l => by
    rw [Seminorm.coe_comp, ContinuousLinearMap.coe_coe]
    exact hq.comp (Dop l).continuous
  have hw : ∀ l : List (Mx n), (∀ X ∈ l, X ∈ lieSet ε) → ∀ w, Sm ε σ w →
      ‖Dw σ l w‖ ≤ (q.comp (Dop l : E →ₗ[ℂ] E)) (T w) := by
    intro l hl
    refine (he2 n ε H σ hU hI E p π dπ hπ hD T hT _ (hcont l) l 0 0 hl).2 fun y hy => ?_
    obtain ⟨h1, h2⟩ := key l hl y hy
    calc ‖Dw σ l y‖ ≤ q (T (Dw σ l y)) := hq1 _ h1
      _ = _ := by rw [h2]; rfl
  have main : ∀ S : List (List (Mx n)), Words (lieSet ε) S →
      ∃ q' : Seminorm ℂ E, Continuous q' ∧ ∀ w, Sm ε σ w → sobNorm σ S w ≤ q' (T w) := by
    intro S
    induction S with
    | nil =>
      intro _
      refine ⟨0, by rw [Seminorm.coe_zero]; exact continuous_zero, fun w _ => ?_⟩
      simp [sobNorm]
    | cons l S ih =>
      intro hS
      obtain ⟨q', hq', h'⟩ := ih (fun m hm => hS m (List.mem_cons_of_mem _ hm))
      have hl : ∀ X ∈ l, X ∈ lieSet ε := hS l List.mem_cons_self
      refine ⟨q.comp (Dop l : E →ₗ[ℂ] E) + q', ?_, fun w hw' => ?_⟩
      · rw [Seminorm.coe_add]
        exact (hcont l).add hq'
      · have e : sobNorm σ (l :: S) w = ‖Dw σ l w‖ + sobNorm σ S w := by
          first
            | rfl
            | simp [sobNorm]
        rw [e, Seminorm.add_apply]
        exact add_le_add (hw l hl w hw') (h' w hw')
  exact main S hS

end PositivityTheory.CW

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.EigenspacesOrthogonal
section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open ReciprocityTheory.ChartRestriction.DS (actM casimirK)
open scoped InnerProductSpace

namespace PositivityTheory.CW

namespace HilbertSchmidtSqEq₂

theorem hs2_eq {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : hs2 g = hs g := rfl

theorem smul_seminorm_cont {E : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] {q : Seminorm ℂ E}
    (hq : Continuous q) (c : NNReal) : Continuous (c • q) := by
  rw [Seminorm.coe_smul]
  exact hq.const_smul c

end HilbertSchmidtSqEq₂

open HilbertSchmidtSqEq₂ in
theorem e3c : SmoothMapSeminormBound := by
  classical
  intro hM e3a e3b n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ hD A hA hMod T hG hd Q N hQc hQg hη
  obtain ⟨m, K, I₀, hK, hmax⟩ := hM n ε (kfin ε σ) A hMod N
  have hC : ∀ e : kfin ε σ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y, Sm ε σ y → ‖⟪(e : H), y⟫_ℂ‖ ≤ C * Q (T y) :=
    fun e => hη e e.2
  choose Ce hCe0 hCe using hC
  set Cs : ℝ := ∑ e ∈ I₀, Ce e with hCs
  have hCs0 : 0 ≤ Cs := Finset.sum_nonneg fun e _ => hCe0 e
  have h3a := e3a n ε (kfin ε σ) A hMod.gl hMod.uni hMod m
  obtain ⟨D, hDm⟩ := e3b n ε H σ hU hI E p π dπ hπ A hA T hd m
  have key : ∀ y : kfin ε σ, ‖(y : H)‖ ≤ K * Cs * Q (D (T y)) := by
    intro y
    obtain ⟨v, hv⟩ := h3a.1 y
    set w : H := ((((1 + casimirK ε A) ^ m) y : kfin ε σ) : H) with hwdef
    have hw : Sm ε σ w := hD.1 _ (((1 + casimirK ε A) ^ m) y).2
    let F : kfin ε σ →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ) :=
      { toFun := fun η g => ⟪w, σ g (η : H)⟫_ℂ
        map_add' := fun a b => by funext g; simp [inner_add_right]
        map_smul' := fun c a => by funext g; simp [inner_smul_right] }
    have hF : ∀ (η : kfin ε σ) g, F η g = ⟪w, σ g (η : H)⟫_ℂ := fun _ _ => rfl
    have h1 : ∀ η : kfin ε σ, ContinuousOn (F η) (ReciprocityTheory.ChartRestriction.DS.UJset ε) := fun η => by
      have := (continuousOn_const (c := w) (s := UJset ε)).inner (𝕜 := ℂ) (hU.2.2 (η : H))
      exact this
    have h2 : ∀ X, ReciprocityTheory.ChartRestriction.DS.inP ε X → ∀ η : kfin ε σ, ∀ g ∈ ReciprocityTheory.ChartRestriction.DS.UJset ε,
        HasDerivAt (fun t : ℝ => F η (g * NormedSpace.exp (t • X))) (F (actM A X η) g) 0 := by
      intro X hX η g hg
      have hXl : X ∈ lieSet ε := hX.1
      have hg' : g ∈ UJset ε := hg
      have hη' : Sm ε σ (η : H) := hD.1 _ η.2
      have ho : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) (η : H)) (dRep σ X η) 0 := by
        have := hasDerivAt_orbit hU hη' hXl 0
        rwa [zero_smul, NormedSpace.exp_zero, sigma_one hU] at this
      have h4 : HasDerivAt (fun t : ℝ => σ g (σ (NormedSpace.exp (t • X)) (η : H))) (σ g (dRep σ X η)) 0 :=
        ((σ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 ho
      have h5 := ((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h4
      simp only [ContinuousLinearMap.coe_restrictScalars', innerSL_apply_apply] at h5
      rw [hF, hA X hXl η]
      refine h5.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      simp only [Function.comp_apply, hF, innerSL_apply_apply]
      rw [sigma_mul hU hg' (exp_mem_UJ hXl t)]
    have h3 : ∀ η : kfin ε σ, ∃ C : ℝ, ∀ g ∈ ReciprocityTheory.ChartRestriction.DS.UJset ε, ‖F η g‖ ≤ C * (1 + hs2 g) ^ N := by
      intro η
      refine ⟨‖w‖ * ‖(η : H)‖, fun g hg => ?_⟩
      have hg' : g ∈ UJset ε := hg
      rw [hF, hs2_eq]
      have e1 : ‖⟪w, σ g (η : H)⟫_ℂ‖ ≤ ‖w‖ * ‖(η : H)‖ := by
        have := norm_inner_le_norm (𝕜 := ℂ) w (σ g (η : H))
        rwa [hU.2.1 g hg' (η : H)] at this
      have e2 : (1 : ℝ) ≤ (1 + hs g) ^ N := one_le_pow₀ (by linarith [hs_nonneg g])
      calc _ ≤ ‖w‖ * ‖(η : H)‖ := e1
        _ = ‖w‖ * ‖(η : H)‖ * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left e2 (by positivity)
    have h5b : ∀ e ∈ I₀, ∀ g ∈ ReciprocityTheory.ChartRestriction.DS.UJset ε, ‖F e g‖ ≤ (Cs * Q (T w)) * (1 + hs2 g) ^ N := by
      intro e he g hg
      have hg' : g ∈ UJset ε := hg
      rw [hF, hs2_eq, inner_sigma hU hg' w (e : H), norm_inner_symm]
      have hgi : g⁻¹ ∈ UJset ε := inv_mem_UJ hg'
      have e1 := hCe e (σ g⁻¹ w) (Sm.translate hU hw hgi)
      rw [hG.1 g⁻¹ hgi w hw] at e1
      have e2 := hQg g⁻¹ hgi (T w)
      rw [hs_inv hg'] at e2
      have e3 : Ce e ≤ Cs := Finset.single_le_sum (f := Ce) (fun x _ => hCe0 x) he
      have hQ0 : 0 ≤ Q (T w) := apply_nonneg _ _
      have hW0 : 0 ≤ (1 + hs g) ^ N := pow_nonneg (by linarith [hs_nonneg g]) _
      calc _ ≤ Ce e * Q (π g⁻¹ (T w)) := e1
        _ ≤ Ce e * ((1 + hs g) ^ N * Q (T w)) := mul_le_mul_of_nonneg_left e2 (hCe0 e)
        _ ≤ Cs * ((1 + hs g) ^ N * Q (T w)) := mul_le_mul_of_nonneg_right e3 (mul_nonneg hW0 hQ0)
        _ = _ := by ring
    have hmv := hmax F h1 h2 h3 (Cs * Q (T w)) (mul_nonneg hCs0 (apply_nonneg _ _)) h5b v
    rw [hv, hF, sigma_one hU] at hmv
    have hin : ⟪w, (v : H)⟫_ℂ = ⟪(y : H), (y : H)⟫_ℂ := by
      rw [hwdef, ← Submodule.coe_inner, ← Submodule.coe_inner, h3a.2 y v, hv]
    have hn : ‖⟪(y : H), (y : H)⟫_ℂ‖ = ‖(y : H)‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K, norm_pow]; simp
    rw [hin, hn] at hmv
    have hTw : T w = D (T y) := hDm y
    rw [hTw] at hmv
    have hy0 : 0 ≤ ‖(y : H)‖ := norm_nonneg _
    have hR0 : 0 ≤ K * Cs * Q (D (T y)) := mul_nonneg (mul_nonneg hK hCs0) (apply_nonneg _ _)
    rcases hy0.eq_or_lt with h0 | h0
    · rw [← h0]; exact hR0
    · have : ‖(y : H)‖ * ‖(y : H)‖ ≤ K * Cs * Q (D (T y)) * ‖(y : H)‖ := by
        have e : K * (Cs * Q (D (T y))) * ‖(y : H)‖ = K * Cs * Q (D (T y)) * ‖(y : H)‖ := by ring
        rw [← e, ← sq]
        exact hmv
      exact le_of_mul_le_mul_right this h0
  refine ⟨(K * Cs).toNNReal • Q.comp (D : E →ₗ[ℂ] E), smul_seminorm_cont ?_ _, fun v hv => ?_⟩
  · rw [Seminorm.coe_comp]
    exact hQc.comp D.continuous
  · rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (mul_nonneg hK hCs0),
      Seminorm.comp_apply]
    exact key ⟨v, hv⟩

end PositivityTheory.CW

end
end

