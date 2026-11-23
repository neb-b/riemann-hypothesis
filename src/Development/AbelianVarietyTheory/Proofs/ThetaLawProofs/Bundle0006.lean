module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MulVecCongrDeg
section
open GlobalTheory.KeyKa
noncomputable section
namespace GlobalTheory.KeyKa.KosKer
open Matrix

theorem mulVec_congr_deg {R Ix : Type} [CommRing R] [Fintype Ix] {deg : Ix → ℕ} {D : Matrix Ix Ix R}
    (h : ∀ p q, deg q ≠ deg p + 1 → D p q = 0) (u u' : Ix → R) (p : Ix)
    (hu : ∀ q, deg q = deg p + 1 → u q = u' q) : (D *ᵥ u) p = (D *ᵥ u') p := by
  simp only [mulVec, dotProduct]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hq : deg q = deg p + 1
  · rw [hu q hq]
  · rw [h p q hq, zero_mul, zero_mul]

theorem clear_denom {O Ix : Type} [CommRing O] [IsDomain O] [Fintype Ix] (D : Matrix Ix Ix O)
    (h : ∀ v, (D.map (algebraMap O (FractionRing O))) *ᵥ v = 0 →
      ∃ w, (D.map (algebraMap O (FractionRing O))) *ᵥ w = v) (x : Ix → O) (hx : D *ᵥ x = 0) :
    ∃ c : O, c ≠ 0 ∧ ∃ u, D *ᵥ u = c • x := by
  have hm : ∀ y : Ix → O, (D.map (algebraMap O (FractionRing O))) *ᵥ (algebraMap O (FractionRing O) ∘ y) =
      algebraMap O (FractionRing O) ∘ (D *ᵥ y) := fun y => funext fun p => (RingHom.map_mulVec _ D y p).symm
  obtain ⟨w, hw⟩ := h (algebraMap O (FractionRing O) ∘ x) (by rw [hm, hx]; ext p; simp)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) w
  choose u hu using hb
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, u, funext fun p => ?_⟩
  apply IsFractionRing.injective O (FractionRing O)
  have e : algebraMap O (FractionRing O) ∘ u = (b : O) • w := funext hu
  have e2 := congrFun (hm u) p
  rw [e, mulVec_smul, hw] at e2
  simp only [Function.comp, Pi.smul_apply] at e2 ⊢
  rw [← e2, smul_eq_mul, map_mul, Algebra.smul_def]

variable {g d : ℕ} {N : ℕ → ℕ}

theorem mulVec_empty {R : Type} [CommRing R] (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R)
    (ev : ∀ j, Matrix (Fin d) (Fin (N j)) R) (u : KIx g d N → R) (a : Fin (N 0)) :
    (kosD m ev *ᵥ u) (.inl ⟨∅, a⟩) = (∑ i, m i 0 1 *ᵥ (fun k => u (.inl ⟨{i}, k⟩))) a := by
  simp only [mulVec, dotProduct, Fintype.sum_sum_type, kosD, zero_mul, Finset.sum_const_zero, add_zero,
    Finset.sum_mul, Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_sigma, Finset.sum_eq_single {i}]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [if_pos ⟨by simp, by simp⟩]
    simp
    rfl
  · intro J _ hJ
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg (fun h => hJ (by simpa using h.2)), zero_mul]
  · simp

theorem mulVec_inr {R : Type} [CommRing R] (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R)
    (ev : ∀ j, Matrix (Fin d) (Fin (N j)) R) (u : KIx g d N → R) (a : Fin d) :
    (kosD m ev *ᵥ u) (.inr a) = (ev 0 *ᵥ (fun k => u (.inl ⟨∅, k⟩))) a := by
  simp only [mulVec, dotProduct, Fintype.sum_sum_type, kosD, zero_mul, Finset.sum_const_zero, add_zero]
  rw [Fintype.sum_sigma, Finset.sum_eq_single ∅]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [if_pos rfl]
    rfl
  · intro J _ hJ
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg hJ, zero_mul]
  · simp

theorem mulVec_inl_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d' : ℕ}
    (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R)
    (ev : ∀ j, Matrix (Fin d) (Fin (N j)) R) (ev' : ∀ j, Matrix (Fin d') (Fin (N j)) S)
    (u : KIx g d N → R) (u' : KIx g d' N → S) (hu : ∀ q, u' (.inl q) = f (u (.inl q))) (p) :
    (kosD (fun i j j' => (m i j j').map f) ev' *ᵥ u') (.inl p) = f ((kosD m ev *ᵥ u) (.inl p)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [mulVec, dotProduct, Fintype.sum_sum_type, kosD, zero_mul, Finset.sum_const_zero, add_zero,
    map_sum, map_mul, hu, apply_ite f, map_zero, map_pow, map_neg, map_one, Matrix.map_apply]

theorem div_unif {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) O) (ev : ∀ j, Matrix (Fin d) (Fin (N j)) O)
    (hD : IsCx kdeg (kosD m ev))
    (hk : ∀ v : KIx g 0 N → IsLocalRing.ResidueField O,
      (kosD (fun i j j' => (m i j j').map (IsLocalRing.residue O)) (fun _ => 0)).mulVec v = 0 →
      ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) =
        (kosD (d := 0) (fun i j j' => (m i j j').map (IsLocalRing.residue O)) (fun _ => 0)).mulVec w (.inl p))
    {π : O} (hπ : Irreducible π) (v : Fin (N 0) → O) (u : KIx g d N → O)
    (hu : ∀ a, π * v a = (kosD m ev *ᵥ u) (.inl ⟨∅, a⟩)) :
    ∃ y : KIx g d N → O, ∀ a, v a = (kosD m ev *ᵥ y) (.inl ⟨∅, a⟩) := by
  classical
  have hres : ∀ x : O, IsLocalRing.residue O x = 0 ↔ π ∣ x := fun x => by
    rw [IsLocalRing.residue_eq_zero_iff, hπ.maximalIdeal_eq, Ideal.mem_span_singleton]
  let u' : KIx g d N → O := fun q => if kdeg q = 2 then u q else 0
  have h1 : ∀ a : Fin (N 0), (kosD m ev *ᵥ u') (.inl ⟨∅, a⟩) = π * v a := fun a => by
    rw [hu a]
    exact mulVec_congr_deg hD.1 _ _ _ fun q hq => if_pos hq
  obtain ⟨wb, hwb⟩ := hk (Sum.elim (fun q => IsLocalRing.residue O (u' (.inl q))) 0) (by
    ext p
    rcases p with ⟨I, a⟩ | a
    · rw [mulVec_inl_map (IsLocalRing.residue O) m ev _ u' _ (fun _ => rfl)]
      by_cases hI : I = ∅
      · subst hI
        rw [h1 a]
        exact (hres _).2 (dvd_mul_right _ _)
      · rw [mulVec_congr_deg hD.1 u' 0 _ fun q hq => if_neg ?_]
        · simp
        · have : I.card ≠ 0 := by simpa using hI
          rw [hq]
          simp only [kdeg]
          omega
    · exact a.elim0)
  choose w0 hw0 using fun q => IsLocalRing.residue_surjective (R := O) (wb (.inl q))
  let w : KIx g d N → O := Sum.elim w0 0
  have h2 : ∀ q : KIx g d N, ∃ y, kdeg q = 2 → (u' - kosD m ev *ᵥ w) q = π * y := by
    rintro (p | a)
    · by_cases hp : p.1 = ∅
      · refine ⟨0, fun h => ?_⟩
        simp [kdeg, hp] at h
      · have e := hwb p hp
        rw [mulVec_inl_map (IsLocalRing.residue O) m ev _ w _ (fun q => (hw0 q).symm)] at e
        obtain ⟨y, hy⟩ := (hres ((u' - kosD m ev *ᵥ w) (.inl p))).1 (by
          rw [Pi.sub_apply, map_sub, ← e]; exact sub_self _)
        exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun h => by simp [kdeg] at h⟩
  choose y hy using h2
  refine ⟨y, fun a => mul_left_cancel₀ hπ.ne_zero ?_⟩
  have e := mulVec_congr_deg hD.1 (u' - kosD m ev *ᵥ w) (π • y) (.inl ⟨∅, a⟩) fun q hq => hy q hq
  rw [mulVec_sub, mulVec_mulVec, hD.2, zero_mulVec, sub_zero, mulVec_smul, h1 a] at e
  exact e

theorem ker_and_image : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (g d : ℕ) (N : ℕ → ℕ) (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) O) (ev : ∀ j, Matrix (Fin d) (Fin (N j)) O), IsCx kdeg (kosD m ev) → (∀ v, ((kosD m ev).map (algebraMap O (FractionRing O))).mulVec v = 0 → ∃ w, ((kosD m ev).map (algebraMap O (FractionRing O))).mulVec w = v) → (∀ v : KIx g 0 N → IsLocalRing.ResidueField O, (kosD (fun i j j' => (m i j j').map (IsLocalRing.residue O)) (fun _ => 0)).mulVec v = 0 → ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) = (kosD (d := 0) (fun i j j' => (m i j j').map (IsLocalRing.residue O)) (fun _ => 0)).mulVec w (.inl p)) → (∀ v, (ev 0).mulVec v = 0 → ∃ w : Fin g → Fin (N 1) → O, v = ∑ i, (m i 0 1).mulVec (w i)) ∧ ∃ c : O, c ≠ 0 ∧ ∀ t, ∃ v, (ev 0).mulVec v = c • t := by
  intro O _ _ _ g d N m ev hD hK hk
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hpow : ∀ (n : ℕ) (v : Fin (N 0) → O), (∃ u : KIx g d N → O, ∀ a, π ^ n * v a = (kosD m ev *ᵥ u) (.inl ⟨∅, a⟩)) →
      ∃ y : KIx g d N → O, ∀ a, v a = (kosD m ev *ᵥ y) (.inl ⟨∅, a⟩) := by
    intro n
    induction n with
    | zero => intro v h; simpa using h
    | succ n ih =>
      rintro v ⟨u, hu⟩
      exact ih v (div_unif m ev hD hk hπ (fun a => π ^ n * v a) u fun a => by rw [← hu a]; ring)
  refine ⟨fun v hv => ?_, ?_⟩
  · let x : KIx g d N → O := Sum.elim (fun p => if h : p.1 = ∅ then v (Fin.cast (by rw [h]; rfl) p.2) else 0) 0
    have hx0 : ∀ a : Fin (N 0), x (.inl ⟨∅, a⟩) = v a := fun a => by
      simp only [x, Sum.elim_inl, dif_pos]
      rfl
    have hx : kosD m ev *ᵥ x = 0 := by
      ext p
      rcases p with p | a
      · rw [mulVec_congr_deg hD.1 x 0 _ ?_]
        · simp
        · rintro (q | q) hq
          · refine dif_neg fun h => ?_
            simp [kdeg, h] at hq
          · rfl
      · rw [mulVec_inr, funext hx0, hv]
        rfl
    obtain ⟨c, hc, u, hu⟩ := clear_denom _ hK x hx
    obtain ⟨n, e, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hπ
    obtain ⟨y, hy⟩ := hpow n v ⟨(↑e⁻¹ : O) • u, fun a => by
      rw [mulVec_smul, hu, smul_smul, ← mul_assoc, Units.inv_mul, one_mul, Pi.smul_apply, hx0, smul_eq_mul]⟩
    exact ⟨fun i k => y (.inl ⟨{i}, k⟩), funext fun a => (hy a).trans (mulVec_empty m ev y a)⟩
  · have h1 : ∀ a : Fin d, ∃ c : O, c ≠ 0 ∧ ∃ v, ev 0 *ᵥ v = c • (Pi.single a 1 : Fin d → O) := by
      intro a
      obtain ⟨c, hc, u, hu⟩ := clear_denom _ hK (Sum.elim 0 (Pi.single a 1)) (by
        ext p
        rcases p with p | p <;> simp [mulVec, dotProduct, Fintype.sum_sum_type, kosD])
      refine ⟨c, hc, fun k => u (.inl ⟨∅, k⟩), funext fun b => ?_⟩
      rw [← mulVec_inr m ev u b, hu]
      rfl
    choose c hc v hv using h1
    refine ⟨∏ a, c a, Finset.prod_ne_zero_iff.2 fun a _ => hc a, fun t => ?_⟩
    choose e he using fun a => Finset.dvd_prod_of_mem c (Finset.mem_univ a)
    refine ⟨∑ a, (t a * e a) • v a, ?_⟩
    rw [mulVec_sum]
    ext b
    simp only [mulVec_smul, hv, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [he b]
    ring

end GlobalTheory.KeyKa.KosKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PointMatrixMulLeftMulMatrix
section
open GlobalTheory.KeyKa

namespace GlobalTheory.KeyKa

theorem pointMatrix_mul_leftMulMatrix {O B Ix : Type} [CommRing O] [CommRing B] [Algebra O B]
    [Fintype Ix] [DecidableEq Ix] (β : Module.Basis Ix O B) (e : Ix → (B →ₐ[O] O)) (y : B) :
    (Matrix.of fun a a' => e a (β a')) * Algebra.leftMulMatrix β y
      = Matrix.diagonal (fun a => e a y) * (Matrix.of fun a a' => e a (β a')) := by
  ext a a'
  rw [Matrix.diagonal_mul, Matrix.mul_apply]
  simp only [Matrix.of_apply, Algebra.leftMulMatrix_eq_repr_mul]
  rw [← map_mul]
  conv_rhs => rw [← β.sum_repr (y * β a')]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

theorem trace_eq_sum_points {O B Ix : Type} [CommRing O] [IsDomain O] [CommRing B] [Algebra O B]
    [Fintype Ix] [DecidableEq Ix] (β : Module.Basis Ix O B) (e : Ix → (B →ₐ[O] O))
    (h : (Matrix.of fun a a' => e a (β a')).det ≠ 0) (y : B) :
    Algebra.trace O B y = ∑ a, e a y := by
  have h1 := pointMatrix_mul_leftMulMatrix β e y
  set P : Matrix Ix Ix O := Matrix.of fun a a' => e a (β a') with hP
  have h2 : P.det • Algebra.leftMulMatrix β y
      = P.adjugate * (Matrix.diagonal (fun a => e a y) * P) := by
    rw [← h1, ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  have h3 := congrArg Matrix.trace h2
  rw [Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul,
    Matrix.mul_one, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_diagonal,
    smul_eq_mul, smul_eq_mul] at h3
  rw [Algebra.trace_eq_matrix_trace β]
  exact mul_left_cancel₀ h h3

theorem discr_norm_eq_of_points :
    ∀ (O B Ix : Type) [CommRing O] [IsDomain O] [CommRing B] [Algebra O B] [Fintype Ix]
      [DecidableEq Ix] (β : Module.Basis Ix O B) (e : Ix → (B →ₐ[O] O)),
      (Matrix.of fun a a' => e a (β a')).det ≠ 0 →
        Algebra.discr O β = (Matrix.of fun a a' => e a (β a')).det ^ 2 ∧
          ∀ y : B, Algebra.norm O y = ∏ a, e a y := by
  intro O B Ix _ _ _ _ _ _ β e h
  refine ⟨?_, fun y => ?_⟩
  · have ht : Algebra.traceMatrix O β
        = (Matrix.of fun a a' => e a (β a')).transpose * (Matrix.of fun a a' => e a (β a')) := by
      ext i j
      rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply, trace_eq_sum_points β e h,
        Matrix.mul_apply]
      simp
    rw [Algebra.discr_def, ht, Matrix.det_mul, Matrix.det_transpose, sq]
  · have h1 := congrArg Matrix.det (pointMatrix_mul_leftMulMatrix β e y)
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, mul_comm] at h1
    rw [Algebra.norm_eq_matrix_det β]
    exact mul_right_cancel₀ h h1

end GlobalTheory.KeyKa
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SignSwap
section
open GlobalTheory.KeyKa
namespace GlobalTheory.KaUnique

theorem sign_swap {R : Type} [CommRing R] {g : ℕ} (P : Finset (Fin g)) {i i' : Fin g} (hi : i ∉ P) (hi' : i' ∉ P)
    (hne : i ≠ i') :
    ((-1 : R) ^ (P.filter (· < i)).card * (-1) ^ ((insert i P).filter (· < i')).card) +
      ((-1 : R) ^ (P.filter (· < i')).card * (-1) ^ ((insert i' P).filter (· < i)).card) = 0 := by
  rw [Finset.filter_insert, Finset.filter_insert]
  rcases lt_or_gt_of_ne hne with h | h
  · rw [if_pos h, if_neg (not_lt.2 h.le), Finset.card_insert_of_notMem (fun hh => hi (Finset.mem_filter.1 hh).1)]
    ring
  · rw [if_pos h, if_neg (not_lt.2 h.le), Finset.card_insert_of_notMem (fun hh => hi' (Finset.mem_filter.1 hh).1)]
    ring

theorem isCx_kosD {R : Type} [CommRing R] {g d : ℕ} {N : ℕ → ℕ}
    (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R) (ev : ∀ j, Matrix (Fin d) (Fin (N j)) R)
    (hc : ∀ i i' j, j + 1 < g → m i j (j + 1) * m i' (j + 1) (j + 1 + 1) = m i' j (j + 1) * m i (j + 1) (j + 1 + 1))
    (he : ∀ i, ev 0 * m i 0 (0 + 1) = 0) : IsCx kdeg (kosD m ev) := by
  have hc' : ∀ i i' j j₁ j₁' j₂, j₁ = j + 1 → j₁' = j + 1 → j₂ = j + 1 + 1 → j₂ ≤ g →
      m i j j₁ * m i' j₁ j₂ = m i' j j₁' * m i j₁' j₂ := by
    rintro i i' j _ _ _ rfl rfl rfl h
    exact hc i i' j h
  have he' : ∀ i j j₁, j = 0 → j₁ = 0 + 1 → ev j * m i j j₁ = 0 := by
    rintro i _ _ rfl rfl
    exact he i
  refine ⟨fun p q h => ?_, ?_⟩
  · rcases p with p | p <;> rcases q with q | q
    · simp only [kosD]
      refine Finset.sum_eq_zero fun i _ => if_neg ?_
      rintro ⟨hi, hq⟩
      apply h
      simp [kdeg, hq, Finset.card_insert_of_notMem hi]
    · rfl
    · simp only [kosD]
      refine if_neg fun hq => h ?_
      simp [kdeg, hq]
    · rfl
  ext p q
  rw [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.zero_apply]
  have h0 : ∑ a : Fin d, kosD m ev p (.inr a) * kosD m ev (.inr a) q = 0 :=
    Finset.sum_eq_zero fun a _ => by rcases p with p | p <;> exact zero_mul _
  rw [h0, add_zero]
  rcases q with ⟨Q, c⟩ | q
  swap
  · exact Finset.sum_eq_zero fun a _ => mul_zero _
  rw [Fintype.sum_sigma]
  rcases p with ⟨P, a⟩ | a
  · let F : Fin g × Fin g → R := fun ii => if ii.1 ∉ P ∧ ii.2 ∉ insert ii.1 P ∧ Q = insert ii.2 (insert ii.1 P) then
      ((-1 : R) ^ (P.filter (· < ii.1)).card * (-1) ^ ((insert ii.1 P).filter (· < ii.2)).card) *
        (m ii.1 P.card (insert ii.1 P).card * m ii.2 (insert ii.1 P).card Q.card) a c else 0
    have h1 : ∑ I : Finset (Fin g), ∑ k : Fin (N I.card), kosD m ev (.inl ⟨P, a⟩) (.inl ⟨I, k⟩) *
        kosD m ev (.inl ⟨I, k⟩) (.inl ⟨Q, c⟩) = ∑ ii, F ii := by
      simp only [kosD, Finset.sum_mul_sum]
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_comm (s := (Finset.univ : Finset (Fin (N _)))) (t := (Finset.univ : Finset (Fin g)))]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [Finset.sum_eq_single (insert i P)]
      · simp only [F, Matrix.mul_apply, Finset.mul_sum]
        by_cases h₁ : i ∉ P
        · by_cases h₂ : i' ∉ insert i P ∧ Q = insert i' (insert i P)
          · rw [if_pos ⟨h₁, h₂⟩]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [if_pos ⟨h₁, trivial⟩, if_pos h₂]; ring
          · rw [if_neg fun hh => h₂ hh.2]
            exact Finset.sum_eq_zero fun k _ => by rw [if_neg h₂, mul_zero]
        · rw [if_neg fun hh => h₁ hh.1]
          exact Finset.sum_eq_zero fun k _ => by rw [if_neg fun hh => h₁ hh.1, zero_mul]
      · intro I _ hI
        exact Finset.sum_eq_zero fun k _ => by rw [if_neg fun hh => hI hh.2, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [h1]
    have hsw : ∀ i i' : Fin g, (i ∉ P ∧ i' ∉ insert i P ∧ Q = insert i' (insert i P)) →
        (i' ∉ P ∧ i ∉ insert i' P ∧ Q = insert i (insert i' P)) := by
      rintro i i' ⟨h₁, h₂, h₃⟩
      rw [Finset.mem_insert, not_or] at h₂
      refine ⟨h₂.2, ?_, h₃.trans (Finset.insert_comm _ _ _)⟩
      rw [Finset.mem_insert, not_or]
      exact ⟨fun e => h₂.1 e.symm, h₁⟩
    refine Finset.sum_involution (fun ii _ => ii.swap) ?_ ?_ (fun _ _ => Finset.mem_univ _) (fun _ _ => rfl)
    · rintro ⟨i, i'⟩ _
      simp only [F, Prod.swap]
      by_cases h : i ∉ P ∧ i' ∉ insert i P ∧ Q = insert i' (insert i P)
      · have h' := hsw _ _ h
        rw [if_pos h, if_pos h', hc' i i' P.card (insert i P).card (insert i' P).card Q.card
          (Finset.card_insert_of_notMem h.1) (Finset.card_insert_of_notMem h'.1)
          (by rw [h.2.2, Finset.card_insert_of_notMem h.2.1, Finset.card_insert_of_notMem h.1])
          (by simpa using Q.card_le_univ), ← add_mul,
          sign_swap P h.1 h'.1 (fun e => h.2.1 (e ▸ Finset.mem_insert_self _ _)), zero_mul]
      · rw [if_neg h, if_neg fun hh => h (hsw _ _ hh), add_zero]
    · rintro ⟨i, i'⟩ _ hF e
      apply hF
      obtain rfl : i' = i := congrArg Prod.fst e
      exact if_neg fun hh => hh.2.1 (Finset.mem_insert_self _ _)
  · refine Finset.sum_eq_zero fun I _ => ?_
    simp only [kosD]
    by_cases hI : I = ∅
    · simp only [if_pos hI, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases h : i ∉ I ∧ Q = insert i I
      · have := congrFun (congrFun (he' i I.card Q.card (by simp [hI])
          (by rw [h.2, Finset.card_insert_of_notMem h.1]; simp [hI])) a) c
        rw [Matrix.mul_apply, Matrix.zero_apply] at this
        simp only [if_pos h, mul_left_comm _ ((-1 : R) ^ _), ← Finset.mul_sum, this, mul_zero]
      · simp only [if_neg h, mul_zero, Finset.sum_const_zero]
    · simp only [if_neg hI, zero_mul, Finset.sum_const_zero]

end GlobalTheory.KaUnique
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SpanModEquationsLift
section
open GlobalTheory.KeyKa

namespace GlobalTheory.SeriesNakayama

theorem mem_pow_smul_top_iff {O M : Type*} [CommRing O] [AddCommGroup M] [Module O M] (π : O)
    (n : ℕ) (x : M) :
    x ∈ (Ideal.span {π} ^ n • ⊤ : Submodule O M) ↔ ∃ y : M, π ^ n • y = x := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp

theorem mem_pow_smul_top_pi {O ι : Type*} [CommRing O] (π : O) (n : ℕ) (x : ι → O) :
    x ∈ (Ideal.span {π} ^ n • ⊤ : Submodule O (ι → O)) ↔
      ∀ i, x i ∈ (Ideal.span {π} ^ n • ⊤ : Submodule O O) := by
  simp only [mem_pow_smul_top_iff]
  refine ⟨fun ⟨y, hy⟩ i => ⟨y i, congrFun hy i⟩, fun h => ?_⟩
  choose y hy using h
  exact ⟨y, funext hy⟩

theorem surjective_of_mod {O ι κ : Type*} [CommRing O] (π : O)
    [IsAdicComplete (Ideal.span {π}) O] (Φ : (ι → O) →ₗ[O] (κ → O))
    (h : ∀ G : κ → O, ∃ x, ∀ j, G j - Φ x j ∈ Ideal.span {π}) : Function.Surjective Φ := by
  have : IsPrecomplete (Ideal.span {π}) (ι → O) := by
    refine ⟨fun u hu => ?_⟩
    have h1 : ∀ i, ∃ L : O, ∀ k, u k i ≡ L [SMOD (Ideal.span {π} ^ k • ⊤ : Submodule O O)] :=
      fun i => IsPrecomplete.prec' (fun k => u k i) fun {a b} hab =>
        SModEq.sub_mem.2 ((mem_pow_smul_top_pi π a _).1 (SModEq.sub_mem.1 (hu hab)) i)
    choose L hL using h1
    exact ⟨L, fun k => SModEq.sub_mem.2
      ((mem_pow_smul_top_pi π k _).2 fun i => SModEq.sub_mem.1 (hL i k))⟩
  have : IsHausdorff (Ideal.span {π}) (κ → O) := by
    refine ⟨fun x hx => funext fun j => IsHausdorff.haus' (I := Ideal.span {π}) (x j) fun n => ?_⟩
    exact SModEq.sub_mem.2 ((mem_pow_smul_top_pi π n _).1 (SModEq.sub_mem.1 (hx n)) j)
  refine surjective_of_mkQ_comp_surjective (I := Ideal.span {π}) fun G => ?_
  obtain ⟨G, rfl⟩ := Submodule.Quotient.mk_surjective _ G
  obtain ⟨x, hx⟩ := h G
  refine ⟨x, ((Submodule.Quotient.eq _).2 ?_).symm⟩
  have := (mem_pow_smul_top_pi π 1 (G - Φ x)).2 fun j => by simpa using hx j
  rwa [pow_one] at this

theorem exists_projection {O K : Type*} [CommRing O] [IsLocalRing O] [Field K] (f : O →+* K)
    (hf : RingHom.ker f = IsLocalRing.maximalIdeal O) :
    ∃ (μ : K →+ K) (l : K → O), (∀ a, f (l a) = μ a) ∧ (∀ a o, μ (a * f o) = μ a * f o) ∧
      ∀ o, μ (f o) = f o := by
  let φ : IsLocalRing.ResidueField O →+* K :=
    Ideal.Quotient.lift _ f fun a ha => by rwa [← hf] at ha
  have hφ : ∀ o, φ (IsLocalRing.residue O o) = f o := fun _ => rfl
  letI := φ.toAlgebra
  obtain ⟨r, hr⟩ := (Algebra.linearMap (IsLocalRing.ResidueField O) K).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 φ.injective)
  choose l hl using fun a => IsLocalRing.residue_surjective (R := O) (r a)
  refine ⟨φ.toAddMonoidHom.comp r.toAddMonoidHom, l, fun a => ?_, fun a o => ?_, fun o => ?_⟩
  · change _ = φ (r a)
    rw [← hl, hφ]
  · change φ (r _) = φ (r a) * _
    have : a * f o = IsLocalRing.residue O o • a := mul_comm _ _
    rw [this, map_smul, smul_eq_mul, map_mul, hφ, mul_comm]
  · change φ (r _) = _
    have : r (f o) = IsLocalRing.residue O o := LinearMap.congr_fun hr (IsLocalRing.residue O o)
    rw [this, hφ]

theorem span_mod_equations_lift (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (K : Type) [Field K] (f : O →+* K) (g N : ℕ)
    (Y : Type) (F : Y → Fin g → (MvPowerSeries (Fin g) O))
    (ρ : Y → Fin N → (MvPowerSeries (Fin g) O))
    (hf : RingHom.ker f = IsLocalRing.maximalIdeal O)
    (h : ∀ G : Y → MvPowerSeries (Fin g) K, ∃ v : Fin N → K, ∀ y,
      G y - ∑ k, v k • MvPowerSeries.map f (ρ y k) ∈
        Ideal.span (Set.range fun i => MvPowerSeries.map f (F y i)))
    (G : Y → (MvPowerSeries (Fin g) O)) :
    ∃ v : Fin N → O, ∀ y, G y - ∑ k, v k • ρ y k ∈ Ideal.span (Set.range (F y)) := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hm := hπ.maximalIdeal_eq
  have : IsAdicComplete (Ideal.span {π}) O := hm ▸ ‹_›
  obtain ⟨μ, l, hl, hμ, hμ1⟩ := exists_projection f hf
  let Φ : (Fin N ⊕ (Y × Fin g × (Fin g →₀ ℕ)) → O) →ₗ[O] (Y × (Fin g →₀ ℕ) → O) :=
    { toFun := fun x j => ∑ k, x (.inl k) * MvPowerSeries.coeff j.2 (ρ j.1 k) +
        ∑ i, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal j.2,
          x (.inr (j.1, i, p.1)) * MvPowerSeries.coeff p.2 (F j.1 i)
      map_add' := fun x x' => funext fun j => by
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
        ring
      map_smul' := fun c x => funext fun j => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_add, Finset.mul_sum,
          mul_assoc] }
  have hΦ : Function.Surjective Φ := by
    refine surjective_of_mod π Φ fun G => ?_
    let G' : Y → MvPowerSeries (Fin g) K := fun y d => f (G (y, d))
    obtain ⟨v, hv⟩ := h G'
    choose H hH using fun y => (Ideal.mem_span_range_iff_exists_fun).1 (hv y)
    refine ⟨Sum.elim (fun k => l (v k)) fun q => l (MvPowerSeries.coeff q.2.2 (H q.1 q.2.1)), ?_⟩
    rintro ⟨y, d⟩
    rw [← hm, ← hf, RingHom.mem_ker]
    have h1 := congrArg (fun s => μ (MvPowerSeries.coeff d s)) (eq_sub_iff_add_eq.1 (hH y))
    have h2 : MvPowerSeries.coeff d (G' y) = f (G (y, d)) := rfl
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sum, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_map,
      MvPowerSeries.coeff_smul, hμ, hμ1, h2] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, map_sub, map_add (f := _), map_sum, map_mul, Sum.elim_inl,
      Sum.elim_inr, hl]
    rw [← h1, add_comm, sub_self]
  obtain ⟨x, hx⟩ := hΦ fun j => MvPowerSeries.coeff j.2 (G j.1)
  refine ⟨fun k => x (.inl k), fun y => Ideal.mem_span_range_iff_exists_fun.2
    ⟨fun i => (show MvPowerSeries (Fin g) O from fun d => x (.inr (y, i, d))), ?_⟩⟩
  ext d
  have h1 : _ = MvPowerSeries.coeff d (G y) := congrFun hx (y, d)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_sum, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_smul, ← h1, Φ,
    LinearMap.coe_mk, AddHom.coe_mk, add_sub_cancel_left]
  exact Finset.sum_congr rfl fun i _ => MvPowerSeries.coeff_mul d _ _

end GlobalTheory.SeriesNakayama
end

