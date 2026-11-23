module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0024

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualInterSelfDualHermitianLatticeSubspace
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.DualInter

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)

noncomputable def hfL (y : Fin n → E) : (Fin n → E) →ₗ[E] E where
  toFun x := hf L Hm x y
  map_add' a b := by simp [hf, add_mul, Finset.sum_add_distrib]
  map_smul' c a := by simp [hf, Finset.mul_sum, mul_assoc]

noncomputable def hfR (x : Fin n → E) : (Fin n → E) →+ E where
  toFun y := hf L Hm x y
  map_add' a b := by simp [hf, mul_add, Finset.sum_add_distrib]
  map_zero' := by simp [hf]

theorem sub_l (a b y : Fin n → E) : hf L Hm (a - b) y = hf L Hm a y - hf L Hm b y :=
  (hfL L Hm y).map_sub a b

theorem smul_l (c : E) (a y : Fin n → E) : hf L Hm (c • a) y = c * hf L Hm a y :=
  (hfL L Hm y).map_smul c a

theorem sum_l {ι : Type} (s : Finset ι) (a : ι → Fin n → E) (y : Fin n → E) :
    hf L Hm (∑ i ∈ s, a i) y = ∑ i ∈ s, hf L Hm (a i) y :=
  map_sum (hfL L Hm y) a s

theorem sub_r (x a b : Fin n → E) : hf L Hm x (a - b) = hf L Hm x a - hf L Hm x b :=
  (hfR L Hm x).map_sub a b

theorem sum_r {ι : Type} (s : Finset ι) (a : ι → Fin n → E) (x : Fin n → E) :
    hf L Hm x (∑ i ∈ s, a i) = ∑ i ∈ s, hf L Hm x (a i) :=
  map_sum (hfR L Hm x) a s

theorem smul_r (c : E) (x a : Fin n → E) : hf L Hm x (c • a) = L.cj c * hf L Hm x a := by
  simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

variable {L Hm}

theorem cj_hf (h : IsHermND L Hm) (x y : Fin n → E) : L.cj (hf L Hm x y) = hf L Hm y x := by
  have hH : ∀ i j, L.cj (Hm i j) = Hm j i := fun i j => congrFun (congrFun h.1 j) i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hf, map_sum, map_mul, hH, L.cj_cj]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem eq_zero_of_hf (h : IsHermND L Hm) {y : Fin n → E} (hy : ∀ x, hf L Hm x y = 0) : y = 0 := by
  have h1 : Hm.mulVec (fun j => L.cj (y j)) = 0 := by
    funext i
    have := hy (Pi.single i 1)
    simpa [hf, Pi.single_apply, Finset.sum_ite_eq, Matrix.mulVec, dotProduct, ite_mul] using this
  have h2 : (fun j => L.cj (y j)) = 0 := by
    have := congrArg (Hm⁻¹.mulVec) h1
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h.2, Matrix.one_mulVec,
      Matrix.mulVec_zero] at this
  funext j
  exact L.cj.injective (by simpa using congrFun h2 j)

theorem hf_eq_zero_of_span {S : Set (Fin n → E)} {y : Fin n → E} (hy : ∀ x ∈ S, hf L Hm x y = 0) :
    ∀ x ∈ Submodule.span E S, hf L Hm x y = 0 := fun x hx =>
  (Submodule.span_le (p := LinearMap.ker (hfL L Hm y))).2 hy hx

variable [IsNonarchimedeanLocalField F]

theorem exists_denom (L : LocE F E) (x : E) : ∃ d ∈ L.O, IsUnit d ∧ d * x ∈ L.O := by
  have := L.free
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; omega)
  have hx : IsAlgebraic 𝒪[F] x :=
    (IsFractionRing.isAlgebraic_iff 𝒪[F] F E).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨d, hd0, hd⟩ := hx.exists_integral_multiple
  refine ⟨algebraMap F E d, (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 d.2,
    (IsUnit.mk0 (d : F) fun h => hd0 (Subtype.ext h)).map _, (L.O_def _).2 ?_⟩
  rwa [Algebra.smul_def] at hd

theorem exists_denom_fg {Λ : Submodule L.O (Fin n → E)} (hΛ : Λ.FG) (y : Fin n → E) :
    ∃ d ∈ L.O, IsUnit d ∧ ∀ x ∈ Λ, d * hf L Hm x y ∈ L.O := by
  induction Λ, hΛ using Submodule.fg_induction with
  | singleton v =>
    obtain ⟨d, h1, h2, h3⟩ := exists_denom L (hf L Hm v y)
    refine ⟨d, h1, h2, fun x hx => ?_⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
    have : hf L Hm (a • v) y = a * hf L Hm v y := smul_l L Hm a v y
    rw [this, mul_left_comm]
    exact L.O.mul_mem a.2 h3
  | sup A B _ _ hA hB =>
    obtain ⟨d, h1, h2, h3⟩ := hA
    obtain ⟨e, k1, k2, k3⟩ := hB
    refine ⟨d * e, L.O.mul_mem h1 k1, h2.mul k2, fun x hx => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    have : hf L Hm (a + b) y = hf L Hm a y + hf L Hm b y := (hfL L Hm y).map_add a b
    rw [this, show d * e * (hf L Hm a y + hf L Hm b y)
      = e * (d * hf L Hm a y) + d * (e * hf L Hm b y) by ring]
    exact L.O.add_mem (L.O.mul_mem k1 (h3 a ha)) (L.O.mul_mem h1 (k3 b hb))

theorem exists_primitive [CharZero F] (h : IsHermND L Hm) {Λ : Submodule L.O (Fin n → E)}
    (hΛ : IsSD L Hm Λ) {y : Fin n → E} (hy : ∀ s : E, s • y = 0 → s = 0) :
    ∃ t : E, IsUnit t ∧ t • y ∈ Λ ∧ ∃ c ∈ Λ, hf L Hm (t • y) c = 1 := by
  have := L.free
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; omega)
  have : IsArtinianRing E := IsArtinianRing.of_finite F E
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hP : IsPrincipalIdealRing L.O := (GlobalTheory.UnramOrder.order_facts L ϖ hϖ).2.2.2.1
  obtain ⟨d, -, hd, hdx⟩ := exists_denom_fg (Hm := Hm) hΛ.1.1 y
  let I : Ideal L.O :=
    { carrier := {r | ∃ x ∈ Λ, (r : E) = d * hf L Hm x y}
      zero_mem' := ⟨0, Λ.zero_mem, by simp [hf]⟩
      add_mem' := by
        rintro r s ⟨a, ha, hr⟩ ⟨b, hb, hs⟩
        refine ⟨a + b, Λ.add_mem ha hb, ?_⟩
        have : hf L Hm (a + b) y = hf L Hm a y + hf L Hm b y := (hfL L Hm y).map_add a b
        rw [this, Subring.coe_add, hr, hs, mul_add]
      smul_mem' := by
        rintro s r ⟨a, ha, hr⟩
        refine ⟨s • a, Λ.smul_mem s ha, ?_⟩
        have : hf L Hm (s • a) y = s * hf L Hm a y := smul_l L Hm s a y
        rw [this, smul_eq_mul, Subring.coe_mul, hr, mul_left_comm] }
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal I).principal
  obtain ⟨c, hc, hgc⟩ : g ∈ I := by rw [hg]; exact Submodule.mem_span_singleton_self g
  have hdiv : ∀ x ∈ Λ, ∃ r ∈ L.O, hf L Hm x y = r * hf L Hm c y := by
    intro x hx
    have : (⟨_, hdx x hx⟩ : L.O) ∈ I := ⟨x, hx, rfl⟩
    rw [hg] at this
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 this
    have hr' : (r : E) * g = d * hf L Hm x y := congrArg Subtype.val hr
    refine ⟨r, r.2, hd.mul_left_cancel ?_⟩
    rw [← hr', hgc]; ring
  have hu : IsUnit (hf L Hm c y) := by
    refine IsArtinianRing.isUnit_of_mem_nonZeroDivisors (mem_nonZeroDivisors_iff_right.2 ?_)
    intro s hs
    have h1 : L.cj s • y = 0 := eq_zero_of_hf h fun x =>
      hf_eq_zero_of_span (S := Λ) (fun z hz => by
        obtain ⟨r, -, hr⟩ := hdiv z hz
        rw [smul_r, L.cj_cj, hr, mul_left_comm, hs, mul_zero]) x (by rw [hΛ.1.2]; trivial)
    exact L.cj.injective (by simpa using hy _ h1)
  obtain ⟨u, hu'⟩ := hu.exists_left_inv
  refine ⟨L.cj u, (IsUnit.of_mul_eq_one _ hu').map _, (hΛ.2 _).1 fun x hx => ?_, c, hc, ?_⟩
  · obtain ⟨r, hr0, hr⟩ := hdiv x hx
    rw [smul_r, L.cj_cj, hr, mul_left_comm, hu', mul_one]
    exact hr0
  · rw [← cj_hf h, smul_r, L.cj_cj, hu', map_one]

theorem exists_dual_family [CharZero F] (h : IsHermND L Hm) {Λ : Submodule L.O (Fin n → E)}
    (hΛ : IsSD L Hm Λ) (m : ℕ) (y : Fin m → Fin n → E) (hy : LinearIndependent E y) :
    ∃ b c : Fin m → Fin n → E, (∀ i, b i ∈ Λ) ∧ (∀ j, c j ∈ Λ) ∧
      Submodule.span E (Set.range b) = Submodule.span E (Set.range y) ∧
      ∀ i j, hf L Hm (b i) (c j) = if i = j then 1 else 0 := by
  induction m with
  | zero => exact ⟨y, y, fun i => i.elim0, fun i => i.elim0, rfl, fun i => i.elim0⟩
  | succ m ih =>
    obtain ⟨b, c, hb, hc, hspan, hbc⟩ := ih (Fin.tail y) (hy.comp _ (Fin.succ_injective m))
    set w := ∑ j, hf L Hm (y 0) (c j) • b j with hw
    have hwm : w ∈ Submodule.span E (Set.range b) :=
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have hz : ∀ j, hf L Hm (y 0 - w) (c j) = 0 := fun j => by
      simp [hw, sub_l, sum_l, smul_l, hbc]
    obtain ⟨t, ht, htm, c', hc', htc⟩ := exists_primitive h hΛ (y := y 0 - w) (fun s hs => by
      refine hy.eq_zero_of_smul_mem_span 0 s ?_
      rw [smul_sub, sub_eq_zero] at hs
      rw [hs]
      refine Submodule.smul_mem _ _ (Submodule.span_mono ?_ (hspan ▸ hwm))
      rintro _ ⟨j, rfl⟩
      exact ⟨j.succ, by simp, rfl⟩)
    have hc0 : c' - ∑ j, hf L Hm c' (b j) • c j ∈ Λ :=
      Λ.sub_mem hc' (Λ.sum_mem fun j _ => Λ.smul_mem ⟨_, (hΛ.2 _).2 (hb j) _ hc'⟩ (hc j))
    refine ⟨Fin.cons (t • (y 0 - w)) b, Fin.cons (c' - ∑ j, hf L Hm c' (b j) • c j) c,
      fun i => Fin.cases htm hb i, fun i => Fin.cases hc0 hc i, ?_, fun i j => ?_⟩
    · rw [Fin.range_cons, Fin.range_fin_succ y, Submodule.span_insert, Submodule.span_insert,
        ← hspan, ← Submodule.span_singleton_smul_eq ht (y 0)]
      have hwt := Submodule.smul_mem _ t hwm
      rw [smul_sub]
      refine le_antisymm (sup_le ?_ le_sup_right) (sup_le ?_ le_sup_right) <;>
        rw [Submodule.span_singleton_le_iff_mem]
      · exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))
          (Submodule.mem_sup_right hwt)
      · have := Submodule.add_mem _ (Submodule.mem_sup_left
          (Submodule.mem_span_singleton_self (t • y 0 - t • w))) (Submodule.mem_sup_right hwt)
        rwa [sub_add_cancel] at this
    · refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Fin.cons_zero, sub_r, sum_r, smul_r, htc]
        simp [smul_l L Hm t, hz]
      · simp [smul_l L Hm t, hz, (Fin.succ_ne_zero j).symm]
      · simp [sub_r, sum_r, smul_r, hbc, cj_hf h]
      · simp [hbc]

theorem dual_inter : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λ, IsSD L Hm Λ → ∀ (m : ℕ) (y : Fin m → Fin n → E), LinearIndependent E y → perp L Hm (perp L Hm (Submodule.span E (Set.range y))) = (Submodule.span E (Set.range y)) ∧ (∀ v, (∀ x ∈ Λ, x ∈ perp L Hm (Submodule.span E (Set.range y)) → hf L Hm x v ∈ L.O) ↔ ∃ a ∈ Λ, v - a ∈ (Submodule.span E (Set.range y))) ∧ (∀ v, (∀ x ∈ Λ, x ∈ (Submodule.span E (Set.range y)) → hf L Hm x v ∈ L.O) ↔ ∃ a ∈ Λ, v - a ∈ perp L Hm (Submodule.span E (Set.range y))) ∧ ∃ b : Fin m → Fin n → E, ∃ c : Fin m → Fin n → E, Λ ⊓ (Submodule.span E (Set.range y)).restrictScalars L.O = Submodule.span L.O (Set.range b) ∧ (∀ j, c j ∈ Λ) ∧ ∀ i j, hf L Hm (b i) (c j) = if i = j then 1 else 0 := by
  intro F _ _ _ _ _ E _ _ _ L n Hm h Λ hΛ m y hy
  obtain ⟨b, c, hb, hc, hspan, hbc⟩ := exists_dual_family h hΛ m y hy
  rw [← hspan]
  set Y := Submodule.span E (Set.range b) with hY
  have hbY : ∀ j, b j ∈ Y := fun j => Submodule.subset_span ⟨j, rfl⟩
  have hsym : ∀ x v, hf L Hm x v = 0 → hf L Hm v x = 0 := fun x v hx => by
    rw [← cj_hf h, hx, map_zero]
  have hperp : ∀ x, (∀ i, hf L Hm (b i) x = 0) → x ∈ perp L Hm Y := fun x hx v hv =>
    hsym _ _ (hf_eq_zero_of_span (by rintro _ ⟨i, rfl⟩; exact hx i) v hv)
  have hproj : ∀ x, x - ∑ j, hf L Hm x (b j) • c j ∈ perp L Hm Y := fun x =>
    hperp _ fun i => by simp [sub_r, sum_r, smul_r, hbc, cj_hf h]
  have hadj : ∀ x v, hf L Hm x (v - ∑ j, hf L Hm v (c j) • b j)
      = hf L Hm (x - ∑ j, hf L Hm x (b j) • c j) v := fun x v => by
    simp [sub_r, sum_r, smul_r, sub_l, sum_l, smul_l, cj_hf h, mul_comm]
  have hsum : ∀ v, ∑ j, hf L Hm v (c j) • b j ∈ Y := fun v =>
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hbY j)
  have hpp : ∀ v, (∀ x ∈ perp L Hm Y, hf L Hm x v = 0) → v = ∑ j, hf L Hm v (c j) • b j :=
    fun v hv => sub_eq_zero.1 (eq_zero_of_hf h fun x => by rw [hadj]; exact hv _ (hproj x))
  refine ⟨?_, fun v => ⟨fun hv => ?_, ?_⟩, fun v => ⟨fun hv => ?_, ?_⟩, b, c, ?_, hc, hbc⟩
  · ext v
    refine ⟨fun hv => ?_, fun hv x hx => hsym _ _ (hx v hv)⟩
    rw [hpp v fun x hx => hsym _ _ (hv x hx)]
    exact hsum v
  · refine ⟨v - ∑ j, hf L Hm v (c j) • b j, (hΛ.2 _).1 fun x hx => ?_, by simpa using hsum v⟩
    rw [hadj]
    refine hv _ (Λ.sub_mem hx (Λ.sum_mem fun j _ => ?_)) (hproj x)
    exact Λ.smul_mem ⟨_, (hΛ.2 _).2 (hb j) _ hx⟩ (hc j)
  · rintro ⟨a, ha, hva⟩ x hx hxp
    have := hxp _ hva
    rw [sub_r, sub_eq_zero] at this
    rw [this]
    exact (hΛ.2 _).2 ha x hx
  · refine ⟨_, Λ.sum_mem fun j _ => ?_, hproj v⟩
    have : hf L Hm v (b j) ∈ L.O := by
      rw [← cj_hf h]
      exact GlobalTheory.UnramOrder.cj_mem L (hv _ (hb j) (hbY j))
    exact Λ.smul_mem ⟨_, this⟩ (hc j)
  · rintro ⟨a, ha, hva⟩ x hx hxp
    have := hsym _ _ (hva x hxp)
    rw [sub_r, sub_eq_zero] at this
    rw [this]
    exact (hΛ.2 _).2 ha x hx
  · refine le_antisymm ?_ (Submodule.span_le.2 ?_)
    · rintro v ⟨hv, hvY⟩
      rw [hpp v fun x hx => hx v hvY]
      refine Submodule.sum_mem _ fun j _ => ?_
      exact Submodule.smul_mem (Submodule.span L.O (Set.range b))
        ⟨_, (hΛ.2 _).2 (hc j) _ hv⟩ (Submodule.subset_span ⟨j, rfl⟩)
    · rintro _ ⟨j, rfl⟩
      exact ⟨hb j, hbY j⟩

end GlobalTheory.HL.DualInter
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EichlerMapMemUnipotentCharacter
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.EichlerUnip
open GlobalTheory.HL.Eichler

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem spanTo_mono (g : Fin (r + 1) → S.V) {a b : ℕ} (h : a ≤ b) : S.spanTo g a ≤ S.spanTo g b :=
  Submodule.span_mono (Set.image_mono fun _ hi => lt_of_lt_of_le hi h)

theorem mem_spanTo (g : Fin (r + 1) → S.V) {a : ℕ} (i : Fin (r + 1)) (h : (i : ℕ) < a) :
    g i ∈ S.spanTo g a := Submodule.subset_span ⟨i, h, rfl⟩

theorem hf_spanTo (g : Fin (r + 1) → S.V) {a : ℕ} (y : S.V)
    (h : ∀ i : Fin (r + 1), (i : ℕ) < a → hf L S.Hm (g i) y = 0) {x : S.V} (hx : x ∈ S.spanTo g a) :
    hf L S.Hm x y = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨i, hi, rfl⟩ := hx; exact h i hi
  | zero => simp [hf]
  | add a b _ _ ha hb => rw [hf_add_l, ha, hb, add_zero]
  | smul c a _ ha => rw [hf_smul_l, ha, mul_zero]

theorem hf_symm0 {x y : S.V} (h : hf L S.Hm x y = 0) : hf L S.Hm y x = 0 := by
  rw [← hf_cj L S.herm.1, h, map_zero]

theorem mem_unipOn {N : ℕ} {A B : Submodule E (Fin N → E)} (hBA : B ≤ A)
    (n : (Fin N → E) ≃ₗ[E] (Fin N → E)) (h1 : ∀ v ∈ A, n v - v ∈ B) (h2 : ∀ v ∈ A, n⁻¹ v - v ∈ B) :
    n ∈ unipOn A B := by
  refine ⟨fun v => ⟨fun hv => ?_, fun hv => ?_⟩, h1⟩
  · have h3 := A.add_mem (hBA (h2 _ hv)) hv
    have h4 : n⁻¹ (n v) = v := n.symm_apply_apply v
    rw [h4] at h3
    simpa using h3
  · simpa using A.add_mem (hBA (h1 _ hv)) hv

end

theorem eichler_mem_unip : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (g : Fin (r + 1) → S.V) (gs : Fin r → S.V), (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es') → ∀ (j : Fin r) (x u : S.V) (s : E), x ∈ S.spanTo g (j + 1) → u ∈ perp L S.Hm (S.spanTo g (j + 1)) → s + L.cj s = S.h u u → ∃ n ∈ S.Nof g, (∀ v, n v = eich L S.Hm x u s v) ∧ (∀ v, n⁻¹ v = eich L S.Hm x (-u) (L.cj s) v) ∧ (∀ v ∈ S.spanTo g (j + 1), n v = v) ∧ ∀ m ∈ S.Nof g, S.psiOf g gs n = L.psi0 (algebraMap F E S.th⁻¹ * (S.h x (gs j) * S.h (m (g j.succ)) u)) := by
  intro F _ _ _ _ _ E _ _ _ L r k S g gs hg j x u s hx hu hs
  have hgram : ∀ a b : Fin (r + 1), (b : ℕ) < r → hf L S.Hm (g a) (g b) = 0 := by
    intro a b hb
    have hb' : b ≠ Fin.last r := fun h => by simp [h] at hb
    rcases hg with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · rw [S.gram]; simp [hb']
    · rw [S.gram']; simp [hb']
  have hdual : ∀ a i, hf L S.Hm (g a) (gs i) = if a = i.castSucc then 1 else 0 := by
    intro a i
    rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact S.dual a i
    · exact S.dual' a i
  have hjr : (j : ℕ) + 1 ≤ r := j.2
  have hgX : ∀ a, ∀ y ∈ S.spanTo g r, hf L S.Hm (g a) y = 0 := fun a y hy =>
    hf_symm0 S (hf_spanTo S g _ (fun i hi => hf_symm0 S (hgram a i hi)) hy)
  have hXX : ∀ {c : ℕ}, ∀ v ∈ S.spanTo g c, v ∈ perp L S.Hm (S.spanTo g r) := fun v hv y hy =>
    hf_spanTo S g y (fun i _ => hgX i y hy) hv
  have hxr : x ∈ S.spanTo g r := spanTo_mono S g hjr hx
  have hE : ∀ (u : S.V) (s : E), ∀ v ∈ perp L S.Hm (S.spanTo g r),
      eich L S.Hm x u s v - v = hf L S.Hm v u • x := by
    intro u s v hv
    simp only [eich, hv x hxr]
    module
  have hfl : ∀ u ∈ perp L S.Hm (S.spanTo g (j + 1)), ∀ (s : E) (i : ℕ), ∀ v ∈ S.spanTo g (i + 1),
      eich L S.Hm x u s v - v ∈ S.spanTo g i := by
    intro u hu s i v hv
    rw [hE u s v (hXX v hv)]
    rcases le_or_gt i j with h | h
    · rw [hf_symm0 S (hu v (spanTo_mono S g (by omega) hv)), zero_smul]
      exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (spanTo_mono S g h hx)
  obtain ⟨n, hn, h1, h2⟩ := eichler_isometry L S.Hm S.herm x u s (hXX x hx x hxr) (hu x hx) hs
  refine ⟨n, ⟨⟨hn, ?_⟩, ?_⟩, h1, h2, ?_, ?_⟩
  · refine Subgroup.mem_iInf.2 fun i => ?_
    refine mem_unipOn (spanTo_mono S g (by omega)) n (fun v hv => ?_) (fun v hv => ?_)
    · rw [h1]; exact hfl u hu s i v hv
    · rw [h2]; exact hfl _ (Submodule.neg_mem _ hu) _ i v hv
  · refine mem_unipOn (fun v hv => hXX v hv) n (fun v hv => ?_) (fun v hv => ?_)
    · rw [h1, hE _ _ v hv]; exact Submodule.smul_mem _ _ hxr
    · rw [h2, hE _ _ v hv]; exact Submodule.smul_mem _ _ hxr
  · intro v hv
    have := hE u s v (hXX v hv)
    rw [hf_symm0 S (hu v hv), zero_smul, sub_eq_zero] at this
    rw [h1, this]
  · rintro m ⟨⟨-, hm1⟩, hm2⟩
    replace hm1 := Subgroup.mem_iInf.1 hm1
    have hm : m (g j.succ) - g j.succ ∈ S.spanTo g (j + 1) := by
      rcases hjr.lt_or_eq with h | h
      · exact (hm1 ⟨j + 1, h⟩).2 _ (mem_spanTo S g _ (by simp))
      · have := hm2.2 (g j.succ) (hgX _)
        exact spanTo_mono S g h.ge this
    have hmu : hf L S.Hm (m (g j.succ)) u = hf L S.Hm (g j.succ) u := by
      have := hf_symm0 S (hu _ hm)
      rwa [hf_sub_l, sub_eq_zero] at this
    have hc : ∀ i : Fin r, S.coef g gs n i = hf L S.Hm x (gs i) * hf L S.Hm (g i.succ) u := by
      intro i
      have h3 := hE u s (g i.succ) (hgX _)
      rw [sub_eq_iff_eq_add, ← h1] at h3
      have h4 : i.succ ≠ i.castSucc := (Fin.castSucc_lt_succ).ne'
      simp only [Frames.coef, Frames.h]
      rw [h3, hf_add_l, hf_smul_l, hdual, if_neg h4]
      ring
    have hsum : ∑ i, S.coef g gs n i = S.h x (gs j) * S.h (m (g j.succ)) u := by
      simp only [Frames.h]
      rw [Finset.sum_eq_single j, hc, hmu]
      · intro i _ hij
        rw [hc]
        rcases lt_or_gt_of_ne hij with h | h
        · have h' : (i : ℕ) < j := h
          rw [hf_symm0 S (hu _ (mem_spanTo S g i.succ (by simp; omega))), mul_zero]
        · have h' : (j : ℕ) < i := h
          rw [hf_spanTo S g (gs i) (fun a ha => ?_) hx, zero_mul]
          rw [hdual, if_neg]
          rintro rfl
          simp at ha
          omega
      · simp
    simp only [Frames.psiOf, hsum]

end GlobalTheory.HL.EichlerUnip
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEqZpowMulUnit
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.UnramVal

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem zpow_mul_unit_mem_iff {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (k : ℤ) (u : (𝒪[F])ˣ) :
    (ϖ : F) ^ k * ((u : 𝒪[F]) : F) ∈ 𝒪[F] ↔ 0 ≤ k := by
  have h0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  constructor
  · intro h
    by_contra hk
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = -((n : ℤ) + 1) := ⟨(-k - 1).toNat, by omega⟩
    refine hϖ.not_isUnit (IsUnit.of_mul_eq_one (ϖ ^ n * ⟨_, h⟩ * ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F])) ?_)
    apply Subtype.ext
    have hu : ((u : 𝒪[F]) : F) * (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) = 1 := by
      rw [← Subring.coe_mul, Units.mul_inv]; rfl
    have h1 : (ϖ : F) * (ϖ : F) ^ n * (ϖ : F) ^ (-((n : ℤ) + 1)) = 1 := by
      rw [zpow_neg, zpow_add_one₀ h0, zpow_natCast]
      field_simp
    simp only [Subring.coe_mul, Subring.coe_pow, Subring.coe_one]
    linear_combination (((u : 𝒪[F]) : F) * (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F)) * h1 + hu
  · intro hk
    lift k to ℕ using hk
    rw [zpow_natCast]
    exact Subring.mul_mem _ (Subring.pow_mem _ ϖ.2 k) (u : 𝒪[F]).2

variable [IsNonarchimedeanLocalField F]

theorem vE_zpow_mul_unit (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (k : ℤ)
    (u : (𝒪[F])ˣ) : vE L ϖ (algebraMap F E ((ϖ : F) ^ k * ((u : 𝒪[F]) : F))) = k := by
  have h0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hset : {m : ℤ | ∃ y ∈ L.O, algebraMap F E ((ϖ : F) ^ k * ((u : 𝒪[F]) : F))
      = algebraMap F E ((ϖ : F) ^ m) * y} = Set.Iic k := by
    ext m
    have hsplit : (ϖ : F) ^ k * ((u : 𝒪[F]) : F)
        = (ϖ : F) ^ m * ((ϖ : F) ^ (k - m) * ((u : 𝒪[F]) : F)) := by
      rw [← mul_assoc, ← zpow_add₀ h0]; congr 2; ring
    have hun : IsUnit (algebraMap F E ((ϖ : F) ^ m)) :=
      (IsUnit.mk0 _ (zpow_ne_zero m h0)).map _
    simp only [Set.mem_ofPred_eq, Set.mem_Iic]
    rw [hsplit, map_mul, ← sub_nonneg, ← zpow_mul_unit_mem_iff hϖ (k - m) u,
      ← GlobalTheory.UnramOrder.algebraMap_mem_iff L]
    constructor
    · rintro ⟨y, hy, h⟩
      rw [hun.mul_left_cancel h]; exact hy
    · intro h; exact ⟨_, h, rfl⟩
  rw [vE, hset, csSup_Iic]

theorem exists_eq_zpow_mul_unit {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {x : F} (hx : x ≠ 0) :
    ∃ (k : ℤ) (u : (𝒪[F])ˣ), x = (ϖ : F) ^ k * ((u : 𝒪[F]) : F) := by
  obtain ⟨k, u, h⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ hx
  refine ⟨k, u, ?_⟩
  rw [h, mul_comm]; rfl

theorem vE_valuation : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ → (∀ x y : F, x ≠ 0 → y ≠ 0 → vE L ϖ (algebraMap F E (x * y)) = vE L ϖ (algebraMap F E x) + vE L ϖ (algebraMap F E y)) ∧ vE L ϖ (algebraMap F E (ϖ : F)) = 1 ∧ (∀ x : F, x ≠ 0 → (0 ≤ vE L ϖ (algebraMap F E x) ↔ x ∈ 𝒪[F])) ∧ (∀ x : F, x ≠ 0 → ∃ u : (𝒪[F])ˣ, x = (ϖ : F) ^ (vE L ϖ (algebraMap F E x)) * ((u : 𝒪[F]) : F)) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ
  have h0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  refine ⟨fun x y hx hy => ?_, ?_, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨k, u, rfl⟩ := exists_eq_zpow_mul_unit hϖ hx
    obtain ⟨l, v, rfl⟩ := exists_eq_zpow_mul_unit hϖ hy
    have : (ϖ : F) ^ k * ((u : 𝒪[F]) : F) * ((ϖ : F) ^ l * ((v : 𝒪[F]) : F))
        = (ϖ : F) ^ (k + l) * (((u * v : (𝒪[F])ˣ) : 𝒪[F]) : F) := by
      rw [zpow_add₀ h0, Units.val_mul, Subring.coe_mul]; ring
    rw [this, vE_zpow_mul_unit L hϖ, vE_zpow_mul_unit L hϖ, vE_zpow_mul_unit L hϖ]
  · simpa using vE_zpow_mul_unit L hϖ 1 1
  · obtain ⟨k, u, rfl⟩ := exists_eq_zpow_mul_unit hϖ hx
    rw [vE_zpow_mul_unit L hϖ, zpow_mul_unit_mem_iff hϖ]
  · obtain ⟨k, u, rfl⟩ := exists_eq_zpow_mul_unit hϖ hx
    exact ⟨u, by rw [vE_zpow_mul_unit L hϖ]⟩

end GlobalTheory.UnramVal
end

