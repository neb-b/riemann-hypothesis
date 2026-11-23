module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassOrbitsEqTsumFiber
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem encard_eq_tsum_fiber {X Z : Type*} (q : X → Z) (Q : X → Prop) :
    (({x | Q x} : Set X).encard : ℝ≥0∞)
      = ∑' z : Z, (({x | q x = z ∧ Q x} : Set X).encard : ℝ≥0∞) := by
  have e : ∀ S : Set X, (S.encard : ℝ≥0∞) = ∑' x, S.indicator (fun _ => (1 : ℝ≥0∞)) x := by
    intro S
    rw [← ENNReal.tsum_set_one, tsum_subtype S (fun _ => (1 : ℝ≥0∞))]
  simp only [e]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun x => ?_
  rw [tsum_eq_single (q x)]
  · simp [Set.indicator]
  · intro z hz
    have : ¬ q x = z := fun h => hz h.symm
    simp [Set.indicator, this]

theorem encard_orbit_fiber {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]
    (H : Subgroup G) (P : X → Prop) (π : X → Y)
    (hP : ∀ h ∈ H, ∀ x, P x → P (h • x) ∧ π (h • x) = h • π x) (x : X) (hx : P x)
    (hfin : (H ⊓ MulAction.stabilizer G x).relIndex (H ⊓ MulAction.stabilizer G (π x)) ≠ 0) :
    ({z | (Quotient.mk'' z : MulAction.orbitRel.Quotient H X) = Quotient.mk'' x ∧
        P z ∧ π z = π x} : Set X).encard
      = (H ⊓ MulAction.stabilizer G x).relIndex (H ⊓ MulAction.stabilizer G (π x)) := by
  have h1 : ({z | (Quotient.mk'' z : MulAction.orbitRel.Quotient H X) = Quotient.mk'' x ∧
        P z ∧ π z = π x} : Set X)
      = MulAction.orbit (↥(H ⊓ MulAction.stabilizer G (π x))) x := by
    ext z
    simp only [Set.mem_setOf_eq, Quotient.eq'', MulAction.orbitRel_apply]
    constructor
    · rintro ⟨⟨h, rfl⟩, -, hz⟩
      have h2 := (hP h h.2 x hx).2
      exact ⟨⟨h, h.2, h2.symm.trans hz⟩, rfl⟩
    · rintro ⟨⟨h, hh, hs⟩, rfl⟩
      have h2 := hP h hh x hx
      exact ⟨⟨⟨h, hh⟩, rfl⟩, h2.1, h2.2.trans hs⟩
  have h2 : (H ⊓ MulAction.stabilizer G x).relIndex (H ⊓ MulAction.stabilizer G (π x))
      = (MulAction.orbit (↥(H ⊓ MulAction.stabilizer G (π x))) x).ncard := by
    rw [← MulAction.index_stabilizer, Subgroup.relIndex]
    congr 1
    ext ⟨h, hh, hs⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
    exact ⟨fun a => a.2, fun a => ⟨hh, a⟩⟩
  rw [h1, h2]
  rw [h2] at hfin
  exact (Set.finite_of_ncard_ne_zero hfin).cast_ncard_eq.symm

theorem mass_orbits_eq_tsum_fiber : ∀ {G X Y : Type} [Group G] [MulAction G X] [MulAction G Y] (H K0 : Subgroup G) (P : X → Prop) (π : X → Y), K0 ≤ H → (∀ h ∈ H, ∀ x, P x → P (h • x) ∧ π (h • x) = h • π x ∧ invVol K0 (H ⊓ MulAction.stabilizer G (h • x)) = invVol K0 (H ⊓ MulAction.stabilizer G x)) → (∀ x, P x → K0.relIndex (H ⊓ MulAction.stabilizer G x) ≠ 0 ∧ (H ⊓ MulAction.stabilizer G x).relIndex K0 ≠ 0 ∧ K0.relIndex (H ⊓ MulAction.stabilizer G (π x)) ≠ 0 ∧ (H ⊓ MulAction.stabilizer G (π x)).relIndex K0 ≠ 0) → (∑' o : MulAction.orbitRel.Quotient H X, if P o.out then ENNReal.ofReal (invVol K0 (H ⊓ MulAction.stabilizer G o.out)) else 0) = ∑' c : MulAction.orbitRel.Quotient H Y, ENNReal.ofReal (invVol K0 (H ⊓ MulAction.stabilizer G c.out)) * (({x | P x ∧ π x = c.out} : Set X).encard : ℝ≥0∞) := by
  intro G X Y _ _ _ H K0 P π _ hP hc
  have hP' : ∀ h ∈ H, ∀ x, P x → P (h • x) ∧ π (h • x) = h • π x :=
    fun h hh x hx => ⟨(hP h hh x hx).1, (hP h hh x hx).2.1⟩
  simp only [fun c : MulAction.orbitRel.Quotient H Y =>
    encard_eq_tsum_fiber (fun z : X => (Quotient.mk'' z : MulAction.orbitRel.Quotient H X))
      (fun x => P x ∧ π x = c.out), ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun o => ?_
  have hmem : ∀ z : X, (Quotient.mk'' z : MulAction.orbitRel.Quotient H X) = o →
      ∃ h ∈ H, h • z = o.out := by
    intro z hz
    have : (Quotient.mk'' o.out : MulAction.orbitRel.Quotient H X) = Quotient.mk'' z := by
      rw [hz]; exact Quotient.out_eq' o
    rw [Quotient.eq'', MulAction.orbitRel_apply] at this
    obtain ⟨h, hh⟩ := this
    exact ⟨h, h.2, hh⟩
  split_ifs with ho
  · set c0 : MulAction.orbitRel.Quotient H Y := Quotient.mk'' (π o.out) with hc0
    rw [tsum_eq_single c0]
    · have : (Quotient.mk'' c0.out : MulAction.orbitRel.Quotient H Y) = Quotient.mk'' (π o.out) :=
        Quotient.out_eq' c0
      rw [Quotient.eq'', MulAction.orbitRel_apply] at this
      obtain ⟨⟨h, hh⟩, hy⟩ := this
      have hy' : h • π o.out = c0.out := hy
      obtain ⟨p1, p2, p3⟩ := hP h hh _ ho
      have ho' : o = Quotient.mk'' (h • o.out) := by
        conv_lhs => rw [← Quotient.out_eq' o]
        symm
        rw [Quotient.eq'', MulAction.orbitRel_apply]
        exact ⟨⟨h, hh⟩, rfl⟩
      rw [← p3, ← hy', ← p2]
      generalize h • o.out = x at p1 ho'
      obtain ⟨a1, a2, a3, a4⟩ := hc x p1
      have hle : H ⊓ MulAction.stabilizer G x ≤ H ⊓ MulAction.stabilizer G (π x) := by
        rintro g ⟨g1, g2⟩
        refine ⟨g1, ?_⟩
        have g3 : g • x = x := g2
        have := (hP' g g1 x p1).2
        rw [g3] at this
        exact this.symm
      obtain ⟨-, -, b, -⟩ := invVol_mul_pos_le_conj K0 _ _ a3 a4 a1 a2
      rw [ho', encard_orbit_fiber H P π hP' x p1 (Subgroup.relIndex_ne_zero_trans a2 a3), b hle,
        ENNReal.ofReal_mul' (Nat.cast_nonneg _)]
      simp
    · intro c hne
      have : ({x | (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) = o ∧ P x ∧ π x = c.out} :
          Set X) = ∅ := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨h1, h2, h3⟩
        obtain ⟨h, hh, e⟩ := hmem z h1
        apply hne
        rw [hc0, ← e, (hP' h hh z h2).2, h3]
        conv_lhs => rw [← Quotient.out_eq' c]
        symm
        rw [Quotient.eq'', MulAction.orbitRel_apply]
        exact ⟨⟨h, hh⟩, rfl⟩
      rw [this]; simp
  · symm
    refine ENNReal.tsum_eq_zero.2 fun c => ?_
    have : ({x | (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) = o ∧ P x ∧ π x = c.out} :
        Set X) = ∅ := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2, -⟩
      obtain ⟨h, hh, e⟩ := hmem z h1
      exact ho (e ▸ (hP' h hh z h2).1)
    rw [this]; simp

end GlobalTheory.HL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemStabilizerSpanIffUnitriangularIntegral
section
open Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise

namespace GlobalTheory.HL

theorem span_pointwise_le_of_int {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : LocE F E) {N m : ℕ} (v : Fin m → Fin N → E)
    (h : (Fin N → E) ≃ₗ[E] (Fin N → E)) (M : Matrix (Fin m) (Fin m) E) (hM : IsIntM L M)
    (hv : ∀ b, h (v b) = ∑ a, M a b • v a) :
    h • Submodule.span L.O (Set.range v) ≤ Submodule.span L.O (Set.range v) := by
  rw [Submodule.smul_span, Submodule.span_le]
  rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
  show h (v b) ∈ _
  rw [hv b]
  refine Submodule.sum_mem _ fun a _ => ?_
  have : M a b • v a = (⟨M a b, hM a b⟩ : L.O) • v a := rfl
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem unistab_iff : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) {N m : ℕ} (v : Fin m → Fin N → E), LinearIndependent E v → ∀ (g : (Fin N → E) ≃ₗ[E] (Fin N → E)) (M : Matrix (Fin m) (Fin m) E), IsUni M → (∀ b, g (v b) = ∑ a, M a b • v a) → (g ∈ MulAction.stabilizer ((Fin N → E) ≃ₗ[E] (Fin N → E)) (Submodule.span L.O (Set.range v)) ↔ IsIntM L M) := by
  intro F _ _ _ E _ _ _ L N m v hli g M hU hg
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro hst a b
    have hmem : g (v b) ∈ Submodule.span L.O (Set.range v) := by
      rw [← hst]
      exact Submodule.smul_mem_pointwise_smul (v b) g _ (Submodule.subset_span ⟨b, rfl⟩)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).1 hmem
    rw [hg b] at hc
    have h0 : ∑ i, (M i b - (c i : E)) • v i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← hc]
      simp [Subring.smul_def]
    have := (Fintype.linearIndependent_iff.1 hli) _ h0 a
    rw [sub_eq_zero] at this
    rw [this]
    exact (c a).2
  · intro hM
    have hdet : M.det = 1 := by
      rw [Matrix.det_of_upperTriangular (fun i j hij => hU.1 i j hij)]
      simp [hU.2]
    let M₀ : Matrix (Fin m) (Fin m) L.O := fun i j => ⟨M i j, hM i j⟩
    have hM₀ : M₀.map L.O.subtype = M := by ext i j; rfl
    have hadj : IsIntM L M.adjugate := by
      intro i j
      have e := congrFun (congrFun (RingHom.map_adjugate L.O.subtype M₀) i) j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at e
      rw [hM₀] at e
      rw [← e]
      exact (M₀.adjugate i j).2
    have hinv : ∀ b, g⁻¹ (v b) = ∑ a, M.adjugate a b • v a := by
      intro b
      have key : g (∑ a, M.adjugate a b • v a) = v b := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_smul, hg, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        have : ∀ c, ∑ a, (M.adjugate a b * M c a) • v c = (M * M.adjugate) c b • v c := by
          intro c
          rw [← Finset.sum_smul, Matrix.mul_apply]
          congr 1
          exact Finset.sum_congr rfl fun a _ => mul_comm _ _
        simp only [this, Matrix.mul_adjugate, hdet, one_smul]
        simp [Matrix.one_apply]
      rw [← key]
      exact g.symm_apply_apply _
    apply le_antisymm
    · exact span_pointwise_le_of_int L v g M hM hg
    · intro x hx
      have hx' : g⁻¹ • x ∈ Submodule.span L.O (Set.range v) :=
        span_pointwise_le_of_int L v g⁻¹ M.adjugate hadj hinv
          (Submodule.smul_mem_pointwise_smul x g⁻¹ _ hx)
      have := Submodule.smul_mem_pointwise_smul (g⁻¹ • x) g _ hx'
      rwa [smul_inv_smul] at this

end GlobalTheory.HL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericDatumLatticeEqPerpQuotientImageTerm
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

noncomputable section

namespace GlobalTheory.InnerRead

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

def hL (y : V) : V →+ E := ⟨⟨fun x => H.h x y, H.h_zero_left y⟩, fun x x' => H.h_add_left x x' y⟩

lemma h_add_right (x y z : V) : H.h x (y + z) = H.h x y + H.h x z := by
  rw [H.h_herm (y + z) x, H.h_add_left, map_add (f := _), ← H.h_herm, ← H.h_herm]

lemma h_smul_right (c : E) (x y : V) : H.h x (c • y) = M.L.cj c * H.h x y := by
  rw [H.h_herm (c • y) x, H.h_smul_left, map_mul, ← H.h_herm]

lemma h_zero_right (x : V) : H.h x 0 = 0 := by
  have := h_smul_right H 0 x 0
  simpa using this

lemma h_sub_left (x y z : V) : H.h (x - y) z = H.h x z - H.h y z := map_sub (hL H z) x y

lemma h_sum_left {ι : Type} (s : Finset ι) (u : ι → V) (y : V) :
    H.h (∑ i ∈ s, u i) y = ∑ i ∈ s, H.h (u i) y := map_sum (hL H y) u s

lemma mkW_eq {r : ℕ} {f : Fin (r + 1) → V} (x y : ↥(H.perp (H.X f))) (h : (x : V) - y ∈ H.X f) :
    H.mkW f x = H.mkW f y := by
  unfold HermSp.mkW
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  simpa using h

def Good (X : Submodule E V) (u : V ≃ₗ[E] V) : Prop :=
  IsUnitary H u ∧ ∀ v ∈ H.perp X, u v - v ∈ X

lemma good_map_le {X : Submodule E V} {u : V ≃ₗ[E] V} (hX : X ≤ H.perp X) (hu : Good H X u) :
    ∀ x ∈ X, u x ∈ X := by
  intro x hx
  have := X.add_mem (hu.2 x (hX hx)) hx
  simpa using this

lemma good_perp {X : Submodule E V} {u : V ≃ₗ[E] V} (hX : X ≤ H.perp X) (hu : Good H X u) :
    ∀ v ∈ H.perp X, u v ∈ H.perp X := by
  intro v hv
  have := (H.perp X).add_mem (hX (hu.2 v hv)) hv
  simpa using this

lemma good_inv {X : Submodule E V} {u : V ≃ₗ[E] V} (hX : X ≤ H.perp X) (hu : Good H X u) :
    Good H X u⁻¹ := by
  refine ⟨fun x y => ?_, fun v hv => ?_⟩
  · have := hu.1 (u.symm x) (u.symm y)
    simp only [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  have hv' : u.symm v ∈ H.perp X := by
    intro x hx
    have := hu.1 (u.symm v) x
    rw [LinearEquiv.apply_symm_apply] at this
    rw [← this]
    exact hv _ (good_map_le H hX hu x hx)
  have := X.neg_mem (hu.2 _ hv')
  rw [LinearEquiv.apply_symm_apply, neg_sub] at this
  exact this

lemma good_mul {X : Submodule E V} {u w : V ≃ₗ[E] V} (hX : X ≤ H.perp X) (hu : Good H X u)
    (hw : Good H X w) : Good H X (u * w) := by
  refine ⟨fun x y => ?_, fun v hv => ?_⟩
  · change H.h (u (w x)) (u (w y)) = _
    rw [hu.1, hw.1]
  · change u (w v) - v ∈ X
    have e : u (w v) - v = (u (w v) - w v) + (w v - v) := by abel
    rw [e]
    exact X.add_mem (hu.2 _ (good_perp H hX hw v hv)) (hw.2 v hv)

variable {H} {r : ℕ} (Fr : FrameD H r)

lemma h_ee (a b : Fin r) : H.h (Fr.e a) (Fr.e b) = 0 :=
  Fr.h_iso _ _ (Or.inl (Fin.castSucc_ne_last a))

lemma h_e_es (a b : Fin r) : H.h (Fr.e a) (Fr.es b) = if a = b then 1 else 0 := Fr.h_es a b

lemma h_es_e (a b : Fin r) : H.h (Fr.es a) (Fr.e b) = if b = a then 1 else 0 := by
  rw [H.h_herm (Fr.e b) (Fr.es a), h_e_es]
  split_ifs <;> simp

lemma mem_perp_iff (v : V) : v ∈ H.perp (H.X Fr.f) ↔ ∀ a, H.h v (Fr.e a) = 0 := by
  constructor
  · intro hv a
    exact hv _ (Submodule.subset_span ⟨a, rfl⟩)
  · intro h x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact h a
    | zero => exact h_zero_right H v
    | add x y _ _ hx hy => rw [h_add_right, hx, hy, add_zero]
    | smul c x _ hx => rw [h_smul_right, hx, mul_zero]

lemma X_le_perp : H.X Fr.f ≤ H.perp (H.X Fr.f) := by
  intro x hx
  rw [mem_perp_iff]
  intro a
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    exact h_ee Fr b a
  | zero => exact H.h_zero_left _
  | add x y _ _ hx hy => rw [H.h_add_left, hx, hy, add_zero]
  | smul c x _ hx => rw [H.h_smul_left, hx, mul_zero]

lemma prF_e (v : V) (b : Fin r) : H.h (Fr.prF v) (Fr.e b) = 0 := by
  unfold FrameD.prF
  rw [h_sub_left, h_sub_left, h_sum_left, h_sum_left]
  simp only [H.h_smul_left, h_ee, h_es_e, mul_zero, Finset.sum_const_zero, mul_ite, mul_one,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

lemma prF_es (v : V) (b : Fin r) : H.h (Fr.prF v) (Fr.es b) = 0 := by
  unfold FrameD.prF
  rw [h_sub_left, h_sub_left, h_sum_left, h_sum_left]
  simp only [H.h_smul_left, h_e_es, Fr.h_ss, mul_zero, Finset.sum_const_zero, mul_ite, mul_one,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

lemma prF_perp (v : V) : Fr.prF v ∈ H.perp (H.X Fr.f) := (mem_perp_iff Fr _).2 (prF_e Fr v)

lemma prF_add (x y : V) : Fr.prF (x + y) = Fr.prF x + Fr.prF y := by
  unfold FrameD.prF
  simp only [H.h_add_left, add_smul, Finset.sum_add_distrib]
  abel

lemma prF_smul (c : E) (x : V) : Fr.prF (c • x) = c • Fr.prF x := by
  unfold FrameD.prF
  simp only [smul_sub, Finset.smul_sum, smul_smul, H.h_smul_left]

lemma prF_of (v : V) (h1 : ∀ a, H.h v (Fr.es a) = 0) (h2 : ∀ a, H.h v (Fr.e a) = 0) :
    Fr.prF v = v := by
  unfold FrameD.prF
  simp [h1, h2]

lemma sub_prF_mem (v : V) (hv : v ∈ H.perp (H.X Fr.f)) : v - Fr.prF v ∈ H.X Fr.f := by
  have h2 := (mem_perp_iff Fr v).1 hv
  have e : v - Fr.prF v = ∑ a, H.h v (Fr.es a) • Fr.e a + ∑ a, H.h v (Fr.e a) • Fr.es a := by
    unfold FrameD.prF; abel
  rw [e]
  simp only [h2, zero_smul, Finset.sum_const_zero, add_zero]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem Lset_LamStd (L : Submodule M.L.O (H.Wb Fr.f)) :
    H.Lset (Fr.LamStd L) Fr.f = (L : Set (H.Wb Fr.f)) := by
  ext w
  constructor
  · rintro ⟨x, hxΛ, rfl⟩
    have hQ : ∀ v ∈ Fr.LamStd L, H.mkW Fr.f ⟨Fr.prF v, prF_perp Fr v⟩ ∈ L := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨-, -, w, hw, hwL⟩ := hv
        have e : (⟨Fr.prF v, prF_perp Fr v⟩ : ↥(H.perp (H.X Fr.f))) = w := Subtype.ext hw.symm
        rw [e]; exact hwL
      | zero =>
        have e : (⟨Fr.prF 0, prF_perp Fr 0⟩ : ↥(H.perp (H.X Fr.f))) = 0 :=
          Subtype.ext (by simpa using prF_smul Fr 0 0)
        rw [e, map_zero]; exact L.zero_mem
      | add x y _ _ hx hy =>
        have e : (⟨Fr.prF (x + y), prF_perp Fr _⟩ : ↥(H.perp (H.X Fr.f))) =
            ⟨Fr.prF x, prF_perp Fr x⟩ + ⟨Fr.prF y, prF_perp Fr y⟩ := Subtype.ext (prF_add Fr x y)
        rw [e, map_add (f := _)]; exact L.add_mem hx hy
      | smul c x _ hx =>
        have e : (⟨Fr.prF (c • x), prF_perp Fr _⟩ : ↥(H.perp (H.X Fr.f))) =
            (c : E) • ⟨Fr.prF x, prF_perp Fr x⟩ := Subtype.ext (prF_smul Fr (c : E) x)
        rw [e, map_smul]
        exact L.smul_mem c hx
    have := hQ x hxΛ
    rwa [mkW_eq H ⟨Fr.prF x, prF_perp Fr x⟩ x (by
      have := (H.X Fr.f).neg_mem (sub_prF_mem Fr x x.2); simpa using this)] at this
  · intro hw
    obtain ⟨x0, rfl⟩ := Submodule.mkQ_surjective _ w
    refine ⟨⟨Fr.prF x0, prF_perp Fr x0⟩, ?_, ?_⟩
    · have hp : Fr.prF (Fr.prF x0) = Fr.prF x0 := prF_of Fr _ (prF_es Fr x0) (prF_e Fr x0)
      refine Submodule.subset_span ⟨fun a => ?_, fun a => ?_, ⟨Fr.prF x0, prF_perp Fr x0⟩, hp.symm, ?_⟩
      · change H.h (Fr.prF x0) (Fr.es a) ∈ _; rw [prF_es]; exact zero_mem _
      · change H.h (Fr.prF x0) (Fr.e a) ∈ _; rw [prF_e]; exact zero_mem _
      · rw [mkW_eq H ⟨Fr.prF x0, prF_perp Fr x0⟩ x0 (by
          have := (H.X Fr.f).neg_mem (sub_prF_mem Fr x0 x0.2); simpa using this)]
        exact hw
    · have := (H.X Fr.f).neg_mem (sub_prF_mem Fr x0 x0.2)
      show H.mkW Fr.f _ = H.mkW Fr.f x0
      exact mkW_eq H _ _ (by simpa using this)

lemma good_of_mem_N {g : V ≃ₗ[E] V} (hg : g ∈ Fr.N) : Good H (H.X Fr.f) g := by
  have hX := X_le_perp Fr
  unfold FrameD.N at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact ⟨hx.1, hx.2.2⟩
  | one => exact ⟨fun x y => rfl, fun v _ => by simp⟩
  | mul x y _ _ hx hy => exact good_mul H hX hx hy
  | inv x _ hx => exact good_inv H hX hx

lemma mem_img (u : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) (x : V) :
    x ∈ img u Λ ↔ ∃ y ∈ Λ, u y = x := by
  unfold img
  rw [Submodule.mem_map]
  rfl

theorem Lset_img {u : V ≃ₗ[E] V} (hu : u ∈ Fr.N) (Λ : Submodule M.L.O V) :
    H.Lset (img u Λ) Fr.f = H.Lset Λ Fr.f := by
  have hX := X_le_perp Fr
  have g1 := good_of_mem_N Fr hu
  have g2 := good_inv H hX g1
  ext w
  constructor
  · rintro ⟨x, hxΛ, rfl⟩
    obtain ⟨y, hy, hyx⟩ := (mem_img u Λ x).1 hxΛ
    have hyp : y ∈ H.perp (H.X Fr.f) := by
      have := good_perp H hX g2 (x : V) x.2
      rw [← hyx] at this
      change u.symm (u y) ∈ _ at this
      rwa [LinearEquiv.symm_apply_apply] at this
    refine ⟨⟨y, hyp⟩, hy, (mkW_eq H _ _ ?_).symm⟩
    change (x : V) - y ∈ _
    rw [← hyx]
    exact g1.2 y hyp
  · rintro ⟨y, hyΛ, rfl⟩
    exact ⟨⟨u y, good_perp H hX g1 y y.2⟩, (mem_img u Λ _).2 ⟨y, hyΛ, rfl⟩,
      mkW_eq H _ _ (g1.2 y y.2)⟩

theorem datum_eq_Lset : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (r : ℕ) (P : LocNG.FPair H r) (d : LocNG.Datum P) (τ : Loc.Term V M r), LocNG.IsTermOver P d τ → (d.L : Set (H.Wb P.A.f)) = H.Lset τ.abelian₂ P.A.f ∧ (d.L' : Set (H.Wb P.B.f)) = H.Lset τ.abelian₂ P.B.f := by
  intro F _ _ _ E _ _ _ _ M V _ _ H r P d τ hτ
  obtain ⟨-, -, ⟨n, hn, -, hΛ⟩, ⟨n', hn', -, hΛ'⟩, -⟩ := hτ
  constructor
  · rw [hΛ, Lset_img P.A hn, Lset_LamStd]
  · rw [hΛ', Lset_img P.B hn', Lset_LamStd]

end GlobalTheory.InnerRead
end
end

