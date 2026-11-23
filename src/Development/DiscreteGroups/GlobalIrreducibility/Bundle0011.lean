module

public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0245
public import Mathlib

@[expose] public section

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.ColUSingleOfGe
section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix

namespace DiscreteGroups.sglob.LConvGenM

variable {k : Type} [Field k] {n : ℕ}

def colM (j : ℕ) (c : Fin n → k) : Matrix (Fin n) (Fin n) k :=
  Matrix.of fun i l => if i.val < j ∧ l.val = j then c i else 0

theorem colM_apply (j : ℕ) (c : Fin n → k) (i l : Fin n) :
    colM j c i l = if i.val < j ∧ l.val = j then c i else 0 := rfl

theorem colM_mul (j : ℕ) (c d : Fin n → k) : colM j c * colM j d = 0 := by
  ext i l
  simp only [Matrix.mul_apply, colM_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  by_cases h1 : i.val < j ∧ a.val = j
  · by_cases h2 : a.val < j ∧ l.val = j
    · exact absurd h2.1 (by omega)
    · simp [h2]
  · simp [h1]

theorem colM_add (j : ℕ) (c d : Fin n → k) : colM j (c + d) = colM j c + colM j d := by
  ext i l
  simp only [colM_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

def colU (j : ℕ) (c : Fin n → k) : GL (Fin n) k :=
  ⟨1 + colM j c, 1 - colM j c, by rw [add_mul, one_mul, mul_sub, mul_one, colM_mul]; abel,
    by rw [sub_mul, one_mul, mul_add, mul_one, colM_mul]; abel⟩

theorem val_colU (j : ℕ) (c : Fin n → k) : (colU j c : Matrix (Fin n) (Fin n) k) = 1 + colM j c := rfl

theorem colU_add (j : ℕ) (c d : Fin n → k) : colU j (c + d) = colU j c * colU j d := by
  ext : 1
  rw [Units.val_mul, val_colU, val_colU, val_colU, colM_add, add_mul, one_mul, mul_add, mul_one, colM_mul]
  abel

theorem colU_zero (j : ℕ) : colU j (0 : Fin n → k) = 1 := by
  ext : 1
  rw [val_colU, Units.val_one]
  have : colM j (0 : Fin n → k) = 0 := by ext i l; simp [colM_apply]
  rw [this, add_zero]

theorem colU_inv (j : ℕ) (c : Fin n → k) : (colU j c)⁻¹ = colU j (-c) := by
  refine (inv_eq_of_mul_eq_one_right ?_)
  rw [← colU_add, add_neg_cancel, colU_zero]

theorem colU_mul_apply (j : ℕ) (hj : j < n) (c : Fin n → k) (M : Matrix (Fin n) (Fin n) k) (i l : Fin n) :
    ((colU j c : Matrix (Fin n) (Fin n) k) * M) i l = M i l + (if i.val < j then c i * M ⟨j, hj⟩ l else 0) := by
  rw [val_colU, add_mul, one_mul, Matrix.add_apply, Matrix.mul_apply]
  congr 1
  rw [Finset.sum_eq_single (⟨j, hj⟩ : Fin n)]
  · simp only [colM_apply, and_true]
    split_ifs <;> simp
  · intro a _ ha
    have : ¬ (a.val = j) := fun h => ha (Fin.ext h)
    simp [colM_apply, this]
  · simp

theorem colU_single_of_lt (j : ℕ) (hj : j < n) {r : Fin n} (hr : r.val < j) (a : k) :
    colU j (Pi.single r a) = GlobalTheory.RootUp.elem (i := r) (j := ⟨j, hj⟩) (fun h => by
      have := congrArg Fin.val h; simp at this; omega) a := by
  ext i l
  rw [val_colU, GlobalTheory.RootUp.val_elem, Matrix.add_apply, Matrix.add_apply]
  congr 1
  rw [colM_apply, Matrix.single_apply]
  by_cases hi : i = r
  · subst hi
    by_cases hl : l.val = j
    · have : (⟨j, hj⟩ : Fin n) = l := Fin.ext hl.symm
      simp [hr, hl, this]
    · have : (⟨j, hj⟩ : Fin n) ≠ l := fun h => hl (by rw [← h])
      simp [hl, this]
  · have : r ≠ i := Ne.symm hi
    simp [Pi.single_apply, hi, this]

theorem colU_single_of_ge (j : ℕ) {r : Fin n} (hr : j ≤ r.val) (a : k) : colU j (Pi.single r a) = 1 := by
  ext i l
  rw [val_colU, Units.val_one, Matrix.add_apply, colM_apply]
  by_cases hi : i = r
  · subst hi; simp [show ¬ i.val < j by omega]
  · simp [Pi.single_apply, hi]

end DiscreteGroups.sglob.LConvGenM
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.LConvKirStep
section
noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.PRep ValuativeRel

namespace DiscreteGroups.sglob.LConvKir

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem step (ψ : AddChar k Circle) (hψc : Continuous ψ) (hψ : ψ ≠ 1) {m : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ (GL (Fin (m + 1)) k) V) (hsm : IsSmooth ρ) (j : ℕ) (hj : j + 1 < m + 1)
    (v : V) : ∃ v' : V, ∀ l : Module.Dual ℂ V, IsFunctional ψ ρ l → l v' = l v ∧
      ((∀ h, InH j h → l (ρ h v) = 0) → ∀ g, InH (j + 1) g → l (ρ g v') = 0) := by
  classical
  obtain ⟨y, hy⟩ : ∃ y, ψ y ≠ 1 := by
    by_contra h
    exact hψ (AddChar.ext _ _ fun x => by rw [not_exists_not.1 h x, AddChar.one_apply])
  set c : Fin (m + 1) := ⟨j + 1, hj⟩ with hc
  set jj : Fin (m + 1) := ⟨j, by omega⟩ with hjj
  have hjc : jj < c := Fin.mk_lt_mk.2 (Nat.lt_succ_self j)
  obtain ⟨γ₁, hγ₁⟩ := kappa_nbhd {g | ρ g v = v} (hsm v) (by simp) jj
  obtain ⟨γ₀, hγ₀⟩ := psi_ball ψ hψc
  let r₁ : ValueGroupWithZero k := valuation k y * ↑γ₁⁻¹
  let L : AddSubgroup (Fin (m + 1) → k) := AddSubgroup.pi Set.univ fun _ => ballLe r₁
  let Sx : AddSubgroup (Fin (m + 1) → k) :=
    { carrier := {x | ρ (U c x) v = v}
      add_mem' := by
        intro a b (ha : ρ (U c a) v = v) (hb : ρ (U c b) v = v)
        show ρ (U c (a + b)) v = v
        rw [U_add, map_mul, Module.End.mul_apply, hb, ha]
      zero_mem' := by
        show ρ (U c 0) v = v
        rw [U_zero, map_one, Module.End.one_apply]
      neg_mem' := by
        intro a (ha : ρ (U c a) v = v)
        show ρ (U c (-a)) v = v
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, ← U_add, neg_add_cancel, U_zero, map_one, Module.End.one_apply] }
  let L'' : AddSubgroup (Fin (m + 1) → k) := Sx ⊓ AddSubgroup.pi Set.univ fun _ => ballLt γ₀
  have hLc : IsCompact (L : Set (Fin (m + 1) → k)) :=
    isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k r₁
  have : CompactSpace L := isCompact_iff_compactSpace.1 hLc
  have hL''o : IsOpen (L'' : Set (Fin (m + 1) → k)) :=
    ((hsm v).preimage (continuous_U c)).inter (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_ballLt γ₀)
  have hQf : Finite (L ⧸ L''.addSubgroupOf L) :=
    AddSubgroup.quotient_finite_of_isOpen _ (hL''o.preimage continuous_subtype_val)
  let _ : Fintype (L ⧸ L''.addSubgroupOf L) := Fintype.ofFinite _
  let xs : (L ⧸ L''.addSubgroupOf L) → Fin (m + 1) → k := fun q => ((Quotient.out q : L) : Fin (m + 1) → k)
  have hN : (Fintype.card (L ⧸ L''.addSubgroupOf L) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨(Fintype.card (L ⧸ L''.addSubgroupOf L) : ℂ)⁻¹ • ∑ q : L ⧸ L''.addSubgroupOf L,
    ((ψ (-(xs q jj)) : Circle) : ℂ) • ρ (U c (xs q)) v, fun l hl => ⟨?_, fun hv g hg => ?_⟩⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [map_smul, map_sum, smul_eq_mul]
      have hq : ∀ q, ((ψ (-(xs q jj)) : Circle) : ℂ) * l (ρ (U c (xs q)) v) = l v := fun q => by
        rw [hl _ (U_mem _ _), superDiag_U, ← mul_assoc, psi_neg_mul, one_mul]
      rw [Finset.sum_congr rfl fun q _ => hq q, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ hN, one_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [map_smul, map_sum, smul_eq_mul]
      let w : Fin (m + 1) → k := fun r => if r < c then (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) jj r else 0
      let χ : (Fin (m + 1) → k) → ℂ := fun x => ((ψ (-(x jj)) : Circle) : ℂ) * (ψ (∑ r, w r * x r) : ℂ)
      have hterm : ∀ x, ((ψ (-(x jj)) : Circle) : ℂ) * l (ρ g (ρ (U c x) v)) = χ x * l (ρ g v) := fun x => by
        rw [l_gU ψ ρ l hl j hj g hg x v]; exact (mul_assoc _ _ _).symm
      rw [mul_eq_zero]; right
      have hS : (∑ q : L ⧸ L''.addSubgroupOf L, ((ψ (-(xs q jj)) : Circle) : ℂ) * l (ρ g (ρ (U c (xs q)) v))) =
          (∑ q : L ⧸ L''.addSubgroupOf L, χ (xs q)) * l (ρ g v) := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun q _ => hterm (xs q)
      refine hS.trans ?_
      by_cases h0 : l (ρ g v) = 0
      · rw [h0, mul_zero]
      have hχadd : ∀ x x', χ (x + x') = χ x * χ x' := fun x x' => by
        show ((ψ (-((x + x') jj)) : Circle) : ℂ) * (ψ (∑ r, w r * (x + x') r) : ℂ) =
          (((ψ (-(x jj)) : Circle) : ℂ) * (ψ (∑ r, w r * x r) : ℂ)) *
            (((ψ (-(x' jj)) : Circle) : ℂ) * (ψ (∑ r, w r * x' r) : ℂ))
        have hs : ∑ r, w r * (x + x') r = ∑ r, w r * x r + ∑ r, w r * x' r := by
          rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun r _ => by rw [Pi.add_apply, mul_add]
        rw [Pi.add_apply, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul, hs, AddChar.map_add_eq_mul, Circle.coe_mul]
        ring
      have hχ'' : ∀ x ∈ L'', χ x = 1 := by
        intro x hx
        have hx1 : ρ (U c x) v = v := (AddSubgroup.mem_inf.1 hx).1
        have hx2 : valuation k (x jj) < γ₀ := (AddSubgroup.mem_pi _).1 (AddSubgroup.mem_inf.1 hx).2 jj (Set.mem_univ _)
        have e1 : ψ (-(x jj)) = 1 := hγ₀ _ (by rwa [Valuation.map_neg])
        have e2 : (ψ (∑ r, w r * x r) : ℂ) = 1 := by
          have := l_gU ψ ρ l hl j hj g hg x v
          rw [hx1] at this
          exact (mul_eq_right₀ h0).1 this.symm
        show ((ψ (-(x jj)) : Circle) : ℂ) * (ψ (∑ r, w r * x r) : ℂ) = 1
        rw [e1, Circle.coe_one, one_mul, e2]
      by_cases hall : ∀ x ∈ L, χ x = 1
      · exfalso
        apply h0
        have hsmall : ∀ i, valuation k (w i - (Pi.single jj (1 : k) : Fin (m + 1) → k) i) < γ₁ := by
          intro i
          refine small_of_triv ψ y hy γ₁ _ fun t ht => ?_
          have hxL : (Pi.single i t : Fin (m + 1) → k) ∈ L := by
            refine (AddSubgroup.mem_pi _).2 fun r _ => ?_
            by_cases hr : r = i
            · rw [hr]
              show valuation k ((Pi.single i t : Fin (m + 1) → k) i) ≤ r₁
              rw [Pi.single_eq_same]; exact ht
            · show valuation k ((Pi.single i t : Fin (m + 1) → k) r) ≤ r₁
              rw [Pi.single_eq_of_ne hr, map_zero]; exact zero_le
          have h3 : ((ψ (-((Pi.single i t : Fin (m + 1) → k) jj)) : Circle) : ℂ) *
              (ψ (∑ r, w r * (Pi.single i t : Fin (m + 1) → k) r) : ℂ) = 1 := hall _ hxL
          have hs : ∑ r, w r * (Pi.single i t : Fin (m + 1) → k) r = w i * t := by
            rw [Finset.sum_eq_single i (fun r _ hr => by rw [Pi.single_eq_of_ne hr, mul_zero]) (by simp),
              Pi.single_eq_same]
          have hsj : (Pi.single i t : Fin (m + 1) → k) jj = (Pi.single jj (1 : k) : Fin (m + 1) → k) i * t := by
            by_cases h : i = jj
            · rw [h, Pi.single_eq_same, Pi.single_eq_same, one_mul]
            · rw [Pi.single_eq_of_ne (Ne.symm h), Pi.single_eq_of_ne h, zero_mul]
          have h4 : ((ψ ((w i - (Pi.single jj (1 : k) : Fin (m + 1) → k) i) * t) : Circle) : ℂ) = 1 := by
            rw [sub_mul, sub_eq_neg_add, AddChar.map_add_eq_mul, Circle.coe_mul, ← hs, ← hsj]
            exact h3
          exact Circle.coe_eq_one.1 h4
        obtain ⟨κ, hκS, hκ, hκi⟩ := hγ₁ w hsmall
        have hgrow : ∀ r, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) jj r = w r := fun r => by
          by_cases hr : r < c
          · simp only [w, if_pos hr]
          · simp only [w, if_neg hr]
            rw [hg jj r (fun h => hr (by rw [Fin.lt_def]; exact h.2)),
              Matrix.one_apply_ne (fun h => hr (by rw [← h]; exact hjc))]
        have hMrow : ∀ q, ((g * κ⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) jj q =
            (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) jj q := by
          intro q
          have hk1 : Kmat jj w * Kinv jj w = 1 := by
            rw [← hκ, ← hκi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
          rw [Units.val_mul, hκi, Matrix.mul_apply, ← hk1, Matrix.mul_apply]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [hgrow r]
          simp only [Kmat, Matrix.of_apply, ↓reduceIte]
        have hMH : InH (j + 1) (g * κ⁻¹) := by
          intro p q hpq
          rw [Units.val_mul, hκi, Matrix.mul_apply]
          by_cases hp : p < c
          · have hq : ¬ q < c := fun hq => hpq ⟨hp, hq⟩
            have hK : ∀ r, Kinv jj w r q = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r q := fun r => by
              by_cases hr : r = jj
              · rw [hr]
                simp only [Kinv, Kinv2, Matrix.of_apply, ↓reduceIte]
                rw [if_neg (fun h => hq (by rw [h]; exact hjc)), show w q = 0 from if_neg hq, neg_zero, zero_mul,
                  Matrix.one_apply_ne (fun h => hq (by rw [← h]; exact hjc))]
              · simp only [Kinv, Kinv2, Matrix.of_apply, if_neg hr]
            rw [Finset.sum_congr rfl fun r _ => by rw [hK r], ← Matrix.mul_apply, Matrix.mul_one]
            exact hg p q hpq
          · rw [Finset.sum_eq_single p (fun r _ hr => by
                rw [hg p r (fun h => hp h.1), Matrix.one_apply_ne (Ne.symm hr), zero_mul]) (by simp),
              hg p p (fun h => hp h.1), Matrix.one_apply_eq, one_mul]
            simp only [Kinv, Kinv2, Matrix.of_apply, if_neg (fun h : p = jj => hp (by rw [h]; exact hjc))]
        obtain ⟨yv, h, hh, hM⟩ := decomp j (by omega) (g * κ⁻¹) hMH hMrow
        have hki : ρ κ⁻¹ v = v := by
          conv_lhs => rw [← (hκS : ρ κ v = v)]
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        have e1 : ρ g v = ρ (g * κ⁻¹) v := by rw [map_mul, Module.End.mul_apply, hki]
        rw [e1, hM, map_mul, Module.End.mul_apply, hl _ (U_mem _ _), hv h hh, mul_zero]
      · push Not at hall
        obtain ⟨x₀, hx₀L, hx₀⟩ := hall
        have hsum := sum_char_eq_zero L L'' χ hχadd hχ'' ⟨x₀, hx₀L⟩ hx₀
        rw [show (∑ q : L ⧸ L''.addSubgroupOf L, χ (xs q)) = 0 from hsum, zero_mul]

end DiscreteGroups.sglob.LConvKir
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.LConvSepR
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Topology

namespace DiscreteGroups.sglob.LConv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}
  {ψ : AddChar k Circle} (hψ : Continuous ψ) {I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ}
  {B : WT (m := m) ψ →ₗ⋆[ℂ] WT (m := m) ψ →ₗ[ℂ] ℂ}

def whittakerPairingValue (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) (W : GL (Fin m) k → ℂ) (x : WT (m := m) ψ) : ℂ :=
  I fun g => (x : GL (Fin m) k → ℂ) g * W g

def pairW (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) (W : GL (Fin m) k → ℂ) : WT (m := m) ψ →ₗ[ℂ] ℂ where
  toFun := whittakerPairingValue I W
  map_add' a b := by
    simp only [whittakerPairingValue]
    rw [← map_add (f := _)]; congr 1; funext g
    simp only [Submodule.coe_add, Pi.add_apply]; ring
  map_smul' c a := by
    simp only [whittakerPairingValue, RingHom.id_apply]
    rw [← map_smul]; congr 1; funext g
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]; ring

include hψ in
theorem repr_delta (hI : PosInt I) (hB : IsInvForm (rhoW ψ) B) {K : Subgroup (GL (Fin m) k)} (hK : Good ψ K)
    {y : WT (m := m) ψ} (hy : ∀ κ ∈ K, rhoW ψ κ y = y) :
    I (fun g => (delta ψ K : GL (Fin m) k → ℂ) g * Wf ψ hψ I B y g) = B y (delta ψ K) := by
  have e : (fun g => (delta ψ K : GL (Fin m) k → ℂ) g * Wf ψ hψ I B y g) = lam ψ hψ I B y •
      fun g => (starRingEnd ℂ) ((delta ψ K : GL (Fin m) k → ℂ) g) * (delta ψ K : GL (Fin m) k → ℂ) g := by
    funext g
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases h : ∃ u ∈ unipB k (Fin m), ∃ κ ∈ K, g = u * κ
    · obtain ⟨u, hu, κ, hκ, rfl⟩ := h
      rw [delta_mul hK hu hκ, Wf_left hψ hI hB y hu, Wf_apply, hy κ hκ, conj_psi]
      ring
    · rw [delta_eq_zero h]
      ring
  rw [e, map_smul, smul_eq_mul, ← formI_apply, lam_eq hψ hI hB hK hy, lamK]
  exact div_mul_cancel₀ _ (cK_ne_zero hI hK)


include hψ in
theorem repr (hI : PosInt I) (hB : IsInvForm (rhoW ψ) B) (y x : WT (m := m) ψ) :
    I (fun g => (x : GL (Fin m) k → ℂ) g * Wf ψ hψ I B y g) = B y x := by
  obtain ⟨K, hK, hKf⟩ := exists_good_fix hψ x y
  have hspan := mem_span_delta hK.1 hK.2.1 x (fun κ hκ => (hKf κ hκ).1)
  refine LinearMap.eqOn_span' (f := pairW I (Wf ψ hψ I B y)) (g := B y) ?_ hspan
  rintro _ ⟨g, hg, rfl⟩
  have hfix : ∀ κ ∈ K.map (MulAut.conj g).toMonoidHom, rhoW ψ κ (rhoW ψ g y) = rhoW ψ g y := by
    intro κ hκ
    have e : κ * g = g * (g⁻¹ * κ * g) := by group
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, (hKf _ (mem_conj.1 hκ)).2]
  have hF := isTestFun_mul (delta ψ (K.map (MulAut.conj g).toMonoidHom)) (Wf ψ hψ I B (rhoW ψ g y))
    (fun u hu h => Wf_left hψ hI hB _ hu h) (isLocallyConstant_Wf hψ _)
  have h1 := hI.1 _ hF g⁻¹
  have h2 := repr_delta hψ hI hB hg hfix
  show whittakerPairingValue I (Wf ψ hψ I B y) _ = _
  simp only [whittakerPairingValue, rhoW_apply]
  rw [← hB.2.2 g y, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply, ← h2,
    ← h1]
  congr 1
  funext h
  rw [Wf_right, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

end DiscreteGroups.sglob.LConv

end
end

