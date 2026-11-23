module

public import Mathlib
public import Formalism.LocalToGlobal.CharacterGerms.Interface
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.RowDataAdaptedChainData
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0005
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0001
public import Formalism.LocalToGlobal.CharacterGerms.CharacteristicFromRanks
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsSaturatedGoodVectorsSmallCorank
section
noncomputable section

open scoped BigOperators
open Formalism.L2.FormalSeriesBounds

namespace GlobalTheory.GoodCorank

variable {C : Type} [Field C] {V : VF C}

theorem div_int {x y : C} (h : V.v y ≤ V.v x) : V.Ge 0 (x / y) := by
  by_cases hy : y = 0
  · subst hy; simpa using VF.Ge.zero (V := V) 0
  · have e : V.v x = V.v y + V.v (x / y) := by
      rw [← V.v.map_mul, mul_div_cancel₀ _ hy]
    have hy' : V.v y ≠ ⊤ := by
      intro h0
      have h1 : V.v (y * y⁻¹) = 0 := by rw [mul_inv_cancel₀ hy, V.v.map_one]
      rw [V.v.map_mul, h0, top_add] at h1
      exact WithTop.top_ne_zero h1
    unfold VF.Ge
    rw [e] at h
    have h2 : V.v y + 0 ≤ V.v y + V.v (x / y) := by simpa using h
    simpa using (WithTop.add_le_add_iff_left hy').mp h2

theorem ge_ite (p : Prop) [Decidable p] : V.Ge 0 (if p then (1 : C) else 0) := by
  split_ifs
  · exact VF.Ge.one
  · exact VF.Ge.zero 0

theorem exists_cut {N : ℕ} (φ : Fin (N + 1) → C) :
    ∃ A : Fin N → Fin (N + 1) → C, IsSat V A ∧ ∀ ν, ∑ k, A ν k * φ k = 0 := by
  obtain ⟨k0, -, hk0⟩ := Finset.exists_min_image Finset.univ (fun k => V.v (φ k)) Finset.univ_nonempty
  refine ⟨fun ν k => (if k = k0.succAbove ν then 1 else 0) -
      (φ (k0.succAbove ν) / φ k0) * (if k = k0 then 1 else 0), ⟨fun ν k => ?_,
      fun k c => if k = k0.succAbove c then 1 else 0, fun k c => ge_ite _, fun c c' => ?_⟩, fun ν => ?_⟩
  · exact (ge_ite _).sub ((div_int (hk0 _ (Finset.mem_univ _))).mul_int (ge_ite _))
  · simp [Fin.succAbove_ne, eq_comm]
  · simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases h0 : φ k0 = 0
    · have h1 := hk0 (k0.succAbove ν) (Finset.mem_univ _)
      rw [h0, V.v.map_zero, top_le_iff] at h1
      have h2 : φ (k0.succAbove ν) = 0 := by
        by_contra hy
        have h3 : V.v (φ (k0.succAbove ν) * (φ (k0.succAbove ν))⁻¹) = 0 := by
          rw [mul_inv_cancel₀ hy, V.v.map_one]
        rw [V.v.map_mul, h1, top_add] at h3
        exact WithTop.top_ne_zero h3
      simp [h0, h2]
    · rw [div_mul_cancel₀ _ h0, sub_self]

theorem isSat_comp {M N : ℕ} {σ : Type} [Fintype σ] {A : Fin M → Fin N → C} {w : Fin N → σ → C}
    (hA : IsSat V A) (hw : IsSat V w) : IsSat V (fun ν c => ∑ k, A ν k * w k c) := by
  obtain ⟨hA0, A', hA', hAA⟩ := hA
  obtain ⟨hw0, w', hw', hww⟩ := hw
  refine ⟨fun ν c => VF.Ge.sum fun k _ => (hA0 _ _).mul_int (hw0 _ _),
    fun x c => ∑ k, w' x k * A' k c, fun x c => VF.Ge.sum fun k _ => (hw' _ _).mul_int (hA' _ _),
    fun c c' => ?_⟩
  have e1 : Matrix.of A * Matrix.of A' = 1 := by
    ext i j; simpa [Matrix.mul_apply, Matrix.one_apply] using hAA i j
  have e2 : Matrix.of w * Matrix.of w' = 1 := by
    ext i j; simpa [Matrix.mul_apply, Matrix.one_apply] using hww i j
  have e3 : (Matrix.of A * Matrix.of w) * (Matrix.of w' * Matrix.of A') = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.of w), e2, Matrix.one_mul, e1]
  simpa [Matrix.mul_apply, Matrix.one_apply] using congrFun (congrFun e3 c) c'

theorem exists_sat_ker {I κ : Type} [Fintype I] [DecidableEq I] (P : Finset I) (φ : κ → I → C) (S : Finset κ) :
    ∃ (N : ℕ) (w : Fin N → I → C), IsSat V w ∧ (∀ ν c, c ∉ P → w ν c = 0) ∧
      (∀ ν, ∀ b ∈ S, ∑ c, w ν c * φ b c = 0) ∧ P.card ≤ N + S.card := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨P.card, fun ν c => if c = (P.equivFin.symm ν : I) then 1 else 0, ⟨fun ν c => ge_ite _,
      fun c ν => if c = (P.equivFin.symm ν : I) then 1 else 0, fun c ν => ge_ite _, fun ν ν' => ?_⟩,
      fun ν c hc => ?_, by simp, by simp⟩
    · simp [Subtype.val_inj, eq_comm]
    · refine if_neg ?_
      rintro rfl
      exact hc (P.equivFin.symm ν).2
  | insert b S hb ih =>
    obtain ⟨N, w, hs, hP, hφ, hN⟩ := ih
    rw [Finset.card_insert_of_notMem hb]
    cases N with
    | zero => exact ⟨0, w, hs, hP, fun ν => ν.elim0, by omega⟩
    | succ N =>
      obtain ⟨A, hA, hA0⟩ := exists_cut (V := V) (fun k => ∑ c, w k c * φ b c)
      have key : ∀ ν b', ∑ c, (∑ k, A ν k * w k c) * φ b' c = ∑ k, A ν k * ∑ c, w k c * φ b' c := by
        intro ν b'
        simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm
      refine ⟨N, fun ν c => ∑ k, A ν k * w k c, isSat_comp hA hs, fun ν c hc => ?_, fun ν b' hb' => ?_, by omega⟩
      · simp [hP _ c hc]
      · rw [key]
        rcases Finset.mem_insert.mp hb' with rfl | hb'
        · exact hA0 ν
        · simp [hφ _ b' hb']

variable {d : ℕ} {I J : Type} [Fintype I] [DecidableEq I]

theorem good_of_int (G : Cart V d I J) {a : ZMod d} {u : I → C} {y : ℕ → I ⊕ J → C} (hy : G.IsCurve a u y)
    (h1 : ∀ b, V.Ge 0 (y 1 (Sum.inl b))) : ∃ x, G.Good a u x := by
  obtain ⟨z, hz, hz0, hzp⟩ := G.t4 (a + 1) (fun b => y 1 (Sum.inl b)) h1
    (fun b hb => hy.2.2 1 _ (by simpa using hb))
  refine ⟨y - Vpow 1 z, ⟨G.Ty.sub_mem hy.1 (G.V_mem _ hz), ?_, fun i n hn => ?_⟩, fun c => ?_⟩
  · funext n
    simp [Vpow, hy.2.1]
  · cases i with
    | zero => simp [Vpow, hy.2.2 0 n hn]
    | succ i =>
      have : z i n = 0 := hzp i n (by
        intro hc; apply hn; rw [hc]; push_cast; ring)
      simp [Vpow, hy.2.2 _ n hn, this]
  · simp [Vpow, hz0]

theorem good_of_ker (G : Cart V d I J) {a : ZMod d} (r : I → I → C)
    (hr : ∀ b c, r b c ^ V.l = (V.l : C) * G.std c 1 (Sum.inl b)) {u : I → C} (hu : ∀ c, V.Ge 0 (u c))
    (hp : ∀ c, G.ty (Sum.inl c) ≠ a → u c = 0)
    (hk : ∀ b, G.ty (Sum.inl b) = a + 1 → ∑ c, u c * r b c = 0) : ∃ x, G.Good a u x := by
  have lpos : ∀ k : ℕ, V.l ^ k ≠ 0 := fun k => (pow_pos V.l_prime.pos k).ne'
  have hy : G.IsCurve a u (∑ c, teich V.l (u c) (G.std c)) := by
    refine ⟨G.Ty.sum_mem fun c _ => G.teich_mem _ (hu c) _ (G.std_spec c).1, ?_, fun i n hn => ?_⟩
    · funext n
      have : ∀ b, G.std b 0 n = Sum.elim (Pi.single b 1) 0 n := fun b => by rw [(G.std_spec b).2.1]
      simp only [Finset.sum_apply, teich, this, pow_zero, pow_one]
      cases n with
      | inl c => simp [Pi.single_apply]
      | inr j => simp
    · simp only [Finset.sum_apply, teich]
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hc : G.ty (Sum.inl c) = a
      · rw [(G.std_spec c).2.2 i n (by rwa [hc]), mul_zero]
      · rw [hp c hc, zero_pow (lpos i), zero_mul]
  refine good_of_int G hy fun b => ?_
  by_cases hb : G.ty (Sum.inl b) = a + 1
  · have hrint : ∀ c, V.Ge 0 (r b c) := fun c => by
      refine GlobalTheory.AdaptedChain.int_of_pow V.l_prime.ne_zero ?_
      rw [hr]
      simpa using (G.bound0 1 _ (G.std_spec c).1 (Sum.inl b)).l_mul
    have hf := (GlobalTheory.AdaptedChain.frob_sum Finset.univ (fun c => u c * r b c)
      (fun c => (hu c).mul_int (hrint c)) 1).neg
    rw [hk b hb, zero_pow (lpos 1), zero_sub, neg_neg] at hf
    have e : ∑ c, (u c * r b c) ^ V.l ^ 1 =
        (V.l : C) * (∑ c, teich V.l (u c) (G.std c)) 1 (Sum.inl b) := by
      simp only [Finset.sum_apply, teich, pow_one, mul_pow, hr, Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [e] at hf
    simpa using hf.of_l_mul
  · rw [hy.2.2 1 _ (by simpa using hb)]
    exact VF.Ge.zero 0

theorem exists_good_sat (C : Type) [Field C] [IsAlgClosed C] (V : VF C) (d : ℕ) (I J : Type) [Fintype I] [Fintype J]
    [DecidableEq I] (G : Cart V d I J) (a : ZMod d) :
    ∃ (N : ℕ) (w : Fin N → I → C) (x : Fin N → ℕ → I ⊕ J → C), (∀ ν, G.Good a (w ν) (x ν)) ∧
      (∀ ν c, G.ty (Sum.inl c) ≠ a → w ν c = 0) ∧ IsSat V w ∧
      (Finset.univ.filter fun c : I => G.ty (Sum.inl c) = a).card ≤
        N + (Finset.univ.filter fun c : I => G.ty (Sum.inl c) = a + 1).card := by
  have hex : ∀ b c : I, ∃ r : C, r ^ V.l = (V.l : C) * G.std c 1 (Sum.inl b) := fun b c =>
    IsAlgClosed.exists_pow_nat_eq _ V.l_prime.pos
  choose r hr using hex
  obtain ⟨N, w, hs, hP, hφ, hN⟩ := exists_sat_ker (V := V)
    (Finset.univ.filter fun c : I => G.ty (Sum.inl c) = a) r
    (Finset.univ.filter fun c : I => G.ty (Sum.inl c) = a + 1)
  have hp : ∀ ν c, G.ty (Sum.inl c) ≠ a → w ν c = 0 := fun ν c hc => hP ν c (by simpa using hc)
  have hx : ∀ ν, ∃ x, G.Good a (w ν) x := fun ν =>
    good_of_ker G r hr (hs.1 ν) (hp ν) fun b hb => hφ ν b (by simpa using hb)
  choose x hx using hx
  exact ⟨N, w, x, hx, hp, hs, hN⟩

end GlobalTheory.GoodCorank

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupCoordinatesPullbackLinearTangentBasis
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

namespace GlobalTheory.MainTerm

theorem linPull_coords : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (t : I → MvPowerSeries I C), S.IsT t → ∀ (ι : Type) [Fintype ι] (e : ι → I → C) (z : I → ι → C) (al : I → ℕ → I → C), (∀ j x, e j x = ∑ b, z b j * S.tan b x) → (∀ c b, al c 0 b = if c = b then 1 else 0) → (∀ c (k : ℕ) x, 1 ≤ k → S.al c k x = ∑ b, al c k b * S.al b 0 x) → (∀ c, MvPowerSeries.constantCoeff (linPull e (t c)) = 0) ∧ (∀ (b : I) (μ : ι →₀ ℕ), ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, al c s b * MvPowerSeries.coeff μ (linPull e (t c) ^ (V.l ^ s)) = MvPowerSeries.coeff μ (∑ j, MvPowerSeries.C (R := C) (z b j) * (MvPowerSeries.X j : MvPowerSeries ι C))) ∧ ∀ (κ : J) (μ : ι →₀ ℕ), MvPowerSeries.coeff μ (linPull e (S.ze t κ)) = -∑ s ∈ Finset.range (μ.degree + 1), ∑ c, S.be c s κ * MvPowerSeries.coeff μ (linPull e (t c) ^ (V.l ^ s)) := by
  intro C _ V d I J _ _ G S t ht ι _ e z al he hal0 hal
  obtain ⟨f, hf⟩ : ∃ f : I → MvPowerSeries ι C,
      f = fun x => ∑ j, e j x • (MvPowerSeries.X j : MvPowerSeries ι C) := ⟨_, rfl⟩
  have hlp : ∀ F : MvPowerSeries I C, linPull e F = MvPowerSeries.subst f F := by
    intro F; subst hf; rfl
  have hf0 : ∀ x, MvPowerSeries.constantCoeff (f x) = 0 := by
    intro x
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hf, map_sum, MvPowerSeries.smul_eq_C_mul]
  have hsub : MvPowerSeries.HasSubst f := MvPowerSeries.hasSubst_of_constantCoeff_zero hf0
  have hl : 2 ≤ V.l := V.l_prime.two_le
  have hal' : ∀ c s x, S.al c s x = ∑ b', al c s b' * S.tan b' x := by
    intro c s x
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · simp only [hal0, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      exact S.cur_zero_inl c x
    · rw [hal c s x hs]
      refine Finset.sum_congr rfl fun b' _ => ?_
      rw [show S.al b' 0 x = S.tan b' x from S.cur_zero_inl b' x]
  simp only [hlp]
  refine ⟨fun c => MvPowerSeries.constantCoeff_subst_eq_zero hsub hf0 (ht.1 c), fun b μ => ?_,
    fun κ μ => ?_⟩
  · set P : I → ℕ → C := fun c s =>
      MvPowerSeries.coeff μ (MvPowerSeries.subst f (t c) ^ V.l ^ s) with hP
    set Y : I → C := fun b' => ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, al c s b' * P c s with hY
    set Zf : I → C := fun b' =>
      MvPowerSeries.coeff μ (∑ j, MvPowerSeries.C (R := C) (z b' j) *
        (MvPowerSeries.X j : MvPowerSeries ι C)) with hZ
    have hx : ∀ x, ∑ b', (Y b' - Zf b') * S.tan b' x = 0 := by
      intro x
      have h := _root_.GlobalTheory.LogSubst.coeff_subst_sum_pow_pow C I ι I V.l hl (fun c s => S.al c s x) t (MvPowerSeries.X x) f hf0 ht.1
        (fun μ' => by rw [MvPowerSeries.coeff_X, ht.2 x μ']) μ
      rw [MvPowerSeries.subst_X hsub] at h
      have eL : MvPowerSeries.coeff μ (f x) = ∑ b', Zf b' * S.tan b' x := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [hf, hZ, map_sum, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_C_mul, he,
          Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      have eR : ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, S.al c s x *
          MvPowerSeries.coeff μ (MvPowerSeries.subst f (t c) ^ V.l ^ s) =
          ∑ b', Y b' * S.tan b' x := by
        calc _ = ∑ s ∈ Finset.range (μ.degree + 1), ∑ b', ∑ c,
              al c s b' * P c s * S.tan b' x := by
              refine Finset.sum_congr rfl fun s _ => ?_
              simp only [hP, hal', Finset.sum_mul]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun c _ => ?_
              ring
          _ = ∑ b', ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, al c s b' * P c s * S.tan b' x :=
              Finset.sum_comm
          _ = _ := by simp only [hY, Finset.sum_mul]
      rw [eL, eR] at h
      simp only [sub_mul, Finset.sum_sub_distrib, h, sub_self]
    have hv : Matrix.vecMul (fun b' => Y b' - Zf b') (Matrix.of S.tan) = 0 := by
      funext x
      simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply]
      exact hx x
    have h0 := congrFun (Matrix.eq_zero_of_vecMul_eq_zero S.U_det_ne hv) b
    exact sub_eq_zero.mp h0
  · have hF : ∀ μ' : I →₀ ℕ, MvPowerSeries.coeff μ' (S.ze t κ) =
        ∑ s ∈ Finset.range (μ'.degree + 1), ∑ c, (-S.be c s κ) *
          MvPowerSeries.coeff μ' (t c ^ V.l ^ s) := by
      intro μ'
      show -(∑ s ∈ Finset.Icc 1 μ'.degree, ∑ c : I,
        S.be c s κ * MvPowerSeries.coeff μ' (t c ^ V.l ^ s)) = _
      simp only [neg_mul, Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_subset
      · intro s hs
        simp only [Finset.mem_Icc, Finset.mem_range] at hs ⊢
        omega
      · intro s hs hns
        have hs0 : s = 0 := by
          simp only [Finset.mem_Icc, Finset.mem_range] at hs hns
          omega
        subst hs0
        simp [show ∀ c, S.be c 0 κ = 0 from fun c => S.be_zero c κ]
    rw [_root_.GlobalTheory.LogSubst.coeff_subst_sum_pow_pow C I ι I V.l hl (fun c s => -S.be c s κ) t (S.ze t κ) f hf0 ht.1 hF μ]
    simp only [neg_mul, Finset.sum_neg_distrib]

end GlobalTheory.MainTerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HPullWUpGTwoGroupEmbeddingEqRename
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

noncomputable section

namespace GlobalTheory.MainTerm

theorem toW_same {C : Type} [Field C] {I : Fin 2 → Type} (g : Fin 2) (u : I g → C) (x : I g) :
    toW g u ⟨g, x⟩ = u x := by
  simp [toW]

theorem toW_other {C : Type} [Field C] {I : Fin 2 → Type} {g g' : Fin 2} (h : g' ≠ g) (u : I g → C)
    (x : I g') : toW g u ⟨g', x⟩ = 0 := by
  simp [toW, h]

theorem hPullW_upG {C : Type} [Field C] {I : Fin 2 → Type} [∀ g, Fintype (I g)] {ι ι' : Type}
    [Fintype ι] [Fintype ι'] (g : Fin 2) (F : MvPowerSeries (I g) C) (a : ι → WV I → C)
    (b : ι' → WV I → C) :
    hPullW (upG g F) a b = MvPowerSeries.subst (fun x : I g =>
      (∑ c, a c ⟨g, x⟩ • MvPowerSeries.X (Sum.inl c) + ∑ c, b c ⟨g, x⟩ • MvPowerSeries.X (Sum.inr c) :
        MvPowerSeries (ι ⊕ ι') C)) F := by
  have hb : MvPowerSeries.HasSubst (fun w : WV I =>
      (∑ c, a c w • MvPowerSeries.X (Sum.inl c) + ∑ c, b c w • MvPowerSeries.X (Sum.inr c) :
        MvPowerSeries (ι ⊕ ι') C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by simp
  have ha : MvPowerSeries.HasSubst (fun x : I g => (MvPowerSeries.X ⟨g, x⟩ : MvPowerSeries (WV I) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by simp
  unfold hPullW upG
  rw [MvPowerSeries.subst_comp_subst_apply ha hb]
  congr 1
  funext x
  rw [MvPowerSeries.subst_X hb]

theorem rename_linPull {C : Type} [Field C] {σ ι τ : Type} [Fintype σ] [Fintype ι] (f : ι → τ)
    (e : ι → σ → C) (F : MvPowerSeries σ C) :
    MvPowerSeries.rename f (linPull e F) = MvPowerSeries.subst (fun x : σ =>
      (∑ c, e c x • MvPowerSeries.X (f c) : MvPowerSeries τ C)) F := by
  have ha : MvPowerSeries.HasSubst (fun x : σ =>
      (∑ c : ι, e c x • MvPowerSeries.X c : MvPowerSeries ι C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by simp
  unfold linPull
  rw [MvPowerSeries.rename_eq_subst,
    MvPowerSeries.subst_comp_subst_apply ha (MvPowerSeries.HasSubst.X_comp f)]
  congr 1
  funext x
  rw [← MvPowerSeries.rename_eq_subst]
  simp

theorem hPullW_upG_toW : ∀ (C : Type) [Field C] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (g : Fin 2) (ι ι' : Type) [Fintype ι] [Fintype ι'] (e : ι → I g → C) (v' : ι' → I (1 - g) → C), (∀ F : MvPowerSeries (I g) C, hPullW (upG g F) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) = MvPowerSeries.rename Sum.inl (linPull e F)) ∧ ∀ F : MvPowerSeries (I (1 - g)) C, hPullW (upG (1 - g) F) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) = MvPowerSeries.rename Sum.inr (linPull v' F) := by
  intro C _ I _ g ι ι' _ _ e v'
  have h : g ≠ 1 - g := by fin_cases g <;> decide
  refine ⟨fun F => ?_, fun F => ?_⟩
  · rw [hPullW_upG, rename_linPull]
    simp [toW_same, toW_other h]
  · rw [hPullW_upG, rename_linPull]
    simp [toW_same, toW_other h.symm]

end GlobalTheory.MainTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IndependentModFirstCoeffChainLastStep
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical GlobalTheory.FrobRoot

namespace GlobalTheory.LastStep

theorem mm_mul_int {C : Type} [Field C] {V : VF C} {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) :
    V.MM (a * b) := by
  unfold VF.MM VF.Ge at *
  rw [V.v.map_mul]
  exact add_pos_of_pos_of_nonneg ha (by simpa using hb)

theorem mm_sum {C : Type} [Field C] {V : VF C} {ι : Type} (s : Finset ι) (f : ι → C)
    (h : ∀ i ∈ s, V.MM (f i)) : V.MM (∑ i ∈ s, f i) := by
  have mm_zero : V.MM (0 : C) := by
    unfold VF.MM; rw [V.v.map_zero]; exact WithTop.top_pos
  have mm_add : ∀ {a b : C}, V.MM a → V.MM b → V.MM (a + b) :=
    fun ha hb => V.v.map_lt_add ha hb
  induction s using Finset.induction_on with
  | empty => simpa using mm_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact mm_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem mm_of_tan {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
    {G : Cart V d I J} (S : Sys G) (w : I → C) (h : ∀ k, V.MM (∑ c, w c * S.tan c k)) (c : I) :
    V.MM (w c) := by
  have h1 : S.U * S.U⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr S.U_det_ne)
  have e : w c = ∑ k, (∑ b, w b * S.tan b k) * S.U⁻¹ k c := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ b, ∑ k, w b * S.tan b k * S.U⁻¹ k c = w b * (S.U * S.U⁻¹) b c := by
      intro b
      rw [Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by simp only [Sys.U, Matrix.of_apply]; ring
    simp only [this, h1, Matrix.one_apply]
    simp
  rw [e]
  exact mm_sum _ _ fun k _ => mm_mul_int (h k) (inv_int S.U S.U_int S.unimod k c)

theorem indepMod_first_coeff : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.Alt → ∀ (g : Fin 2) (a : ZMod d), X.big g a → ∀ (i : ℕ) (S : Sys (X.G g)) (Z : Type) (D : Formalism.BaseCaseIdentities.Data C Z (I g)), Adapted S D a i → ∀ s : ℕ, s < Formalism.BaseCaseIdentities.Kn i → ∀ (m : ℕ) (y : Fin m → I g → C), (∀ δ c, V.Ge 0 (y δ c)) → IndepMod V (fun δ c => if D.lev c = s then y δ c else 0) → IndepMod V (fun δ (κ : J g) => ∑ c ∈ Finset.univ.filter (fun c => D.lev c = s), y δ c ^ V.l * ((V.l : C) * S.be c 1 κ)) := by
  intro C _ V d _ I J _ _ X hA g a ha i S Z D hD s hs m y hy hind co hco hsum
  have mm_add : ∀ {a b : C}, V.MM a → V.MM b → V.MM (a + b) :=
    fun ha hb => V.v.map_lt_add ha hb
  have mm_pow : ∀ {a : C}, V.MM a → ∀ {n : ℕ}, n ≠ 0 → V.MM (a ^ n) := by
    intro a ha n hn
    unfold VF.MM at *
    rw [V.v.map_pow]
    exact nsmul_pos ha hn
  have ge_of_pow : ∀ {a : C} {n : ℕ}, n ≠ 0 → V.Ge 0 (a ^ n) → V.Ge 0 a := by
    intro a n hn ha
    unfold VF.Ge at *
    rw [V.v.map_pow] at ha
    rw [WithTop.coe_zero] at ha ⊢
    by_contra h
    exact absurd ha (not_le.mpr (nsmul_neg (not_le.mp h) hn))
  let R : Subring C := {
    carrier := {x | V.Ge 0 x}
    mul_mem' := fun ha hb => VF.Ge.mul_int ha hb
    one_mem' := VF.Ge.one
    add_mem' := fun ha hb => VF.Ge.add ha hb
    zero_mem' := VF.Ge.zero 0
    neg_mem' := fun ha => VF.Ge.neg ha }
  have mm_add_pow : ∀ (e : ℕ) {a b : C}, V.Ge 0 a → V.Ge 0 b →
      V.MM ((a + b) ^ (V.l ^ e) - (a ^ (V.l ^ e) + b ^ (V.l ^ e))) := by
    intro e a b ha hb
    obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq V.l_prime (⟨a, ha⟩ : R) (⟨b, hb⟩ : R) e
    have h := congrArg (Subtype.val) hr
    push_cast at h
    rw [h, add_sub_cancel_left]
    have hr0 : V.Ge 0 (r : C) := r.2
    have mm_of_ge_one : ∀ {x : C}, V.Ge 1 x → V.MM x := by
      intro x hx
      refine lt_of_lt_of_le ?_ hx
      exact_mod_cast (zero_lt_one : (0 : ℝ) < 1)
    apply mm_of_ge_one
    first
      | simpa using hr0.l_mul
      | simpa [mul_assoc] using (ha.mul_int (hb.mul_int hr0)).l_mul
  have mm_sum_pow : ∀ (e : ℕ) {ι : Type} (s : Finset ι) (x : ι → C),
      (∀ i ∈ s, V.Ge 0 (x i)) →
      V.MM ((∑ i ∈ s, x i) ^ (V.l ^ e) - ∑ i ∈ s, x i ^ (V.l ^ e)) := by
    intro e ι s x hx
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, Finset.sum_empty, zero_pow (pow_ne_zero e V.l_prime.ne_zero), sub_zero]
      unfold VF.MM; rw [V.v.map_zero]; exact WithTop.top_pos
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have hs : ∀ i ∈ s, V.Ge 0 (x i) := fun i hi => hx i (Finset.mem_insert_of_mem hi)
      have h := mm_add (mm_add_pow e (hx a (Finset.mem_insert_self a s)) (VF.Ge.sum hs)) (ih hs)
      convert h using 1 <;> ring
  haveI := X.algClosed
  have hl : V.l ≠ 0 := V.l_prime.ne_zero
  choose r hr using fun δ => IsAlgClosed.exists_pow_nat_eq (co δ) (Nat.pos_of_ne_zero hl)
  have hr0 : ∀ δ, V.Ge 0 (r δ) := fun δ => ge_of_pow hl (by rw [hr]; exact hco δ)
  set w : I g → C := fun c => ∑ δ, r δ * y δ c with hw
  have hw0 : ∀ c, V.Ge 0 (w c) := fun c => VF.Ge.sum fun δ _ => (hr0 δ).mul_int (hy δ c)
  set T := Finset.univ.filter (fun c => D.lev c = s) with hT
  have hbig : X.big g (a + ((2 * s : ℕ) : ZMod d)) :=
    (S4.parity_of_alt (X.big g) (CharacteristicFromRanks.alt_step X.big X.big_compl hA g) a ha (2 * s)).2 (even_two_mul s)
  have hgood : ∀ c ∈ T, (X.G g).Good (a + ((2 * s : ℕ) : ZMod d)) (S.tan c) (S.cur c) := by
    intro c hc
    have h1 : D.lev c = s := (Finset.mem_filter.1 hc).2
    have h2 : D.lev c < Formalism.BaseCaseIdentities.Kn i := h1 ▸ hs
    have h3 := hD.2.2.2.2 c h2
    rw [h1] at h3
    rw [← h3]
    exact hD.good (D.pure_good c (by rw [hD.2.2.1]; exact h2))
  have hG := Cart.Good.comb T (co := w) (fun c _ => hw0 c) hgood
  have hR := X.R2 hA g _ hbig _ _ hG (by
    intro κ
    rw [Cart.c0'_comb]
    have h1 : V.MM (∑ c ∈ T, (w c ^ V.l - ∑ δ, (r δ * y δ c) ^ V.l) * ((V.l : C) * S.be c 1 κ)) := by
      refine mm_sum _ _ fun c _ => mm_mul_int ?_ (l_mul_be_one_int S c κ)
      have := mm_sum_pow 1 Finset.univ (fun δ => r δ * y δ c) (fun δ _ => (hr0 δ).mul_int (hy δ c))
      simpa only [pow_one] using this
    have h2 := mm_add h1 (hsum κ)
    convert h2 using 1
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm (s := Finset.univ) (t := T), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [mul_pow, hr, sub_mul, Finset.sum_mul, mul_assoc, sub_add_cancel]
    rfl)
  have hwm : ∀ c, V.MM (if D.lev c = s then w c else 0) := by
    refine mm_of_tan S _ fun k => ?_
    convert hR k using 1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hT, Finset.sum_filter, ite_mul, zero_mul]
  intro δ
  rw [← hr δ]
  refine mm_pow (hind r hr0 (fun c => ?_) δ) hl
  convert hwm c using 1
  by_cases hc : D.lev c = s <;> simp [hw, hc]

end GlobalTheory.LastStep
end

