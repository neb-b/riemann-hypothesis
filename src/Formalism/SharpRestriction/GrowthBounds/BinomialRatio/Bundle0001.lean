module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSystems

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.KeptFin
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem kf_coarseA_le {s r p : ℕ} (S : SegData s) (b : SegBlock s r) (i : Fin s) : coarseA p S b i ≤ S.bTop i := by
  unfold coarseA
  exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)

theorem kf_coarseC_le {s r p : ℕ} (S : SegData s) (aTop : Fin s → ℕ) (b : SegBlock s r) (i : Fin s) :
    coarseC p S aTop b i ≤ aTop i := by
  unfold coarseC
  exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)

def kfTuple {s r : ℕ} (b : SegBlock s r) :
    (Fin s → Fin (r + 1) → ℕ) × (Fin s → Fin (r + 1) → ℕ) × (Fin s → ℕ) × (Fin s → ℕ) × (Fin s → ℕ) × ℕ :=
  (b.rz, b.ry, b.o, b.w, b.sg, b.oPlus)

theorem kfTuple_inj {s r : ℕ} : Function.Injective (@kfTuple s r) := by
  rintro ⟨a1, a2, a3, a4, a5, a6⟩ ⟨b1, b2, b3, b4, b5, b6⟩ h
  simp only [kfTuple, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  rfl

theorem kf_cap_le {s r p : ℕ} (S : SegData s) (b : SegBlock s r) (l : ℕ) :
    cap p S b l ≤ S.A0 p + ∑ i, (S.bTop i : ℤ) := by
  unfold cap
  gcongr with i
  split_ifs
  · have h1 := kf_coarseA_le (p := p) S b i
    omega
  · omega

theorem kf_kept_finite (p r : ℕ) {s : ℕ} (S : SegData s) (aTop : Fin s → ℕ) :
    {b : SegBlock s r | Kept p r S aTop b}.Finite := by
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = ((S.A0 p + ∑ i, (S.bTop i : ℤ) : ℤ) : ℝ) +
      (S.La / (r + 1) + 4 / (p : ℝ) ^ 2) * ∑ i, 2 * (S.a : ℝ) / (S.P p i : ℝ) +
      S.La * (S.bPlus : ℝ) / (r + 1) := ⟨_, rfl⟩
  have hT := Set.Finite.prod (Set.Finite.pi fun i => Set.Finite.pi fun (_ : Fin (r + 1)) => Set.finite_Iic (S.P p i))
    (Set.Finite.prod (Set.Finite.pi fun i => Set.Finite.pi fun (_ : Fin (r + 1)) => Set.finite_Iic (S.P p i))
    (Set.Finite.prod (Set.Finite.pi fun i => Set.finite_Iic (S.bTop i))
    (Set.Finite.prod (Set.Finite.pi fun i => Set.finite_Iic (S.bTop i))
    (Set.Finite.prod (Set.Finite.pi fun i => Set.finite_Iic (aTop i)) (Set.finite_Iic ⌈R⌉₊)))))
  refine (hT.preimage kfTuple_inj.injOn).subset ?_
  rintro b ⟨⟨hdig, -, -⟩, hge, hlt, hop⟩
  simp only [Set.mem_preimage, kfTuple, Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Iic,
    forall_const]
  refine ⟨fun i c => (hdig i c).1.le, fun i c => (hdig i c).2.le, fun i => ?_, fun i => ?_, fun i => ?_, ?_⟩
  · by_cases h : S.sigma ≤ (i : ℕ)
    · exact (hge i h).1.trans (kf_coarseA_le S b i)
    · rw [(hlt i (not_le.mp h)).1]
      exact Nat.zero_le _
  · by_cases h : (i : ℕ) < S.sigma
    · exact (hlt i h).2.1.trans (kf_coarseA_le S b i)
    · rw [(hge i (not_lt.mp h)).2.2.1]
      exact Nat.zero_le _
  · by_cases h : (i : ℕ) < S.sigma
    · exact (hlt i h).2.2.1.trans (kf_coarseC_le S aTop b i)
    · rw [(hge i (not_lt.mp h)).2.2.2]
      exact Nat.zero_le _
  · have hc : (cap p S b s : ℝ) ≤ ((S.A0 p + ∑ i, (S.bTop i : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast kf_cap_le S b s
    have h1 : (b.oPlus : ℝ) ≤ R := by
      refine hop.trans ?_
      rw [hR]
      unfold Oplus
      linarith
    exact_mod_cast h1.trans (Nat.le_ceil R)

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Transported
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

def TransportedAlt (P : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop) : Prop :=
  ∀ Cc : ℝ, 0 ≤ Cc → ∃ T0 : ℝ, 0 < T0 ∧ ∀ C0 : ℝ, T0 ≤ C0 →
    ∃ T1 : ℝ, 0 < T1 ∧ ∀ CE1 CE2 Cm : ℝ, T1 ≤ CE1 → T1 ≤ CE2 → T1 ≤ Cm →
      ∃ T2 : ℝ, 0 < T2 ∧ ∀ CYb Cde Ck CD Cb : ℝ, T2 ≤ CYb → T2 ≤ Cde → T2 ≤ Ck → T2 ≤ CD → T2 ≤ Cb →
        P C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc

theorem TransportedAlt.mono {P P' : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop}
    (hP : ∀ C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc, P C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc →
      P' C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc) (h : TransportedAlt P) : TransportedAlt P' := by
  intro Cc hCc
  obtain ⟨T0, hT0, h0⟩ := h Cc hCc
  refine ⟨T0, hT0, fun C0 hC0 => ?_⟩
  obtain ⟨T1, hT1, h1⟩ := h0 C0 hC0
  refine ⟨T1, hT1, fun CE1 CE2 Cm a1 a2 a3 => ?_⟩
  obtain ⟨T2, hT2, h2⟩ := h1 CE1 CE2 Cm a1 a2 a3
  exact ⟨T2, hT2, fun CYb Cde Ck CD Cb b1 b2 b3 b4 b5 =>
    hP _ _ _ _ _ _ _ _ _ _ (h2 CYb Cde Ck CD Cb b1 b2 b3 b4 b5)⟩

theorem TransportedAlt.and {P P' : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop} (h : TransportedAlt P) (h' : TransportedAlt P') :
    TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc =>
      P C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc ∧ P' C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc := by
  intro Cc hCc
  obtain ⟨T0, hT0, h0⟩ := h Cc hCc
  obtain ⟨T0', -, h0'⟩ := h' Cc hCc
  refine ⟨max T0 T0', lt_max_of_lt_left hT0, fun C0 hC0 => ?_⟩
  obtain ⟨T1, hT1, h1⟩ := h0 C0 ((le_max_left _ _).trans hC0)
  obtain ⟨T1', -, h1'⟩ := h0' C0 ((le_max_right _ _).trans hC0)
  refine ⟨max T1 T1', lt_max_of_lt_left hT1, fun CE1 CE2 Cm a1 a2 a3 => ?_⟩
  obtain ⟨T2, hT2, h2⟩ := h1 CE1 CE2 Cm ((le_max_left _ _).trans a1) ((le_max_left _ _).trans a2)
    ((le_max_left _ _).trans a3)
  obtain ⟨T2', -, h2'⟩ := h1' CE1 CE2 Cm ((le_max_right _ _).trans a1) ((le_max_right _ _).trans a2)
    ((le_max_right _ _).trans a3)
  refine ⟨max T2 T2', lt_max_of_lt_left hT2, fun CYb Cde Ck CD Cb b1 b2 b3 b4 b5 => ⟨?_, ?_⟩⟩
  · exact h2 CYb Cde Ck CD Cb ((le_max_left _ _).trans b1) ((le_max_left _ _).trans b2)
      ((le_max_left _ _).trans b3) ((le_max_left _ _).trans b4) ((le_max_left _ _).trans b5)
  · exact h2' CYb Cde Ck CD Cb ((le_max_right _ _).trans b1) ((le_max_right _ _).trans b2)
      ((le_max_right _ _).trans b3) ((le_max_right _ _).trans b4) ((le_max_right _ _).trans b5)

theorem TransportedAlt.of_all {P : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop}
    (h : ∀ C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc, P C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc) : TransportedAlt P :=
  fun _ _ => ⟨1, one_pos, fun _ _ => ⟨1, one_pos, fun _ _ _ _ _ _ =>
    ⟨1, one_pos, fun _ _ _ _ _ _ _ _ _ _ => h _ _ _ _ _ _ _ _ _ _⟩⟩⟩

theorem TransportedAlt.of_explicit {P : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop} (t0 : ℝ → ℝ) (t1 : ℝ → ℝ → ℝ)
    (t2 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ)
    (h : ∀ C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc, 0 ≤ Cc → 1 ≤ C0 → t0 Cc ≤ C0 → 1 ≤ CE1 → 1 ≤ CE2 → 1 ≤ Cm →
      t1 Cc C0 ≤ CE1 → t1 Cc C0 ≤ CE2 → t1 Cc C0 ≤ Cm →
      1 ≤ CYb → 1 ≤ Cde → 1 ≤ Ck → 1 ≤ CD → 1 ≤ Cb →
      t2 Cc C0 CE1 CE2 Cm ≤ CYb → t2 Cc C0 CE1 CE2 Cm ≤ Cde → t2 Cc C0 CE1 CE2 Cm ≤ Ck →
      t2 Cc C0 CE1 CE2 Cm ≤ CD → t2 Cc C0 CE1 CE2 Cm ≤ Cb → P C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc) : TransportedAlt P := by
  intro Cc hCc
  refine ⟨max 1 (t0 Cc), lt_max_of_lt_left one_pos, fun C0 hC0 => ?_⟩
  refine ⟨max 1 (t1 Cc C0), lt_max_of_lt_left one_pos, fun CE1 CE2 Cm a1 a2 a3 => ?_⟩
  refine ⟨max 1 (t2 Cc C0 CE1 CE2 Cm), lt_max_of_lt_left one_pos, fun CYb Cde Ck CD Cb b1 b2 b3 b4 b5 => ?_⟩
  exact h _ _ _ _ _ _ _ _ _ _ hCc (le_trans (le_max_left _ _) hC0) (le_trans (le_max_right _ _) hC0)
    (le_trans (le_max_left _ _) a1) (le_trans (le_max_left _ _) a2) (le_trans (le_max_left _ _) a3)
    (le_trans (le_max_right _ _) a1) (le_trans (le_max_right _ _) a2) (le_trans (le_max_right _ _) a3)
    (le_trans (le_max_left _ _) b1) (le_trans (le_max_left _ _) b2) (le_trans (le_max_left _ _) b3)
    (le_trans (le_max_left _ _) b4) (le_trans (le_max_left _ _) b5)
    (le_trans (le_max_right _ _) b1) (le_trans (le_max_right _ _) b2) (le_trans (le_max_right _ _) b3)
    (le_trans (le_max_right _ _) b4) (le_trans (le_max_right _ _) b5)

theorem closed_of_thr {P : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop}
    (h : TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc => ∃ Ckap Ct Cs : ℝ, 0 < Ckap ∧ 0 < Ct ∧ 0 < Cs ∧
      P C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Ct Cc Cs) : Closed P := h

def be (X : Loc) (C0 : ℝ) : ℝ := (X.bh - X.bl) / X.b' + 2 * X.La C0 / X.k

structure Std (C0 Cde CE1 CE2 H : ℝ) (X : Loc) : Prop where
  pP : X.p.Prime
  p5 : 5 ≤ X.p
  n2 : 2 ≤ X.n'
  nEven : Even X.n'
  Y1 : 1 ≤ X.Y
  pk : X.k ^ 2 * X.Y ^ 2 ≤ (X.p : ℝ)
  N1k : 2 * (X.N1 : ℝ) + 3 ≤ X.k
  N1pos : 1 ≤ X.N1
  seg2 : 2 ≤ numSeg X.TT
  N2 : 2 ≤ X.N
  segB : ∀ j, segG X.TT j ≤ X.G' ∧ segS X.TT j ≤ X.N1
  bpos : 0 < X.b'
  loga : 1 ≤ Real.log X.a
  La1 : 1 ≤ X.La C0
  LaNY : 8 * Real.log (X.N * X.Y) ≤ X.La C0
  LaN : 2 * X.N * X.La C0 ≤ X.k
  LaK : 40 * X.N1 * X.La C0 / X.k ≤ X.de C0 Cde
  de6 : X.de C0 Cde < 1 / 6
  beLe : be X C0 ≤ X.de C0 Cde / 2 - 18 * X.N1 * X.La C0 / X.k
  be0 : 0 ≤ be X C0
  winA : ∀ s ∈ X.TT, (X.a : ℝ) ≤ X.aT s ∧ (X.aT s : ℝ) ≤ X.a * (1 + 2 / (X.k * X.Y))
  winB : ∀ s ∈ X.TT, X.b' * (1 - be X C0) ≤ X.bT s ∧ (X.bT s : ℝ) ≤ X.b' * (1 + be X C0)
  pab : (X.p : ℝ) < X.a / X.b'
  ab : X.k * X.Y ^ 2 * X.N * X.La C0 * Real.log X.a ≤ X.a / X.b'
  band : ∀ d : ℕ, Odd d → ¬ ((X.a / X.b') * (1 - 2 * X.de C0 Cde) ≤ (X.p : ℝ) ^ d ∧
      (X.p : ℝ) ^ d ≤ (X.a / X.b') * (1 + 2 * X.de C0 Cde))
  Hc : H * X.k ^ 3 * X.N * X.Q ^ 4 * X.c * X.Y ≤ X.b'
  Hb : H * X.k ^ 3 * X.N * X.Q ^ 4 * X.Y ≤ X.b'
  E0nn : 0 ≤ X.E0 C0 CE1 CE2
  N5 : X.E0 C0 CE1 CE2 / X.a + X.Q / X.a ≤ X.N1 * X.La C0 / X.k

end Formalism.MainNotions.ColumnSystems.Pf
end
end

