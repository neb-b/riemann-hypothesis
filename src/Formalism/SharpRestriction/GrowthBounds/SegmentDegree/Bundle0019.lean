module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.TauDegreeOnPathBound
public import Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.SumTotalLoss
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle0018

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DminusLeBeS
section
noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem residue_class_count : ResidueClassCount := by
  classical
  intro r Q be c ρ hr hQ
  have hQ0 : 0 < Q := by omega
  have hcore := Formalism.InvariantFactorPaths.BranchingDimensions.residueClassLowerBound r Q be (ρ % Q + (Q - c % Q)) hr hQ
  refine le_trans hcore ?_
  have hle : ((Finset.univ : Finset (Fin r → Fin (Q - 2 * be))).filter
      (fun u => (∑ l, (u l : ℕ)) % Q = (ρ % Q + (Q - c % Q)) % Q)).card ≤
      ((Fintype.piFinset fun _ : Fin r => Finset.range (Q - 2 * be)).filter
        fun w => (c + ∑ i, w i) % Q = ρ % Q).card := by
    refine Finset.card_le_card_of_injOn (fun u => fun l => (u l : ℕ)) ?_ ?_
    · intro u hu
      have hu' := (Finset.mem_filter.mp (Finset.mem_coe.mp hu)).2
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun l =>
        Finset.mem_range.mpr (u l).isLt, ?_⟩)
      have h1 : (∑ l, (u l : ℕ)) ≡ ρ % Q + (Q - c % Q) [MOD Q] := hu'
      have h2 : c + ∑ l, (u l : ℕ) ≡ c + (ρ % Q + (Q - c % Q)) [MOD Q] := Nat.ModEq.add_left c h1
      have h3 : c + (ρ % Q + (Q - c % Q)) ≡ ρ [MOD Q] := by
        have hc : c % Q < Q := Nat.mod_lt _ hQ0
        have e1 : c + (ρ % Q + (Q - c % Q)) = (c - c % Q + Q) + ρ % Q := by
          have := Nat.mod_le c Q
          omega
        rw [e1]
        have e2 : c - c % Q + Q ≡ 0 [MOD Q] := by
          have hd : Q ∣ c - c % Q := Nat.dvd_sub_mod c
          exact (Nat.modEq_zero_iff_dvd.mpr (Dvd.dvd.add hd (dvd_refl Q)))
        have e3 : ρ % Q ≡ ρ [MOD Q] := Nat.mod_modEq ρ Q
        simpa using e2.add e3
      exact h2.trans h3
    · intro u _ u' _ huu
      funext l
      exact Fin.ext (congrFun huu l)
  exact_mod_cast hle

theorem tele_le : ∀ (n : ℕ) (hn : 0 < n) (f g : Fin n → ℤ),
    (∀ (a : Fin n) (h : a.val + 1 < n), f ⟨a.val + 1, h⟩ ≤ g a) →
    ∑ a, (f a - g a) ≤ f ⟨0, hn⟩ - g ⟨n - 1, by omega⟩ := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  intro f g h
  rw [Finset.sum_sub_distrib, Fin.sum_univ_succ f, Fin.sum_univ_castSucc g]
  have h1 : ∑ i : Fin m, f i.succ ≤ ∑ i : Fin m, g i.castSucc :=
    Finset.sum_le_sum fun i _ => h i.castSucc (by simp)
  have e : (⟨m + 1 - 1, by omega⟩ : Fin (m + 1)) = Fin.last m := Fin.ext (by simp)
  rw [e]
  have e0 : (⟨0, hn⟩ : Fin (m + 1)) = 0 := rfl
  rw [e0]
  linarith

section D21

variable {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (p K : ℕ)

theorem dminus_le_beS (hX : X.Hyp p K) (j : ℤ) (b : ℤ → ℕ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ)
    (dd : Fin (segN X.F j) → ℕ) (hP : X.IsPATH p K j b μ dd) (s : ℕ) :
    T.dminus (segLL X.F j) dd s ≤ X.beS p K j b := by
  classical
  have hr : 0 < r := NeZero.pos r
  have hV := hX.valid
  have hrN := k_r_le_segN X.F hV hr j
  unfold T.dminus Dat.beS
  have himg : (X.F.letters j).filter (· < X.F.fr j 0) =
      (Finset.univ.filter fun l : Fin (segN X.F j) => l.val < segN X.F j - r).image (segE X.F j) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hx, hlt⟩
      obtain ⟨i, rfl⟩ := segE_surj X.F j hx
      exact ⟨i, (segE_lt_fr_iff X.F hV hr j i).mp hlt, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨segE_mem X.F j i, (segE_lt_fr_iff X.F hV hr j i).mpr hi⟩
  rw [himg, Finset.sum_image (fun a _ b _ h => (segE_strictMono X.F j).injective h), Finset.sum_filter]
  refine Finset.sum_le_sum fun l _ => ?_
  split_ifs with h1 h2 h2
  · rw [hP.degs l ((segE_lt_fr_iff X.F hV hr j l).mpr h2)]
  · exfalso
    have hl := l.isLt
    have ht : l.val - (segN X.F j - r) < r := by omega
    have hseg : segE X.F j l = X.F.fr j (l.val - (segN X.F j - r)) :=
      (segE_eq_fr_iff X.F hV j l ht).mpr (by omega)
    have hvec : (segLL X.F j).vec l = true := by
      rw [comb_vec, hseg]; exact (hV.2.2.2.2.1 j _ ht).2
    rw [hvec] at h1
    exact absurd h1.2 (by simp)
  · exact Nat.zero_le _
  · exact le_rfl

end D21

theorem tau_degree_on_path_bound : TauDegreeOnPathBound := by
  intro p n' r K _ _ _ X hX j b μ dd hP i hi
  classical
  have hr : 0 < r := NeZero.pos r
  have hV := hX.valid
  have hrN := k_r_le_segN X.F hV hr j
  obtain ⟨P, hPμ⟩ := hP.path
  have hil := i.isLt
  have hnot : ¬ i.val < segN X.F j - r := fun h => by
    have := (segE_lt_fr_iff X.F hV hr j i).mpr h
    omega
  have ht : i.val - (segN X.F j - r) < r := by omega
  have hseg : segE X.F j i = X.F.fr j (i.val - (segN X.F j - r)) :=
    (segE_eq_fr_iff X.F hV j i ht).mpr (by omega)
  have hvec : (segLL X.F j).vec i = true := by
    rw [comb_vec, hseg]; exact (hV.2.2.2.2.1 j _ ht).2
  have hs := T.step_vec P i hvec
  rw [hPμ] at hs
  have hn : 0 < r + K := by omega
  have h1 := tele_le (r + K) hn (μ i.succ) (μ i.castSucc) hs.2.1
  rw [hs.2.2] at h1
  have h2 : μ i.succ ⟨0, hn⟩ = (X.beS p K j b : ℤ) :=
    hP.head i ⟨i.val - (segN X.F j - r), ht⟩ hseg ⟨0, hn⟩ (Nat.zero_le _)
  have h3 := T.neg_dminus_le_mu P i.val (by omega) ⟨r + K - 1, by omega⟩
  rw [hPμ] at h3
  have h4 := dminus_le_beS X p K hX j b μ dd hP i.val
  have h5 : μ i.castSucc = μ ⟨i.val, by omega⟩ := rfl
  rw [h2, h5] at h1
  have h4' : (T.dminus (segLL X.F j) dd i.val : ℤ) ≤ (X.beS p K j b : ℤ) := by exact_mod_cast h4
  have : (dd i : ℤ) ≤ 2 * (X.beS p K j b : ℤ) := by linarith
  exact_mod_cast this

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.SumPosOfPer
section
noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Finset Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Geo

variable {n' r : ℕ} [NeZero n'] [NeZero r] {F : Frames n' r} {L₁ N₁ : ℕ}

theorem fr_add_mul_period (hV : F.Valid L₁ N₁) (j : ℤ) (i : ℕ) (m : ℤ) :
    F.fr (j + m * F.J) i = F.fr j i + m * n' := by
  have hper := hV.2.1
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have h1 := hper (j + k * F.J) i
    rw [show j + ((k : ℤ) + 1) * (F.J : ℤ) = j + k * F.J + F.J by ring, h1, ih]
    ring
  | pred k ih =>
    have h1 := hper (j + (-(k : ℤ) - 1) * F.J) i
    rw [show j + (-(k : ℤ) - 1) * (F.J : ℤ) + F.J = j + -(k : ℤ) * F.J by ring, ih] at h1
    linarith

theorem fr_lt_fr_of_lt_of_valid (hV : F.Valid L₁ N₁) (j : ℤ) (i : ℕ) :
    ∀ i', i < i' → i' < r → F.fr j i < F.fr j i' := by
  intro i' hii' hi'r
  induction i' with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hii' with h | h
    · exact lt_trans (ih h (by omega)) (hV.2.2.1 j k (by omega))
    · subst h
      exact hV.2.2.1 j i (by omega)

theorem sum_fr_le (hV : F.Valid L₁ N₁) (j : ℤ) (i i' : ℕ) (h : i ≤ i') (h' : i' < r) :
    F.fr j i ≤ F.fr j i' := by
  rcases h.lt_or_eq with h | h
  · exact (fr_lt_fr_of_lt_of_valid hV j i i' h h').le
  · subst h
    exact le_rfl

theorem sum_posOf_per (x m : ℤ) : posOf n' (x + m * n') = posOf n' x := by
  unfold posOf
  congr 3
  simp

theorem dist_add_mul_period (hV : F.Valid L₁ N₁) (j x m : ℤ) : F.dist (j + m * F.J) (x + m * n') = F.dist j x := by
  unfold Frames.dist
  rw [fr_add_mul_period hV]
  congr 1
  ring

theorem sum_prod_Ioc (g : ℕ → ℤ) (hg : Monotone g) (P : ℤ → Prop) [DecidablePred P] (ψ : ℤ → ℝ) (m : ℕ) :
    ∏ j ∈ Finset.range m, ∏ x ∈ (Finset.Ioc (g j) (g (j + 1))).filter P, ψ x =
      ∏ x ∈ (Finset.Ioc (g 0) (g m)).filter P, ψ x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, ih, ← Finset.prod_union
      (Finset.disjoint_filter_filter (Finset.Ioc_disjoint_Ioc_of_le le_rfl)), ← Finset.filter_union,
      Finset.Ioc_union_Ioc_eq_Ioc (hg (Nat.zero_le m)) (hg (Nat.le_succ m))]

end Geo

section GeoX

variable {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) {L₁ N₁ : ℕ} (p K : ℕ)

theorem mem_late_iff (hV : X.F.Valid L₁ N₁) (j x : ℤ) :
    x ∈ X.toLate j ↔ (eFr X.F (j - 1) < x ∧ x ≤ eFr X.F j) ∧ posOf n' x ∈ X.F.TT := by
  classical
  have : X.toLate j = nonW X.F j := rfl
  rw [this, nonW_eq hV, Finset.mem_filter, Finset.mem_Ioc]

theorem exists_shift_of_posOf_eq_of_mem_late (hV : X.F.Valid L₁ N₁) {j j' x x' : ℤ} (hx : x ∈ X.toLate j) (hx' : x' ∈ X.toLate j')
    (h : posOf n' x = posOf n' x') : ∃ m : ℤ, j' = j + m * X.F.J ∧ x' = x + m * n' := by
  have h1 : x % (n' : ℤ) = x' % (n' : ℤ) := by rw [← posOf_val, ← posOf_val, h]
  have h2 : (n' : ℤ) ∣ x' - x := Int.ModEq.dvd h1
  obtain ⟨m, hm⟩ := h2
  have hm' : x' = x + m * n' := by linarith [mul_comm (n' : ℤ) m]
  refine ⟨m, ?_, hm'⟩
  have a1 := (mem_late_iff X hV j x).mp hx
  have a2 := (mem_late_iff X hV j' x').mp hx'
  have p1 : eFr X.F (j + m * X.F.J) = eFr X.F j + m * n' := fr_add_mul_period hV j (r - 1) m
  have p0 : eFr X.F (j + m * X.F.J - 1) = eFr X.F (j - 1) + m * n' := by
    have := fr_add_mul_period hV (j - 1) (r - 1) m
    rw [show j + m * X.F.J - 1 = j - 1 + m * X.F.J by ring]
    exact this
  exact idx_unique (eFr_strictMono hV) (x := x') a2.1.1 a2.1.2 (by rw [p0]; linarith [a1.1.1])
    (by rw [p1]; linarith [a1.1.2])

theorem sum_Rj_per (hV : X.F.Valid L₁ N₁) (j m : ℤ) : X.Rj p K (j + m * X.F.J) = X.Rj p K j := by
  unfold Dat.Rj
  have e : j + m * X.F.J - 1 = (j - 1) + m * X.F.J := by ring
  rw [e, fr_add_mul_period hV (j - 1) 0 m, dist_add_mul_period hV]

theorem sum_Pz_per (hV : X.F.Valid L₁ N₁) (j x m : ℤ) :
    X.Pz p K (j + m * X.F.J) (x + m * n') = X.Pz p K j x := by
  unfold Dat.Pz
  rw [dist_add_mul_period hV, sum_Rj_per X p K hV]

theorem sum_Qc_per (hV : X.F.Valid L₁ N₁) (j m : ℤ) : X.Qc p K (j + m * X.F.J) = X.Qc p K j := by
  unfold Dat.Qc
  have e : j + m * X.F.J + 1 = (j + 1) + m * X.F.J := by ring
  rw [e, fr_add_mul_period hV (j + 1) (r - 1) m, fr_add_mul_period hV j (r - 1) m, sum_Rj_per X p K hV, sum_Rj_per X p K hV]
  congr 2
  ring

theorem sum_uniqP (hV : X.F.Valid L₁ N₁) (j j' x x' : ℤ) (hx : x ∈ X.toLate j) (hx' : x' ∈ X.toLate j')
    (h : posOf n' x = posOf n' x') : X.Pz p K j x = X.Pz p K j' x' := by
  obtain ⟨m, rfl, rfl⟩ := exists_shift_of_posOf_eq_of_mem_late X hV hx hx' h
  exact (sum_Pz_per X p K hV j x m).symm

theorem sum_perW (hV : X.F.Valid L₁ N₁) (j : ℤ) (i : Fin r) :
    X.Bw p K (j + X.F.J) (X.F.fr (j + X.F.J - 1) i.val) = X.Bw p K j (X.F.fr (j - 1) i.val) := by
  have e1 : X.F.fr (j + X.F.J - 1) i.val = X.F.fr (j - 1) i.val + 1 * n' := by
    have := fr_add_mul_period hV (j - 1) i.val 1
    rw [show j + (X.F.J : ℤ) - 1 = j - 1 + 1 * X.F.J by ring]
    exact this
  have e2 : j + (X.F.J : ℤ) = j + 1 * X.F.J := by ring
  unfold Dat.Bw
  rw [e1, e2, sum_posOf_per, dist_add_mul_period hV, sum_Rj_per X p K hV]

theorem prod_tiling (hV : X.F.Valid L₁ N₁) (φ : Fin n' → ℝ) :
    ∏ t ∈ X.F.TT, φ t = ∏ j ∈ Finset.range X.F.J, ∏ x ∈ X.toLate (j : ℤ), φ (posOf n' x) := by
  classical
  have hm := eFr_strictMono hV
  have h1 : ∀ j ∈ Finset.range X.F.J, ∏ x ∈ X.toLate (j : ℤ), φ (posOf n' x) =
      ∏ x ∈ (Finset.Ioc ((fun i : ℕ => eFr X.F ((i : ℤ) - 1)) j) ((fun i : ℕ => eFr X.F ((i : ℤ) - 1)) (j + 1))).filter
        (fun x => posOf n' x ∈ X.F.TT), φ (posOf n' x) := by
    intro j _
    have : X.toLate (j : ℤ) = nonW X.F j := rfl
    rw [this, nonW_eq hV]
    simp
  rw [Finset.prod_congr rfl h1, sum_prod_Ioc (fun i : ℕ => eFr X.F ((i : ℤ) - 1))
    (fun a b hab => hm.monotone (by omega)) (fun x => posOf n' x ∈ X.F.TT) (fun x => φ (posOf n' x)) X.F.J]
  have h2 : eFr X.F ((X.F.J : ℤ) - 1) = eFr X.F (((0 : ℕ) : ℤ) - 1) + n' := by
    have := hV.2.1 (-1) (r - 1)
    simp only [eFr]
    have e1 : ((X.F.J : ℤ) - 1) = -1 + X.F.J := by ring
    have e2 : (((0 : ℕ) : ℤ) - 1) = -1 := by norm_num
    rw [e1, e2, this]
  simp only [h2]
  set a := eFr X.F (((0 : ℕ) : ℤ) - 1) with ha
  symm
  refine Finset.prod_bij (fun x _ => posOf n' x) ?_ ?_ ?_ ?_
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · intro x hx y hy hxy
    exact posOf_injOn a (Finset.mem_Ioc.mp (Finset.mem_filter.mp hx).1) (Finset.mem_Ioc.mp (Finset.mem_filter.mp hy).1) hxy
  · intro t ht
    have hn : (0 : ℤ) < n' := by exact_mod_cast NeZero.pos n'
    have b0 := Int.emod_nonneg ((t.val : ℤ) - (a + 1)) hn.ne'
    have b1 := Int.emod_lt_of_pos ((t.val : ℤ) - (a + 1)) hn
    have hpos : posOf n' (a + 1 + ((t.val : ℤ) - (a + 1)) % (n' : ℤ)) = t := by
      have e : a + 1 + ((t.val : ℤ) - (a + 1)) % (n' : ℤ) =
          (t.val : ℤ) + (-(((t.val : ℤ) - (a + 1)) / (n' : ℤ))) * n' := by
        have := Int.emod_add_mul_ediv ((t.val : ℤ) - (a + 1)) (n' : ℤ)
        linarith
      rw [e, sum_posOf_per, posOf_natCast]
    refine ⟨a + 1 + ((t.val : ℤ) - (a + 1)) % (n' : ℤ), ?_, hpos⟩
    rw [Finset.mem_filter, Finset.mem_Ioc, hpos]
    exact ⟨⟨by omega, by omega⟩, ht⟩
  · intro x _
    rfl

theorem sum_LLsub (hV : X.F.Valid L₁ N₁) (j x : ℤ) (hx : x ∈ X.F.LLset j) : x ∈ X.toLate j ∧ x < X.F.fr j 0 := by
  classical
  unfold Frames.LLset at hx
  rw [Finset.mem_filter, Finset.mem_Ioo] at hx
  refine ⟨(mem_late_iff X hV j x).mpr ⟨⟨hx.1.1, ?_⟩, hx.2⟩, hx.1.2⟩
  exact hx.1.2.le.trans (fr_zero_le_eFr hV j)

theorem sum_frlate (hV : X.F.Valid L₁ N₁) (j : ℤ) (i : Fin r) : X.F.fr j i.val ∈ X.toLate j := by
  refine (mem_late_iff X hV j _).mpr ⟨⟨?_, ?_⟩, (hV.2.2.2.2.1 j i.val i.isLt).1⟩
  · have h1 := hV.2.2.2.1 (j - 1)
    rw [sub_add_cancel] at h1
    exact lt_of_lt_of_le h1 (fr_zero_le hV j i.val i.isLt)
  · exact sum_fr_le hV j i.val (r - 1) (by have := i.isLt; omega) (Nat.sub_lt (NeZero.pos r) Nat.one_pos)

theorem sum_split (hV : X.F.Valid L₁ N₁) (j : ℤ) (ψ : ℤ → ℝ) :
    ∏ x ∈ X.toLate j, ψ x = (∏ x ∈ X.F.LLset j, ψ x) * ∏ i : Fin r, ψ (X.F.fr j i.val) := by
  classical
  have hinj : Function.Injective (fun i : Fin r => X.F.fr j i.val) := by
    intro a b hab
    by_contra hne
    rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with h | h
    · exact absurd hab (ne_of_lt (fr_lt_fr_of_lt_of_valid hV j a.val b.val h b.isLt))
    · exact absurd hab.symm (ne_of_lt (fr_lt_fr_of_lt_of_valid hV j b.val a.val h a.isLt))
  have hU : X.toLate j = X.F.LLset j ∪ Finset.univ.image (fun i : Fin r => X.F.fr j i.val) := by
    ext x
    rw [Finset.mem_union, Finset.mem_image]
    constructor
    · intro hx
      have a1 := (mem_late_iff X hV j x).mp hx
      by_cases h0 : x < X.F.fr j 0
      · left
        unfold Frames.LLset
        rw [Finset.mem_filter, Finset.mem_Ioo]
        exact ⟨⟨a1.1.1, h0⟩, a1.2⟩
      · right
        obtain ⟨i, hi, rfl⟩ := comb_frame_top X.F hV j x a1.2 (not_lt.mp h0) (r - 1)
          (Nat.sub_lt (NeZero.pos r) Nat.one_pos) a1.1.2
        exact ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩
    · rintro (hx | ⟨i, -, rfl⟩)
      · exact (sum_LLsub X hV j x hx).1
      · exact sum_frlate X hV j i
  have hdisj : Disjoint (X.F.LLset j) (Finset.univ.image (fun i : Fin r => X.F.fr j i.val)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx'
    have := (sum_LLsub X hV j _ hx).2
    have := fr_zero_le hV j i.val i.isLt
    omega
  rw [hU, Finset.prod_union hdisj, Finset.prod_image (fun a _ b _ h => hinj h)]

theorem J_le_card_TT_of_valid (hV : X.F.Valid L₁ N₁) : X.F.J ≤ X.F.TT.card := by
  classical
  refine le_trans ?_ (sum_card_nonW hV)
  calc X.F.J = ∑ _j ∈ Finset.range X.F.J, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum fun j _ => Finset.card_pos.mpr
      ⟨X.F.fr (j : ℤ) (⟨0, NeZero.pos r⟩ : Fin r).val, sum_frlate X hV (j : ℤ) ⟨0, NeZero.pos r⟩⟩

end GeoX

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

