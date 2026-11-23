module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DiscPowerMonomialMemSupported

@[expose] public section

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem mem_degAt_det {R : Type} [CommRing R] {n : ℕ} (y : Fin n → ℤ) (t : ℤ) :
    DegAt t (∑ a : Fin n, if y a = t then 1 else 0)
      (Matrix.det (Matrix.of fun a c : Fin n => (MvPolynomial.X (y a, c) : MvPolynomial (ℤ × Fin n) R))) := by
  classical
  rw [Matrix.det_apply]
  refine degAt_sum _ _ fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  have h1 : (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : MvPolynomial (ℤ × Fin n) R) = C (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) := by
    simp
  rw [h1]
  refine degAt_C_mul _ ?_
  have h2 := degAt_prod (R := R) (x := t) Finset.univ
    (fun i : Fin n => (MvPolynomial.X (y (σ i), i) : MvPolynomial (ℤ × Fin n) R))
    (fun i => if y (σ i) = t then 1 else 0) (fun i _ => degAt_X (x := t) (y (σ i), i))
  rw [Equiv.sum_comp σ (fun a => if y a = t then 1 else 0)] at h2
  exact h2

namespace Dat

variable {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (p K : ℕ)

def discPowerMonomialDegree (j : ℤ) (b : ℤ → ℕ) (x : ℤ) : ℕ :=
  X.m0 K * (∑ a : Fin r, if X.F.fr (j - 1) a.val = x then 1 else 0) +
    ∑ i : Fin r, ((b (X.F.fr (j - 1) i.val) : ℤ) - X.Bw p K j (X.F.fr (j - 1) i.val)).toNat *
      (if X.F.fr (j - 1) i.val = x then 1 else 0)


omit [NeZero n'] [NeZero r] in
def memdMu (j : ℤ) (u : Fin r × Fin r → ℕ) (x : ℤ) : ℕ :=
  ∑ v : Fin r × Fin r, u v * (if X.F.fr j v.1.val = x then 1 else 0)

end Dat

section Deg

variable {p n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] {X : Dat n' r}

theorem degAt_disc_power_monomial (O : Type) [CommRing O] (j : ℤ) (b : ℤ → ℕ) (x : ℤ) :
    DegAt x (X.discPowerMonomialDegree p K j b x) (X.discPowerTimesMonomial p K O j b) := by
  classical
  unfold Dat.discPowerMonomialDegree Dat.discPowerTimesMonomial Dat.Dw
  refine degAt_mul (degAt_pow (mem_degAt_det _ x) _) ?_
  exact degAt_prod Finset.univ _ _ fun i _ => degAt_pow (degAt_X (x := x) (X.F.fr (j - 1) i.val, (0 : Fin r))) _

theorem mem_degAt_Mu (O : Type) [CommRing O] (j : ℤ) (u : Fin r × Fin r → ℕ) (x : ℤ) :
    DegAt x (X.memdMu j u x) (X.memMu O j u) := by
  classical
  unfold Dat.memdMu Dat.memMu
  exact degAt_prod Finset.univ _ _ fun v _ => degAt_pow (degAt_X (x := x) (X.F.fr j v.1.val, v.2)) _

theorem disc_power_monomial_degree_off (j : ℤ) (b : ℤ → ℕ) (x : ℤ) (h : ∀ a : Fin r, X.F.fr (j - 1) a.val ≠ x) :
    X.discPowerMonomialDegree p K j b x = 0 := by
  unfold Dat.discPowerMonomialDegree
  simp [h]

theorem mem_dMu_off (j : ℤ) (u : Fin r × Fin r → ℕ) (x : ℤ) (h : ∀ a : Fin r, X.F.fr j a.val ≠ x) :
    X.memdMu j u x = 0 := by
  unfold Dat.memdMu
  simp [h]

theorem disc_power_monomial_degree_at_w (hX : X.Hyp p K) (j : ℤ) (b : ℤ → ℕ) (a0 : Fin r) :
    X.discPowerMonomialDegree p K j b (X.F.fr (j - 1) a0.val) =
      X.m0 K + ((b (X.F.fr (j - 1) a0.val) : ℤ) - X.Bw p K j (X.F.fr (j - 1) a0.val)).toNat := by
  classical
  have hinj := fr_injective X.F hX.valid (j - 1)
  have hiff : ∀ a : Fin r, (X.F.fr (j - 1) a.val = X.F.fr (j - 1) a0.val) ↔ a = a0 :=
    fun a => ⟨fun h => hinj h, fun h => by rw [h]⟩
  unfold Dat.discPowerMonomialDegree
  simp only [hiff]
  simp

theorem mem_dMu_tau (hX : X.Hyp p K) (j : ℤ) (u : Fin r × Fin r → ℕ) (t : Fin r) :
    X.memdMu j u (X.F.fr j t.val) = ∑ c, u (t, c) := by
  classical
  have hinj := fr_injective X.F hX.valid j
  have hiff : ∀ a : Fin r, (X.F.fr j a.val = X.F.fr j t.val) ↔ a = t :=
    fun a => ⟨fun h => hinj h, fun h => by rw [h]⟩
  unfold Dat.memdMu
  rw [Fintype.sum_prod_type]
  simp only [hiff]
  rw [Finset.sum_eq_single t]
  · simp
  · intro a _ ha
    simp [ha]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem mem_degAt_segRen_off {R : Type} [CommRing R] (j : ℤ) {n : ℕ} (A : MvPolynomial (Fin (segN X.F j) × Fin n) R)
    (x : ℤ) (hx : x ∉ X.F.letters j) : DegAt x 0 (segRen X.F j R n A) := by
  refine degAt_of_supported {v : ℤ × Fin n | v.1 ∈ X.F.letters j} ?_ ?_
  · refine mem_supported.mpr fun v hv => ?_
    obtain ⟨u, _, rfl⟩ := mem_vars_rename _ _ (Finset.mem_coe.mp hv)
    exact segE_mem X.F j u.1
  · intro v hv h
    exact hx (h ▸ hv)

end Deg

theorem restMemB_of (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) (C₀ : ℝ) : RestMemB C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk j b hb q mm hmm x hx hW
  classical
  have : Fact p.Prime := ⟨hX.prime⟩
  have hV := hX.valid
  have hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D := hAdm.2.2.2.2.2.2.2.2.1
  obtain ⟨dd, b', b'', P, P1, P2, hPμ, h1, h2, hsum, hC, hPATH, hGood, hSt, hu, hd⟩ := exists_path_decomposition D hAdm hX j b q
  have H : PlHyp (segN X.F j - r) (X.beS p K j (X.restr j b) : ℤ) (plPart q.1.1) := by
    let μ := q.1.1
    let b := X.restr j b
    have hP : X.IsPATH p K j b μ dd := hPATH
    classical
    have hr : 0 < r := NeZero.pos r
    have hV := hX.valid
    obtain ⟨P, hPμ⟩ := hP.path
    have hrN : r ≤ segN X.F j := k_r_le_segN X.F hV hr j
    have hNK : segN X.F j + r ≤ K := le_trans (Nat.add_le_add_right (hX.card j) r) hX.NsK
  
    have htau : ∀ t (ht : t < r), ∃ l : Fin (segN X.F j), l.val = segN X.F j - r + t ∧
        segE X.F j l = X.F.fr j t ∧ HStrip (stg μ (segN X.F j - r + t)) (stg μ (segN X.F j - r + t + 1)) (dd l) := by
      intro t ht
      let l : Fin (segN X.F j) := ⟨segN X.F j - r + t, by omega⟩
      have hl : segE X.F j l = X.F.fr j t := (segE_eq_fr_iff X.F hV j l ht).mpr rfl
      have hvec : (segLL X.F j).vec l = true := by
        rw [comb_vec, hl]; exact (hV.2.2.2.2.1 j t ht).2
      have hs := T.step_vec P l hvec
      rw [hPμ, stg_castSucc μ, stg_succ μ] at hs
      exact ⟨l, rfl, hl, hs⟩
    have hlow : ∀ i ≤ segN X.F j - r, ∀ m, stg μ i m ≤ (X.beS p K j b : ℤ) := by
      intro i hi m
      have h1 := T.mu_le_dplus P i (by omega) m
      rw [hPμ, stg_eq μ i (by omega)] at h1
      have h2 : T.dplus (segLL X.F j) dd i ≤ X.beS p K j b := by
        let s := i
        have hs : s ≤ segN X.F j - r := hi
        classical
        have hr : 0 < r := NeZero.pos r
        have hV := hX.valid
        unfold T.dplus Dat.beS
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
        · omega
        · exact Nat.zero_le _
        · exact le_rfl
      exact le_trans h1 (by exact_mod_cast h2)
    have hup : ∀ t ≤ r, ∀ m, stg μ (segN X.F j - r + t) m ≤ (X.beS p K j b : ℤ) := by
      intro t
      induction t with
      | zero => intro _ m; exact hlow _ le_rfl m
      | succ t ih =>
        intro ht m
        obtain ⟨l, hlv, hl, hs⟩ := htau t (by omega)
        rw [show segN X.F j - r + (t + 1) = segN X.F j - r + t + 1 by ring]
        by_cases hm : m.val = 0
        · have := hP.head l ⟨t, by omega⟩ hl m (by omega)
          rw [stg_succ μ, hlv] at this
          rw [this]
        · have hm' := m.isLt
          have h2 := hs.2.1 ⟨m.val - 1, by omega⟩ (by simp only []; omega)
          have e : (⟨(⟨m.val - 1, by omega⟩ : Fin (r + K)).val + 1, by simp only []; omega⟩ : Fin (r + K)) = m :=
            Fin.ext (by simp only []; omega)
          rw [e] at h2
          exact le_trans h2 (ih (by omega) _)
    have hdom : ∀ k, k < segN X.F j + 1 → Antitone (stg (plPart μ) k) := by
      intro k hk a a' haa
      rw [stg_plPart, stg_plPart, ← stg_eq μ k hk, ← hPμ]
      exact P.dom _ (by rw [Fin.le_def]; simpa using haa)
    refine ⟨?_, ?_, ?_⟩
    · intro i hi m
      rw [stg_plPart]
      constructor
      · have h1 := T.mu_nonneg P i (by omega) (Fin.castAdd K m) (by
          have := m.isLt
          simp only [Fin.val_castAdd]; omega)
        rwa [hPμ, stg_eq μ i (by omega)] at h1
      · by_cases h : i ≤ segN X.F j - r
        · exact hlow i h _
        · have := hup (i - (segN X.F j - r)) (by omega) (Fin.castAdd K m)
          rwa [show segN X.F j - r + (i - (segN X.F j - r)) = i by omega] at this
    · intro m
      rw [stg_plPart]
      obtain ⟨l, hlv, hl, -⟩ := htau (r - 1) (by omega)
      have := hP.head l ⟨r - 1, by omega⟩ hl (Fin.castAdd K m) (by
        have := m.isLt
        simp only [Fin.val_castAdd]; omega)
      rw [stg_succ μ, hlv, show segN X.F j - r + (r - 1) + 1 = segN X.F j by omega] at this
      exact this
    · intro t ht c
      obtain ⟨l, hlv, hl, hs⟩ := htau t ht
      refine colH_step (hdom _ (by omega)) (hdom _ (by omega)) ?_ ?_ c
      · intro a
        rw [stg_plPart, stg_plPart]
        exact hs.1 _
      · intro a h
        rw [stg_plPart, stg_plPart]
        have := hs.2.1 (Fin.castAdd K a) (by simp only [Fin.val_castAdd]; omega)
        exact this
  have hI' : IsSt P1.mu (Ican P1.mu) := by rw [h1]; exact mem_isSt_Ican H
  have hI'' : IsSt P2.mu q.1.2.1 := by rw [h2]; exact hSt
  have u1 := (standard_polynomial_mem_bounds (segLL X.F j) b' (fun th M => (hA3 p O S _ r (segLL X.F j) b' th M).1) P1 _ hI').1
  have u2 := (standard_polynomial_mem_bounds (segLL X.F j) b'' (fun th M => (hA3 p O S _ K (segLL X.F j) b'' th M).1) P2 _ hI'').1
  rw [h1] at u1
  rw [h2] at u2
  obtain ⟨i, rfl⟩ := segE_surj X.F j hx
  have hevW : ∀ a : Fin r, Even (X.F.fr (j - 1) a.val) := fun a => (hV.2.2.2.2.1 (j - 1) a.val a.isLt).2
  have hevT : ∀ a : Fin r, Even (X.F.fr j a.val) := fun a => (hV.2.2.2.2.1 j a.val a.isLt).2
  have hA : ¬ Even (segE X.F j i) → DegAt (segE X.F j i) (0 + 0 + b' i) (X.memA p K O j b q.1) := by
    intro ho
    unfold Dat.memA
    refine degAt_mul (degAt_mul ?_ ?_) (degAt_segRen X.F j u1 i)
    · refine degAt_of_supported {v : ℤ × Fin r | Even v.1} (disc_power_monomial_mem_supported O j b _ fun a _ => hevW a) ?_
      intro v hv h
      exact ho (h ▸ hv)
    · refine degAt_of_supported {v : ℤ × Fin r | Even v.1} (mem_Mu_supported O j _ _ fun a _ => hevT a) ?_
      intro v hv h
      exact ho (h ▸ hv)
  have hG : Even (segE X.F j i) → DegAt (segE X.F j i) (b'' i) (X.memG K O j q.1) := fun _ =>
    degAt_segRen X.F j u2 i
  rw [ordDeg_prod hA hG mm hmm]
  obtain ⟨-, gE, gO⟩ := hGood i hW
  split_ifs with he
  · have hs := (T.step_vec P2 i ((comb_vec X.F j i).mpr he)).2.2
    rw [h2] at hs
    have := gE he
    rw [hs] at this
    exact_mod_cast this
  · have hvec : (segLL X.F j).vec i = false := by
      by_contra h
      exact he ((comb_vec X.F j i).mp (by simpa using h))
    have hs := (T.step_cov P1 i hvec).2.2
    rw [h1] at hs
    have := gO he
    rw [hs] at this
    simpa using this

end Formalism.MainNotions.SelectionLemmas.Pf
