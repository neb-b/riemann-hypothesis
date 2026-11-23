module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0014

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PQuotTrans
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

namespace QuotTrans

section CechFacts

variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] {G : Cell U → Type v}
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}

theorem subsingleton_H_one_iff :
    Subsingleton (Cech.H G ρ 1) ↔
      ∀ z : Cech.Cochain G 1, Cech.d G ρ 1 z = 0 → ∃ w : Cech.Cochain G 0, Cech.d G ρ 0 w = z := by
  unfold Cech.H
  rw [Submodule.Quotient.subsingleton_iff, Submodule.comap_subtype_eq_top]
  constructor
  · intro h z hz
    exact h (LinearMap.mem_ker.mpr hz)
  · intro h z hz
    exact h z (LinearMap.mem_ker.mp hz)

theorem sgn_mul_sgn_erase {J : Finset (Fin n)} {j k : Fin n} (hj : j ∈ J) (hk : k ∈ J) (hjk : j ≠ k) :
    Cech.sgn J j * Cech.sgn (J.erase j) k = -(Cech.sgn J k * Cech.sgn (J.erase k) j) := by
  wlog h : j < k generalizing j k
  · have h' : k < j := lt_of_le_of_ne (not_lt.mp h) hjk.symm
    rw [this hk hj hjk.symm h', neg_neg]
  have hmem : j ∈ J.filter (· < k) := Finset.mem_filter.mpr ⟨hj, h⟩
  have e1 : (J.erase j).filter (· < k) = (J.filter (· < k)).erase j := by rw [Finset.filter_erase]
  have e2 : (J.erase k).filter (· < j) = J.filter (· < j) := by
    rw [Finset.filter_erase]
    apply Finset.erase_eq_of_notMem
    simp only [Finset.mem_filter, not_and, not_lt]
    intro _; exact h.le
  have hb : 1 ≤ (J.filter (· < k)).card := Finset.card_pos.mpr ⟨j, hmem⟩
  unfold Cech.sgn
  rw [e1, e2, Finset.card_erase_of_mem hmem]
  obtain ⟨b', hb'⟩ : ∃ b', (J.filter (· < k)).card = b' + 1 := ⟨_, (Nat.sub_add_cancel hb).symm⟩
  rw [hb', Nat.add_sub_cancel, pow_succ]
  ring

theorem d_one_d_zero
    (hρ : ∀ (I J K : Cell U) (h : I.1 ⊆ J.1) (h' : J.1 ⊆ K.1) (m : G I),
      ρ J K h' (ρ I J h m) = ρ I K (h.trans h') m)
    (w : Cech.Cochain G 0) : Cech.d G ρ 1 (Cech.d G ρ 0 w) = 0 := by
  funext J
  have key : ∀ (K K' : Cech.Idx U 0) (h : K.1.1 ⊆ J.1.1) (h' : K'.1.1 ⊆ J.1.1), K = K' →
      ρ K.1 J.1 h (w K) = ρ K'.1 J.1 h' (w K') := by
    rintro K _ h h' rfl; rfl
  rw [Cech.d_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Cech.d_apply, map_sum, map_zsmul, hρ, Finset.smul_sum, smul_smul]
  rw [Pi.zero_apply, Finset.sum_sigma']
  refine Finset.sum_involution
    (fun p _ => ⟨⟨p.2.1, Finset.mem_of_mem_erase p.2.2⟩,
      ⟨p.1.1, Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp p.2.2).1.symm, p.1.2⟩⟩⟩) ?_ ?_
    (fun _ _ => Finset.mem_univ _) (fun p _ => rfl)
  · rintro ⟨⟨j, hj⟩, ⟨k, hk⟩⟩ -
    have hk' := Finset.mem_erase.mp hk
    have hidx : Cech.face (Cech.face J ⟨j, hj⟩) ⟨k, hk⟩ =
        Cech.face (Cech.face J ⟨k, hk'.2⟩) ⟨j, Finset.mem_erase.mpr ⟨hk'.1.symm, hj⟩⟩ :=
      Subtype.ext (Subtype.ext (Finset.erase_right_comm))
    dsimp only
    rw [key _ _ _ (((Cech.face_subset _ _).trans (Cech.face_subset _ _))) hidx, ← add_smul]
    have hs : Cech.sgn J.1.1 j * Cech.sgn (Cech.face J ⟨j, hj⟩).1.1 k =
        -(Cech.sgn J.1.1 k * Cech.sgn (Cech.face J ⟨k, hk'.2⟩).1.1 j) :=
      sgn_mul_sgn_erase hj hk'.2 hk'.1.symm
    rw [hs, neg_add_cancel, zero_smul]
  · rintro ⟨⟨j, hj⟩, ⟨k, hk⟩⟩ - - heq
    exact (Finset.mem_erase.mp hk).1 (congrArg (fun p => p.1.1) heq)

theorem subsingleton_H_one_of_exact {A B C : Cell U → Type v}
    [∀ I, AddCommGroup (A I)] [∀ I, Module R (A I)] [∀ I, AddCommGroup (B I)] [∀ I, Module R (B I)]
    [∀ I, AddCommGroup (C I)] [∀ I, Module R (C I)]
    {ρA : ∀ I J : Cell U, I.1 ⊆ J.1 → A I →ₗ[R] A J} {ρB : ∀ I J : Cell U, I.1 ⊆ J.1 → B I →ₗ[R] B J}
    {ρC : ∀ I J : Cell U, I.1 ⊆ J.1 → C I →ₗ[R] C J}
    (ι : ∀ I, A I →ₗ[R] B I) (π : ∀ I, B I →ₗ[R] C I)
    (hι : ∀ I J h m, ι J (ρA I J h m) = ρB I J h (ι I m))
    (hπ : ∀ I J h m, π J (ρB I J h m) = ρC I J h (π I m))
    (hinj : ∀ I, Function.Injective (ι I)) (hsurj : ∀ I, Function.Surjective (π I))
    (hex : ∀ I b, π I b = 0 → ∃ a, ι I a = b)
    (hρB : ∀ (I J K : Cell U) (h : I.1 ⊆ J.1) (h' : J.1 ⊆ K.1) (m : B I),
      ρB J K h' (ρB I J h m) = ρB I K (h.trans h') m)
    (hA : Subsingleton (Cech.H A ρA 1)) (hC : Subsingleton (Cech.H C ρC 1)) :
    Subsingleton (Cech.H B ρB 1) := by
  rw [subsingleton_H_one_iff] at hA hC ⊢
  intro z hz
  have hπd := Cech.mapC_d (R := R) (G := B) (G' := C) π hπ
  have hιd := Cech.mapC_d (R := R) (G := A) (G' := B) ι hι

  obtain ⟨wc, hwc⟩ := hC (Cech.mapC (R := R) (G := B) (G' := C) π 1 z) (by rw [← hπd, hz, map_zero])
  choose w hw using fun I : Cech.Idx U 0 => hsurj I.1 (wc I)
  have hmw : Cech.mapC (R := R) (G := B) (G' := C) π 0 w = wc := funext hw
  have hr : Cech.mapC (R := R) (G := B) (G' := C) π 1 (z - Cech.d B ρB 0 w) = 0 := by
    rw [map_sub, hπd 0, hmw, hwc, sub_self]

  choose g hg using fun J : Cech.Idx U 1 => hex J.1 _ (congrFun hr J)
  have hg' : Cech.mapC (R := R) (G := A) (G' := B) ι 1 g = z - Cech.d B ρB 0 w := funext hg
  have hdg : Cech.d A ρA 1 g = 0 := by
    have h2 : Cech.mapC (R := R) (G := A) (G' := B) ι (1 + 1) (Cech.d A ρA 1 g) = 0 := by
      rw [hιd 1 g, hg', map_sub, hz, d_one_d_zero hρB, sub_zero]
    funext J
    exact hinj J.1 ((congrFun h2 J).trans (map_zero (ι J.1)).symm)
  obtain ⟨v, hv⟩ := hA g hdg
  refine ⟨w + Cech.mapC (R := R) (G := A) (G' := B) ι 0 v, ?_⟩
  rw [map_add (f := _), ← hιd, hv, hg', add_sub_cancel]

end CechFacts

end QuotTrans

theorem QuotTrans.proof : QuotTrans.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ F₁ F₂ F₃ h32 h21 h23 h12
  unfold SubSystem.quotH at h23 h12 ⊢

  let π : ∀ I, (F₁.sub I ⧸ SubSystem.quotSub F₁ F₃ I) →ₗ[S] (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) :=
    fun I => (SubSystem.quotSub F₁ F₃ I).mapQ (SubSystem.quotSub F₁ F₂ I) LinearMap.id
      (fun y hy => h32 I hy)

  let incl : ∀ I, F₂.sub I →ₗ[S] F₁.sub I := fun I =>
    { toFun := fun y => ⟨y, h21 I y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let ι : ∀ I, (F₂.sub I ⧸ SubSystem.quotSub F₂ F₃ I) →ₗ[S] (F₁.sub I ⧸ SubSystem.quotSub F₁ F₃ I) :=
    fun I => (SubSystem.quotSub F₂ F₃ I).mapQ (SubSystem.quotSub F₁ F₃ I) (incl I) (fun _ hy => hy)
  refine QuotTrans.subsingleton_H_one_of_exact ι π ?_ ?_ ?_ ?_ ?_ ?_ h23 h12
  · intro I J h m
    induction m using Submodule.Quotient.induction_on
    rfl
  · intro I J h m
    induction m using Submodule.Quotient.induction_on
    rfl
  ·
    intro I
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro q hq
    induction q using Submodule.Quotient.induction_on with
    | H y =>
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        ((Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F₁ F₃ I)).mp (LinearMap.mem_ker.mp hq))
  · intro I q
    induction q using Submodule.Quotient.induction_on with
    | H y => exact ⟨Submodule.Quotient.mk y, rfl⟩
  ·
    intro I b hb
    induction b using Submodule.Quotient.induction_on with
    | H y =>
      have hy : (y : E) ∈ F₂.sub I := (Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F₁ F₂ I)).mp hb
      exact ⟨Submodule.Quotient.mk ⟨y, hy⟩, rfl⟩
  · intro I J K h h' m
    induction m using Submodule.Quotient.induction_on
    rfl

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCountDrop
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

universe u w

namespace SectionCount.Drop

theorem pow_add_le (c n : ℝ) (hc : 0 ≤ c) (hn : 1 ≤ n) :
    ∀ e : ℕ, (n + c) ^ e ≤ n ^ e + ((1 + c) ^ e - 1) * (n ^ e / n)
  | 0 => by simp
  | e + 1 => by
    have ih := pow_add_le c n hc hn e
    have hn0 : 0 < n := by linarith
    have hA : 0 ≤ (1 + c) ^ e - 1 := by
      have : 1 ≤ (1 + c) ^ e := one_le_pow₀ (by linarith)
      linarith
    have hq : n ^ e / n ≤ n ^ e := div_le_self (by positivity) hn
    have hq' : n ^ (e + 1) / n = n ^ e := by
      rw [pow_succ]; field_simp
    have hqn : n ^ e / n * n = n ^ e := by field_simp
    have h1 : (n + c) ^ e * (n + c) ≤ (n ^ e + ((1 + c) ^ e - 1) * (n ^ e / n)) * (n + c) :=
      mul_le_mul_of_nonneg_right ih (by linarith)
    have h2 : ((1 + c) ^ e - 1) * c * (n ^ e / n) ≤ ((1 + c) ^ e - 1) * c * n ^ e :=
      mul_le_mul_of_nonneg_left hq (mul_nonneg hA hc)
    rw [hq', pow_succ, pow_succ, pow_succ]
    nlinarith [h1, h2, hqn]

theorem pow_add_le_mul (c n : ℝ) (hc : 0 ≤ c) (hn : 1 ≤ n) (e : ℕ) :
    (n + c) ^ e ≤ (1 + c) ^ e * n ^ e := by
  rw [← mul_pow]
  exact pow_le_pow_left₀ (by linarith) (by nlinarith) e

theorem term_le (I C c n h : ℝ) (e d : ℕ) (hed : e ≤ d) (hc : 0 ≤ c) (hn : 1 ≤ n)
    (hh : |h - I * (n + c) ^ e / (e.factorial : ℝ)| ≤ C * (n + c) ^ e / (n + c)) :
    h ≤ (if e = d then I else 0) * n ^ d / (d.factorial : ℝ) +
      (|I| + |C|) * (1 + c) ^ e * (n ^ d / n) := by
  have hn0 : 0 < n := by linarith
  have hnc : n ≤ n + c := by linarith
  have hP : (n + c) ^ e ≤ (1 + c) ^ e * n ^ e := pow_add_le_mul c n hc hn e
  have hPe : 0 ≤ (n + c) ^ e := by positivity
  have hne : n ^ e ≤ n ^ d := pow_le_pow_right₀ hn hed
  have h1 := (abs_le.mp hh).2

  have hC : C * (n + c) ^ e / (n + c) ≤ |C| * (1 + c) ^ e * (n ^ d / n) := by
    calc C * (n + c) ^ e / (n + c) ≤ |C| * (n + c) ^ e / (n + c) := by
          gcongr; exact le_abs_self C
      _ ≤ |C| * (n + c) ^ e / n := by
          apply div_le_div_of_nonneg_left (by positivity) hn0 hnc
      _ ≤ |C| * ((1 + c) ^ e * n ^ e) / n := by gcongr
      _ ≤ |C| * ((1 + c) ^ e * n ^ d) / n := by gcongr
      _ = |C| * (1 + c) ^ e * (n ^ d / n) := by ring
  have hfac : (1 : ℝ) ≤ (e.factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero e)

  have hM : I * (n + c) ^ e / (e.factorial : ℝ) ≤
      (if e = d then I else 0) * n ^ d / (d.factorial : ℝ) + |I| * (1 + c) ^ e * (n ^ d / n) := by
    split_ifs with hde
    · subst hde
      have hA := pow_add_le c n hc hn e
      have hlow : n ^ e ≤ (n + c) ^ e := pow_le_pow_left₀ hn0.le hnc e
      have hD : 0 ≤ (n + c) ^ e - n ^ e := by linarith
      have hq : 0 ≤ n ^ e / n := by positivity
      have hdiff : I * ((n + c) ^ e - n ^ e) ≤ |I| * (1 + c) ^ e * (n ^ e / n) := by
        calc I * ((n + c) ^ e - n ^ e) ≤ |I| * ((n + c) ^ e - n ^ e) :=
              mul_le_mul_of_nonneg_right (le_abs_self I) hD
          _ ≤ |I| * (((1 + c) ^ e - 1) * (n ^ e / n)) :=
              mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg I)
          _ ≤ |I| * (1 + c) ^ e * (n ^ e / n) := by
              rw [mul_assoc]
              exact mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg I)
      have hpos : (0 : ℝ) < (e.factorial : ℝ) := by linarith
      have hR : 0 ≤ |I| * (1 + c) ^ e * (n ^ e / n) := by positivity
      rw [div_le_iff₀ hpos]
      have : I * (n + c) ^ e = I * n ^ e + I * ((n + c) ^ e - n ^ e) := by ring
      rw [this, add_mul, div_mul_cancel₀ _ hpos.ne']
      nlinarith
    · have hlt : e < d := lt_of_le_of_ne hed hde
      have hd1 : n ^ e ≤ n ^ d / n := by
        rw [le_div_iff₀ hn0, ← pow_succ]
        exact pow_le_pow_right₀ hn hlt
      have hpos : (0 : ℝ) < (e.factorial : ℝ) := by linarith
      calc I * (n + c) ^ e / (e.factorial : ℝ) ≤ |I| * (n + c) ^ e / (e.factorial : ℝ) := by
            gcongr; exact le_abs_self I
        _ ≤ |I| * (n + c) ^ e := div_le_self (by positivity) hfac
        _ ≤ |I| * ((1 + c) ^ e * n ^ e) := by gcongr
        _ ≤ |I| * ((1 + c) ^ e * (n ^ d / n)) := by gcongr
        _ = 0 * n ^ d / (d.factorial : ℝ) + |I| * (1 + c) ^ e * (n ^ d / n) := by ring
  have : (|I| + |C|) * (1 + c) ^ e * (n ^ d / n) =
      |I| * (1 + c) ^ e * (n ^ d / n) + |C| * (1 + c) ^ e * (n ^ d / n) := by ring
  rw [this]
  linarith

theorem interNum_fin_congr {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} {a a' : ℕ} (h : a = a') (pp : Ideal (Poly S N)) (F : SubSystem S x Ω) :
    interNum pp (fun _ : Fin a => F) = interNum pp (fun _ : Fin a' => F) := by
  subst h; rfl

end SectionCount.Drop


open Classical in
theorem SectionCount.Drop.proof (hF : SectionCount.Drop.Filt.Statement.{u, w})
    (hT : SectionCount.Drop.Term.Statement.{u, w}) (hH : SectionCount.Drop.HilbW.Statement.{u, w})
    (hR : GenericPointSectionInput.Statement.{u, w}) : SectionCount.Drop.Statement.{u, w} := by
  intro k _ Ω _ _ N x d Nb b hZ hN hb
  obtain ⟨β, hβ, hβZ, m, pp, e, c, hpp, hcount, hloss⟩ := hF k Ω N x d Nb b hZ hb
  choose c' hc' using fun j => hT k Ω N x Nb b (pp j) (e j) (c j) hN (hpp j).1
  choose C hC using fun j => hH k Ω N x Nb (pp j) (e j) hN (hpp j).1
  obtain ⟨-, hsym, -, hcut, -⟩ := hR k Ω N x
  set g : Ideal (Poly k N) → ℤ := fun qq => interNum qq (fun _ : Fin d => Nb.toSubSystem) with hg

  have hkey : ∑ j, (if e j = d then interNum (pp j) (fun _ : Fin (e j) => Nb.toSubSystem) else 0) =
      interNum (primeOf (S := k) x) (Fin.cons (α := fun _ => SubSystem k x Ω) (twistSys k x (b : ℤ))
        (fun _ : Fin d => Nb.toSubSystem)) := by
    have h1 : ∀ j, (if e j = d then interNum (pp j) (fun _ : Fin (e j) => Nb.toSubSystem) else 0) =
        if e j = d then g (pp j) else 0 := fun j => by
      split_ifs with h
      · exact SectionCount.Drop.interNum_fin_congr h _ _
      · rfl
    have hc4 := hcut d (primeOf (S := k) x) (fun _ => Nb) (twistBundle k x (b : ℤ)) β hZ hβ hβZ
    have htb : (twistBundle k x (b : ℤ)).toSubSystem = twistSys k x (b : ℤ) := rfl
    simp only [htb] at hc4
    have hrot := hsym (d + 1) (primeOf (S := k) x)
      (Fin.cons (α := fun _ => LineBundle k x) (twistBundle k x (b : ℤ)) (fun _ => Nb))
      (finRotate (d + 1)) hZ
    have hL : (fun i => (Fin.cons (α := fun _ => LineBundle k x) (twistBundle k x (b : ℤ))
        (fun _ => Nb) i).toSubSystem) = Fin.cons (α := fun _ => SubSystem k x Ω) (twistSys k x (b : ℤ))
          (fun _ : Fin d => Nb.toSubSystem) := by
      funext i; refine Fin.cases ?_ (fun i => ?_) i
      · simp only [Fin.cons_zero]; rfl
      · simp only [Fin.cons_succ]
    have hLr : (fun i => (Fin.cons (α := fun _ => LineBundle k x) (twistBundle k x (b : ℤ))
        (fun _ => Nb) (finRotate (d + 1) i)).toSubSystem) =
          Fin.snoc (α := fun _ => SubSystem k x Ω) (fun i : Fin d => ((fun _ => Nb) i).toSubSystem)
            (twistSys k x (b : ℤ)) := by
      funext i; refine Fin.lastCases ?_ (fun i => ?_) i
      · simp; rfl
      · simp [finRotate_apply]
    rw [← hL, ← hrot, hLr, hc4, Finset.sum_congr rfl (fun j _ => h1 j)]
    have hTq : ∀ qq : Ideal (Poly k N),
        (if h : qq ∈ (primeOf (S := k) x ⊔ zeroIdeal (twistSys k x (b : ℤ)) β).minimalPrimes ∧
            IsSubvar x qq d then
          haveI : qq.IsPrime := h.1.1.1
          ((cutMult (primeOf (S := k) x ⊔ zeroIdeal (twistSys k x (b : ℤ)) β) qq).toNat : ℤ) *
            interNum qq (fun _ : Fin d => Nb.toSubSystem)
        else 0) = ∑ j, if e j = d ∧ pp j = qq then g qq else 0 := by
      intro qq
      have hq := hcount qq
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      by_cases hP : qq ∈ (primeOf (S := k) x ⊔ zeroIdeal (twistSys k x (b : ℤ)) β).minimalPrimes ∧
          IsSubvar x qq d
      · rw [dite_eq_left hP]; rw [dite_eq_left hP] at hq; rw [hq]
      · rw [dite_eq_right hP]; rw [dite_eq_right hP] at hq; rw [hq]; simp
    rw [finsum_congr hTq, finsum_eq_sum_of_support_subset (s := Finset.univ.image pp)]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      by_cases hd : e j = d
      · simp only [hd, true_and, if_true]
        rw [Finset.sum_ite_eq]
        simp
      · simp [hd]
    · intro qq hqq
      rw [Function.mem_support] at hqq
      obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hqq
      have : pp j = qq := by
        by_contra hne; simp [hne] at hj
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
      exact ⟨j, this⟩
  have hkeyR : ∑ j, (if e j = d then (interNum (pp j) (fun _ : Fin (e j) => Nb.toSubSystem) : ℝ) else 0) =
      (interNum (primeOf (S := k) x) (Fin.cons (α := fun _ => SubSystem k x Ω) (twistSys k x (b : ℤ))
        (fun _ : Fin d => Nb.toSubSystem)) : ℝ) := by
    rw [← hkey]; push_cast; rfl
  have hev : ∀ᶠ n : ℕ in atTop, ∀ j,
      |(Module.finrank k (SubSystem.quotH (twistMul Nb.toSubSystem (n + c' j) 0)
          ((twistMul Nb.toSubSystem (n + c' j) 0).twist (idealSys x (pp j))) 0) : ℝ) -
        (interNum (pp j) (fun _ : Fin (e j) => Nb.toSubSystem) : ℝ) * ((n + c' j : ℕ) : ℝ) ^ (e j) /
          ((e j).factorial : ℝ)| ≤ C j * ((n + c' j : ℕ) : ℝ) ^ (e j) / ((n + c' j : ℕ) : ℝ) := by
    rw [eventually_all]; intro j
    exact (tendsto_add_atTop_nat (c' j)).eventually (hC j)
  refine ⟨∑ j, (|(interNum (pp j) (fun _ : Fin (e j) => Nb.toSubSystem) : ℝ)| + |C j|) *
    (1 + (c' j : ℝ)) ^ (e j), ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1 i _
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have h1 := (Int.cast_le (R := ℝ)).mpr (hloss n i)
  push_cast at h1
  have h3 : ∀ j, (Module.finrank k (SubSystem.quotH (twistMul Nb.toSubSystem (n + c' j) 0)
      ((twistMul Nb.toSubSystem (n + c' j) 0).twist (idealSys x (pp j))) 0) : ℝ) ≤
      (if e j = d then (interNum (pp j) (fun _ : Fin (e j) => Nb.toSubSystem) : ℝ) else 0) *
        (n : ℝ) ^ d / (d.factorial : ℝ) +
      (|(interNum (pp j) (fun _ : Fin (e j) => Nb.toSubSystem) : ℝ)| + |C j|) * (1 + (c' j : ℝ)) ^ (e j) *
        ((n : ℝ) ^ d / n) := fun j => by
    have hj := hn j
    push_cast at hj
    exact SectionCount.Drop.term_le _ _ _ _ _ (e j) d (hpp j).2.1 (Nat.cast_nonneg _) hn1' hj
  calc _ ≤ _ := h1
    _ ≤ _ := Finset.sum_le_sum (fun j _ => by exact_mod_cast ((hc' j) n i).2)
    _ ≤ _ := Finset.sum_le_sum (fun j _ => h3 j)
    _ = (∑ j, (if e j = d then (interNum (pp j) (fun _ : Fin (e j) => Nb.toSubSystem) : ℝ) else 0)) *
          (n : ℝ) ^ d / (d.factorial : ℝ) +
        (∑ j, (|(interNum (pp j) (fun _ : Fin (e j) => Nb.toSubSystem) : ℝ)| + |C j|) *
          (1 + (c' j : ℝ)) ^ (e j)) * ((n : ℝ) ^ d / n) := by
      simp only [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_div]
    _ = _ := by rw [hkeyR]; ring

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionMulInjSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def SectionMulInj.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (pp : Ideal (Poly k N)), pp.IsPrime → (∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) →
    primeOf (S := k) x ≤ pp →
    ∀ (D M : LineBundle k x) (s : Ω), (∃ f ∈ zeroIdeal D.toSubSystem s, f ∉ pp) →
    ∀ (I : Chart x), ∀ y ∈ M.sub I,
      s * y ∈ ((M.toSubSystem.twist D.toSubSystem).twist (idealSys x pp)).sub I →
      y ∈ (M.toSubSystem.twist (idealSys x pp)).sub I

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperDevissageSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def SnapperDevissage.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    (F : SubFamily k x E), (∀ I, (F.sub I).FG) →
    ∃ (r : ℕ) (pp : Fin r → Ideal (Poly k N)) (a : Fin r → ℤ),
      (∀ m, (pp m).IsPrime ∧ (∀ f ∈ pp m, ∀ d : ℕ, homogeneousComponent d f ∈ pp m) ∧
        primeOf (S := k) x ≤ pp m) ∧
      ∀ (t : ℕ) (L : Fin t → LineBundle k x) (n : Fin t → ℕ) (c : ℤ),
        eulerChar k ((F.toSubSystem.twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c)) =
          ∑ m, pieceChar k (pp m) (a m) L n c

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperDiffPolySt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def SnapperDiffPoly.Statement : Prop :=
  ∀ (t D : ℕ) (f : (Fin t → ℕ) → ℤ → ℚ) (μ : Fin t → ℤ),
    IsNumPolyLT t D (fun n c => f n (c + 1) - f n c) →
    (∀ j, IsNumPolyLT t D (fun n c => f (Function.update n j (n j + 1)) (c + μ j) - f n c)) →
    IsNumPolyLT t (D + 1) f

end

end GroundTheory.Heights₂.Heights.Kleiman
end

