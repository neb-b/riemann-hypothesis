module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle0004
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle0002
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle0005

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.NegDminusLeMu
section
noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf.T

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

variable {n N : ℕ} {LL : Letters (Fin N)} {dd : Fin N → ℕ}

theorem step_vec (P : PPath n N LL dd) (i : Fin N) (h : LL.vec i = true) :
    HStrip (P.mu i.castSucc) (P.mu i.succ) (dd i) := by
  simpa [h] using P.step i

theorem step_cov (P : PPath n N LL dd) (i : Fin N) (h : LL.vec i = false) :
    HStrip (P.mu i.succ) (P.mu i.castSucc) (dd i) := by
  simpa [h] using P.step i

theorem mu_nonneg (P : PPath n N LL dd) :
    ∀ (s : ℕ) (hs : s < N + 1) (m : Fin n), m.val + s < n → 0 ≤ P.mu ⟨s, hs⟩ m := by
  intro s
  induction s with
  | zero =>
    intro hs m _
    have h0 : (⟨0, hs⟩ : Fin (N + 1)) = 0 := Fin.ext (by simp)
    rw [h0, P.zero]
    simp
  | succ s ih =>
    intro hs m hm
    have hsN : s < N := by omega
    cases hv : LL.vec ⟨s, hsN⟩
    · have hstr : HStrip (P.mu ⟨s + 1, hs⟩) (P.mu ⟨s, by omega⟩) (dd ⟨s, hsN⟩) := step_cov P ⟨s, hsN⟩ hv
      have hm1 : m.val + 1 < n := by omega
      calc (0 : ℤ) ≤ P.mu ⟨s, by omega⟩ ⟨m.val + 1, hm1⟩ :=
            ih (by omega) ⟨m.val + 1, hm1⟩ (show m.val + 1 + s < n by omega)
        _ ≤ P.mu ⟨s + 1, hs⟩ m := hstr.2.1 m hm1
    · have hstr : HStrip (P.mu ⟨s, by omega⟩) (P.mu ⟨s + 1, hs⟩) (dd ⟨s, hsN⟩) := step_vec P ⟨s, hsN⟩ hv
      calc (0 : ℤ) ≤ P.mu ⟨s, by omega⟩ m := ih (by omega) m (by omega)
        _ ≤ P.mu ⟨s + 1, hs⟩ m := hstr.1 m

theorem mu_nonpos (P : PPath n N LL dd) :
    ∀ (s : ℕ) (hs : s < N + 1) (m : Fin n), s ≤ m.val → P.mu ⟨s, hs⟩ m ≤ 0 := by
  intro s
  induction s with
  | zero =>
    intro hs m _
    have h0 : (⟨0, hs⟩ : Fin (N + 1)) = 0 := Fin.ext (by simp)
    rw [h0, P.zero]
    simp
  | succ s ih =>
    intro hs m hm
    have hsN : s < N := by omega
    obtain ⟨mv, hmv⟩ := m
    have hm' : s + 1 ≤ mv := hm
    cases hv : LL.vec ⟨s, hsN⟩
    · have hstr : HStrip (P.mu ⟨s + 1, hs⟩) (P.mu ⟨s, by omega⟩) (dd ⟨s, hsN⟩) := step_cov P ⟨s, hsN⟩ hv
      calc P.mu ⟨s + 1, hs⟩ ⟨mv, hmv⟩ ≤ P.mu ⟨s, by omega⟩ ⟨mv, hmv⟩ := hstr.1 _
        _ ≤ 0 := ih (by omega) ⟨mv, hmv⟩ (show s ≤ mv by omega)
    · have hstr : HStrip (P.mu ⟨s, by omega⟩) (P.mu ⟨s + 1, hs⟩) (dd ⟨s, hsN⟩) := step_vec P ⟨s, hsN⟩ hv
      obtain _ | mv := mv
      · omega
      · calc P.mu ⟨s + 1, hs⟩ ⟨mv + 1, hmv⟩ ≤ P.mu ⟨s, by omega⟩ ⟨mv, by omega⟩ := hstr.2.1 ⟨mv, by omega⟩ hmv
          _ ≤ 0 := ih (by omega) ⟨mv, by omega⟩ (show s ≤ mv by omega)

def dplus (LL : Letters (Fin N)) (dd : Fin N → ℕ) (s : ℕ) : ℕ :=
  ∑ l : Fin N, if l.val < s ∧ LL.vec l = true then dd l else 0

def dminus (LL : Letters (Fin N)) (dd : Fin N → ℕ) (s : ℕ) : ℕ :=
  ∑ l : Fin N, if l.val < s ∧ LL.vec l = false then dd l else 0

theorem dsum_succ (f : Fin N → Prop) [DecidablePred f] (dd : Fin N → ℕ) (s : ℕ) (hs : s < N) :
    (∑ l : Fin N, if l.val < s + 1 ∧ f l then dd l else 0) =
      (∑ l : Fin N, if l.val < s ∧ f l then dd l else 0) + if f ⟨s, hs⟩ then dd ⟨s, hs⟩ else 0 := by
  have key : ∀ l : Fin N, (if l.val < s + 1 ∧ f l then dd l else 0) =
      (if l.val < s ∧ f l then dd l else 0) + (if l = ⟨s, hs⟩ then (if f ⟨s, hs⟩ then dd ⟨s, hs⟩ else 0) else 0) := by
    intro l
    by_cases h1 : l = ⟨s, hs⟩
    · subst h1
      simp
    · have hne : l.val ≠ s := fun h => h1 (Fin.ext h)
      have hiff : (l.val < s + 1 ∧ f l) ↔ (l.val < s ∧ f l) :=
        ⟨fun ⟨a, b⟩ => ⟨by omega, b⟩, fun ⟨a, b⟩ => ⟨by omega, b⟩⟩
      simp only [hiff, h1, if_false, add_zero]
  rw [Finset.sum_congr rfl (fun l _ => key l), Finset.sum_add_distrib]
  simp

theorem strip_le_add {nu mu : Fin n → ℤ} {b : ℕ} (h : HStrip nu mu b) (m : Fin n) : mu m ≤ nu m + b := by
  have h1 : mu m - nu m ≤ ∑ a, (mu a - nu a) :=
    Finset.single_le_sum (f := fun a => mu a - nu a) (fun a _ => sub_nonneg.mpr (h.1 a)) (Finset.mem_univ m)
  rw [h.2.2] at h1
  linarith

theorem mu_le_dplus (P : PPath n N LL dd) :
    ∀ (s : ℕ) (hs : s < N + 1) (m : Fin n), P.mu ⟨s, hs⟩ m ≤ (dplus LL dd s : ℤ) := by
  intro s
  induction s with
  | zero =>
    intro hs m
    have h0 : (⟨0, hs⟩ : Fin (N + 1)) = 0 := Fin.ext (by simp)
    rw [h0, P.zero]
    simp
  | succ s ih =>
    intro hs m
    have hsN : s < N := by omega
    have hd : (∑ l : Fin N, if l.val < s + 1 ∧ LL.vec l = true then dd l else 0) =
        (∑ l : Fin N, if l.val < s ∧ LL.vec l = true then dd l else 0) +
          if LL.vec ⟨s, hsN⟩ = true then dd ⟨s, hsN⟩ else 0 :=
      dsum_succ (fun l : Fin N => LL.vec l = true) dd s hsN
    have h1 := ih (by omega) m
    cases hv : LL.vec ⟨s, hsN⟩
    · have hstr : HStrip (P.mu ⟨s + 1, hs⟩) (P.mu ⟨s, by omega⟩) (dd ⟨s, hsN⟩) := step_cov P ⟨s, hsN⟩ hv
      have h2 : dplus LL dd (s + 1) = dplus LL dd s := by
        unfold dplus
        rw [hd, hv]
        simp
      rw [h2]
      exact (hstr.1 m).trans h1
    · have hstr : HStrip (P.mu ⟨s, by omega⟩) (P.mu ⟨s + 1, hs⟩) (dd ⟨s, hsN⟩) := step_vec P ⟨s, hsN⟩ hv
      have h2 : dplus LL dd (s + 1) = dplus LL dd s + dd ⟨s, hsN⟩ := by
        unfold dplus
        rw [hd, hv]
        simp
      have h3 := strip_le_add hstr m
      rw [h2]
      push_cast
      linarith

theorem neg_dminus_le_mu (P : PPath n N LL dd) :
    ∀ (s : ℕ) (hs : s < N + 1) (m : Fin n), -(dminus LL dd s : ℤ) ≤ P.mu ⟨s, hs⟩ m := by
  intro s
  induction s with
  | zero =>
    intro hs m
    have h0 : (⟨0, hs⟩ : Fin (N + 1)) = 0 := Fin.ext (by simp)
    rw [h0, P.zero]
    simp
  | succ s ih =>
    intro hs m
    have hsN : s < N := by omega
    have hd : (∑ l : Fin N, if l.val < s + 1 ∧ LL.vec l = false then dd l else 0) =
        (∑ l : Fin N, if l.val < s ∧ LL.vec l = false then dd l else 0) +
          if LL.vec ⟨s, hsN⟩ = false then dd ⟨s, hsN⟩ else 0 :=
      dsum_succ (fun l : Fin N => LL.vec l = false) dd s hsN
    have h1 := ih (by omega) m
    cases hv : LL.vec ⟨s, hsN⟩
    · have hstr : HStrip (P.mu ⟨s + 1, hs⟩) (P.mu ⟨s, by omega⟩) (dd ⟨s, hsN⟩) := step_cov P ⟨s, hsN⟩ hv
      have h2 : dminus LL dd (s + 1) = dminus LL dd s + dd ⟨s, hsN⟩ := by
        unfold dminus
        rw [hd, hv]
        simp
      have h3 := strip_le_add hstr m
      rw [h2]
      push_cast
      linarith
    · have hstr : HStrip (P.mu ⟨s, by omega⟩) (P.mu ⟨s + 1, hs⟩) (dd ⟨s, hsN⟩) := step_vec P ⟨s, hsN⟩ hv
      have h2 : dminus LL dd (s + 1) = dminus LL dd s := by
        unfold dminus
        rw [hd, hv]
        simp
      rw [h2]
      exact h1.trans (hstr.1 m)

def vcount (LL : Letters (Fin N)) (t s : ℕ) : ℕ :=
  (Finset.univ.filter fun l : Fin N => t ≤ l.val ∧ l.val < s ∧ LL.vec l = true).card

theorem vcount_self (LL : Letters (Fin N)) (t : ℕ) : vcount LL t t = 0 := by
  unfold vcount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro l _ h
  obtain ⟨h1, h2, -⟩ := h
  omega

theorem vcount_succ (LL : Letters (Fin N)) (t s : ℕ) (hts : t ≤ s) (hs : s < N) :
    vcount LL t (s + 1) = vcount LL t s + if LL.vec ⟨s, hs⟩ = true then 1 else 0 := by
  unfold vcount
  by_cases hv : LL.vec ⟨s, hs⟩ = true
  · rw [if_pos hv]
    have hset : (Finset.univ.filter fun l : Fin N => t ≤ l.val ∧ l.val < s + 1 ∧ LL.vec l = true) =
        insert ⟨s, hs⟩ (Finset.univ.filter fun l : Fin N => t ≤ l.val ∧ l.val < s ∧ LL.vec l = true) := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · rintro ⟨h1, h2, h3⟩
        by_cases hl : l.val = s
        · left
          exact Fin.ext hl
        · right
          exact ⟨h1, by omega, h3⟩
      · rintro (rfl | ⟨h1, h2, h3⟩)
        · exact ⟨hts, Nat.lt_succ_self s, hv⟩
        · exact ⟨h1, by omega, h3⟩
    rw [hset, Finset.card_insert_of_notMem]
    simp
  · rw [if_neg hv, add_zero]
    congr 1
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, ?_, h3⟩
      by_contra hc
      have hl : l = ⟨s, hs⟩ := Fin.ext (show l.val = s by omega)
      subst hl
      exact hv h3
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, by omega, h3⟩

theorem row_back (P : PPath n N LL dd) (t : ℕ) :
    ∀ (s : ℕ) (_hts : t ≤ s) (hs : s < N + 1) (m m' : Fin n), m'.val = m.val + vcount LL t s →
      P.mu ⟨s, hs⟩ m' ≤ P.mu ⟨t, by omega⟩ m := by
  intro s hts
  induction s, hts using Nat.le_induction with
  | base =>
    intro hs m m' hm
    rw [vcount_self, add_zero] at hm
    have he : m' = m := Fin.ext hm
    subst he
    exact le_refl _
  | succ s hts ih =>
    intro hs m m' hm
    have hsN : s < N := by omega
    rw [vcount_succ LL t s hts hsN] at hm
    cases hv : LL.vec ⟨s, hsN⟩
    · rw [hv] at hm
      simp only [Bool.false_eq_true, if_false, add_zero] at hm
      have hstr : HStrip (P.mu ⟨s + 1, hs⟩) (P.mu ⟨s, by omega⟩) (dd ⟨s, hsN⟩) := step_cov P ⟨s, hsN⟩ hv
      exact (hstr.1 m').trans (ih (by omega) m m' hm)
    · rw [hv] at hm
      simp only [if_true] at hm
      have hstr : HStrip (P.mu ⟨s, by omega⟩) (P.mu ⟨s + 1, hs⟩) (dd ⟨s, hsN⟩) := step_vec P ⟨s, hsN⟩ hv
      have hlt := m'.isLt
      have ha : m.val + vcount LL t s < n := by omega
      have he : m' = ⟨m.val + vcount LL t s + 1, by omega⟩ := Fin.ext hm
      rw [he]
      exact (hstr.2.1 ⟨m.val + vcount LL t s, ha⟩ (by simp only; omega)).trans
        (ih (by omega) m ⟨m.val + vcount LL t s, ha⟩ rfl)

end Formalism.MainNotions.SelectionLemmas.Pf.T
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.RestLamOfRests
section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

namespace Dat

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)

def lamG : Fin X.F.J → ℤ × Fin (r + K) → Fin n' × Fin (r + K) := fun _ v => (posOf n' v.1, v.2)

def lamE : Fin X.F.J → ℤ × Fin (r + K) → ℕ := fun j v => p ^ (X.F.dist (j.val : ℤ) v.1 + X.Rj p K (j.val : ℤ))


omit [NeZero n'] in
def lamL (la : Fin n' → Fin (r + K) → ℕ) : Fin n' × Fin (r + K) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => la v.1 v.2

def lamS (la : Fin n' → Fin (r + K) → ℕ) (e : Fin X.F.J → Fin r → ℕ) (j : Fin X.F.J) :
    Set (ℤ × Fin (r + K) →₀ ℕ) :=
  {m | (∀ v, m v ≠ 0 → v ∈ okVars X.F K (j.val : ℤ)) ∧
    m ∈ segDegSet (r := r) K (X.bfam p K la e (j.val : ℤ)) ∧ m ∈ X.resSet p K (j.val : ℤ)}

end Dat

def RestLamA : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → ∀ (j : ℤ) (b : ℤ → ℕ),
    (∀ x, x ∉ X.F.letters j → b x = 0) →
    ∃ y : Fin (Module.finrank O (X.Mj p K O j b)) → SegRing O r K, (∀ i, y i ∈ X.Mj p K O j b) ∧
      LinearIndependent (FF O) fun i => MvPolynomial.map (IsLocalRing.residue O) (y i)

def RestLamInj (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ la ∈ X.LA p K, ∀ e ∈ X.EE p K la, ∀ la' ∈ X.LA p K, ∀ e' ∈ X.EE p K la',
    ∀ m m' : Fin X.F.J → (ℤ × Fin (r + K) →₀ ℕ), (∀ j, m j ∈ X.lamS p K la e j) → (∀ j, m' j ∈ X.lamS p K la' e' j) →
      Dat.lamL K la + ∑ j, imgMon (X.lamG K j) (X.lamE p K j) (m j) =
        Dat.lamL K la' + ∑ j, imgMon (X.lamG K j) (X.lamE p K j) (m' j) → (la = la' ∧ e = e') ∧ m = m'

def RestLamDeg (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ la ∈ X.LA p K, ∀ e ∈ X.EE p K la, X.IsCLabel p K (Dat.lamL K la) ∧
    ∀ m : Fin X.F.J → (ℤ × Fin (r + K) →₀ ℕ), (∀ j, m j ∈ X.lamS p K la e j) →
      ∀ t, ∑ c : Fin (r + K), (Dat.lamL K la + ∑ j, imgMon (X.lamG K j) (X.lamE p K j) (m j)) (t, c) = X.a' p K t

theorem lam_map_phc {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n' r : ℕ} [NeZero n'] (X : Dat n' r)
    (p K : ℕ) (j : Fin X.F.J) (P : SegRing R r K) :
    MvPolynomial.map f (X.phc p K R (j.val : ℤ) P) = lam_ph (X.lamG K) (X.lamE p K) j (MvPolynomial.map f P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [Dat.phc, lam_ph]
  | add u v hu hv => simp only [map_add (f := _), hu, hv]
  | mul_X q v h =>
    simp only [map_mul, h, map_X]
    simp [Dat.phc, lam_ph, Dat.lamG, Dat.lamE]

theorem lam_mem_lamS {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (p K : ℕ) [NeZero K] (O : Type) [CommRing O]
    (la : Fin n' → Fin (r + K) → ℕ) (e : Fin X.F.J → Fin r → ℕ) (j : Fin X.F.J) {y : SegRing O r K}
    (hy : y ∈ X.Mj p K O (j.val : ℤ) (X.bfam p K la e (j.val : ℤ))) : y ∈ restrictSupport O (X.lamS p K la e j) := by
  classical
  obtain ⟨⟨h1, h2⟩, h3⟩ := hy
  have hs := XX'_supported O X.F (j.val : ℤ) _ _ _ h1
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro m hm
  have hm' : m ∈ y.support := Finset.mem_coe.mp hm
  refine ⟨fun v hv => ?_, (MvPolynomial.mem_restrictSupport_iff (R := O)).mp h2 hm,
    (MvPolynomial.mem_restrictSupport_iff (R := O)).mp h3 hm⟩
  have hvars : v ∈ y.vars := by
    rw [MvPolynomial.mem_vars_iff_mem_support]
    exact ⟨m, hm', Finsupp.mem_support_iff.mpr hv⟩
  exact (MvPolynomial.mem_supported.mp hs) (Finset.mem_coe.mpr hvars)

theorem restLam_of_rests (C₀ : ℝ) (hA : RestLamA) (hI : RestLamInj C₀) (hD : RestLamDeg C₀) : RestLam C₀ := by
  intro p n' r K _ _ _ X O _ _ _ Sd hX hLa hk
  classical
  let SS := (X.LA p K).sigma fun la => X.EE p K la
  let Φ := {x // x ∈ SS}
  have hΦ : ∀ f : Φ, f.1.1 ∈ X.LA p K ∧ f.1.2 ∈ X.EE p K f.1.1 := fun f => Finset.mem_sigma.mp f.2
  let nn : Φ → Fin X.F.J → ℕ := fun f j =>
    Module.finrank O (X.Mj p K O (j.val : ℤ) (X.bfam p K f.1.1 f.1.2 (j.val : ℤ)))
  have hex := fun (f : Φ) (j : Fin X.F.J) => hA p n' r K X O Sd hX (j.val : ℤ) (X.bfam p K f.1.1 f.1.2 (j.val : ℤ))
    (fun x hx => by simp [Dat.bfam, hx])
  choose y hyM hyL using hex
  set res := MvPolynomial.map (σ := ℤ × Fin (r + K)) (IsLocalRing.residue O) with hres
  have hli := lam_li_all (F := FF O) (X.lamG K) (X.lamE p K) (fun f : Φ => Dat.lamL K f.1.1)
    (fun f j => X.lamS p K f.1.1 f.1.2 j) (fun f j => Fin (nn f j)) (fun f j i => res (y f j i))
    (fun f j => hyL f j)
    (fun f j i => map_mem_restrictSupport _ _ (lam_mem_lamS X p K O f.1.1 f.1.2 j (hyM f j i)))
    (by
      intro f f' m m' hm hm' h
      obtain ⟨⟨h1, h2⟩, h3⟩ := hI p n' r K X hX hLa hk f.1.1 (hΦ f).1 f.1.2 (hΦ f).2 f'.1.1 (hΦ f').1 f'.1.2 (hΦ f').2
        m m' hm hm' h
      refine ⟨Subtype.ext ?_, h3⟩
      obtain ⟨⟨la, e⟩, hf⟩ := f
      obtain ⟨⟨la', e'⟩, hf'⟩ := f'
      simp only at h1 h2
      subst h1
      subst h2
      rfl)

  have hmem : ∀ x : (Σ f : Φ, ∀ j, Fin (nn f j)),
      monomial (Dat.lamL K x.1.1.1) (1 : FF O) * ∏ j, lam_ph (X.lamG K) (X.lamE p K) j (res (y x.1 j (x.2 j))) ∈
        X.LamBar p K O := by
    rintro ⟨f, a⟩
    let Yf : Fin X.F.J → SegRing O r K := fun i => y f i (a i)
    let y' : ℤ → SegRing O r K := fun j => if h : 0 ≤ j ∧ j.toNat < X.F.J then Yf ⟨j.toNat, h.2⟩ else 0
    have hy'i : ∀ i : Fin X.F.J, y' (i.val : ℤ) = Yf i := by
      intro i
      have h : 0 ≤ (i.val : ℤ) ∧ ((i.val : ℤ)).toNat < X.F.J := ⟨by positivity, by simpa using i.isLt⟩
      simp only [y', dif_pos h]
      exact congrArg Yf (Fin.ext (by simp))
    obtain ⟨hlab, hdeg⟩ := hD p n' r K X hX hLa hk f.1.1 (hΦ f).1 f.1.2 (hΦ f).2
    have hprod : (∏ j ∈ Finset.range X.F.J, X.phc p K O (j : ℤ) (y' j)) =
        ∏ j : Fin X.F.J, lam_ph (R := O) (X.lamG K) (X.lamE p K) j (Yf j) := by
      rw [Finset.prod_range]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hy'i]
      rfl
    refine Submodule.subset_span ⟨(∏ j ∈ Finset.range X.F.J, X.phc p K O (j : ℤ) (y' j)) *
      monomial (Dat.lamL K f.1.1) 1, ⟨fun j => X.bfam p K f.1.1 f.1.2 j, y', Dat.lamL K f.1.1, ?_, hlab, rfl, ?_⟩, ?_⟩
    · intro j
      by_cases h : 0 ≤ j ∧ j.toNat < X.F.J
      · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h.1
        have hk' : k < X.F.J := by simpa using h.2
        have := hy'i ⟨k, hk'⟩
        simp only at this
        rw [this]
        exact hyM f ⟨k, hk'⟩ (a ⟨k, hk'⟩)
      · simp only [y', dif_neg h]
        exact Submodule.zero_mem _
    · rw [hprod, lam_expand]
      unfold RRdeg
      rw [MvPolynomial.mem_restrictSupport_iff]
      intro n hn
      have hn' := MvPolynomial.mem_support_iff.mp (Finset.mem_coe.mp hn)
      rw [mul_comm, coeff_monomial_mul'] at hn'
      split_ifs at hn' with hle
      · rw [one_mul, coeff_sum] at hn'
        obtain ⟨m, hm, hm0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn'
        rw [coeff_monomial] at hm0
        split_ifs at hm0 with heq
        · have hn2 : n = Dat.lamL K f.1.1 + ∑ j, imgMon (X.lamG K j) (X.lamE p K j) (m j) := by
            rw [heq]; exact (add_tsub_cancel_of_le hle).symm
          intro t
          rw [hn2]
          refine hdeg m (fun j => ?_) t
          exact (MvPolynomial.mem_restrictSupport_iff (R := O)).mp
            (lam_mem_lamS X p K O f.1.1 f.1.2 j (hyM f j (a j))) (Finset.mem_coe.mpr (Fintype.mem_piFinset.mp hm j))
        · exact absurd rfl hm0
      · exact absurd rfl hn'
    · rw [map_mul, map_monomial, map_one, mul_comm, Finset.prod_range, map_prod]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [lam_map_phc, hy'i]
  have hfin : Module.Finite (FF O) (X.LamBar p K O) := by
    have := finite_restrictSupport (FF O) _ _ (degSet_finite n' (r + K) (X.a' p K))
    refine Submodule.finiteDimensional_of_le
      (S₂ := restrictSupport (FF O) {m : Fin n' × Fin (r + K) →₀ ℕ | ∀ t, ∑ c : Fin (r + K), m (t, c) = X.a' p K t}) ?_
    unfold Dat.LamBar
    rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨_, _, _, -, -, -, h⟩ := hg
    exact map_mem_restrictSupport _ _ h
  have hli' : LinearIndependent (FF O) (fun x : (Σ f : Φ, ∀ j, Fin (nn f j)) =>
      (⟨_, hmem x⟩ : X.LamBar p K O)) := by
    refine LinearIndependent.of_comp (X.LamBar p K O).subtype ?_
    exact hli
  have hcard := hli'.fintype_card_le_finrank
  refine le_trans (le_of_eq ?_) hcard
  rw [Fintype.card_sigma]
  simp only [Fintype.card_pi, Fintype.card_fin]
  rw [← Finset.sum_sigma (X.LA p K) (fun la => X.EE p K la)
    (fun x => ∏ j : Fin X.F.J, Module.finrank O (X.Mj p K O (j.val : ℤ) (X.bfam p K x.1 x.2 (j.val : ℤ))))]
  exact (Finset.sum_coe_sort SS
    (fun x => ∏ j : Fin X.F.J, Module.finrank O (X.Mj p K O (j.val : ℤ) (X.bfam p K x.1 x.2 (j.val : ℤ))))).symm

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

