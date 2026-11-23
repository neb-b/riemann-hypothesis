module

public import Mathlib
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0007
public import Formalism.RealPlaceAnalysis.Bundle0003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.WhittakerZeroStatement

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeBackwardStable
section
noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgHeckeBack

open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (tensVd eeVd)
open CompanionTheory.RgExh CompanionTheory.RgExh.Hk

variable {n : ℕ}

theorem tensVd_apply (X : GMod n) (a b : Fin n) (f : Fin n → X.V) (i : Fin n) :
    tensVd X.E a b f i = X.E a b (f i) - if i = b then f a else 0 := by
  by_cases h : i = b <;> simp [tensVd, h]

theorem eeVd_apply (X : GMod n) (f : Fin n → X.V) (a : Fin n) :
    eeVd X.E f a = -∑ c, X.E a c (f c) := by
  simp [eeVd]

theorem commute_tensVd_eeVd (X : GMod n) (c d : Fin n) : Commute (tensVd X.E c d) (eeVd X.E) := by
  refine LinearMap.ext fun f => funext fun a => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Module.End.mul_apply, tensVd_apply, eeVd_apply, map_neg, map_sum, map_sub]
  simp only [comm_apply X c d a _ _, sum_sub_distrib, sum_add_distrib, apply_ite (X.E a _), map_zero]
  by_cases h : a = d
  · subst h
    simp
    abel
  · simp [h, Ne.symm h]

theorem backStable : BackStable := fun _ X z a b _ hx =>
  Module.End.mapsTo_maxGenEigenspace_of_comm (commute_tensVd_eeVd X a b).symm (-z - cn _) hx

end GlobalTheory.CompanionTheory.RgHeckeBack
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeNonVanishing
section
noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgExhHecke.NonVanProof

open CompanionTheory.RgExh CompanionTheory.RgExh.Hk
open Formalism.REAL (GlRel qdet)
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (cminor capelliC capEntry nnPlus eeV capelliAPlus capelliExpand)

theorem eeV_eq_om {n : ℕ} (X : GMod n) : eeV X.E = om X := by
  refine LinearMap.ext fun u => funext fun b => ?_
  simp [eeV, om_apply]

theorem exists_ker {M : Type} [AddCommGroup M] [Module ℂ M] [Nontrivial M] (T : Module.End ℂ M) {k : ℕ}
    (h : T ^ k = 0) : ∃ v : M, v ≠ 0 ∧ T v = 0 := by
  obtain ⟨w, hw⟩ := exists_ne (0 : M)
  have hex : ∃ j : ℕ, (T ^ j) w = 0 := ⟨k, by simp [h]⟩
  classical
  have hj := Nat.find_spec hex
  have hmin := fun i => Nat.find_min hex (m := i)
  set j := Nat.find hex with hjdef
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · rw [h0] at hj
    exact absurd (by simpa using hj) hw
  · refine ⟨(T ^ (j - 1)) w, hmin _ (by omega), ?_⟩
    rw [← Module.End.mul_apply, ← pow_succ', Nat.sub_add_cancel hpos]
    exact hj

theorem eq_zero_of_nilp {M : Type} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) {c : ℂ} {k : ℕ}
    (hc : c ≠ 0) (h : (T - c • (1 : Module.End ℂ M)) ^ k = 0) {v : M} (hv : T v = 0) : v = 0 := by
  have key : ∀ j : ℕ, ((T - c • (1 : Module.End ℂ M)) ^ j) v = (-c) ^ j • v := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, Module.End.mul_apply]
      have : (T - c • (1 : Module.End ℂ M)) v = (-c) • v := by simp [hv]
      rw [this, map_smul, ih, smul_smul, pow_succ, mul_comm]
  have := key k
  rw [h] at this
  have h2 : (-c) ^ k • v = 0 := by simpa using this.symm
  exact (smul_eq_zero.mp h2).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr hc))

theorem exists_nnPlus_ne {m : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
    (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ M) (hE : GlRel E) (w : ℂ) {v : M} (hv0 : v ≠ 0)
    (hinj : capelliC E (w - 1) v = 0 → v = 0) :
    ∃ y : Fin (m + 1) → ℂ, nnPlus E y w v ≠ 0 := by
  by_contra hall
  push_neg at hall
  have hmin : ∀ d c : Fin (m + 1), cminor E d.succAbove c.succAbove (w - 1) v = 0 := by
    intro d c
    have h := congrFun (hall (Pi.single c 1)) d
    simp only [nnPlus, Pi.zero_apply] at h
    rw [Finset.sum_eq_single c (fun b _ hb => by simp [Pi.single_eq_of_ne hb])
      (fun hc => absurd (Finset.mem_univ c) hc)] at h
    simpa [pow_ne_zero] using h
  have hexp := (capelliExpand (𝒰 := Module.End ℂ M) m E (w - 1) hE).2 0 0
  have happ := LinearMap.congr_fun hexp v
  simp only [if_true, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply, hmin, map_zero,
    smul_zero, Finset.sum_const_zero] at happ
  exact hv0 (hinj happ.symm)

theorem nonVan : NonVan := by
  intro n X χ s hX hnt hfree
  have hQ := GlobalTheory.CompanionTheory.RgExhHecke.qdetEq
  obtain ⟨k, hk⟩ := hX
  haveI := hnt
  cases n with
  | zero => exact s.elim0
  | succ m =>
    set w : ℂ := (((m + 1 : ℕ) : ℂ) - 1) / 2 - χ s with hw

    have h1 := hk (-χ s)
    have hcap0 : Formalism.QuantumDeterminants.capP χ (-χ s) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ s) (by simp)
    rw [hcap0, zero_smul, sub_zero] at h1
    obtain ⟨v, hv0, hv⟩ := exists_ker _ h1
    have hCw : capelliC X.E w v = 0 := by
      rw [← hQ]
      rw [show w = -χ s + (((m + 1 : ℕ) : ℂ) - 1) / 2 by rw [hw]; ring]
      exact hv

    have h2 := hk (-χ s - 1)
    have hc : Formalism.QuantumDeterminants.capP χ (-χ s - 1) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun t _ h => hfree t ?_
      linear_combination h
    have hinj : capelliC X.E (w - 1) v = 0 → v = 0 := by
      intro h
      rw [← hQ] at h
      rw [show w - 1 = -χ s - 1 + (((m + 1 : ℕ) : ℂ) - 1) / 2 by rw [hw]; ring] at h
      exact eq_zero_of_nilp _ hc h2 h
    obtain ⟨y, hy⟩ := exists_nnPlus_ne X.E X.gl w hv0 hinj
    have hev := capelliAPlus X.V m X.E y w v X.gl hCw
    rw [eeV_eq_om] at hev
    intro hbot
    apply hy
    have hmem : nnPlus X.E y w v ∈ stepSub X (χ s) := by
      unfold stepSub
      refine Module.End.mem_maxGenEigenspace _ _ _ |>.mpr ⟨1, ?_⟩
      rw [pow_one, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hev]
      rw [hw, ← sub_smul]
      have : -((((m + 1 : ℕ) : ℂ) - 1) / 2 - χ s) - (χ s - (((m + 1 : ℕ) : ℂ) - 1) / 2) = 0 := by ring
      rw [this, zero_smul]
    rw [hbot] at hmem
    simpa using hmem

end GlobalTheory.CompanionTheory.RgExhHecke.NonVanProof
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeRankOne
section
open Finset Formalism.REAL ReciprocityTheory.ChartRestriction.DS.Lap.Capelli CompanionTheory.RgExh

namespace GlobalTheory.CompanionTheory.RgExhHecke

variable {n : ℕ}

theorem capEntry_tensE_apply (X : GMod n) (x : ℂ) (a b : Fin n) (f : Fin n → X.V) (d : Fin n) :
    capEntry (tensE X) x a b f d = capEntry X.E x a b (f d) + if d = a then f b else 0 := by
  unfold capEntry
  by_cases h : a = b
  · simp [h, tensE_apply, Module.algebraMap_end_apply]; abel
  · simp [h, tensE_apply]

theorem capEntry_apply_shift {V : Type} [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (x : ℂ) (a b : Fin n) (v : V) :
    capEntry E x a b v = capEntry E (x - 1) a b v + if b = a then v else 0 := by
  unfold capEntry
  by_cases h : a = b
  · subst h
    simp [Module.algebraMap_end_apply, sub_smul, add_assoc]
  · simp [h, Ne.symm h]

theorem sum_pair_swap {M : Type*} [AddCommMonoid M] {q : ℕ} (Φ : Fin (q + 2) → Fin (q + 1) → M) :
    ∑ i, ∑ k, Φ i k = ∑ i : Fin (q + 2), ∑ k : Fin (q + 1), Φ (i.succAbove k) (k.predAbove i) := by
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  let τ : Equiv.Perm (Fin (q + 2) × Fin (q + 1)) :=
    Function.Involutive.toPerm (fun p => (p.1.succAbove p.2, p.2.predAbove p.1)) (by
      rintro ⟨i, k⟩
      simp only [Fin.succAbove_succAbove_predAbove, Fin.predAbove_predAbove_succAbove])
  exact (Equiv.sum_comp τ (fun p => Φ p.1 p.2)).symm

theorem sign_pair_swap {q : ℕ} (i : Fin (q + 2)) (k : Fin (q + 1)) :
    (-1 : ℂ) ^ (i.succAbove k : ℕ) * (-1) ^ (k.predAbove i : ℕ) = -((-1) ^ (i : ℕ) * (-1) ^ (k : ℕ)) := by
  have h : (i.succAbove k : ℕ) + (k.predAbove i : ℕ) + 1 = (i : ℕ) + (k : ℕ) ∨
      (i.succAbove k : ℕ) + (k.predAbove i : ℕ) = (i : ℕ) + (k : ℕ) + 1 := by
    simp only [Fin.succAbove, Fin.predAbove, Fin.lt_def, Fin.val_castSucc, apply_dite Fin.val, Fin.val_pred,
      Fin.coe_castPred, dite_eq_ite, apply_ite Fin.val, Fin.val_succ]
    split_ifs <;> omega
  rw [← pow_add, ← pow_add]
  rcases h with h | h
  · rw [← h, pow_succ]; ring
  · rw [h, pow_succ]; ring

theorem cminor_zero {V : Type} [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (R C : Fin 0 → Fin n) (x : ℂ) : cminor E R C x = 1 := by
  simp [cminor]

section Key

variable {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) {q : ℕ}
  (R C : Fin (q + 2) → Fin n) (x : ℂ) (f : Fin n → V) (d : Fin n)

def dbl (i : Fin (q + 2)) (k : Fin (q + 1)) (l : Fin (q + 1)) : V :=
  cminor E ((R ∘ i.succAbove) ∘ k.succAbove) ((C ∘ Fin.succ) ∘ l.succAbove) (x - 1 - 1) (f (C l.succ))

theorem dbl_swap (i : Fin (q + 2)) (k l : Fin (q + 1)) :
    dbl E R C x f (i.succAbove k) (k.predAbove i) l = dbl E R C x f i k l := by
  unfold dbl
  have : (R ∘ (i.succAbove k).succAbove) ∘ (k.predAbove i).succAbove = (R ∘ i.succAbove) ∘ k.succAbove := by
    funext t
    simp only [Function.comp, Fin.succAbove_succAbove_succAbove_predAbove]
  rw [this]

theorem minor_expand (i : Fin (q + 2)) (l : Fin (q + 1)) :
    cminor E (R ∘ i.succAbove) (C ∘ l.succ.succAbove) (x - 1) (f (C l.succ)) =
      ∑ k : Fin (q + 1), ((-1 : ℂ) ^ (k : ℕ)) •
        capEntry E (x - 1) (R (i.succAbove k)) (C 0) (dbl E R C x f i k l) := by
  rw [cminor_succ_col]
  have h0 : (C ∘ l.succ.succAbove) 0 = C 0 := by simp
  have h1 : (C ∘ l.succ.succAbove) ∘ Fin.succ = (C ∘ Fin.succ) ∘ l.succAbove := by
    funext t
    simp [Function.comp, Fin.succ_succAbove_succ]
  rw [h0, h1]
  simp [dbl, LinearMap.sum_apply, Module.End.mul_apply]

theorem key_identity :
    (∑ i : Fin (q + 2), ((-1 : ℂ) ^ (i : ℕ)) • capEntry E x (R i) (C 0)
        (∑ k : Fin (q + 1), ∑ l : Fin (q + 1), if d = (R ∘ i.succAbove) k then
          ((-1 : ℂ) ^ ((k : ℕ) + (l : ℕ))) • dbl E R C x f i k l else 0)) +
      (∑ i : Fin (q + 2), ((-1 : ℂ) ^ (i : ℕ)) • (if d = R i then
        (∑ k : Fin (q + 1), ∑ l : Fin (q + 1), if C 0 = (R ∘ i.succAbove) k then
          ((-1 : ℂ) ^ ((k : ℕ) + (l : ℕ))) • dbl E R C x f i k l else 0) else 0)) =
    ∑ i : Fin (q + 2), ∑ l : Fin (q + 1), if d = R i then
      ((-1 : ℂ) ^ ((i : ℕ) + ((l.succ : Fin (q + 2)) : ℕ))) •
        cminor E (R ∘ i.succAbove) (C ∘ l.succ.succAbove) (x - 1) (f (C l.succ)) else 0 := by
  have h1 : (∑ i : Fin (q + 2), ((-1 : ℂ) ^ (i : ℕ)) • capEntry E x (R i) (C 0)
        (∑ k : Fin (q + 1), ∑ l : Fin (q + 1), if d = (R ∘ i.succAbove) k then
          ((-1 : ℂ) ^ ((k : ℕ) + (l : ℕ))) • dbl E R C x f i k l else 0)) =
      ∑ i : Fin (q + 2), ∑ k : Fin (q + 1), ∑ l : Fin (q + 1), ((-1 : ℂ) ^ (i : ℕ)) •
        capEntry E x (R i) (C 0) (if d = R (i.succAbove k) then
          ((-1 : ℂ) ^ ((k : ℕ) + (l : ℕ))) • dbl E R C x f i k l else 0) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Finset.smul_sum, Function.comp]
  have h2 : (∑ i : Fin (q + 2), ((-1 : ℂ) ^ (i : ℕ)) • (if d = R i then
        (∑ k : Fin (q + 1), ∑ l : Fin (q + 1), if C 0 = (R ∘ i.succAbove) k then
          ((-1 : ℂ) ^ ((k : ℕ) + (l : ℕ))) • dbl E R C x f i k l else 0) else 0)) =
      ∑ i : Fin (q + 2), ∑ k : Fin (q + 1), ∑ l : Fin (q + 1), ((-1 : ℂ) ^ (i : ℕ)) •
        (if d = R i then (if C 0 = R (i.succAbove k) then
          ((-1 : ℂ) ^ ((k : ℕ) + (l : ℕ))) • dbl E R C x f i k l else 0) else 0) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : d = R i <;> simp [h, Finset.smul_sum]
  have h3 : (∑ i : Fin (q + 2), ∑ l : Fin (q + 1), if d = R i then
      ((-1 : ℂ) ^ ((i : ℕ) + ((l.succ : Fin (q + 2)) : ℕ))) •
        cminor E (R ∘ i.succAbove) (C ∘ l.succ.succAbove) (x - 1) (f (C l.succ)) else 0) =
      ∑ i : Fin (q + 2), ∑ k : Fin (q + 1), ∑ l : Fin (q + 1), if d = R i then
        ((-1 : ℂ) ^ ((i : ℕ) + ((l.succ : Fin (q + 2)) : ℕ))) • ((-1 : ℂ) ^ (k : ℕ)) •
          capEntry E (x - 1) (R (i.succAbove k)) (C 0) (dbl E R C x f i k l) else 0 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases h : d = R i
    · simp only [h, if_true, minor_expand, Finset.smul_sum]
    · simp [h]
  rw [h1, h2, h3, sum_pair_swap, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Fin.succAbove_succAbove_predAbove, dbl_swap]
  have hs : (-1 : ℂ) ^ (i.succAbove k : ℕ) * (-1) ^ (((k.predAbove i : Fin (q + 1)) : ℕ) + (l : ℕ)) =
      -((-1) ^ (i : ℕ) * (-1) ^ ((k : ℕ) + (l : ℕ))) := by
    rw [pow_add, ← mul_assoc, sign_pair_swap, pow_add]; ring
  by_cases hd : d = R i
  · simp only [hd, if_true, map_smul, smul_smul, hs]
    rw [capEntry_apply_shift E x (R (i.succAbove k)) (C 0)]
    by_cases hc : C 0 = R (i.succAbove k)
    · simp only [hc, if_true, smul_add, Fin.val_succ, pow_add, pow_one]
      module
    · simp only [hc, if_false, add_zero, smul_zero, Fin.val_succ, pow_add, pow_one]
      module
  · simp [hd]

end Key

theorem cminor_tensE_apply (X : GMod n) (q : ℕ) : ∀ (R C : Fin (q + 1) → Fin n) (x : ℂ)
    (f : Fin n → X.V) (d : Fin n),
    cminor (tensE X) R C x f d = cminor X.E R C x (f d) +
      ∑ i : Fin (q + 1), ∑ j : Fin (q + 1), if d = R i then
        ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) •
          cminor X.E (R ∘ i.succAbove) (C ∘ j.succAbove) (x - 1) (f (C j)) else 0 := by
  induction q with
  | zero =>
    intro R C x f d
    rw [cminor_succ_col, cminor_succ_col X.E]
    simp [cminor_zero, capEntry_tensE_apply, Module.End.mul_apply, LinearMap.sum_apply]
  | succ q ih =>
    intro R C x f d
    have hL : cminor (tensE X) R C x f d =
        ∑ i : Fin (q + 2), ((-1 : ℂ) ^ (i : ℕ)) •
          (capEntry X.E x (R i) (C 0) (cminor (tensE X) (R ∘ i.succAbove) (C ∘ Fin.succ) (x - 1) f d) +
            if d = R i then cminor (tensE X) (R ∘ i.succAbove) (C ∘ Fin.succ) (x - 1) f (C 0) else 0) := by
      rw [cminor_succ_col]
      simp only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply,
        Module.End.mul_apply, capEntry_tensE_apply]
    have hR := key_identity X.E R C x f d
    have hsplit : ∀ i : Fin (q + 2), (∑ j : Fin (q + 2), if d = R i then
          ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) •
            cminor X.E (R ∘ i.succAbove) (C ∘ j.succAbove) (x - 1) (f (C j)) else 0) =
        ((-1 : ℂ) ^ (i : ℕ)) • (if d = R i then
          cminor X.E (R ∘ i.succAbove) (C ∘ Fin.succ) (x - 1) (f (C 0)) else 0) +
        ∑ l : Fin (q + 1), if d = R i then
          ((-1 : ℂ) ^ ((i : ℕ) + ((l.succ : Fin (q + 2)) : ℕ))) •
            cminor X.E (R ∘ i.succAbove) (C ∘ l.succ.succAbove) (x - 1) (f (C l.succ)) else 0 := by
      intro i
      rw [Fin.sum_univ_succ]
      by_cases h : d = R i
      · simp [h, Fin.succAbove_zero]
      · simp [h]
    rw [hL]
    simp only [hsplit, Finset.sum_add_distrib]
    rw [← hR, cminor_succ_col X.E R C x]
    have hit : ∀ (p : Prop) [Decidable p] (a b : X.V),
        (if p then a + b else 0) = (if p then a else 0) + (if p then b else 0) := by
      intro p _ a b
      split_ifs <;> simp
    simp only [ih, hit, map_add (f := _), smul_add, Finset.sum_add_distrib, LinearMap.sum_apply, LinearMap.smul_apply,
      Module.End.mul_apply]
    simp only [dbl, Function.comp_apply]
    abel

abbrev minorOp {m : ℕ} (X : GMod (m + 1)) (y : ℂ) : Module.End ℂ (Fin (m + 1) → X.V) :=
  Hk.minorOp X y

theorem minorOp_apply {m : ℕ} (X : GMod (m + 1)) (y : ℂ) (f : Fin (m + 1) → X.V) (a : Fin (m + 1)) :
    minorOp X y f a = ∑ c : Fin (m + 1), ((-1 : ℂ) ^ ((a : ℕ) + (c : ℕ))) • cminor X.E a.succAbove c.succAbove y (f c) :=
  rfl

theorem rankOneTens : ∀ (m : ℕ) (X : GMod (m + 1)) (u : ℂ),
    qdet (tensE X) u = (qdet X.E u).compLeft (Fin (m + 1)) + minorOp X (u - 1) := by
  intro m X u
  rw [qdet_eq_capelliC, qdet_eq_capelliC]
  refine LinearMap.ext fun f => funext fun d => ?_
  rw [capelliC, capelliC, cminor_tensE_apply X m id id u f d]
  simp only [LinearMap.add_apply, Pi.add_apply, minorOp_apply, LinearMap.compLeft_apply,
    Function.comp_apply, id_eq, Function.id_comp]
  simp

theorem rankOne : Hk.RankOne := rankOneTens

end GlobalTheory.CompanionTheory.RgExhHecke
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantEqualityStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.QuantumDeterminantEquality : CompanionTheory.RgExh.Hk.QdetEq := by
  first | exact @GlobalTheory.CompanionTheory.RgExhHecke.qdetEq | exact GlobalTheory.CompanionTheory.RgExhHecke.qdetEq | (intros; apply GlobalTheory.CompanionTheory.RgExhHecke.qdetEq <;> assumption)
end

