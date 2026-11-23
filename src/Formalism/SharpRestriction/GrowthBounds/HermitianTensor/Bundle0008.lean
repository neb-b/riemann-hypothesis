module

public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.NuOfLoZero
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.QaWeightRowInd
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0012
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.Bundle0005
public import Formalism.SharpRestriction.GrowthBounds.Bundle0005
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.Bundle0007
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.Bundle0002

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.ContractionOfPairingLemmas
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem contraction_of_pairing_lemmas (hPh : QPh) (hSC : SubCoeffP) (hSM : SubMapP) (hSR : SubRowP) (hLC : LamCoeffP) (hLE : LamEquivP)
    (hLM : LamMulP) (hLV : LamEvalP) (hMem : LamMemP) (hMu : SubMuP) (hTop : TopLineP) (hLift : LiftP) (hDD : DetDivP)
    (hIC : IntCapP) (hHw : HwMulP) : ContractionStandardLattice := by
  classical
  intro p n' R mm hmm a ccl P Q lam hlam h0 hl hmid h8
  have hfr := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  have := R.charZero
  have : Infinite R.Kf := inferInstance
  have hloA : Antitone (lam - wtPQ (mm + 1) P Q) := caLo_anti mm ccl P Q lam hlam h0 hl hmid
  have hlo'A : Antitone (dualWt (lam - wtPQ (mm + 1) P Q)) := qsDualWt_anti _ hloA
  have hαZ := nuOf_lam_mid mm ccl Q lam hl hmid
  have hβZ := nuOf_lo_mid mm ccl P Q lam h0 hl hmid
  have hβ'Z := nuOf_lo'_mid mm ccl P Q lam h0 hl hmid
  have hbd := lam_mid_bd mm ccl lam hmid
  have hαA : Antitone (fun j => nuOf lam (midI mm j)) := fun i j hij => nuOf_anti lam hlam (midI_mono mm hij)
  have hαN : ∀ i, (fun j => nuOf lam (midI mm j)) i ≤ Q + 2 * ccl := by
    intro i
    show nuOf lam (midI mm i) ≤ Q + 2 * ccl
    have := hαZ i; have := hbd i; omega
  have hαc : ∀ i j, (fun j => nuOf lam (midI mm j)) i ≤ (fun j => nuOf lam (midI mm j)) j + 2 * ccl := by
    intro i j
    show nuOf lam (midI mm i) ≤ nuOf lam (midI mm j) + 2 * ccl
    have := hαZ i; have := hαZ j; have := hbd i; have := hbd j; omega
  obtain ⟨L, hInv, hInt, nb, u, u', ka, hnb, hka, hu, hu', hdiag⟩ :=
    hPh p n' R mm hmm a (2 * ccl) (Q + 2 * ccl) (fun j => nuOf lam (midI mm j)) hαA hαN hαc h8
  have hα' : (fun i : Fin mm => Q + 2 * ccl - (fun j => nuOf lam (midI mm j)) i.rev) =
      fun j => nuOf (dualWt (lam - wtPQ (mm + 1) P Q)) (midI mm j) := by
    funext j
    show Q + 2 * ccl - nuOf lam (midI mm j.rev) = _
    have h1 := hβ'Z j; have h2 := hαZ j.rev; have h3 := hbd j.rev; omega
  rw [hα'] at hInv hInt hu'
  have hαβ : (fun j => nuOf lam (midI mm j)) = fun j => nuOf (lam - wtPQ (mm + 1) P Q) (midI mm j) + Q := by
    funext j
    have := hαZ j; have := hβZ j; omega
  have hwA : ∀ a b, Antitone (nuOf (wtPQ (mm + 1) a b)) := fun a b => nuOf_anti _ (wtPQ_anti (mm + 1) a b (by omega))
  have hK : ∀ v ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf lam),
      ∀ t ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q))),
        lamOf R.Kf mm L (blockEmb R.Kf true v * blockEmb R.Kf false t) ∈
          dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (wtPQ (mm + 1) (P + 2 * ccl) (Q + 2 * ccl))) :=
    hMem R.Kf mm (Q + 2 * ccl) (nuOf lam) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q)))
      (nuOf (wtPQ (mm + 1) (P + 2 * ccl) (Q + 2 * ccl))) L (nuOf_last _) (nuOf_last _) (nuOf_last _)
      (by rw [nuOf_wt_zero, nuOf_lam_zero mm ccl P Q lam h0 hl, nuOf_lo'_zero mm ccl P Q lam h0 hl]; omega)
      (fun j => nuOf_wt_mid mm _ _ j) hInv
  refine ⟨lamOf R.Kf mm L, hK, fun g _ v _ t _ => hLE R.Kf mm L g v t, ?_, ?_⟩
  · intro v hv t ht
    refine hIC R.O R.Kf hinj _ _ _ (hK v (intO_le _ _ v hv) t (intO_le _ _ t ht)) ?_
    intro x
    obtain ⟨v0, hv0, rfl⟩ := hv
    obtain ⟨t0, ht0, rfl⟩ := ht
    have e1 : (mapAlgHom (Algebra.ofId R.O R.Kf)).toLinearMap v0 = map (algebraMap R.O R.Kf) v0 := rfl
    have e2 : (mapAlgHom (Algebra.ofId R.O R.Kf)).toLinearMap t0 = map (algebraMap R.O R.Kf) t0 := rfl
    rw [hLC, e1, e2, hSM, hSM]
    have : (∑ y ∈ Finset.HasAntidiagonal.antidiagonal x,
        L (blockEmb R.Kf true (AddMonoidAlgebra.coeff (map (map (algebraMap R.O R.Kf)) (subY R.O mm v0)) y.1) *
          blockEmb R.Kf false (AddMonoidAlgebra.coeff (map (map (algebraMap R.O R.Kf)) (subY R.O mm t0)) y.2))) ∈
        (algebraMap R.O R.Kf).range := by
      refine sum_mem fun y _ => ?_
      rw [coeff_map, coeff_map]
      exact hInt _ ⟨AddMonoidAlgebra.coeff (subY R.O mm v0) y.1, hSC R.O mm _ v0 hv0 _, rfl⟩ _
        ⟨AddMonoidAlgebra.coeff (subY R.O mm t0) y.2, hSC R.O mm _ t0 ht0 _, rfl⟩
    exact this
  · have hβA : Antitone (fun j => nuOf (lam - wtPQ (mm + 1) P Q) (midI mm j)) :=
      fun i j hij => nuOf_anti _ hloA (midI_mono mm hij)
    have hβc : ∀ j, (fun j => nuOf (lam - wtPQ (mm + 1) P Q) (midI mm j)) j ≤ 2 * ccl := by
      intro j
      show nuOf (lam - wtPQ (mm + 1) P Q) (midI mm j) ≤ 2 * ccl
      have := hβZ j; have := hbd j; omega
    have hβ'A : Antitone (fun j => nuOf (dualWt (lam - wtPQ (mm + 1) P Q)) (midI mm j)) :=
      fun i j hij => nuOf_anti _ hlo'A (midI_mono mm hij)
    have hβ'c : ∀ j, (fun j => nuOf (dualWt (lam - wtPQ (mm + 1) P Q)) (midI mm j)) j ≤ 2 * ccl := by
      intro j
      show nuOf (dualWt (lam - wtPQ (mm + 1) P Q)) (midI mm j) ≤ 2 * ccl
      have := hβ'Z j; have := hbd j.rev; omega
    have hS : ∀ b, ∃ s0 ∈ dualWeyl R.O (mm + 1 + 1) (mm + 1 + 1) (nuOf (lam - wtPQ (mm + 1) P Q)),
        RowA 0 s0 (2 * ccl) ∧ RowA (Fin.last (mm + 1)) s0 0 ∧
          map (algebraMap R.O R.Kf) (detY R.O mm ^ Q * resY R.O mm s0) = u b := by
      intro b
      obtain ⟨f, hf, hfe⟩ := hu b
      rw [hαβ] at hf
      obtain ⟨w0, hw0, rfl⟩ := hDD R.O mm Q _ hmm hβA f hf
      obtain ⟨s0, hs0, hr0, hrl, hres⟩ := hLift R.O mm (2 * ccl) _ hβA hβc w0 hw0
      rw [shapeC_lo mm ccl P Q lam h0 hl] at hs0
      exact ⟨s0, hs0, hr0, hrl, by rw [hres]; exact hfe⟩
    have hS' : ∀ a', ∃ s0 ∈ dualWeyl R.O (mm + 1 + 1) (mm + 1 + 1) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q))),
        RowA 0 s0 (2 * ccl) ∧ RowA (Fin.last (mm + 1)) s0 0 ∧ map (algebraMap R.O R.Kf) (resY R.O mm s0) = u' a' := by
      intro a'
      obtain ⟨f, hf, hfe⟩ := hu' a'
      obtain ⟨s0, hs0, hr0, hrl, hres⟩ := hLift R.O mm (2 * ccl) _ hβ'A hβ'c f hf
      rw [shapeC_lo' mm ccl P Q lam h0 hl] at hs0
      exact ⟨s0, hs0, hr0, hrl, by rw [hres]; exact hfe⟩
    choose s0 hs0 hs0r hs0l hs0e using hS
    choose t0 ht0 ht0r ht0l ht0e using hS'
    refine ⟨nb, fun b => map (algebraMap R.O R.Kf) (s0 b), fun a' => map (algebraMap R.O R.Kf) (t0 a'), ka, ?_, hka,
      fun b => ⟨⟨s0 b, hs0 b, rfl⟩, rowA_map _ 0 _ _ (hs0r b)⟩, fun a' => ⟨⟨t0 a', ht0 a', rfl⟩, rowA_map _ 0 _ _ (ht0r a')⟩, ?_⟩
    · have e : (fun j : Fin mm => ((nuOf lam (midI mm j) : ℕ) : ℤ)) = fun j => lam (midI mm j) + ((Q : ℤ) + ccl) := by
        funext j
        rw [hαZ j]; ring
      rw [hnb, e]
      exact weylDim_add_const mm (fun j => lam (midI mm j)) ((Q : ℤ) + ccl)
    · intro a' b F hF
      have e1 := hLM R.Kf mm Q L F (map (algebraMap R.O R.Kf) (s0 b)) (map (algebraMap R.O R.Kf) (t0 a'))
        (hMu p n' R mm hmm P Q F hF)
      have hF0 : hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q)) ∈
          dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (wtPQ (mm + 1) 0 Q)) := hwMem R.Kf _ _ le_rfl _ (hwA 0 Q)
      have hF0sub := hMu p n' R mm hmm 0 Q _ hF0
      have e2 := hLM R.Kf mm Q L _ (map (algebraMap R.O R.Kf) (s0 b)) (map (algebraMap R.O R.Kf) (t0 a')) hF0sub
      have hSK : map (algebraMap R.O R.Kf) (s0 b) ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (lam - wtPQ (mm + 1) P Q)) :=
        dualWeylMap R.O R.Kf _ _ _ _ _ (hs0 b)
      have hTK : map (algebraMap R.O R.Kf) (t0 a') ∈
          dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q))) :=
        dualWeylMap R.O R.Kf _ _ _ _ _ (ht0 a')
      have hInv' : PhInv R.Kf mm (Q + 2 * ccl)
          (fun j => (nuOf (wtPQ (mm + 1) 0 Q) + nuOf (lam - wtPQ (mm + 1) P Q)) (midI mm j))
          (fun j => nuOf (dualWt (lam - wtPQ (mm + 1) P Q)) (midI mm j)) L := by
        have e : (fun j => (nuOf (wtPQ (mm + 1) 0 Q) + nuOf (lam - wtPQ (mm + 1) P Q)) (midI mm j)) =
            fun j => nuOf lam (midI mm j) := by
          funext j
          rw [Pi.add_apply, nuOf_wt_mid]
          have := hαZ j; have := hβZ j; omega
        rw [e]; exact hInv
      have hΨmem := hMem R.Kf mm (Q + 2 * ccl) (nuOf (wtPQ (mm + 1) 0 Q) + nuOf (lam - wtPQ (mm + 1) P Q))
        (nuOf (dualWt (lam - wtPQ (mm + 1) P Q))) (nuOf (wtPQ (mm + 1) (2 * ccl) (Q + 2 * ccl))) L
        (by rw [Pi.add_apply, nuOf_last, nuOf_last]) (nuOf_last _) (nuOf_last _)
        (by rw [nuOf_wt_zero, Pi.add_apply, nuOf_wt_zero, nuOf_lo_zero mm ccl P Q lam h0 hl,
              nuOf_lo'_zero mm ccl P Q lam h0 hl]; omega)
        (fun j => nuOf_wt_mid mm _ _ j) hInv' _ (dualWeyl_mul R.Kf _ _ _ _ hF0 hSK) _ hTK
      have hr0 : RowA 0 (hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q))) Q := by
        have h := rowA_hw R.Kf _ _ (hwA 0 Q) 0
        rwa [nuOf_wt_zero, zero_add] at h
      have hrl : RowA (Fin.last (mm + 1)) (hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q))) 0 := by
        have h := rowA_hw R.Kf _ _ (hwA 0 Q) (Fin.last (mm + 1))
        rwa [nuOf_last] at h
      have hΨ0 := rowA_lam hLC hSR R.Kf mm L 0 _ _ _ _
        (rowA_mul 0 _ _ _ _ hr0 (rowA_map (algebraMap R.O R.Kf) 0 _ _ (hs0r b)))
        (rowA_map (algebraMap R.O R.Kf) 0 _ _ (ht0r a'))
      have hΨl := rowA_lam hLC hSR R.Kf mm L (Fin.last (mm + 1)) _ _ _ _
        (rowA_mul (Fin.last (mm + 1)) _ _ _ _ hrl (rowA_map (algebraMap R.O R.Kf) _ _ _ (hs0l b)))
        (rowA_map (algebraMap R.O R.Kf) _ _ _ (ht0l a'))
      have ed : Q + 2 * ccl + 2 * ccl = 2 * ccl + (Q + 2 * ccl) := by omega
      rw [ed] at hΨ0
      have hΨ := hTop p n' R mm hmm (2 * ccl) (Q + 2 * ccl) _ hΨmem hΨ0 hΨl
      have hres0 : resY R.Kf mm (hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q))) = detY R.Kf mm ^ Q := by
        unfold resY
        rw [hF0sub, map_mul, eval_C, evalId_map, (hHw R.Kf _ _ _ (hwA 0 Q) (hwA 0 Q)).2, map_one, mul_one]
      have hκ : eval (idPoint R.Kf (mm + 1 + 1) (mm + 1 + 1))
          (lamOf R.Kf mm L (blockEmb R.Kf true (hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q)) *
            map (algebraMap R.O R.Kf) (s0 b)) * blockEmb R.Kf false (map (algebraMap R.O R.Kf) (t0 a')))) =
          if a' = b then (p : R.Kf) ^ ka b else 0 := by
        have hub : u b = detY R.Kf mm ^ Q * map (algebraMap R.O R.Kf) (resY R.O mm (s0 b)) := by
          rw [← hs0e b, map_mul, map_pow, detY_map]
        rw [hLV, resY_mul, hres0, resY_map hSM, resY_map hSM, ht0e, ← hub, hdiag a' b]
      have hsh : nuOf (wtPQ (mm + 1) (2 * ccl) (Q + 2 * ccl)) =
          nuOf (wtPQ (mm + 1) (2 * ccl) (2 * ccl)) + nuOf (wtPQ (mm + 1) 0 Q) := by
        have := nuOf_wt_add mm (2 * ccl) (2 * ccl) 0 Q
        rwa [add_zero, add_comm (2 * ccl) Q] at this
      rw [hκ, hsh, (hHw R.Kf _ _ _ (hwA (2 * ccl) (2 * ccl)) (hwA 0 Q)).1] at hΨ
      have hne : hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q)) ≠ 0 := hwNe R.Kf _ _ le_rfl _
      have hΦ := mul_left_cancel₀ hne (a := hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q)))
        (c := C (if a' = b then (p : R.Kf) ^ ka b else 0) * hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) (2 * ccl) (2 * ccl))))
        (by rw [← e2, hΨ]; ring)
      rw [e1, hΦ]
      split_ifs
      · rw [smul_eq_C_mul]; ring
      · rw [C_0, zero_mul, mul_zero]

end Formalism.MainNotions.flipOneThree.Pf

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.DerivativeRepresentation
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

def qcOm (n s : ℕ) : Fin n → ℕ := fun t => if t.val < s then 1 else 0

theorem qc_shapeDeg_succ {n K : ℕ} (sz : Fin (K + 1) → ℕ) :
    (shapeDeg sz : Fin n → ℕ) = qcOm n (sz 0) + shapeDeg (fun k : Fin K => sz k.succ) := by
  funext t
  simp only [shapeDeg, qcOm, Pi.add_apply, Finset.card_filter]
  rw [Fin.sum_univ_succ]

theorem qc_shapeDeg_zero {n : ℕ} (sz : Fin 0 → ℕ) : (shapeDeg sz : Fin n → ℕ) = 0 := by
  funext t
  simp [shapeDeg]

theorem qc_initMinor_mem (R : Type) [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n) :
    initMinor R I hs ∈ dualWeyl R r n (qcOm n s) := by
  have h := bidetMem R r n 1 (fun _ => s) (fun _ => hs) (fun _ => I)
  have h1 : bideterminant R (fun _ : Fin 1 => s) (fun _ => hs) (fun _ => I) = initMinor R I hs := by
    simp [bideterminant]
  have h2 : (shapeDeg (fun _ : Fin 1 => s) : Fin n → ℕ) = qcOm n s := by
    funext t
    simp only [shapeDeg, qcOm, Finset.card_filter]
    simp
  rw [h1, h2] at h
  exact h

theorem qc_bidet_succ (R : Type) [CommRing R] {r n K : ℕ} (sz : Fin (K + 1) → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) :
    bideterminant R sz hsz I = initMinor R (I 0) (hsz 0) *
      bideterminant R (fun k : Fin K => sz k.succ) (fun k => hsz k.succ) (fun k => I k.succ) := by
  unfold bideterminant
  rw [Fin.prod_univ_succ]

theorem qc_bidet_zero (R : Type) [CommRing R] {r n : ℕ} (sz : Fin 0 → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) : bideterminant R sz hsz I = 1 := by
  simp [bideterminant]

theorem qc_pow_mem (R : Type) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) (y : MvPolynomial (Fin r × Fin n) R)
    (hy : y ∈ dualWeyl R r n ν) (k : ℕ) : y ^ k ∈ dualWeyl R r n (k • ν) := by
  induction k with
  | zero => rw [pow_zero, zero_smul]; exact one_mem_dualWeyl R r n
  | succ k ih => rw [pow_succ, succ_nsmul]; exact dualWeyl_mul R r n _ _ ih hy

theorem qc_full_minor (A : Type) [CommRing A] (r s : ℕ) (hs : s ≤ r) (I : Fin s → Fin r) (hI : StrictMono I)
    (h : s = r) : initMinor A I hs = detY A r := by
  subst h
  have hid : I = id := by
    exact (StrictMono.range_inj_of_wellFoundedLT hI strictMono_id).1
      (by rw [Set.range_id]; exact (Finite.injective_iff_surjective.1 hI.injective).range_eq)
  subst hid
  rfl

theorem qc_empty_minor (A : Type) [CommRing A] {r n : ℕ} (s : ℕ) (hs : s ≤ n) (I : Fin s → Fin r) (h : s = 0) :
    initMinor A I hs = 1 := by
  subst h
  unfold initMinor
  exact Matrix.det_isEmpty

theorem qcOm_zero (n : ℕ) : qcOm n 0 = 0 := by
  funext t
  simp [qcOm]

theorem qc_detDiv_bidet (A : Type) [CommRing A] (r : ℕ) : ∀ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ r)
    (I : ∀ k, Fin (sz k) → Fin r), (∀ k, StrictMono (I k)) →
    ∃ (n : ℕ) (γ : Fin r → ℕ) (u₀ : MvPolynomial (Fin r × Fin r) A), (∀ t, shapeDeg sz t = γ t + n) ∧
      (∀ t : Fin r, t.val + 1 = r → γ t = 0) ∧ u₀ ∈ dualWeyl A r r γ ∧ bideterminant A sz hsz I = detY A r ^ n * u₀ := by
  intro K
  induction K with
  | zero =>
    intro sz hsz I _
    exact ⟨0, 0, 1, by intro t; rw [qc_shapeDeg_zero]; rfl, fun _ _ => rfl, one_mem_dualWeyl A r r,
      by rw [qc_bidet_zero, pow_zero, one_mul]⟩
  | succ K ih =>
    intro sz hsz I hI
    obtain ⟨n, γ, u₀, h1, h2, h3, h4⟩ :=
      ih (fun k => sz k.succ) (fun k => hsz k.succ) (fun k => I k.succ) (fun k => hI k.succ)
    by_cases hr : sz 0 = r
    · refine ⟨n + 1, γ, u₀, ?_, h2, h3, ?_⟩
      · intro t
        rw [qc_shapeDeg_succ, Pi.add_apply, h1 t]
        have : qcOm r (sz 0) t = 1 := by
          unfold qcOm
          rw [ite_eq_left (by rw [hr]; exact t.isLt)]
        omega
      · rw [qc_bidet_succ, h4, qc_full_minor A r _ (hsz 0) (I 0) (hI 0) hr]
        ring
    · refine ⟨n, qcOm r (sz 0) + γ, initMinor A (I 0) (hsz 0) * u₀, ?_, ?_,
        dualWeyl_mul A r r _ _ (qc_initMinor_mem A (I 0) (hsz 0)) h3, ?_⟩
      · intro t
        rw [qc_shapeDeg_succ, Pi.add_apply, Pi.add_apply, h1 t]
        omega
      · intro t ht
        rw [Pi.add_apply, h2 t ht, add_zero]
        unfold qcOm
        rw [ite_eq_right]
        have := hsz 0
        omega
      · rw [qc_bidet_succ, h4]
        ring

theorem detDivP : DetDivP := by
  intro A _ _ r Q β hr hβ u hu
  obtain ⟨b, ⟨-, hspan, -⟩, hb⟩ := sSBasis A r r (fun j => β j + Q)
  rw [← hspan] at hu
  refine Submodule.span_induction (p := fun u _ => ∃ u₀ ∈ dualWeyl A r r β, u = detY A r ^ Q * u₀) ?_ ?_ ?_ ?_ hu
  · rintro _ ⟨m, rfl⟩
    obtain ⟨-, -, K, sz, hsz, I, hsh, hI, hbm⟩ := hb m
    obtain ⟨n, γ, u₀, h1, h2, h3, h4⟩ := qc_detDiv_bidet A r K sz hsz I hI
    have h1' : ∀ t, β t + Q = γ t + n := by
      intro t
      have := h1 t
      rwa [hsh] at this
    have hl : γ ⟨r - 1, by omega⟩ = 0 := h2 _ (by show r - 1 + 1 = r; omega)
    have hn : Q ≤ n := by
      have := h1' ⟨r - 1, by omega⟩
      omega
    refine ⟨detY A r ^ (n - Q) * u₀, ?_, ?_⟩
    · have hd : detY A r ∈ dualWeyl A r r (qcOm r r) := by
        rw [← qc_full_minor A r r le_rfl id strictMono_id rfl]
        exact qc_initMinor_mem A id le_rfl
      have h5 := dualWeyl_mul A r r _ _ (qc_pow_mem A r r _ _ hd (n - Q)) h3
      have e : (n - Q) • qcOm r r + γ = β := by
        funext t
        have := h1' t
        simp only [Pi.add_apply, Pi.smul_apply, qcOm, t.isLt, ite_true, smul_eq_mul, mul_one]
        omega
      rwa [e] at h5
    · rw [hbm, h4, ← mul_assoc, ← pow_add]
      congr 2
      omega
  · exact ⟨0, Submodule.zero_mem _, by rw [mul_zero]⟩
  · rintro x y _ _ ⟨a, ha, rfl⟩ ⟨b', hb', rfl⟩
    exact ⟨a + b', Submodule.add_mem _ ha hb', by rw [mul_add]⟩
  · rintro c x _ ⟨a, ha, rfl⟩
    exact ⟨c • a, Submodule.smul_mem _ _ ha, by rw [mul_smul_comm]⟩

end Formalism.MainNotions.flipOneThree.Pf

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.DetYNeZero
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem detY_ne_zero (K : Type) [Field K] (r : ℕ) : detY K r ≠ 0 :=
  Matrix.det_mvPolynomialX_ne_zero (Fin r) K

theorem qPh_of (hTau : TauP) (hSm : SmithP) (hBil : BilinP) (hDet : DetFactsP) (hNum : NumP) (hDD : DetDivP) : QPh := by
  intro p n' R r hr a c N α hαA hαN hc hca
  letI := R.charZeroO
  haveI := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  obtain ⟨e, he_def⟩ : ∃ e, α (Fin.last m) = e := ⟨_, rfl⟩
  have he : ∀ i, e ≤ α i := fun i => he_def ▸ hαA (Fin.le_last i)
  have hex : ∃ i, α i = e := ⟨_, he_def⟩
  have heN : e ≤ N := he_def ▸ hαN _
  have hγA : Antitone (fun i => α i - e) := by
    intro i j hij
    have := hαA hij
    show α j - e ≤ α i - e
    omega
  have wtK : ∀ {ν ν' : Fin (m + 1) → ℕ} {f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf},
      ν = ν' → f ∈ dualWeyl R.Kf (m + 1) (m + 1) ν → f ∈ dualWeyl R.Kf (m + 1) (m + 1) ν' := by
    rintro _ _ _ rfl h
    exact h
  have wtO : ∀ {ν ν' : Fin (m + 1) → ℕ} {f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.O},
      ν = ν' → f ∈ dualWeyl R.O (m + 1) (m + 1) ν → f ∈ dualWeyl R.O (m + 1) (m + 1) ν' := by
    rintro _ _ _ rfl h
    exact h
  have hwα : (fun j => (fun i => α i - e) j + e) = α := by
    funext j
    have := he j
    simp only
    omega
  obtain ⟨τ, hτK, hτO, hτsurj, hτeq⟩ := hTau R.O R.Kf hinj (m + 1) N e α (by omega) hαA hαN he hex
  obtain ⟨B, hBeq, hBint, nb, x, x', ka, hnb, hka, hx, hx', hdual⟩ :=
    hSm p n' R m (fun i => α i - e) hγA (by simp [he_def])
  set D : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf := detY R.Kf (m + 1) ^ e with hD_def
  have hD0 : D ≠ 0 := pow_ne_zero _ (detY_ne_zero R.Kf _)
  let μ : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf →ₗ[R.Kf]
      MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf := LinearMap.mulLeft R.Kf D
  have hμ : Function.Injective μ := fun u v h => mul_left_cancel₀ hD0 h
  obtain ⟨Cc, hCc⟩ := Submodule.exists_isCompl (LinearMap.range μ)
  let σ : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf →ₗ[R.Kf]
      MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf :=
    (LinearEquiv.ofInjective μ hμ).symm.toLinearMap ∘ₗ (LinearMap.range μ).projectionOnto Cc hCc
  have hσ : ∀ g, σ (D * g) = g := by
    intro g
    have hmem : D * g ∈ LinearMap.range μ := ⟨g, rfl⟩
    show (LinearEquiv.ofInjective μ hμ).symm ((LinearMap.range μ).projectionOnto Cc hCc (D * g)) = g
    rw [show D * g = ((⟨D * g, hmem⟩ : LinearMap.range μ) : MvPolynomial _ _) from rfl,
      Submodule.linearProjOfIsCompl_apply_left hCc, LinearEquiv.symm_apply_eq]
    ext1
    rw [LinearEquiv.ofInjective_apply]
    rfl
  obtain ⟨L, hL⟩ := hBil R.Kf (m + 1) ((B.compl₂ τ) ∘ₗ σ)
  have hL' : ∀ f f', L ((blockEmb R.Kf true) f * (blockEmb R.Kf false) f') = B (σ f) (τ f') := by
    intro f f'
    rw [hL]
    rfl
  have hmapD : map (algebraMap R.O R.Kf) (detY R.O (m + 1) ^ e) = D := by
    rw [map_pow, detY_map]
  have hdivK : ∀ f ∈ dualWeyl R.Kf (m + 1) (m + 1) α,
      ∃ g ∈ dualWeyl R.Kf (m + 1) (m + 1) (fun i => α i - e), f = D * g := by
    intro f hf
    exact hDD R.Kf (m + 1) e (fun i => α i - e) (by omega) hγA f (wtK hwα.symm hf)
  have hdivO : ∀ f ∈ intO R.O (m + 1) α,
      ∃ g ∈ intO R.O (m + 1) (fun i => α i - e), f = D * g := by
    intro f hf
    obtain ⟨fO, hfO, rfl⟩ := Submodule.mem_map.1 hf
    obtain ⟨gO, hgO, hfg⟩ := hDD R.O (m + 1) e (fun i => α i - e) (by omega) hγA fO (wtO hwα.symm hfO)
    refine ⟨map (algebraMap R.O R.Kf) gO, Submodule.mem_map.2 ⟨gO, hgO, rfl⟩, ?_⟩
    show map (algebraMap R.O R.Kf) fO = _
    rw [hfg, map_mul, hmapD]
  choose U hU hτU using fun a' => hτsurj (x' a') (hx' a')
  refine ⟨L, ?_, ?_, nb, fun b => D * x b, U, ka, ?_, ?_, ?_, hU, ?_⟩
  · intro l hl f hf f' hf'
    obtain ⟨g, hg, rfl⟩ := hdivK f hf
    rw [hL', hL', hσ]
    have hrD : rowAct R.Kf l (D * g) = D * (l.det ^ e • rowAct R.Kf l g) := by
      rw [map_mul, hD_def, map_pow, (hDet R.Kf (m + 1) e).2 l, MvPolynomial.smul_eq_C_mul, map_pow]
      ring
    rw [hrD, hσ, map_smul, LinearMap.smul_apply, hBeq, hτeq l hl f' hf', map_smul, smul_eq_mul,
      smul_eq_mul, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' heN]
  · intro f hf f' hf'
    obtain ⟨g, hg, rfl⟩ := hdivO f hf
    rw [hL', hσ]
    exact hBint g hg (τ f') (hτO f' hf')
  · rw [hnb]
    unfold weylDim
    refine Finset.prod_congr rfl (fun i _ => Finset.prod_congr rfl (fun j _ => ?_))
    simp only [Nat.cast_sub (he i), Nat.cast_sub (he j), sub_sub_sub_cancel_right]
  · intro b
    refine (hka b).trans ?_
    have h1 := hc 0 (Fin.last m)
    exact hNum p a c (m + 1) (α 0 - e) R.std.1.prime.two_le (by omega) (by omega) hca
  · intro b
    obtain ⟨xO, hxO, hxe⟩ := Submodule.mem_map.1 (hx b)
    refine Submodule.mem_map.2 ⟨detY R.O (m + 1) ^ e * xO,
      wtO (by funext j; have := he j; simp only [Pi.add_apply]; omega)
        (dualWeyl_mul R.O (m + 1) (m + 1) _ _ (hDet R.O (m + 1) e).1 hxO), ?_⟩
    show map (algebraMap R.O R.Kf) (detY R.O (m + 1) ^ e * xO) = D * x b
    rw [map_mul, hmapD, ← hxe]
    rfl
  · intro a' b
    rw [hL', hσ, hτU]
    exact hdual a' b

end Formalism.MainNotions.flipOneThree.Pf

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.TheoremIOfTwoLetterClausesContraction
section
namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem cloud_maps_of_contraction (hQ : ContractionStandardLattice) (hCD : CartanDomain) (hCO : CartanOnto) (hIncl : DualHeightInclusion) : RestCloudMaps :=
  restCloudMaps_of (restCloudLat_of (cloudOne_of hQ) hCO (cloudIso hCD hCO)) hIncl

theorem theorem_I_of_two_letter_clauses_contraction (D : Formalism.BasicNotions.D7) (h1 : ExplicitMapInjective) (h2 : ExplicitMapOntoTwoLetters) (h5 : TwoLetterLatticeGaussInverse) (hQ : ContractionStandardLattice) : SecondPartClosed D := by
  intro hA
  have hT := tools_of_admitted_statements D hA
  have h11 : GradedLatticeStable D := hT.2.2.2.2.2.2.1
  have h13 : TypeDecompositionsCommute D := hT.2.2.2.2.2.2.2.2.1
  have h16 : PairedPathIndependence D := hT.2.2.2.2.2.2.2.2.2.2.2
  exact theorem_I_of_explicit_minor_map D (tiePsi_of D h1 h2 h5 h11.2 h16.1) (cloud_maps_of_contraction hQ h11.1 h11.2 h13.2.1) hA

end Formalism.MainNotions.flipOneThree.Pf
end

