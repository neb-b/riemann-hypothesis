module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1646
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralActionUnitCharacterEigen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1791
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1794
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1812
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1786
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1727
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0488
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0133
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1806
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairFirstConjEqSumCosetIndicators
section
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

noncomputable section

namespace GlobalTheory.StdExpand

open GlobalTheory.BotClassDict (finQ)
open GlobalTheory.StdRead.CharVal

variable {D : D7}

def invM {a : ℕ} (k : Formalism.MainNotions.StandardLatticesGL3.GA D a) : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D) :=
  (((k : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))

def valM {a : ℕ} (k : Formalism.MainNotions.StandardLatticesGL3.GA D a) : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D) :=
  ((k : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))

theorem invM_mul {a : ℕ} (k : Formalism.MainNotions.StandardLatticesGL3.GA D a) : invM k * valM k = 1 := Units.inv_mul _

theorem valM_mul {a : ℕ} (k : Formalism.MainNotions.StandardLatticesGL3.GA D a) : valM k * invM k = 1 := Units.mul_inv _

theorem int_of_hat {𝔪 : Ideal (𝓞 D.host.E)} {x : Formalism.MainNotions.StandardLatticesGL3.AE D} (hx : x ∈ hatId D 𝔪) : x ∈ OhE D :=
  (toE_int_iff x).1 ((_root_.GlobalTheory.StdRead.IdealDict.inId_toE_iff 𝔪 x).2 hx).1

theorem hat_mul_mat {𝔪 : Ideal (𝓞 D.host.E)} {a : ℕ} {A B : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)} (hA : ∀ i j, A i j ∈ hatId D 𝔪)
    (hB : ∀ i j, B i j ∈ OhE D) (i j : Fin a) : (A * B) i j ∈ hatId D 𝔪 := by
  rw [Matrix.mul_apply]
  refine sum_mem fun l _ => ?_
  rw [mul_comm]
  exact GlobalTheory.FunObj.StdDatum.mul_mem_hatId (hB l j) (hA i l)

theorem cong_iff {𝔪 : Ideal (𝓞 D.host.E)} {a : ℕ} {N : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)} {r k : Formalism.MainNotions.StandardLatticesGL3.GA D a}
    (hk : k ∈ intG D a) (h : ∀ i j, (N - invM k) i j ∈ hatId D 𝔪) :
    (∀ i j, (N - invM r) i j ∈ hatId D 𝔪) ↔ CongOne D 𝔪 (r⁻¹ * k) := by
  have hi := (GlobalTheory.NormSum.mem_intG k).1 hk
  change _ ↔ ∀ i j, (invM r * valM k - 1) i j ∈ hatId D 𝔪
  constructor
  · intro h' i j
    have e : invM r * valM k - 1 = ((N - invM k) - (N - invM r)) * valM k := by
      rw [sub_sub_sub_cancel_left, sub_mul, invM_mul]
    rw [e]
    exact hat_mul_mat (fun i j => sub_mem (h i j) (h' i j)) (fun i j => (hi i j).1) i j
  · intro h' i j
    have e : N - invM r = (N - invM k) - (invM r * valM k - 1) * invM k := by
      rw [sub_mul, mul_assoc, valM_mul, mul_one, one_mul, sub_sub, add_sub_cancel]
    rw [e]
    exact sub_mem (h i j) (hat_mul_mat h' (fun i j => (hi i j).2) i j)

theorem value {e : AE D} {𝔪 : Ideal (𝓞 D.host.E)} (hG : GoodMod e 𝔪) {ν : (AE D)ˣ →* Circle} (hK : KillsCong ν 𝔪) {a : ℕ}
    {N : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)} {r : Formalism.MainNotions.StandardLatticesGL3.GA D a} (hr : r ∈ intG D a)
    (h : ∀ i j, (N - invM r) i j ∈ hatId D 𝔪) :
    (∃ x, IsUnitDet e (N.map (toE D)) x) ∧ starRingEnd ℂ (unitChar ν e (N.map (toE D))) = unitChar ν e (matE r) := by
  have hi := (GlobalTheory.NormSum.mem_intG r).1 hr
  have h1 := GlobalTheory.T.unitDetCharIndicator_eq_one_of_congruent_one e 𝔪 hG ν hK (N * valM r) fun i j => by
    rw [← invM_mul r, ← sub_mul]
    exact hat_mul_mat h (fun i j => (hi i j).1) i j
  obtain ⟨S, -, he, -⟩ := hG
  have he_mul := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have he_int : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    GlobalTheory.IdemRes.toEAf_mem_of_finPart (GlobalTheory.AdIdem.idempotent_mem_intAE D _
      (by rw [← map_mul, he_mul]))
  have h2 := _root_.GlobalTheory.StdRead.CharMul.unitChar_mul ν e he_mul he_int (N.map (toE D))
    (Matrix.GeneralLinearGroup.map (toE D) (r : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))) (fun i j => (toE_int_iff _).2 (hi i j).1)
    (fun i j => (toE_int_iff _).2 (hi i j).2)
  rw [Matrix.map_mul] at h1
  have h3 : unitChar ν e (N.map (toE D)) * unitChar ν e (matE r) = 1 := h2.symm.trans h1
  have hx : ∃ x, IsUnitDet e (N.map (toE D)) x := by
    by_contra hx
    rw [unitChar, dite_eq_right hx, zero_mul] at h3
    exact zero_ne_one h3
  refine ⟨hx, ?_⟩
  obtain ⟨x, hx⟩ := hx
  rw [unitChar_eq ν e _ hx] at h3 ⊢
  rw [← Circle.coe_inv_eq_conj, Circle.coe_inv]
  exact inv_eq_of_mul_eq_one_right h3

theorem unitBlock_mul {a d : ℕ} (M : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (i : Fin d) (j : Fin a) :
    (HMul.hMul ((unitBlock D 0 a d).map (inc D)) M : Matrix (Fin d) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j =
      if h : i.1 < a then M ⟨i.1, h⟩ j else 0 := by
  rw [Matrix.mul_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨i.1, h⟩ (fun l _ hl => ?_) (fun hh => (hh (Finset.mem_univ _)).elim)]
    · simp [unitBlock]
    · have : i.1 ≠ l.1 := fun hh => hl (Fin.ext hh.symm)
      simp [unitBlock, this]
  · refine Finset.sum_eq_zero fun l _ => ?_
    have : i.1 ≠ l.1 := fun hh => h (hh ▸ l.2)
    simp [unitBlock, this]

theorem coset_iff {ε : Formalism.MainNotions.StandardLatticesGL3.AE D} {𝔪 : Ideal (𝓞 D.host.E)} (hε : 1 - ε ∈ hatId D 𝔪) {a d : ℕ} (had : a ≤ d)
    {r : Formalism.MainNotions.StandardLatticesGL3.GA D a} {z : Matrix (Fin d) (Fin a) D.host.E} (hz : IsIntE z) (ha : Approx 𝔪 0 r z)
    (W : Matrix (Fin d) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :
    (∀ i j, W i j - ε * inc D (z i j) ∈ hatId D 𝔪) ↔
      (∀ i j, (topL a W - invM r) i j ∈ hatId D 𝔪) ∧ ∀ i j, a ≤ i.1 → W i j ∈ hatId D 𝔪 := by
  have h1 : ∀ i j, (W i j - if h : i.1 < a then invM r ⟨i.1, h⟩ j else 0) - (W i j - ε * inc D (z i j)) ∈ hatId D 𝔪 := by
    intro i j
    have h2 : inc D (z i j) - (if h : i.1 < a then invM r ⟨i.1, h⟩ j else 0) ∈ hatId D 𝔪 := by
      rw [← unitBlock_mul]
      exact ha i j
    obtain ⟨b, hb⟩ := hz i j
    have h3 := sub_mem h2 (GlobalTheory.FunObj.StdDatum.mul_mem_hatId (hb ▸ inc_int b : inc D (z i j) ∈ OhE D) hε)
    convert h3 using 1
    ring
  have h4 : ∀ (i : Fin a) j, (topL a W - invM r) i j = W ⟨i.1, i.2.trans_le had⟩ j - invM r i j := fun i j => by
    rw [Matrix.sub_apply, topL, dite_eq_left ⟨i.2.trans_le had, j.2⟩]
  constructor
  · intro h
    have h5 := fun i j => add_mem (h1 i j) (h i j)
    simp only [sub_add_cancel] at h5
    refine ⟨fun i j => ?_, fun i j hi => ?_⟩
    · have := h5 ⟨i.1, i.2.trans_le had⟩ j
      rwa [dite_eq_left i.2, ← h4] at this
    · have := h5 i j
      rwa [dite_eq_right (not_lt.2 hi), sub_zero] at this
  · rintro ⟨h, h'⟩ i j
    have h6 : (W i j - if h : i.1 < a then invM r ⟨i.1, h⟩ j else 0) ∈ hatId D 𝔪 := by
      split_ifs with hi
      · have := h ⟨i.1, hi⟩ j
        rwa [h4] at this
      · rw [sub_zero]
        exact h' i j (not_lt.1 hi)
    have := sub_mem h6 (h1 i j)
    rwa [sub_sub_cancel] at this

theorem sum_eq {e : AE D} {𝔪 : Ideal (𝓞 D.host.E)} (hG : GoodMod e 𝔪) {ν : (AE D)ˣ →* Circle} (hK : KillsCong ν 𝔪) {a d : ℕ}
    (had : a ≤ d) {R : Finset (Formalism.MainNotions.StandardLatticesGL3.GA D a)} (hR : ∀ r ∈ R, r ∈ intG D a)
    (hU : ∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k)) (W : Matrix (Fin d) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :
    ∑ r ∈ R, unitChar ν e (matE r) *
        (if (∀ i j, (topL a W - invM r) i j ∈ hatId D 𝔪) ∧ ∀ i j, a ≤ i.1 → W i j ∈ hatId D 𝔪 then 1 else 0) =
      if (∀ i j, W i j ∈ OhE D) ∧ ∀ i j, a ≤ i.1 → W i j ∈ hatId D 𝔪 then
        starRingEnd ℂ (unitChar ν e ((topL a W).map (toE D))) else 0 := by
  by_cases hc : ((∀ i j, W i j ∈ OhE D) ∧ ∀ i j, a ≤ i.1 → W i j ∈ hatId D 𝔪) ∧ ∃ x, IsUnitDet e ((topL a W).map (toE D)) x
  · obtain ⟨hc, x, hx⟩ := hc
    have hN : ∀ i j, topL a W i j ∈ OhE D := fun i j => by
      rw [topL, dite_eq_left ⟨i.2.trans_le had, j.2⟩]
      exact hc.1 _ _
    obtain ⟨S, -, he, -⟩ := id hG
    obtain ⟨k, hk, hkN⟩ := _root_.GlobalTheory.StdRead.IntLift.exists_lift e S he _ hN x hx
    have h1 : ∀ i j, (topL a W - invM k) i j ∈ hatId D 𝔪 := fun i j => by
      have := GlobalTheory.FunObj.StdDatum.mul_mem_hatId (sub_mem (hN i j) ((GlobalTheory.NormSum.mem_intG k).1 hk i j).2) (one_sub_eps_mod hG)
      convert this using 1
      rw [Matrix.sub_apply, invM]
      linear_combination -hkN i j
    obtain ⟨r, ⟨hr, hrk⟩, hu⟩ := hU k hk
    have h2 := (cong_iff hk h1).2 hrk
    rw [ite_eq_left hc, Finset.sum_eq_single r (fun s hs hsr => ?_) (fun h => (h hr).elim), ite_eq_left ⟨h2, hc.2⟩, mul_one,
      (value hG hK (hR r hr) h2).2]
    rw [ite_eq_right fun h => hsr (hu s ⟨hs, (cong_iff hk h1).1 h.1⟩), mul_zero]
  · rw [Finset.sum_eq_zero fun r hr => ?_]
    · split_ifs with h
      · rw [unitChar, dite_eq_right fun hx => hc ⟨h, hx⟩, map_zero]
      · rfl
    · rw [ite_eq_right fun h => hc ⟨⟨fun i j => ?_, h.2⟩, (value hG hK (hR r hr) h.1).1⟩, mul_zero]
      by_cases hi : i.1 < a
      · have := add_mem (int_of_hat (h.1 ⟨i.1, hi⟩ j)) ((GlobalTheory.NormSum.mem_intG r).1 (hR r hr) ⟨i.1, hi⟩ j).2
        rwa [Matrix.sub_apply, invM, sub_add_cancel, topL, dite_eq_left ⟨i.2, j.2⟩] at this
      · exact int_of_hat (h.2 i j (not_lt.1 hi))

theorem conj_stdFst_eq_sum : ∀ {D : D7} (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d), a ≤ d → ∀ (e : AE D) (𝔪 : Ideal (𝓞 D.host.E)), GoodMod e 𝔪 →
  ∀ ν : (AE D)ˣ →* Circle, KillsCong ν 𝔪 → ∀ β : GL (Fin S.rank) (EAf D), IsIntM β.val → IsIntM (β⁻¹).val →
  ∀ R : Finset (Formalism.MainNotions.StandardLatticesGL3.GA D a), (∀ r ∈ R, r ∈ intG D a) → (∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k)) →
  ∀ z : Formalism.MainNotions.StandardLatticesGL3.GA D a → Matrix (Fin d) (Fin a) D.host.E, (∀ r ∈ R, IsIntE (z r) ∧ Approx 𝔪 0 r (z r)) →
  (fun w => starRingEnd ℂ (stdFst ν e 𝔪 S T β 1 w)) =
    starRingEnd ℂ (unitChar ν e β.val) • ∑ r ∈ R, unitChar ν e (matE r) • cosInd e 𝔪 hS hT (z r) := by
  intro D S T a d hS hT had e 𝔪 hG ν hK β hβ hβ' R hR hU z hz
  subst hS hT
  funext t
  obtain ⟨SS, -, he, -⟩ := id hG
  let W : Matrix (Fin T.rank) (Fin S.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D) := Matrix.of fun i j => finQ D (t i j)
  have hW : ∀ i j, toEAf D (t i j) = toE D (W i j) := fun i j => (toE_finQ _).symm
  have hN : topL S.rank (Matrix.of fun i j => toEAf D (t i j)) = (topL S.rank W).map (toE D) := by
    ext i j
    rw [Matrix.map_apply, topL, topL, dite_eq_left ⟨i.2.trans_le had, j.2⟩, dite_eq_left ⟨i.2.trans_le had, j.2⟩]
    exact hW _ _
  have hc : ∀ r ∈ R, cosInd e 𝔪 rfl rfl (z r) t = if IsHalf e t then
      (if (∀ i j, (topL S.rank W - invM r) i j ∈ hatId D 𝔪) ∧ ∀ i j, S.rank ≤ i.1 → W i j ∈ hatId D 𝔪 then 1 else 0)
      else 0 := fun r hr => by
    rw [← ite_and, cosInd]
    refine if_congr (and_congr_right fun _ => ?_) rfl rfl
    rw [← coset_iff (one_sub_eps_mod hG) had (hz r hr).1 (hz r hr).2 W]
    refine forall₂_congr fun i j => ?_
    rw [← _root_.GlobalTheory.StdRead.IdealDict.inId_toE_iff, RingHom.map_sub, RingHom.map_mul, ← hW, toE_finQ, ← finQ_incA, toE_finQ]
    rfl
  have he_mul := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have he_int : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    GlobalTheory.IdemRes.toEAf_mem_of_finPart (GlobalTheory.AdIdem.idempotent_mem_intAE D _
      (by rw [← map_mul, he_mul]))
  rw [_root_.GlobalTheory.StdReadFrame.stdFst_frame S T ν e 𝔪 β hβ hβ' t,
    _root_.GlobalTheory.StdRead.CharMul.unitChar_mul ν e he_mul he_int _ β hβ hβ', hN]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl fun r hr => by rw [hc r hr]]
  by_cases ht : IsHalf e t
  · simp only [ht, true_and, ite_true]
    rw [sum_eq hG hK had hR hU W]
    simp only [hW, toE_int_iff, _root_.GlobalTheory.StdRead.IdealDict.inId_toE_iff]
    split_ifs
    · rw [map_mul, mul_comm]
    · rw [map_zero, mul_zero]
  · simp [ht]

end GlobalTheory.StdExpand

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedLiftInvariantExtensionLocalisation
section
open IsLocalRing

namespace GlobalTheory

theorem twisted_lift_to_localisation (A B A₂ : Type) [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B]
    [CommRing A₂] [IsLocalRing A₂] (G : Type) [Group G] [Finite G] [MulSemiringAction G B]
    [SMulCommClass G A B] [Algebra.IsInvariant A B G] (f : B →+* A₂) :
    IsLocalHom (f.comp (algebraMap A B)) → (∀ y : A₂, ∃ b s : B, IsUnit (f s) ∧ y * f s = f b) →
    (∀ b : B, f b = 0 → ∃ s : B, IsUnit (f s) ∧ s * b = 0) →
    ∀ (V' : Type) [CommRing V'] [IsLocalRing V'] (e₁ : A →+* V') (β : B →+* V'),
      IsLocalHom e₁ → β.comp (algebraMap A B) = e₁ →
      ∃ ev₂ : A₂ →+* V', IsLocalHom ev₂ ∧ ev₂.comp (f.comp (algebraMap A B)) = e₁ := by
  intro hfl hsurj hker V' _ _ e₁ β he₁ hβ
  set q : Ideal B := (maximalIdeal A₂).comap f with hq
  set c : Ideal B := (maximalIdeal V').comap β with hc
  haveI : q.IsPrime := Ideal.comap_isPrime f (maximalIdeal A₂)
  haveI : c.IsPrime := Ideal.comap_isPrime β (maximalIdeal V')
  have hqA : Ideal.under A q = maximalIdeal A := by
    ext a
    simp only [Ideal.under, Ideal.mem_comap, hq, mem_maximalIdeal, mem_nonunits_iff]
    rw [← RingHom.comp_apply, isUnit_map_iff (f.comp (algebraMap A B))]
  have hcA : Ideal.under A c = maximalIdeal A := by
    ext a
    simp only [Ideal.under, Ideal.mem_comap, hc, mem_maximalIdeal, mem_nonunits_iff]
    rw [← RingHom.comp_apply, hβ, isUnit_map_iff e₁]
  obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A B G c q (hcA.trans hqA.symm)
  set β' : B →+* V' := β.comp (MulSemiringAction.toRingHom G B σ⁻¹) with hβ'
  have hβ'q : ∀ b : B, b ∈ q ↔ ¬ IsUnit (β' b) := by
    intro b
    rw [hσ, Ideal.mem_pointwise_smul_iff_inv_smul_mem, hc, Ideal.mem_comap, mem_maximalIdeal,
      mem_nonunits_iff]
    rfl
  have hfq : ∀ b : B, b ∈ q ↔ ¬ IsUnit (f b) := by
    intro b
    rw [hq, Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
  have hβ'A : β'.comp (algebraMap A B) = e₁ := by
    rw [← hβ]
    ext a
    simp only [hβ', RingHom.comp_apply, MulSemiringAction.toRingHom_apply, smul_algebraMap]
  letI : Algebra B A₂ := f.toAlgebra
  haveI hloc : IsLocalization q.primeCompl A₂ := by
    rw [isLocalization_iff]
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨s, hs⟩
      have : s ∉ q := hs
      rw [hfq, not_not] at this
      exact this
    · intro z
      obtain ⟨b, s, hs, h⟩ := hsurj z
      have hs' : s ∈ q.primeCompl := by
        show s ∉ q
        rw [hfq, not_not]; exact hs
      exact ⟨(b, ⟨s, hs'⟩), h⟩
    · intro x y hxy
      have h0 : f (x - y) = 0 := by
        rw [map_sub]; exact sub_eq_zero.mpr hxy
      obtain ⟨s, hs, h⟩ := hker _ h0
      have hs' : s ∈ q.primeCompl := by
        show s ∉ q
        rw [hfq, not_not]; exact hs
      refine ⟨⟨s, hs'⟩, ?_⟩
      show s * x = s * y
      rw [mul_sub] at h
      exact sub_eq_zero.mp h
  have hunits : ∀ y : q.primeCompl, IsUnit (β' y) := by
    rintro ⟨s, hs⟩
    have : s ∉ q := hs
    rw [hβ'q, not_not] at this
    exact this
  have hcomp : (IsLocalization.lift hunits).comp f = β' :=
    IsLocalization.lift_comp (M := q.primeCompl) (S := A₂) hunits
  refine ⟨IsLocalization.lift hunits, ?_, ?_⟩
  · refine ⟨fun x hx => ?_⟩
    obtain ⟨b, s, hs, h⟩ := hsurj x
    have hsq : IsUnit (β' s) := by
      have : s ∉ q := by rw [hfq, not_not]; exact hs
      rw [hβ'q, not_not] at this
      exact this
    have hb : IsUnit (β' b) := by
      have h2 := congrArg (IsLocalization.lift hunits) h
      rw [map_mul, ← RingHom.comp_apply, ← RingHom.comp_apply, hcomp] at h2
      rw [← h2]
      exact hx.mul hsq
    have hfb : IsUnit (f b) := by
      have : b ∉ q := by rw [hβ'q, not_not]; exact hb
      rw [hfq, not_not] at this
      exact this
    rw [← h] at hfb
    exact isUnit_of_mul_isUnit_left hfb
  · rw [← RingHom.comp_assoc, hcomp, hβ'A]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCongruenceDetEqOneOfThreeLe
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

open Matrix Polynomial

namespace GlobalTheory.UnitaryCongruenceDetAny

theorem det_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E), 3 ≤ M → G.det ≠ 0 → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → IsUStab G Λ γ → (∀ x ∈ Λ, ∃ y ∈ Λ, (γ : Matrix (Fin r) (Fin r) E).mulVec x - x = M • y) → (γ : Matrix (Fin r) (Fin r) E).det = 1 := by
  intro E _ _ _ r M G Λ γ hM hG hfg hspan hst hcong
  classical
  obtain ⟨hherm, -⟩ := hst
  set g : Matrix (Fin r) (Fin r) E := (γ : Matrix (Fin r) (Fin r) E) with hg
  let φ : E →+* AlgebraicClosure E := algebraMap E (AlgebraicClosure E)
  have hM0 : (M : AlgebraicClosure E) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have hME : (M : E) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  set A : Matrix (Fin r) (Fin r) E := (M : E)⁻¹ • (g - 1) with hA
  have hAΛ : ∀ x ∈ Λ, A *ᵥ x ∈ Λ := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hcong x hx
    have : A *ᵥ x = y := by
      rw [hA, smul_mulVec, sub_mulVec, one_mulVec, hxy, ← Nat.cast_smul_eq_nsmul E,
        smul_smul, inv_mul_cancel₀ hME, one_smul]
    rw [this]; exact hy
  have hAmap : A.map φ = (M : AlgebraicClosure E)⁻¹ • (g.map φ - 1) := by
    ext i j
    by_cases hij : i = j <;> simp [hA, Matrix.one_apply, hij]
  have hroot : ∀ l ∈ (g.map φ).charpoly.roots,
      IsIntegral ℤ ((l - 1) / (M : AlgebraicClosure E)) := by
    intro l hl
    have hdet : (scalar (Fin r) l - g.map φ).det = 0 := by
      rw [← Matrix.eval_charpoly]; exact (mem_roots'.1 hl).2
    obtain ⟨u, hu, hu0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
    apply GlobalTheory.UnitaryCongruenceDet.isIntegral_of_left_eigen A Λ hfg hspan hAΛ _ u hu
    have hgu : u ᵥ* g.map φ = l • u := by
      rw [vecMul_sub, sub_eq_zero] at hu0
      rw [← hu0]
      funext j
      simp [scalar_apply, vecMul_diagonal, mul_comm]
    rw [hAmap, vecMul_smul, vecMul_sub, vecMul_one, hgu]
    funext j
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
  obtain ⟨z, hz, hprod⟩ := GlobalTheory.UnitaryCongruenceDet.prod_eq_one_add M hM0 _ hroot
  have hφdet : φ g.det = 1 + M * z := by
    rw [RingHom.map_det, ← hprod]
    exact Matrix.det_eq_prod_roots_charpoly _

  set z₀ : E := (g.det - 1) / (M : E) with hz₀
  have hφz : φ z₀ = z := by
    rw [hz₀, map_div₀, map_sub, map_one, map_natCast, hφdet]
    field_simp
    ring
  have hz₀int : IsIntegral ℤ z₀ := by
    have h1 : IsIntegral ℤ (φ z₀) := by rw [hφz]; exact hz
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ E (AlgebraicClosure E))
      (algebraMap E (AlgebraicClosure E)).injective).1 h1

  have hcc := GlobalTheory.UnitaryCongruenceDet.det_mul_cc_det G g hG hherm
  have hnorm : ∀ ψ : E →+* ℂ, ‖ψ g.det‖ = 1 := by
    intro ψ
    have h1 := congrArg ψ hcc
    rw [map_mul, map_one, cc, IsCMField.complexEmbedding_complexConj, Complex.mul_conj] at h1
    have h2 : Complex.normSq (ψ g.det) = 1 := by exact_mod_cast h1
    rw [Complex.normSq_eq_norm_sq] at h2
    exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 (h2.trans (one_pow 2).symm)

  have hsmall : ∀ ψ : E →+* ℂ, ‖ψ z₀‖ < 1 := by
    intro ψ
    have hMR : (3 : ℝ) ≤ M := by exact_mod_cast hM
    rw [hz₀, map_div₀, map_sub, map_one, map_natCast, norm_div, Complex.norm_natCast,
      div_lt_one (by linarith)]
    calc ‖ψ g.det - 1‖ ≤ ‖ψ g.det‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [hnorm, norm_one]; norm_num
      _ < M := by linarith
  have hz0 : z₀ = 0 := by
    by_contra hne
    let α : 𝓞 E := ⟨z₀, hz₀int⟩
    have hα : α ≠ 0 := by
      intro h; apply hne
      have := congrArg (fun a : 𝓞 E => (a : E)) h
      exact this
    obtain ⟨σ, hσ⟩ := NumberField.exists_conjugate_one_le_norm hα
    exact absurd hσ (not_le.2 (hsmall σ))
  have : g.det - 1 = 0 := by
    have h := hz0
    rw [hz₀, div_eq_zero_iff] at h
    exact h.resolve_right hME
  exact sub_eq_zero.1 this

end GlobalTheory.UnitaryCongruenceDetAny
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VariableMatrixDetPolyPowMulMemDualWeyl
section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameRead

theorem detPol_mem_dualWeyl_one (R : Type) [CommRing R] (n : ℕ) :
    detPol R n ∈ dualWeyl R n n (fun _ => 1) := by
  have h := Formalism.GradedWeylDivisibility.bidetMem R n n 1 (fun _ => n) (fun _ => le_refl n) (fun _ => id)
  have hb : bideterminant R (r := n) (n := n) (fun _ : Fin 1 => n) (fun _ => le_refl n) (fun _ => id) = detPol R n := by
    simp [bideterminant, initMinor, detPol]
  have hs : shapeDeg (n := n) (fun _ : Fin 1 => n) = fun _ => 1 := by
    funext t
    simp [shapeDeg, t.isLt]
  rw [hb, hs] at h
  exact h

theorem detPol_pow_mul_mem_dualWeyl : ∀ (R : Type) [CommRing R] (n k : ℕ) (ν : Fin n → ℕ) (f : MvPolynomial (Fin n × Fin n) R), f ∈ dualWeyl R n n ν → detPol R n ^ k * f ∈ dualWeyl R n n fun a => ν a + k := by
  intro R _ n k ν f hf
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    have h := (Formalism.GradedWeylDivisibility.dualWeylMul R n n (fun _ => 1) (fun a => ν a + k) (detPol R n) (detPol R n ^ k * f)).1
      (detPol_mem_dualWeyl_one R n) ih
    have he : ((fun _ => 1) + fun a => ν a + k) = fun a : Fin n => ν a + (k + 1) := by
      funext a; simp only [Pi.add_apply]; omega
    rw [he, ← mul_assoc, ← pow_succ'] at h
    exact h

end GlobalTheory.FrameRead
end

