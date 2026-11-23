module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0047
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsGraphGenTwistBundleZero
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0043
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0012

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeVanish
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section Compare

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

theorem coe_d_sub (F : SubSystem S x E) {i : ℕ} (t : Cech.Cochain (fun I : Chart x => ↥(F.sub I)) i)
    (J : Cech.Idx (support x) (i + 1)) :
    ((Cech.d (fun I : Chart x => ↥(F.sub I)) F.res i t J : F.sub J.1) : E) =
      ∑ j : J.1.1, Cech.sgn J.1.1 j • (t (Cech.face J j) : E) := by
  rw [Cech.d_apply, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Submodule.coe_smul_of_tower]
  rfl

variable (M : FinGradedSub (S := S) (x := x) E) (c : ℤ)

def liftTilde (I : StdCell N) (hI : I.1 ⊆ support x) (y : M.tilde c ⟨I.1, I.2.1, hI⟩) :
    LocMod S N M.coneSubE I.1 :=
  Classical.choose (exists_locConeE_eq M c I hI y.2)

theorem liftTilde_mem (I : StdCell N) (hI : I.1 ⊆ support x) (y : M.tilde c ⟨I.1, I.2.1, hI⟩) :
    liftTilde M c I hI y ∈ degLoc M.coneGradedE c I :=
  (Classical.choose_spec (exists_locConeE_eq M c I hI y.2)).1

theorem locConeE_liftTilde (I : StdCell N) (hI : I.1 ⊆ support x) (y : M.tilde c ⟨I.1, I.2.1, hI⟩) :
    locConeE M I.1 hI (liftTilde M c I hI y) = singleE S x E c y :=
  (Classical.choose_spec (exists_locConeE_eq M c I hI y.2)).2

def liftCochain {i : ℕ} (t : Cech.Cochain (fun I : Chart x => ↥((M.tildeSys c).sub I)) i) :
    Cech.Cochain (locSys S N M.coneSubE) i := fun J =>
  if hJ : J.1.1 ⊆ support x then liftTilde M c J.1 hJ (t ⟨⟨J.1.1, J.1.2.1, hJ⟩, J.2⟩) else 0

theorem liftCochain_of {i : ℕ} (t : Cech.Cochain (fun I : Chart x => ↥((M.tildeSys c).sub I)) i)
    (J : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) i) (hJ : J.1.1 ⊆ support x) :
    liftCochain M c t J = liftTilde M c J.1 hJ (t ⟨⟨J.1.1, J.1.2.1, hJ⟩, J.2⟩) :=
  dif_pos hJ

theorem liftCochain_mem {i : ℕ} (t : Cech.Cochain (fun I : Chart x => ↥((M.tildeSys c).sub I)) i) :
    liftCochain M c t ∈ Cech.Cdeg (locSys S N M.coneSubE) (degLoc M.coneGradedE c) i := by
  intro J _
  by_cases hJ : J.1.1 ⊆ support x
  · rw [liftCochain_of M c t J hJ]
    exact liftTilde_mem M c _ hJ _
  · change (if hJ : J.1.1 ⊆ support x then _ else 0) ∈ _
    rw [dite_eq_right hJ]
    exact zero_mem _

theorem locConeE_d {i : ℕ} (z : Cech.Cochain (locSys S N M.coneSubE) i)
    (K : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) (i + 1)) (hK : K.1.1 ⊆ support x) :
    locConeE M K.1.1 hK (Cech.d (locSys S N M.coneSubE) locResS i z K) =
      ∑ j : K.1.1, Cech.sgn K.1.1 j • locConeE M (Cech.face K j).1.1
        ((Cech.face_subset K j).trans hK) (z (Cech.face K j)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Cech.d_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul]
  congr 1
  exact locConeE_locRes M (Cech.face_subset K j) hK _

theorem d_liftCochain {i : ℕ} (t : Cech.Cochain (fun I : Chart x => ↥((M.tildeSys c).sub I)) (i + 1))
    (ht : Cech.d (fun I : Chart x => ↥((M.tildeSys c).sub I)) (M.tildeSys c).res (i + 1) t = 0) :
    Cech.d (locSys S N M.coneSubE) locResS (i + 1) (liftCochain M c t) = 0 := by
  funext K
  change _ = 0
  by_cases hK : K.1.1 ⊆ support x
  · apply locConeE_injective M K.1.1 hK
    rw [locConeE_d M (liftCochain M c t) K hK, map_zero]
    have h0 := coe_d_sub (M.tildeSys c) t ⟨⟨K.1.1, K.1.2.1, hK⟩, K.2⟩
    rw [ht] at h0
    calc ∑ j : K.1.1, Cech.sgn K.1.1 j • locConeE M (Cech.face K j).1.1
          ((Cech.face_subset K j).trans hK) (liftCochain M c t (Cech.face K j))
        = ∑ j : K.1.1, Cech.sgn K.1.1 j • singleE S x E c
            (t (Cech.face (⟨⟨K.1.1, K.1.2.1, hK⟩, K.2⟩ : Cech.Idx (support x) (i + 1 + 1)) j) : E) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [liftCochain_of M c t _ ((Cech.face_subset K j).trans hK)]
          congr 1
          exact locConeE_liftTilde M c _ _ _
      _ = singleE S x E c (∑ j : K.1.1, Cech.sgn K.1.1 j •
            (t (Cech.face (⟨⟨K.1.1, K.1.2.1, hK⟩, K.2⟩ : Cech.Idx (support x) (i + 1 + 1)) j) : E)) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_zsmul]
      _ = 0 := by
          rw [← h0]
          exact map_zero _
  · haveI := locModE_subsingleton (S := S) M (Finset.not_subset.mp hK).choose_spec.1
      (by simpa [mem_support] using (Finset.not_subset.mp hK).choose_spec.2)
    exact Subsingleton.elim _ _

theorem tildeSys_H_subsingleton (k : ℕ) (h : Subsingleton (cohom M.coneGradedE (k + 1) c)) :
    Subsingleton ((M.tildeSys c).H (k + 1)) := by
  unfold cohom Cech.Hdeg at h
  rw [Submodule.Quotient.subsingleton_iff, Submodule.eq_top_iff'] at h
  unfold SubSystem.H Cech.H
  set_option synthInstance.maxHeartbeats 200000 in
    refine Submodule.Quotient.subsingleton_iff.mpr (Submodule.eq_top_iff'.mpr ?_)
  rintro ⟨t, ht⟩
  rw [Submodule.mem_comap]
  change t ∈ LinearMap.range (Cech.d _ (M.tildeSys c).res k)
  have hz : liftCochain M c t ∈
      Cech.cocyDeg (locSys S N M.coneSubE) (degLoc M.coneGradedE c) locResS (k + 1) :=
    ⟨d_liftCochain M c t (LinearMap.mem_ker.mp ht), liftCochain_mem M c t⟩
  have hb := h ⟨_, hz⟩
  rw [Submodule.mem_comap] at hb
  change liftCochain M c t ∈ (Cech.Cdeg (locSys S N M.coneSubE) (degLoc M.coneGradedE c) k).map
    (Cech.d (locSys S N M.coneSubE) locResS k) at hb
  obtain ⟨y, hy, hyz⟩ := hb
  have hu : ∀ I : Cech.Idx (support x) k, coeffE S x E c (locConeE M I.1.1 I.1.2.2
      (y ⟨⟨I.1.1, I.1.2.1, Finset.subset_univ _⟩, I.2⟩)) ∈ (M.tildeSys c).sub I.1 := fun I => by
    obtain ⟨v, hv, hyv⟩ := locConeE_degLoc M c _ I.1.2.2
      (hy ⟨⟨I.1.1, I.1.2.1, Finset.subset_univ _⟩, I.2⟩ (Set.mem_univ _))
    rw [hyv, coeffE_singleE_same]
    exact hv
  refine ⟨fun I => ⟨_, hu I⟩, ?_⟩
  funext J
  apply Subtype.ext
  rw [coe_d_sub]
  have e1 := locConeE_liftTilde M c ⟨J.1.1, J.1.2.1, Finset.subset_univ _⟩ J.1.2.2 (t J)
  have e2 := congrFun hyz ⟨⟨J.1.1, J.1.2.1, Finset.subset_univ _⟩, J.2⟩
  rw [liftCochain_of M c t _ J.1.2.2] at e2
  rw [← coeffE_singleE_same (S := S) (x := x) c (t J : E), ← e1, ← e2]
  refine Eq.trans ?_ (congrArg (coeffE S x E c)
    (locConeE_d M y ⟨⟨J.1.1, J.1.2.1, Finset.subset_univ _⟩, J.2⟩ J.1.2.2)).symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul]
  rfl

end Compare

theorem TildeVanish.proof (h : SerreVanish.Statement.{u, v}) : TildeVanish.Statement.{u, v, w} := by
  intro S _ _ Ω _ _ N x E _ _ _ _ M
  obtain ⟨c₀, hc₀⟩ := h S N M.coneSubE M.coneGradedE M.coneSubE_finite
  refine ⟨c₀, fun i hi c hc => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  exact tildeSys_H_subsingleton M c k (hc₀ (k + 1) hi c hc)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RestrLenPrimeOfEqFinrank
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial Filter

noncomputable section

universe u w

section Lemmas

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem foldl_twist_twistSys {n : ℕ} (b : Fin n → ℤ) (l : List (Fin n)) (a : ℤ) :
    l.foldl (fun F i => F.twist (twistSys S x (b i))) (twistSys S x a) =
      twistSys S x (a + (l.map b).sum) := by
  induction l generalizing a with
  | nil => simp
  | cons i l ih =>
    rw [List.foldl_cons, twistSys_twist_eq_add, ih, List.map_cons, List.sum_cons, add_assoc]

theorem tensorSub_twistSys {n : ℕ} (b : Fin n → ℤ) (T : Finset (Fin n)) :
    tensorSub (fun i => twistSys S x (b i)) T = twistSys S x (∑ i ∈ T, b i) := by
  classical
  rw [tensorSub, foldl_twist_twistSys, zero_add,
    ← List.sum_toFinset b ((List.nodup_finRange n).filter _)]
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  simp

theorem interSum_twistSys (pp : Ideal (Poly S N)) {n : ℕ} (b : Fin n → ℤ) (c : ℕ) :
    interSum pp (fun i => twistSys S x (b i)) c =
      ∑ T : Finset (Fin n), (-1) ^ (n - T.card) * restrLen pp (twistSys S x (∑ i ∈ T, b i + c)) := by
  unfold interSum
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [tensorSub_twistSys, twistSys_twist_eq_add]

end Lemmas

section Differences

variable {K : Type*}

theorem foldr_diffStep_eq {n : ℕ} (bs : Fin n → K → ℤ) (h : (K → ℤ) → ℤ) (l : List (Fin n))
    (hl : l.Nodup) (m : K → ℤ) :
    (l.map bs).foldr NumbersDVR.diffStep h m =
      ∑ T ∈ l.toFinset.powerset, (-1) ^ T.card * h (m - ∑ i ∈ T, bs i) := by
  classical
  induction l generalizing m with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ha, hl'⟩ := List.nodup_cons.mp hl
    have ha' : a ∉ l.toFinset := fun h' => ha (List.mem_toFinset.mp h')
    rw [List.map_cons, List.foldr_cons, List.toFinset_cons, Finset.sum_powerset_insert ha']
    change (l.map bs).foldr NumbersDVR.diffStep h m - (l.map bs).foldr NumbersDVR.diffStep h (m - bs a) = _
    rw [ih hl' m, ih hl' (m - bs a), sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun t ht => ?_
    have hat : a ∉ t := fun h' => ha' (Finset.mem_powerset.mp ht h')
    rw [Finset.card_insert_of_notMem hat, Finset.sum_insert hat, pow_succ, sub_sub]
    ring

theorem mixedDiff_eq_sum {n : ℕ} (bs : Fin n → K → ℤ) (h : (K → ℤ) → ℤ) (m : K → ℤ) :
    NumbersDVR.mixedDiff bs h m = ∑ T : Finset (Fin n), (-1) ^ T.card * h (m - ∑ i ∈ T, bs i) := by
  classical
  rw [NumbersDVR.mixedDiff, List.ofFn_eq_map, foldr_diffStep_eq bs h _ (List.nodup_finRange n),
    List.toFinset_finRange, Finset.powerset_univ]

end Differences

section Point

variable {k : Type u} [Field k] {K' : Type w} [Field K'] [Algebra k K'] {N : ℕ}

theorem restrLen_primeOf_eq_finrank (y : Fin (N + 1) → K') {j : Fin (N + 1)} (hyj : y j ≠ 0)
    (F : SubSystem k y K') : restrLen (primeOf (S := k) y) F = Module.finrank k F.secs := by
  have hid : ∀ I : Chart y, idealMod (x := y) (primeOf (S := k) y) I = ⊥ := by
    intro I
    refine Submodule.span_eq_bot.mpr ?_
    rintro _ ⟨f, s, e, hf, _, hfe, _, rfl⟩
    rw [(mem_primeOf_of_isHomogeneous y hfe).mp hf, zero_div]
  have hbot : ∀ I : Chart y, (F.twist (idealSys y (primeOf (S := k) y))).sub I = ⊥ := by
    intro I
    refine Submodule.span_eq_bot.mpr ?_
    rintro _ ⟨q, hq, z, _, rfl⟩
    have hq' : q ∈ idealMod (x := y) (primeOf (S := k) y) I := hq
    rw [hid I, Submodule.mem_bot] at hq'
    rw [hq', zero_smul]
  have hsecs : (F.twist (idealSys y (primeOf (S := k) y))).secs = ⊥ := by
    refine eq_bot_iff.mpr fun z hz => ?_
    have h1 := (Submodule.mem_iInf _).mp hz (singleChart hyj)
    rw [Submodule.restrictScalars_mem, hbot] at h1
    exact h1
  unfold restrLen
  rw [hsecs, Submodule.comap_bot, Submodule.ker_subtype,
    (Submodule.quotEquivOfEqBot (⊥ : Submodule k F.secs) rfl).length_eq, Module.length_eq_rank]
  rfl

end Point

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

