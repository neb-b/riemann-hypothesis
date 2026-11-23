module

public import Formalism.GaussJetBounds.Bundle0001
public import Formalism.GaussJetBounds.StatementE
public import Formalism.GaussJetBounds.GaussJetProofs.SubstitutionWeightBound
public import Formalism.GaussJetBounds.GaussJetProofs.PureCrossTermWeight
public import Formalism.GaussJetBounds.GaussJetProofs.Bundle0002
public import Formalism.GaussJetBounds.GaussJetProofs.Bundle0001
public import Formalism.IncomingBounds.WeightIdentities
public import Formalism.GaussJetBounds.Bundle0004
public import Formalism.GaussJetBounds.GaussJetProofs.FrameCoeffMulLin
public import Formalism.GaussJetBounds.GaussJetProofs.CapacityLeReachCapacity

@[expose] public section

-- bundled from Formalism.GaussJetBounds.GaussJetProofs.ThmAJet
section
noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

section Collapse

variable {K : Type u} [NormedField K] {ι σ : Type*} (lt : ι → σ)

def jetHom (n : σ →₀ ℕ) (f : MvPowerSeries ι K) : Prop :=
  ∀ m, MvPowerSeries.coeff m f ≠ 0 → m.mapDomain lt = n

theorem jetHom_one : jetHom lt 0 (1 : MvPowerSeries ι K) := by
  classical
  intro m hm
  rw [MvPowerSeries.coeff_one] at hm
  split_ifs at hm with h
  · subst h; simp
  · exact absurd rfl hm

theorem jetHom_mul {n1 n2 : σ →₀ ℕ} {f g : MvPowerSeries ι K} (hf : jetHom lt n1 f)
    (hg : jetHom lt n2 g) : jetHom lt (n1 + n2) (f * g) := by
  classical
  intro m hm
  rw [MvPowerSeries.coeff_mul] at hm
  obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have h1 : MvPowerSeries.coeff p.1 f ≠ 0 := left_ne_zero_of_mul hne
  have h2 : MvPowerSeries.coeff p.2 g ≠ 0 := right_ne_zero_of_mul hne
  rw [← hp, Finsupp.mapDomain_add, hf _ h1, hg _ h2]

theorem jetHom_pow {n : σ →₀ ℕ} {f : MvPowerSeries ι K} (hf : jetHom lt n f) (k : ℕ) :
    jetHom lt (k • n) (f ^ k) := by
  induction k with
  | zero => simpa using jetHom_one (K := K) lt
  | succ k ih => rw [pow_succ, succ_nsmul]; exact jetHom_mul lt ih hf

theorem jetHom_prod {α : Type*} (s : Finset α) (n : α → σ →₀ ℕ) (F : α → MvPowerSeries ι K)
    (h : ∀ a ∈ s, jetHom lt (n a) (F a)) : jetHom lt (∑ a ∈ s, n a) (∏ a ∈ s, F a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using jetHom_one (K := K) lt
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact jetHom_mul lt (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem jetHom_lin [Fintype ι] (c : ι → K) (t : σ) (hc : ∀ i, c i ≠ 0 → lt i = t) :
    jetHom lt (Finsupp.single t 1) (∑ i, MvPowerSeries.C (c i) * MvPowerSeries.X i) := by
  classical
  intro m hm
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X] at hm
  obtain ⟨i, -, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  split_ifs at hne with h
  · subst h; rw [Finsupp.mapDomain_single, hc i (left_ne_zero_of_mul hne)]
  · simp at hne

theorem jetHom_substProd (a : σ → MvPowerSeries ι K)
    (ha : ∀ t, jetHom lt (Finsupp.single t 1) (a t)) (n : σ →₀ ℕ) :
    jetHom lt n (n.prod fun s e => a s ^ e) := by
  classical
  have h := jetHom_prod lt n.support (fun s => n s • Finsupp.single s 1) (fun s => a s ^ n s)
    fun s _ => jetHom_pow lt (ha s) (n s)
  have hd : ∑ s ∈ n.support, n s • Finsupp.single s 1 = n := by
    simp_rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    exact Finsupp.sum_single n
  rw [hd] at h
  simpa [Finsupp.prod] using h

end Collapse

theorem jet_collapse {K : Type u} [NormedField K] [IsUltrametricDist K] {d N0 N1 : ℕ} [NeZero d]
    {ι : Type*}
    [Fintype ι] [DecidableEq ι] (lt : ι → ZMod d) (M : ZV d N0 N1 → ι → K)
    (hM1 : ∀ x i, ‖M x i‖ ≤ 1) (hMlt : ∀ x i, M x i ≠ 0 → lt i = x.1)
    (be : MvPowerSeries (ZMod d) K) (m : ι →₀ ℕ) :
    ‖MvPowerSeries.coeff m (bSum M be)‖ ≤ ‖MvPowerSeries.coeff (m.mapDomain lt) be‖ := by
  classical
  unfold bSum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun ab _ => ?_
  have hlin0 : ∀ s, MvPowerSeries.constantCoeff (linSub M (s, ab.1, ab.2)) = 0 := fun s => by
    simp [linSub]
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero hlin0
  have hhom : ∀ t, jetHom lt (Finsupp.single t 1) (linSub M (t, ab.1, ab.2)) := fun t =>
    jetHom_lin lt _ t fun i hi => hMlt _ i hi
  have hlinI : ∀ t, WtGe (1 : ℝ) (fun _ : ι => (0 : ℝ)) 0 (linSub M (t, ab.1, ab.2)) := by
    intro t
    unfold linSub
    refine wtGe_sum one_pos _ _ fun i _ => ?_
    simpa using wtGe_CX (K := K) one_pos (fun _ : ι => (0 : ℝ)) i (hM1 (t, ab.1, ab.2) i)
  rw [MvPowerSeries.coeff_subst hs, finsum_eq_single _ (m.mapDomain lt)]
  · rw [smul_eq_mul, norm_mul]
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    have hp := wtGe_prod (K := K) one_pos (r := fun _ : ι => (0 : ℝ)) (m.mapDomain lt).support
      (fun s => ((m.mapDomain lt) s : ℝ) * 0)
      (fun s => linSub M (s, ab.1, ab.2) ^ (m.mapDomain lt) s)
      (fun s _ => wtGe_pow one_pos (hlinI s) _) m
    rw [monoWtGe_iff, Real.one_rpow] at hp
    simpa [Finsupp.prod] using hp
  · intro n hn
    have h0 : MvPowerSeries.coeff m (n.prod fun s e => linSub M (s, ab.1, ab.2) ^ e) = 0 := by
      by_contra h
      exact hn (jetHom_substProd lt (fun s => linSub M (s, ab.1, ab.2)) hhom n m h).symm
    rw [h0, smul_zero]

theorem jet_parity {d : ℕ} [NeZero d] (hde : Even d) {s s' : ZMod d} {α β : ℕ}
    (hs : s.val % 2 = 0) (hs' : s'.val % 2 = 1) (h : s + (α : ZMod d) = s' + (β : ZMod d)) :
    Odd (α + β) := by
  have h' : ((s.val + α : ℕ) : ZMod d) = ((s'.val + β : ℕ) : ZMod d) := by
    push_cast; rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  rw [ZMod.natCast_eq_natCast_iff] at h'
  have h2 := Nat.ModEq.of_dvd (even_iff_two_dvd.mp hde) h'
  unfold Nat.ModEq at h2
  rw [Nat.odd_iff]
  omega

theorem jet_bipower {d : ℕ} [NeZero d] (hde : Even d) {l : ℕ} (hl : 2 ≤ l) {t1 t2 : ZMod d}
    {α β : ℕ} (h : IsBiPower l (Finsupp.single t1 (l ^ α) + Finsupp.single t2 (l ^ β))) :
    t1 ≠ t2 ∧ t1 + (α : ZMod d) = t2 + (β : ZMod d) ∧ Odd (α + β) := by
  classical
  obtain ⟨s, s', α', β', hs, hs', -, heq, hn⟩ := h
  have hss : s ≠ s' := by rintro rfl; omega
  have hpar := jet_parity hde hs hs' heq
  have hpos : ∀ k : ℕ, l ^ k ≠ 0 := fun k => pow_ne_zero _ (by omega)
  have hinj : ∀ a b : ℕ, l ^ a = l ^ b → a = b := fun a b hab =>
    Nat.pow_right_injective hl hab
  have F1 : (Finsupp.single t1 (l ^ α) + Finsupp.single t2 (l ^ β)) s = l ^ α' := by
    rw [hn]; simp [hss]
  have F2 : (Finsupp.single t1 (l ^ α) + Finsupp.single t2 (l ^ β)) s' = l ^ β' := by
    rw [hn]; simp [Ne.symm hss]
  have F3 : ∀ t, (Finsupp.single t1 (l ^ α) + Finsupp.single t2 (l ^ β)) t ≠ 0 →
      t = s ∨ t = s' := by
    intro t ht
    rw [hn] at ht
    by_contra hc
    simp only [not_or] at hc
    apply ht
    simp [Ne.symm hc.1, Ne.symm hc.2]
  have G3 : ∀ t, (Finsupp.single t1 (l ^ α) + Finsupp.single t2 (l ^ β)) t ≠ 0 →
      t = t1 ∨ t = t2 := by
    intro t ht
    by_contra hc
    simp only [not_or] at hc
    apply ht
    simp [Ne.symm hc.1, Ne.symm hc.2]
  have ht12 : t1 ≠ t2 := by
    rintro rfl
    have a := G3 s (by rw [F1]; exact hpos _)
    have b := G3 s' (by rw [F2]; exact hpos _)
    simp only [or_self] at a b
    exact hss (a.trans b.symm)
  have H1 : (Finsupp.single t1 (l ^ α) + Finsupp.single t2 (l ^ β)) t1 = l ^ α := by
    simp [ht12]
  have H2 : (Finsupp.single t1 (l ^ α) + Finsupp.single t2 (l ^ β)) t2 = l ^ β := by
    simp [Ne.symm ht12]
  refine ⟨ht12, ?_⟩
  rcases F3 t1 (by rw [H1]; exact hpos _) with h1 | h1 <;>
    rcases F3 t2 (by rw [H2]; exact hpos _) with h2 | h2
  · exact absurd (h1.trans h2.symm) ht12
  · subst h1 h2
    have e1 := hinj _ _ (H1.symm.trans F1)
    have e2 := hinj _ _ (H2.symm.trans F2)
    subst e1 e2
    exact ⟨heq, hpar⟩
  · subst h1 h2
    have e1 := hinj _ _ (H1.symm.trans F2)
    have e2 := hinj _ _ (H2.symm.trans F1)
    subst e1 e2
    exact ⟨heq.symm, by rwa [add_comm]⟩
  · exact absurd (h1.trans h2.symm) ht12

theorem jet_rowRad_ge {d : ℕ} {ι : Type} (l : ℕ) (sig eps : ZMod d → ℝ) (lt : ι → ZMod d)
    (isTop : ι → Bool) (spec : ι → Option (ZMod d × ℤ)) (i : ι) (hi : isTop i = false) :
    sig (lt i) ≤ rowRad l sig eps lt isTop spec i := by
  unfold rowRad
  rw [if_neg (by simp [hi])]
  rcases spec i with _ | ⟨s, j⟩
  · exact le_rfl
  · dsimp only
    split_ifs
    · exact le_max_left _ _
    · exact le_max_left _ _

theorem jet_rowRad_nonneg {d : ℕ} {ι : Type} (l : ℕ) (sig eps : ZMod d → ℝ) (lt : ι → ZMod d)
    (isTop : ι → Bool) (spec : ι → Option (ZMod d × ℤ)) (hs : ∀ s, 0 ≤ sig s)
    (he : ∀ s, 0 ≤ eps s) (i : ι) : 0 ≤ rowRad l sig eps lt isTop spec i := by
  cases hi : isTop i
  · exact (hs _).trans (jet_rowRad_ge l sig eps lt isTop spec i hi)
  · unfold rowRad; rw [if_pos hi]; exact he _

theorem jet_rowRad_top {d : ℕ} {ι : Type} (l : ℕ) (sig eps : ZMod d → ℝ) (lt : ι → ZMod d)
    (isTop : ι → Bool) (spec : ι → Option (ZMod d × ℤ)) (i : ι) (hi : isTop i = true) :
    rowRad l sig eps lt isTop spec i = eps (lt i) := by
  unfold rowRad; rw [if_pos hi]

theorem jet_rowRad_spec {d : ℕ} {ι : Type} (l : ℕ) (sig eps : ZMod d → ℝ) (lt : ι → ZMod d)
    (isTop : ι → Bool) (spec : ι → Option (ZMod d × ℤ)) (i : ι) (hi : isTop i = false)
    {s0 : ZMod d} {j : ℤ} (hs : spec i = some (s0, j)) :
    rowRad l sig eps lt isTop spec i = if 0 < j then max (sig (lt i)) (1 - (l : ℝ) ^ j.toNat * eps s0)
      else max (sig (lt i)) ((l : ℝ) ^ (-j).toNat)⁻¹ := by
  unfold rowRad
  rw [if_neg (by simp [hi]), hs]

end Formalism.DworkPowerSeriesWeights
end
end

-- bundled from Formalism.GaussJetBounds.GaussJetProofs.Transfer
section
noncomputable section
open scoped BigOperators

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds MvPowerSeries

namespace Transfer

section Maps

variable {F K : Type} [Field F] [Field K] (φ : F →+* K) {d : ℕ}

theorem map_substZero (s : ZMod d) : map φ (s0 (K := F) s) = s0 s := by
  simp [s0]
theorem map_substOne (s : ZMod d) : map φ (s1 (K := F) s) = s1 s := by
  unfold s1
  split_ifs <;> simp
theorem map_substTwo (s : ZMod d) : map φ (s2 (K := F) s) = s2 s := by
  unfold s2
  split_ifs <;> simp
theorem map_substOne' (s : ZMod d) : map φ (s1' (K := F) s) = s1' s := by
  unfold s1'
  split_ifs <;> simp
theorem map_substTwo' (s : ZMod d) : map φ (s2' (K := F) s) = s2' s := by
  unfold s2'
  split_ifs <;> simp

theorem constantCoeff_substZero (s : ZMod d) : constantCoeff (s0 (K := F) s) = 0 := by
  simp [s0]
theorem constantCoeff_substOne (s : ZMod d) : constantCoeff (s1 (K := F) s) = 0 := by
  unfold s1
  split_ifs <;> simp
theorem constantCoeff_substTwo (s : ZMod d) : constantCoeff (s2 (K := F) s) = 0 := by
  unfold s2
  split_ifs <;> simp
theorem constantCoeff_substOne' (s : ZMod d) : constantCoeff (s1' (K := F) s) = 0 := by
  unfold s1'
  split_ifs <;> simp
theorem constantCoeff_substTwo' (s : ZMod d) : constantCoeff (s2' (K := F) s) = 0 := by
  unfold s2'
  split_ifs <;> simp

theorem map_torus (l : ℕ) (ζ : F) (s : ZMod d) :
    map φ (torus l ζ s) = torus l (φ ζ) s := by
  simp [torus]

theorem cc_torus (l : ℕ) (ζ : F) (s : ZMod d) : constantCoeff (torus l ζ s) = 0 := by
  simp [torus]

theorem map_letterLog (l : ℕ) (x : V2 d) :
    map φ (letterLog (K := F) l x) = letterLog l x := by
  ext n
  rw [MvPowerSeries.coeff_map]
  change φ (letterLog (K := F) l x n) = letterLog (K := K) l x n
  simp only [letterLog]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> simp

theorem cc_letterLog (l : ℕ) (x : V2 d) : constantCoeff (letterLog (K := F) l x) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  change letterLog (K := F) l x 0 = 0
  simp only [letterLog]
  refine Finset.sum_eq_zero fun e he => ?_
  have he0 : e = 0 := by simpa using he
  subst he0
  rw [if_neg]
  intro h
  have h1 := Finsupp.single_eq_zero.mp h.symm
  simp at h1

theorem map_entLog {N0 N1 : ℕ} (l : ℕ) (x : ZV d N0 N1) :
    map φ (entLog (K := F) l x) = entLog l x := by
  ext n
  rw [MvPowerSeries.coeff_map]
  change φ (entLog (K := F) l x n) = entLog (K := K) l x n
  simp only [entLog]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> simp

variable [NeZero d]

theorem map_defectOne (be : MvPowerSeries (ZMod d) F) : map φ (de1 be) = de1 (map φ be) := by
  have hs : ∀ (a : ZMod d → MvPowerSeries (V2 d) F), (∀ s, MvPowerSeries.constantCoeff (a s) = 0) →
      MvPowerSeries.map φ (MvPowerSeries.subst a be) =
        MvPowerSeries.subst (fun s => MvPowerSeries.map φ (a s)) (MvPowerSeries.map φ be) :=
    fun a ha => MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) be
  unfold de1
  rw [map_sub, map_sub, hs s1 constantCoeff_substOne, hs s0 constantCoeff_substZero, hs s2 constantCoeff_substTwo]
  simp only [map_substOne, map_substZero, map_substTwo]

theorem map_defectTwo (be : MvPowerSeries (ZMod d) F) : map φ (de2 be) = de2 (map φ be) := by
  have hs : ∀ (a : ZMod d → MvPowerSeries (V2 d) F), (∀ s, MvPowerSeries.constantCoeff (a s) = 0) →
      MvPowerSeries.map φ (MvPowerSeries.subst a be) =
        MvPowerSeries.subst (fun s => MvPowerSeries.map φ (a s)) (MvPowerSeries.map φ be) :=
    fun a ha => MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) be
  unfold de2
  rw [map_sub, map_sub, hs s1' constantCoeff_substOne', hs s0 constantCoeff_substZero, hs s2' constantCoeff_substTwo']
  simp only [map_substOne', map_substZero, map_substTwo']

theorem constantCoeff_defectOne {be : MvPowerSeries (ZMod d) F} (h : constantCoeff be = 0) :
    constantCoeff (de1 be) = 0 := by
  have hz : ∀ (a : ZMod d → MvPowerSeries (V2 d) F), (∀ s, MvPowerSeries.constantCoeff (a s) = 0) →
      MvPowerSeries.constantCoeff (MvPowerSeries.subst a be) = 0 :=
    fun a ha => MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) ha h
  unfold de1
  rw [map_sub, map_sub, hz s1 constantCoeff_substOne, hz s0 constantCoeff_substZero, hz s2 constantCoeff_substTwo]
  simp

theorem constantCoeff_defectTwo {be : MvPowerSeries (ZMod d) F} (h : constantCoeff be = 0) :
    constantCoeff (de2 be) = 0 := by
  have hz : ∀ (a : ZMod d → MvPowerSeries (V2 d) F), (∀ s, MvPowerSeries.constantCoeff (a s) = 0) →
      MvPowerSeries.constantCoeff (MvPowerSeries.subst a be) = 0 :=
    fun a ha => MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) ha h
  unfold de2
  rw [map_sub, map_sub, hz s1' constantCoeff_substOne', hz s0 constantCoeff_substZero, hz s2' constantCoeff_substTwo']
  simp

theorem cc_of_noLow {be : MvPowerSeries (ZMod d) F} (h : NoLowBidegree be) :
    constantCoeff be = 0 := by
  by_contra hc
  have h0 := (h 0 (by rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply])).1
  simp [degE] at h0

end Maps

section Normed

variable {F K : Type} [NormedField F] [CharZero F] [NormedField K] [CharZero K] (φ : F →+* K)

theorem map_mvExp {ι : Type} {f : MvPowerSeries ι F} (h : constantCoeff f = 0) :
    map φ (mvExp f) = mvExp (map φ f) := by
  unfold mvExp
  rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero h), PowerSeries.map_exp]

theorem integral_map (hφ : ∀ z, ‖φ z‖ = ‖z‖) {ι : Type} {U : MvPowerSeries ι F}
    (h : Integral U) : Integral (map φ U) := by
  intro n
  rw [MvPowerSeries.coeff_map, hφ]
  exact h n

theorem map_logExp {d : ℕ} [NeZero d] (l : ℕ) {f : MvPowerSeries (V2 d) F}
    (h : constantCoeff f = 0) :
    map φ (subst (letterLog (K := F) l) (mvExp f)) =
      subst (letterLog (K := K) l) (mvExp (map φ f)) := by
  have hL : ∀ x : V2 d, MvPowerSeries.constantCoeff (letterLog (K := F) l x) = 0 := cc_letterLog l
  rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero hL), map_mvExp φ h]
  congr 1
  funext x
  exact map_letterLog φ l x

end Normed

end Transfer

open Transfer in
theorem admissibleTransfer : TransferB := by
  intro F K _ _ _ _ φ hφ l d N0 N1 _ K0 ζ be
  refine ⟨?_, ?_, ?_, fun U hU => integral_map φ hφ hU⟩
  · intro hU a ha ha0
    obtain ⟨b, hb, rfl⟩ := Subfield.mem_map.mp ha
    have hb0 : b ≠ 0 := by
      rintro rfl
      simp at ha0
    obtain ⟨k, hk⟩ := hU b hb hb0
    exact ⟨k, by rw [hφ, hk, ← map_natCast φ l, hφ]⟩
  · rintro ⟨h1, h2, h3, ⟨h4, h5⟩, ⟨h6, h7⟩⟩
    have hcc : MvPowerSeries.constantCoeff be = 0 := cc_of_noLow h3
    have E1 : MvPowerSeries.subst (letterLog (K := K) l) (mvExp (de1 (MvPowerSeries.map φ be))) =
        MvPowerSeries.map φ (MvPowerSeries.subst (letterLog (K := F) l) (mvExp (de1 be))) := by
      rw [← map_defectOne, map_logExp φ l (constantCoeff_defectOne hcc)]
    have E2 : MvPowerSeries.subst (letterLog (K := K) l) (mvExp (de2 (MvPowerSeries.map φ be))) =
        MvPowerSeries.map φ (MvPowerSeries.subst (letterLog (K := F) l) (mvExp (de2 be))) := by
      rw [← map_defectTwo, map_logExp φ l (constantCoeff_defectTwo hcc)]
    have hcm : ∀ G : MvPowerSeries (V2 d) F,
        MvPowerSeries.constantCoeff (MvPowerSeries.map φ G) = φ (MvPowerSeries.constantCoeff G) := by
      intro G
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
        MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    refine ⟨fun n => ?_, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [MvPowerSeries.coeff_map]
      exact Subfield.mem_map.mpr ⟨_, h1 n, rfl⟩
    · have ht : ∀ s : ZMod d, MvPowerSeries.constantCoeff (torus l ζ s) = 0 := fun s => cc_torus l ζ s
      have := congrArg (MvPowerSeries.map φ) h2
      rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ht)] at this
      simpa only [map_torus] using this
    · intro n hn
      rw [MvPowerSeries.coeff_map] at hn
      exact h3 n (fun h0 => hn (by rw [h0, map_zero]))
    · rw [E1]
      exact integral_map φ hφ h4
    · rw [E1, hcm, h5, map_one]
    · rw [E2]
      exact integral_map φ hφ h6
    · rw [E2, hcm, h7, map_one]
  · intro g hg hgs
    refine ⟨fun y => ?_, fun y => ?_⟩
    · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
        MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hg y, map_zero]
    · have := congrArg (MvPowerSeries.map φ) (hgs y)
      rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero hg), map_entLog,
        MvPowerSeries.map_X] at this
      exact this

end Formalism.DworkPowerSeriesWeights
end
end

