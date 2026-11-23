module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowTypeMulOnLevelAtTwistPrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

noncomputable section

namespace GlobalTheory.TwistRowMul

open GlobalTheory.TwistRowType

variable {E : Type} [Field E] [NumberField E]

theorem isUnit_of_reduction_mul {K : Type} [Field K] {P : HeightOneSpectrum (𝓞 E)} (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    {a b c : E} (h : redP P c = redP P a * redP P b) : LocE.unitV ξ c = LocE.unitV ξ a * LocE.unitV ξ b := by
  unfold LocE.unitV
  by_cases hc : IsUnit (redP P c)
  · have hab := hc
    rw [h] at hab
    have ha : IsUnit (redP P a) := isUnit_of_mul_isUnit_left hab
    have hb : IsUnit (redP P b) := isUnit_of_mul_isUnit_right hab
    rw [dite_eq_left ha, dite_eq_left hb, dite_eq_left hc, ← Units.val_mul, ← map_mul]
    have : hc.unit = ha.unit * hb.unit := Units.ext (by simpa using h)
    rw [this]
  · rw [dite_eq_right hc]
    by_cases ha : IsUnit (redP P a)
    · by_cases hb : IsUnit (redP P b)
      · exact absurd (h ▸ ha.mul hb) hc
      · rw [dite_eq_right hb, mul_zero]
    · rw [dite_eq_right ha, zero_mul]

variable [StarRing E]

theorem mem_parL' (P : HeightOneSpectrum (𝓞 E)) (q kj n c : ℕ) (x : Sp E (n + c)) :
    x ∈ LocE.parL P q kj n c ↔
      ∀ i : Fin (n + c), IntAt P (((q : E) ^ (if kj ≤ i.1 ∧ i.1 < n then (1 : ℤ) else 0))⁻¹ * x i) := by
  unfold LocE.parL LocE.sclLat
  rw [Submodule.mem_comap, mem_stdAt]
  rfl

theorem block_mul' (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (hq0 : q ≠ 0) (hq : (q : 𝓞 E) ∈ P.asIdeal) (kj n c : ℕ)
    {g g' : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hg : g ∈ stabL E (n + c) (stdAt E (n + c) P))
    (hg' : g' ∈ stabL E (n + c) (stdAt E (n + c) P)) (hp : g ∈ stabL E (n + c) (LocE.parL P q kj n c)) :
    (redHom P).mapMatrix (blockD P kj n hg * blockD P kj n hg') =
      (redHom P).mapMatrix (blockD P kj n (mul_mem hg hg')) := by
  ext s t
  have hs0 : kj + s.1 < n := by have := s.2; omega
  have hs : kj + s.1 < n + c := by omega
  set v : Sp E (n + c) := g' (Loc.eN E (n + c) (kj + t.1)) with hv
  have hvi : ∀ i, IntAt P (v i) := (GlobalTheory.TwistRowType.mem_stdAt P _).1 ((hg' _).2 (eN_mem P _ _))
  set w : Sp E (n + c) := fun l => if kj ≤ l.1 ∧ l.1 < n then 0 else v l with hw
  have hdec : v = w + ∑ u : Fin (n - kj), Loc.atN v (kj + u.1) • Loc.eN E (n + c) (kj + u.1) := by
    funext l
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Loc.eN, hw, smul_eq_mul]
    by_cases hl : kj ≤ l.1 ∧ l.1 < n
    · have hl2 := l.2
      rw [if_pos hl, zero_add, Finset.sum_eq_single (⟨l.1 - kj, by omega⟩ : Fin (n - kj))]
      · have e : kj + (l.1 - kj) = l.1 := by omega
        simp only [e, if_true, mul_one, Loc.atN]
        rw [dite_eq_left hl2]
      · intro u _ hu
        rw [if_neg, mul_zero]
        intro h
        apply hu
        apply Fin.ext
        simp only
        omega
      · simp
    · rw [if_neg hl, Finset.sum_eq_zero, add_zero]
      intro u _
      have := u.2
      rw [if_neg (by omega), mul_zero]
  have hwp : w ∈ LocE.parL P q kj n c := by
    rw [mem_parL']
    intro i
    by_cases hl : kj ≤ i.1 ∧ i.1 < n
    · simp only [hw, if_pos hl, mul_zero]
      exact (intSub P).zero_mem
    · simp only [hw, if_neg hl, zpow_zero, inv_one, one_mul]
      exact hvi i
  have hgw := (mem_parL' P q kj n c _).1 ((hp w).2 hwp) ⟨kj + s.1, hs⟩
  rw [if_pos ⟨by simp, hs0⟩, zpow_one] at hgw
  have hqE : (q : E) ≠ 0 := Nat.cast_ne_zero.2 hq0
  have hqi : IntAt P (q : E) := natCast_mem (intSub P) q
  have e1 : g w ⟨kj + s.1, hs⟩ = (q : E) * ((q : E)⁻¹ * g w ⟨kj + s.1, hs⟩) := by
    rw [mul_inv_cancel_left₀ hqE]
  have hgwi : IntAt P (g w ⟨kj + s.1, hs⟩) := by rw [e1]; exact hqi.mul hgw
  have hred : redP P (g w ⟨kj + s.1, hs⟩) = 0 := by
    rw [e1, reduction_mul hqi hgw]
    have : redP P (q : E) = 0 := by
      have h := reduction_coe P (q : 𝓞 E)
      rw [map_natCast] at h
      rw [h, Ideal.Quotient.eq_zero_iff_mem]
      exact hq
    rw [this, zero_mul]
  have key : (⟨g w ⟨kj + s.1, hs⟩, hgwi⟩ : intSub P) + (blockD P kj n hg * blockD P kj n hg') s t =
      blockD P kj n (mul_mem hg hg') s t := by
    apply Subtype.ext
    have h2 : (blockD P kj n (mul_mem hg hg') s t : E) = g v ⟨kj + s.1, hs⟩ := by
      simp only [blockD, Matrix.of_apply, Loc.atN]
      rw [dite_eq_left hs]
      rfl
    have h1 : g v ⟨kj + s.1, hs⟩ = g w ⟨kj + s.1, hs⟩ +
        ∑ u : Fin (n - kj), Loc.atN v (kj + u.1) * g (Loc.eN E (n + c) (kj + u.1)) ⟨kj + s.1, hs⟩ := by
      set_option synthInstance.maxHeartbeats 100000 in
        conv_lhs => rw [hdec, map_add (f := _), map_sum]
      simp only [map_smul, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [h2, h1, Matrix.mul_apply, Subring.coe_add, AddSubmonoidClass.coe_finsetSum]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Subring.coe_mul, mul_comm]
    congr 1
    simp only [blockD, Matrix.of_apply, Loc.atN]
    rw [dite_eq_left hs]
  have h3 := congrArg (redHom P) key
  rw [map_add (f := _), redHom_apply, hred, zero_add] at h3
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, h3]
  rfl

theorem lamQB_mul {K : Type} [Field K] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (hq0 : q ≠ 0) (hq : (q : 𝓞 E) ∈ P.asIdeal)
    (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (kj n c : ℕ) {g g' : Sp E (n + c) ≃ₗ[E] Sp E (n + c)}
    (hg : g ∈ LocE.JQ P q kj n c) (hg' : g' ∈ LocE.JQ P q kj n c) :
    LocE.lamQB ξ kj n (g * g').toLinearMap = LocE.lamQB ξ kj n g.toLinearMap * LocE.lamQB ξ kj n g'.toLinearMap := by
  have hg1 : g ∈ stabL E (n + c) (stdAt E (n + c) P) := hg.1
  have hg2 : g' ∈ stabL E (n + c) (stdAt E (n + c) P) := hg'.1
  unfold LocE.lamQB
  rw [← mul_inv]
  congr 1
  apply isUnit_of_reduction_mul
  rw [redP_det_block P kj n hg1, redP_det_block P kj n hg2, redP_det_block P kj n (mul_mem hg1 hg2), ← Matrix.det_mul,
    ← map_mul, block_mul' P q hq0 hq kj n c hg1 hg2 hg.2]

theorem lamRow_mul : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∉ Pr.vGs → ∀ g ∈ Jat (Pr := Pr) (R := R) sharp j P, ∀ g' ∈ Jat (Pr := Pr) (R := R) sharp j P, lamRow Ch mu sharp j P (g * g').toLinearMap = lamRow Ch mu sharp j P g.toLinearMap * lamRow Ch mu sharp j P g'.toLinearMap := by
  intro X Pr R Ch S mu sharp j P hP g hg g' hg'
  unfold Jat at hg hg'
  rw [if_neg hP] at hg hg'
  unfold lamRow
  rw [if_neg hP, if_neg hP, if_neg hP]
  exact lamQB_mul P (qOf P) (fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)) (Ideal.absNorm_mem _) _ _ _ _ hg hg'

end GlobalTheory.TwistRowMul

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowTypeOneAddPrimeSmulEqOne
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

noncomputable section

namespace GlobalTheory.Mem.Col2.IdxEx.Cong

open GlobalTheory.LastSteps

section Loc

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

omit [StarRing E] in
theorem unitV_one (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) : LocE.unitV χ (1 : E) = 1 := by
  have h : IsUnit (redP P (1 : E)) := by
    rw [GlobalTheory.TopStep.reduction_one₂]
    exact isUnit_one
  have h1 : h.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, GlobalTheory.TopStep.reduction_one₂, Units.val_one])
  unfold LocE.unitV
  rw [dite_eq_left h, h1, map_one, Units.val_one]

omit [StarRing E] in
theorem unitV_det_delta (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {t : ℕ} {A : Fin t → Fin t → E}
    (hA : ∀ s s', A s s' = if s = s' then 1 else 0) : LocE.unitV χ (Matrix.det (Matrix.of fun s s' => A s s')) = 1 := by
  have : (Matrix.of fun s s' => A s s') = 1 := by
    ext s s'
    rw [Matrix.of_apply, hA, Matrix.one_apply]
  rw [this, Matrix.det_one, unitV_one]


omit [NumberField E] [StarRing E] in
theorem entB_id (q : ℕ) {k₀ c n : ℕ} (hk : k₀ ≤ n) (ex : ℕ → ℕ) {p p' : ℕ} (hp : p < n + c) (hp' : p' < n + c) :
    LocE.entB q k₀ c n c n ex ex (LinearMap.id : HomE E (n + c) (n + c)) p p' = if p = p' then 1 else 0 := by
  have h1 : LocE.fIdx k₀ c n p < n + c := by
    unfold LocE.fIdx
    split_ifs <;> omega
  have h2 : LocE.fIdx k₀ c n p = LocE.fIdx k₀ c n p' ↔ p = p' := by
    refine ⟨fun h => ?_, fun h => by rw [h]⟩
    unfold LocE.fIdx at h
    split_ifs at h <;> omega
  unfold LocE.entB Loc.atN
  rw [dite_eq_left h1, LinearMap.id_apply]
  unfold Loc.eN
  by_cases h : p = p'
  · subst h
    simp
  · rw [if_neg h, if_neg (fun h' => h (h2.1 h')), zero_mul]

variable (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)

omit [StarRing E] in
theorem blocks_delta {r t j : ℕ} {M : ℕ → ℕ → E}
    (hM : ∀ p p', p < r + j * t → p' < r + j * t → M p p' = if p = p' then 1 else 0) :
    ∏ i ∈ Finset.range j, LocE.unitV (χ i)
      (Matrix.det (Matrix.of fun s s' : Fin t => M (r + i * t + s.1) (r + i * t + s'.1))) = 1 := by
  refine Finset.prod_eq_one fun i hi => unitV_det_delta _ fun s s' => ?_
  have h1 : ∀ s : Fin t, r + i * t + s.1 < r + j * t := fun s => by
    have := Finset.mem_range.1 hi
    have := s.2
    nlinarith
  rw [hM _ _ (h1 s) (h1 s')]
  simp [Fin.ext_iff]

omit [StarRing E] in
theorem int_delta {N : ℕ} {M : ℕ → ℕ → E} (hM : ∀ p p', p < N → p' < N → M p p' = if p = p' then 1 else 0)
    (p p' : ℕ) (h : p < N) (h' : p' < N) : IntAt P (M p p') := by
  rw [hM _ _ h h']
  split_ifs
  · exact GlobalTheory.TopStep.intAt_one
  · exact GlobalTheory.TopStep.intAt_zero

omit [StarRing E] in
theorem lamGv_delta {r t j : ℕ} {M : ℕ → ℕ → E}
    (hM : ∀ p p', p < r + j * t → p' < r + j * t → M p p' = if p = p' then 1 else 0) :
    LocE.lamGv ψ₀ χ r t j M = 1 := by
  unfold LocE.lamGv
  rw [blocks_delta χ hM, mul_one, Finset.sum_eq_zero, GlobalTheory.TopStep.reduction_zero, AddChar.map_zero_eq_one]
  intro i hi
  have := Finset.mem_range.1 hi
  rw [hM _ _ (by omega) (by omega), if_neg (by omega)]

omit [StarRing E] in
theorem lamGvS_delta {k₀ r t j : ℕ} (hk : k₀ ≤ r) {M : ℕ → ℕ → E}
    (hM : ∀ p p', p < r + j * t → p' < r + j * t → M p p' = if p = p' then 1 else 0) :
    LocE.lamGvS ψ₀ χ k₀ r t j M = 1 := by
  unfold LocE.lamGvS
  rw [blocks_delta χ hM, mul_one, Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero, GlobalTheory.TopStep.reduction_zero,
    AddChar.map_zero_eq_one]
  all_goals
    intro i hi
    have := Finset.mem_range.1 hi
    rw [hM _ _ (by omega) (by omega), if_neg (by omega)]

theorem lamQB_cong (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (kj n c : ℕ) {y : HomE E (n + c) (n + c)}
    (hy : y ∈ homS (LocE.lamY P (qOf P) n c 0) (LocE.lamY P (qOf P) n c 0)) :
    LocE.lamQB ξ kj n (LinearMap.id + (qOf P : E) • y) = 1 := by
  unfold LocE.lamQB
  have hl : ∀ s : Fin (n - kj), kj + s.1 < n + c := fun s => by
    have := s.2
    omega
  have e : (fun s t : Fin (n - kj) => Loc.atN ((LinearMap.id + (qOf P : E) • y : HomE E (n + c) (n + c))
      (Loc.eN E (n + c) (kj + t.1))) (kj + s.1)) =
      fun s t : Fin (n - kj) => (if s = t then 1 else 0) + (qOf P : E) * y (Pi.single ⟨_, hl t⟩ 1) ⟨_, hl s⟩ := by
    funext s t
    unfold Loc.atN
    rw [dite_eq_left (hl s), eN_eq (hl t)]
    simp [Pi.single_apply, Fin.ext_iff]
  rw [e, unitV_congr ξ (redP_det_add_q (A := fun s t => if s = t then 1 else 0) (fun s t => ?_) fun s t => ?_),
    unitV_det_delta ξ fun _ _ => rfl, inv_one]
  · split_ifs
    · exact GlobalTheory.TopStep.intAt_one
    · exact GlobalTheory.TopStep.intAt_zero
  · simpa [LocE.scE] using mem_homS_sclLat.1 hy ⟨_, hl s⟩ ⟨_, hl t⟩

end Loc

theorem lamRow_cong : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), j < R.m → ∀ y : HomE X.E (R.N j + cOf R j) (R.N j + cOf R j), (∀ x ∈ lamYat (Pr := Pr) (R := R) j P, y x ∈ lamYat (Pr := Pr) (R := R) j P) → lamRow Ch mu sharp j P (LinearMap.id + (qOf P : X.E) • y) = 1 := by
  intro X Pr R Ch S mu sharp j P hj y hy
  have hN : R.N j + cOf R j = R.r + j * R.t := by
    unfold Ranks.N cOf Ranks.r
    rw [mul_add, mul_one]
    omega
  have hk : R.k ≤ R.N j := Nat.le_add_right _ _
  have hr : R.k ≤ R.r := by
    unfold Ranks.r
    omega
  unfold lamYat at hy
  unfold lamRow
  by_cases hP : P ∈ Pr.vGs
  · rw [if_pos hP] at hy ⊢
    have hZ := entB_int R.k (x := y) hy
    have hM : ∀ p p', p < R.r + j * R.t → p' < R.r + j * R.t →
        LocE.entB (qOf P) R.k (cOf R j) (R.N j) (cOf R j) (R.N j) (fun i => i + 1) (fun i => i + 1)
          (LinearMap.id : HomE X.E (R.N j + cOf R j) (R.N j + cOf R j)) p p' = if p = p' then 1 else 0 :=
      fun p p' h h' => entB_id _ hk _ (hN ▸ h) (hN ▸ h')
    split_ifs
    · unfold LocE.lamGBS
      rw [entB_add_smul, lamGvS_congr _ _ (int_delta hM) hZ, lamGvS_delta _ _ hr hM]
    · unfold LocE.lamGB
      rw [entB_add_smul, lamGv_congr _ _ (int_delta hM) hZ, lamGv_delta _ _ hM]
  · rw [if_neg hP] at hy ⊢
    exact lamQB_cong _ _ _ _ hy

end GlobalTheory.Mem.Col2.IdxEx.Cong

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramInIffDifferentIdealEqTop
section
set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.NT

namespace GlobalTheory.UnramDiscr

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

theorem not_dvd_iff_inertia (P : Ideal (𝓞 L)) [P.IsPrime] (hP : P ≠ ⊥) :
    ¬ P ∣ differentIdeal (𝓞 K) (𝓞 L) ↔ P.inertia (L ≃ₐ[K] L) = ⊥ := by
  let _ : Algebra (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) := FractionRing.liftAlgebra _ _
  haveI : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP
  rw [not_dvd_differentIdeal_iff, ← Ideal.ramificationIdx_eq_one_iff,
    ← Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 K)) P (L ≃ₐ[K] L),
    ← Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) (P.under (𝓞 K)) P,
    Subgroup.card_eq_one]

theorem unramIn_iff_differentIdeal_eq_top :
    (∀ 𝔭 : HeightOneSpectrum (𝓞 K), UnramIn L 𝔭) ↔ differentIdeal (𝓞 K) (𝓞 L) = ⊤ := by
  let _ : Algebra (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) := FractionRing.liftAlgebra _ _
  have hD0 : differentIdeal (𝓞 K) (𝓞 L) ≠ ⊥ := differentIdeal_ne_bot
  unfold UnramIn InInertia
  constructor
  · intro h
    by_contra hD
    obtain ⟨M, hM, hDM⟩ := Ideal.exists_le_maximal _ hD
    haveI := hM
    have hMb : M ≠ ⊥ := by
      rintro rfl
      exact hD0 (le_bot_iff.mp hDM)
    have hMu : M.under (𝓞 K) ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hMb
    have hb : M.inertia (L ≃ₐ[K] L) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro σ hσ
      exact h ⟨M.under (𝓞 K), inferInstance, hMu⟩ σ ⟨M, inferInstance, ⟨rfl⟩, fun x => hσ x⟩
    exact (not_dvd_iff_inertia K L M hMb).mpr hb (Ideal.dvd_iff_le.mpr hDM)
  · rintro hD 𝔭 σ ⟨P, hP, hPo, hσ⟩
    haveI := hP
    haveI := hPo
    have hPb : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P
    have hnd : ¬ P ∣ differentIdeal (𝓞 K) (𝓞 L) := by
      rw [hD]
      exact fun hd => hP.ne_top (top_le_iff.mp (Ideal.dvd_iff_le.mp hd))
    have hb := (not_dvd_iff_inertia K L P hPb).mp hnd
    have hmem : σ ∈ P.inertia (L ≃ₐ[K] L) := fun x => hσ x
    rw [hb] at hmem
    exact Subgroup.mem_bot.mp hmem


omit K L in
theorem unramIn_iff_natAbs_discr :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L],
      (∀ 𝔭 : HeightOneSpectrum (𝓞 K), UnramIn L 𝔭) ↔
        (discr L).natAbs = (discr K).natAbs ^ Module.finrank K L := by
  intro K L _ _ _ _ _ _
  rw [unramIn_iff_differentIdeal_eq_top K L,
    natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)]
  have h0 : 0 < (discr K).natAbs ^ Module.finrank K L :=
    pow_pos (Int.natAbs_pos.mpr (discr_ne_zero K)) _
  constructor
  · intro h
    rw [h, Ideal.absNorm_top, one_mul]
  · intro h
    apply Ideal.absNorm_eq_one_iff.mp
    apply Nat.eq_of_mul_eq_mul_right h0
    rw [h, one_mul]

end GlobalTheory.UnramDiscr
end

