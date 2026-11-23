module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0002

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumZeroSlot
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open GroundTheory.Heights₂.Heights.NumbersDVR Filter

universe u

section

variable {K : Type*}

theorem diffStep_zero_left (h : (K → ℤ) → ℤ) : diffStep 0 h = 0 := by
  funext m
  simp [diffStep]

theorem diffStep_zero_right (b : K → ℤ) : diffStep b (0 : (K → ℤ) → ℤ) = 0 := by
  funext m
  simp [diffStep]

theorem foldr_diffStep_eq_zero_of_mem (l : List (K → ℤ)) (hl : (0 : K → ℤ) ∈ l)
    (h : (K → ℤ) → ℤ) : l.foldr diffStep h = 0 := by
  induction l with
  | nil => simp at hl
  | cons a t ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp hl with rfl | ht
    · exact diffStep_zero_left _
    · rw [ih ht]
      exact diffStep_zero_right a

theorem mixedDiff_coord_zero {n : ℕ} (bs : Fin n → K → ℤ) (i : Fin n) (hi : bs i = 0)
    (h : (K → ℤ) → ℤ) : mixedDiff bs h = 0 :=
  foldr_diffStep_eq_zero_of_mem _ (List.mem_ofFn.mpr ⟨i, hi⟩) h

theorem diffStep_eventually_zero {b : K → ℤ} {h : (K → ℤ) → ℤ}
    (hh : ∀ᶠ m in atTop, h m = 0) : ∀ᶠ m in atTop, diffStep b h m = 0 := by
  have hs : ∀ᶠ m in atTop, h (m + -b) = 0 :=
    (tendsto_atTop_add_const_right atTop (-b) tendsto_id).eventually hh
  filter_upwards [hh, hs] with m h1 h2
  simp only [diffStep, h1, ← sub_eq_add_neg] at h2 ⊢
  rw [h2, sub_zero]

theorem mixedDiff_eventually_zero {n : ℕ} (bs : Fin n → K → ℤ) {h : (K → ℤ) → ℤ}
    (hh : ∀ᶠ m in atTop, h m = 0) : ∀ᶠ m in atTop, mixedDiff bs h m = 0 := by
  unfold mixedDiff
  induction List.ofFn bs with
  | nil => simpa using hh
  | cons a t ih => exact diffStep_eventually_zero ih

theorem eventualValue_eq_zero {f : (K → ℤ) → ℤ} (hf : ∀ᶠ m in atTop, f m = 0) :
    eventualValue f = 0 := by
  unfold eventualValue
  have hex : ∃ c, ∀ᶠ m in atTop, f m = c := ⟨0, hf⟩
  rw [dite_eq_left hex]
  obtain ⟨m, h1, h2⟩ := (hex.choose_spec.and hf).exists
  rw [← h1, h2]

end

theorem exists_nat_of_le_of_lt {x : WithBot (WithTop ℤ)} {t n : ℕ}
    (h1 : (t : WithBot (WithTop ℤ)) ≤ x) (h2 : x < n) : ∃ d : ℕ, x = d := by
  rw [← WithBot.coe_natCast, ← WithTop.coe_natCast] at h1 h2
  induction x using WithBot.recBotCoe with
  | bot => exact absurd h1 (not_le.mpr (WithBot.bot_lt_coe _))
  | coe y =>
    induction y using WithTop.recTopCoe with
    | top => exact absurd h2 (not_lt.mpr (WithBot.coe_le_coe.mpr le_top))
    | coe z =>
      have hz : (t : ℤ) ≤ z := WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp h1)
      refine ⟨z.toNat, ?_⟩
      rw [← WithBot.coe_natCast, ← WithTop.coe_natCast, Int.toNat_of_nonneg (by omega)]

theorem IntNumZeroSlot.proof (h₁ : MixedDiffConst.Statement.{u})
    (h₂ : HilbEventuallyPoly.Statement.{u}) (h₃ : HilbDegreeBound.Statement.{u}) :
    IntNumZeroSlot.Statement.{u} := by
  intro F _ K _ _ ι _ I
  refine ⟨fun n bs i hi => ?_, fun hI n bs hn => ?_⟩
  · unfold intNum
    refine eventualValue_eq_zero (Eventually.of_forall fun m => ?_)
    rw [mixedDiff_coord_zero bs i hi]
    rfl
  · unfold intNum
    apply eventualValue_eq_zero
    by_cases hR : IsRelevant I
    · by_cases hd : ∃ d : ℕ, relDim I = d
      · obtain ⟨d, hd⟩ := hd
        have hdn : d < n := by
          rw [hd] at hn
          exact_mod_cast hn
        exact (h₁ F K ι I hI hR d hd).2 n hdn bs
      · obtain ⟨p, hp⟩ := h₂ F K ι I hI
        have hp0 : p = 0 := by
          by_contra hne
          exact hd (exists_nat_of_le_of_lt ((h₃ F K ι I hI).1 hR p hp hne) hn)
        apply mixedDiff_eventually_zero
        filter_upwards [hp] with m hm
        rw [hp0, map_zero] at hm
        exact_mod_cast hm
    · exact mixedDiff_eventually_zero bs ((h₃ F K ι I hI).2 hR)

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMixedDiffConst
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter

noncomputable section

universe u

namespace MixedDiffConst

variable {K : Type}

def shiftPoly (b : K → ℤ) (p : MvPolynomial K ℚ) : MvPolynomial K ℚ :=
  aeval (fun k => X k - C ((b k : ℤ) : ℚ)) p

def polyStep (b : K → ℤ) (p : MvPolynomial K ℚ) : MvPolynomial K ℚ :=
  p - shiftPoly b p

theorem eval_shiftPoly (b : K → ℤ) (p : MvPolynomial K ℚ) (x : K → ℚ) :
    eval x (shiftPoly b p) = eval (fun k => x k - b k) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [shiftPoly]
  | add p q hp hq => simp only [shiftPoly, map_add (f := _)] at hp hq ⊢; rw [hp, hq]
  | mul_X p k hp => simp only [shiftPoly, map_mul] at hp ⊢; rw [hp]; simp

theorem monomial_good (b : K → ℤ) (s : K →₀ ℕ) (a : ℚ) :
    (shiftPoly b (monomial s a)).totalDegree ≤ (monomial s a).totalDegree ∧
      (polyStep b (monomial s a) = 0 ∨
        (polyStep b (monomial s a)).totalDegree + 1 ≤ (monomial s a).totalDegree) := by
  refine MvPolynomial.induction_on_monomial (motive := fun q =>
    (shiftPoly b q).totalDegree ≤ q.totalDegree ∧
      (polyStep b q = 0 ∨ (polyStep b q).totalDegree + 1 ≤ q.totalDegree)) ?_ ?_ s a
  · intro a; simp [shiftPoly, polyStep]
  · intro p k hp
    obtain ⟨h1, h2⟩ := hp
    by_cases hp0 : p = 0
    · subst hp0; simp [shiftPoly, polyStep]
    have hdeg : (p * X k).totalDegree = p.totalDegree + 1 := by
      rw [totalDegree_mul_of_isDomain hp0 (X_ne_zero k), totalDegree_X]
    have hXC : (X k - C ((b k : ℤ) : ℚ) : MvPolynomial K ℚ).totalDegree ≤ 1 :=
      (totalDegree_sub _ _).trans (max_le (totalDegree_X k).le (by rw [totalDegree_C]; omega))
    have hsh : shiftPoly b (p * X k) = shiftPoly b p * (X k - C ((b k : ℤ) : ℚ)) := by
      simp [shiftPoly]
    have hst : polyStep b (p * X k) = polyStep b p * X k + C ((b k : ℤ) : ℚ) * shiftPoly b p := by
      rw [polyStep, polyStep, hsh]; ring
    refine ⟨?_, Or.inr ?_⟩
    · rw [hsh, hdeg]
      exact (totalDegree_mul _ _).trans (add_le_add h1 hXC)
    · rw [hst, hdeg, add_le_add_iff_right]
      refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · rcases h2 with h2 | h2
        · rw [h2, zero_mul, totalDegree_zero]; exact zero_le
        · exact (totalDegree_mul _ _).trans (by rw [totalDegree_X]; exact h2)
      · exact (totalDegree_mul _ _).trans (by rw [totalDegree_C, zero_add]; exact h1)

theorem sum_eq (b : K → ℤ) (p : MvPolynomial K ℚ) :
    shiftPoly b p = ∑ v ∈ p.support, shiftPoly b (monomial v (AddMonoidAlgebra.coeff p v)) ∧
      polyStep b p = ∑ v ∈ p.support, polyStep b (monomial v (AddMonoidAlgebra.coeff p v)) := by
  have hs : shiftPoly b p = ∑ v ∈ p.support, shiftPoly b (monomial v (AddMonoidAlgebra.coeff p v)) := by
    conv_lhs => rw [p.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [shiftPoly, map_sum]
  refine ⟨hs, ?_⟩
  simp only [polyStep, Finset.sum_sub_distrib]
  rw [← hs, ← p.as_sum]

theorem monomial_le (p : MvPolynomial K ℚ) {v : K →₀ ℕ} (hv : v ∈ p.support) :
    (monomial v (AddMonoidAlgebra.coeff p v)).totalDegree ≤ p.totalDegree :=
  (totalDegree_monomial_le _ _).trans (le_totalDegree hv)

theorem polyStep_deg (b : K → ℤ) (p : MvPolynomial K ℚ) :
    polyStep b p = 0 ∨ (polyStep b p).totalDegree + 1 ≤ p.totalDegree := by
  by_cases h0 : p.totalDegree = 0
  · left
    rw [totalDegree_eq_zero_iff_eq_C] at h0
    rw [h0]; simp [polyStep, shiftPoly]
  · right
    have : (polyStep b p).totalDegree ≤ p.totalDegree - 1 := by
      rw [(sum_eq b p).2]
      refine totalDegree_finsetSum_le fun v hv => ?_
      rcases (monomial_good b v (AddMonoidAlgebra.coeff p v)).2 with h | h
      · rw [h, totalDegree_zero]; exact zero_le
      · have := monomial_le p hv; omega
    omega

section Eventual

theorem eventuallyPoly_diffStep (b : K → ℤ) {g : (K → ℤ) → ℤ} {q : MvPolynomial K ℚ}
    (hq : EventuallyPoly g q) : EventuallyPoly (diffStep b g) (polyStep b q) := by
  have ht : Tendsto (fun m : K → ℤ => m - b) atTop atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-b) tendsto_id
  filter_upwards [hq, ht.eventually hq] with m h1 h2
  simp only [diffStep, polyStep, map_sub, eval_shiftPoly]
  rw [Int.cast_sub, h1, h2]
  simp [Pi.sub_apply]

theorem eventuallyPoly_foldr (L : List (K → ℤ)) {h : (K → ℤ) → ℤ} {p : MvPolynomial K ℚ}
    (hp : EventuallyPoly h p) : EventuallyPoly (L.foldr diffStep h) (L.foldr polyStep p) := by
  induction L with
  | nil => simpa using hp
  | cons b L ih => simpa using eventuallyPoly_diffStep b ih

theorem foldr_polyStep_deg (L : List (K → ℤ)) (p : MvPolynomial K ℚ) :
    L.foldr polyStep p = 0 ∨ (L.foldr polyStep p).totalDegree + L.length ≤ p.totalDegree := by
  induction L with
  | nil => simp
  | cons b L ih =>
    simp only [List.foldr_cons, List.length_cons]
    rcases ih with h0 | hd
    · left; rw [h0]; simp [polyStep, shiftPoly]
    · rcases polyStep_deg b (L.foldr polyStep p) with h | h
      · exact Or.inl h
      · right; omega

end Eventual

end MixedDiffConst


open MixedDiffConst in
theorem MixedDiffConst.proof (h1 : HilbDegreeBound.Statement.{u})
    (h2 : HilbEventuallyPoly.Statement.{u}) : MixedDiffConst.Statement.{u} := by
  intro F _ K _ _ ι _ I hI hrel n hn
  obtain ⟨p, hp⟩ := h2 F K ι I hI
  have hdeg : p.totalDegree ≤ n := by
    by_cases hp0 : p = 0
    · simp [hp0]
    · have := (h1 F K ι I hI).1 hrel p hp hp0
      rw [hn] at this
      exact_mod_cast this
  have key : ∀ (r : ℕ) (bs : Fin r → K → ℤ), n ≤ r → ∃ c : ℚ, (n < r → c = 0) ∧
      ∀ᶠ m in atTop, (mixedDiff bs (hilbFn I) m : ℚ) = c := by
    intro r bs hr
    have hE := eventuallyPoly_foldr (List.ofFn bs) hp
    rcases foldr_polyStep_deg (List.ofFn bs) p with h0 | hd
    · refine ⟨0, fun _ => rfl, ?_⟩
      filter_upwards [hE] with m hm
      rw [mixedDiff, hm, h0, map_zero]
    · rw [List.length_ofFn] at hd
      have hq0 : ((List.ofFn bs).foldr polyStep p).totalDegree = 0 := by omega
      refine ⟨AddMonoidAlgebra.coeff ((List.ofFn bs).foldr polyStep p) 0, fun hlt => by omega, ?_⟩
      rw [totalDegree_eq_zero_iff_eq_C] at hq0
      filter_upwards [hE] with m hm
      rw [mixedDiff, hm, hq0, eval_C, coeff_C, if_pos rfl]
  constructor
  · intro bs
    obtain ⟨c, -, hc⟩ := key n bs le_rfl
    obtain ⟨m0, hm0⟩ := hc.exists
    have hc' : ∀ᶠ m in atTop, mixedDiff bs (hilbFn I) m = mixedDiff bs (hilbFn I) m0 :=
      hc.mono fun m hm => by exact_mod_cast hm.trans hm0.symm
    have hex : ∃ c, ∀ᶠ m in atTop, mixedDiff bs (hilbFn I) m = c := ⟨_, hc'⟩
    have hval : intNum F I bs = mixedDiff bs (hilbFn I) m0 := by
      unfold intNum eventualValue
      rw [dite_eq_left hex]
      obtain ⟨m, hm1, hm2⟩ := (hex.choose_spec.and hc').exists
      rw [← hm1, hm2]
    filter_upwards [hc'] with m hm
    rw [hm, hval]
  · intro r hr bs
    obtain ⟨c, hc0, hc⟩ := key r bs hr.le
    filter_upwards [hc] with m hm
    rw [hc0 hr] at hm
    exact_mod_cast hm

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PNoetherIntegralClosure
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

theorem NoetherIntegralClosureFinite.proof : NoetherIntegralClosureFinite.Statement := by
  intro k A _ _ _ _ _ K _ _ _ L _ _ _ _ _
  refine finite_integralClosure_of_forall_mvPolynomial k A K L fun s L' _ _ _ _ _ => ?_
  obtain ⟨p, hp⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k p with hp' | rfl
  · have : Fact p.Prime := ⟨hp'⟩
    exact finite_integralClosure_mvPolynomial_of_charP k p s L'
  · have : CharZero k := CharP.charP_to_charZero k
    exact finite_integralClosure_mvPolynomial_of_charZero k s L'

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsExamples
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem relDim_bot {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {F : Type*} [Field F] :
    relDim (⊥ : Ideal (MRing ι F)) =
      (((Fintype.card (Σ k, ι k) : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) := by
  unfold relDim
  rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field, zero_add,
    Nat.card_eq_fintype_card]
  rfl

abbrev ProjIdx (N : ℕ) : Unit → Type := fun _ => Fin (N + 1)

theorem relDim_projectiveSpace {F : Type*} [Field F] (N : ℕ) :
    relDim (⊥ : Ideal (MRing (ProjIdx N) F)) = (N : WithBot (WithTop ℤ)) := by
  rw [relDim_bot]
  simp [Fintype.card_sigma]
  rfl

def binomFn (N : ℕ) (t : ℤ) : ℤ := if 0 ≤ t then ((t.toNat + N).choose N : ℤ) else 0

theorem binomFn_sub (N : ℕ) (t : ℤ) :
    binomFn (N + 1) t - binomFn (N + 1) (t - 1) = binomFn N t := by
  unfold binomFn
  rcases lt_trichotomy t 0 with h | rfl | h
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp
  · simp
  · obtain ⟨u, rfl⟩ : ∃ u : ℕ, t = u + 1 := ⟨(t - 1).toNat, by omega⟩
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
    have h1 : ((u : ℤ) + 1).toNat = u + 1 := by omega
    have h2 : ((u : ℤ) + 1 - 1).toNat = u := by omega
    have h3 := Nat.choose_succ_succ (u + N + 1) N
    rw [h1, h2, show u + 1 + (N + 1) = u + N + 1 + 1 by omega, h3,
      show u + (N + 1) = u + N + 1 by omega, show u + 1 + N = u + N + 1 by omega]
    push_cast
    ring

theorem weight_projIdx (N : ℕ) (d : (Σ _ : Unit, ProjIdx N ()) →₀ ℕ) :
    Finsupp.weight (blockWeight (ProjIdx N)) d () = ∑ x, d x := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply]
  simp [blockWeight]

theorem finrank_gradedPiece_projectiveSpace (F : Type*) [Field F] (N a : ℕ) :
    Module.finrank F (gradedPiece (⊥ : Ideal (MRing (ProjIdx N) F)) (fun _ => a)) =
      (a + N).choose N := by
  have hinj : Function.Injective
      (Ideal.Quotient.mkₐ F (⊥ : Ideal (MRing (ProjIdx N) F))).toLinearMap := by
    intro x y h
    simpa [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq, sub_eq_zero] using h
  unfold gradedPiece
  rw [← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _),
    weightedHomogeneousSubmodule_eq_finsupp_supported]
  let s : Set ((Σ _ : Unit, ProjIdx N ()) →₀ ℕ) :=
    {d | Finsupp.weight (blockWeight (ProjIdx N)) d = fun _ => a}
  let e : s ≃ (Finset.univ.finsuppAntidiag a : Finset ((Σ _ : Unit, ProjIdx N ()) →₀ ℕ)) :=
    Equiv.subtypeEquivRight fun d => by
      rw [Finset.mem_finsuppAntidiag]
      simp only [s, Set.mem_ofPred_eq, Finset.subset_univ, and_true]
      constructor
      · intro h
        rw [← weight_projIdx]
        exact congrFun h ()
      · intro h
        funext u
        rw [weight_projIdx]
        exact h
  have : Fintype s := Fintype.ofEquiv _ e.symm
  rw [LinearEquiv.finrank_eq (AddMonoidAlgebra.supportedEquivFinsupp (R := F) (S := F) s), Module.finrank_finsupp_self,
    Fintype.card_congr e, Fintype.card_coe, Finset.card_finsuppAntidiag_nat_eq_choose]
  simp [Fintype.card_sigma]
  rw [add_comm, Nat.choose_symm_add]

theorem hilbFn_projectiveSpace (F : Type*) [Field F] (N : ℕ) (m : Unit → ℤ) :
    hilbFn (⊥ : Ideal (MRing (ProjIdx N) F)) m = binomFn N (m ()) := by
  unfold hilbFn binomFn
  by_cases hm : 0 ≤ m ()
  · rw [if_pos (fun k => hm), if_pos hm]
    have : (fun k => (m k).toNat) = fun _ : Unit => (m ()).toNat := rfl
    rw [this, finrank_gradedPiece_projectiveSpace]
  · rw [if_neg (fun h => hm (h ())), if_neg hm]

theorem foldr_diffStep_binomFn (j N : ℕ) :
    (List.replicate j (1 : Unit → ℤ)).foldr diffStep (fun m => binomFn (N + j) (m ())) =
      fun m => binomFn N (m ()) := by
  induction j generalizing N with
  | zero => simp
  | succ j ih =>
    rw [List.replicate_succ, List.foldr_cons, show N + (j + 1) = (N + 1) + j by omega, ih]
    funext m
    simp only [diffStep, Pi.sub_apply, Pi.one_apply]
    exact binomFn_sub N (m ())

theorem intNum_projectiveSpace (F : Type*) [Field F] (N : ℕ) :
    intNum F (⊥ : Ideal (MRing (ProjIdx N) F)) (fun _ : Fin N => (1 : Unit → ℤ)) = 1 := by
  have hh : hilbFn (⊥ : Ideal (MRing (ProjIdx N) F)) = fun m => binomFn (0 + N) (m ()) := by
    funext m
    rw [zero_add, hilbFn_projectiveSpace]
  unfold intNum mixedDiff
  rw [List.ofFn_const, hh, foldr_diffStep_binomFn]
  have hev : ∀ᶠ m : Unit → ℤ in Filter.atTop, binomFn 0 (m ()) = 1 :=
    (Filter.eventually_ge_atTop 0).mono fun m hm => by
      have : (0 : ℤ) ≤ m () := hm ()
      simp [binomFn, this]
  have hex : ∃ c, ∀ᶠ m : Unit → ℤ in Filter.atTop, binomFn 0 (m ()) = c := ⟨1, hev⟩
  unfold eventualValue
  rw [dite_eq_left hex]
  obtain ⟨m, h1, h2⟩ := (hex.choose_spec.and hev).exists
  exact h1.symm.trans h2

theorem blockIncl_injective {K K' : Type*} (j : K ↪ K') (ι' : K' → Type*) :
    Function.Injective (blockIncl j ι') := by
  rintro ⟨a, x⟩ ⟨b, y⟩ h
  simp only [blockIncl, Sigma.mk.inj_iff] at h
  obtain ⟨h1, h2⟩ := h
  cases j.injective h1
  rw [eq_of_heq h2]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsRename
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section Split

variable {K K' : Type}

end Split

def RenameMultiHomog.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K K' : Type) [DecidableEq K] [DecidableEq K'] (j : K ↪ K')
    (ι : K → Type) (ι' : K' → Type) (g : (Σ k, ι k) → (Σ k', ι' k')), (∀ v, (g v).1 = j v.1) →
    ∀ (f : MRing ι R) (d : K → ℕ), IsMultiHomog f d →
      IsMultiHomog (rename g f) (Function.extend j d 0)

def RenameHilbFn.Statement : Prop :=
  ∀ (F : Type u) [Field F] (S K' : Type) [DecidableEq S] [DecidableEq K'] (κ : S → Type)
    (ι' : K' → Type) (E : S ≃ K') (σ : (Σ s, κ s) ≃ (Σ k', ι' k')), (∀ v, (σ v).1 = E v.1) →
    ∀ (P : Ideal (MRing ι' F)) (m : S → ℤ),
      hilbFn (P.comap (rename σ)) m = hilbFn P (m ∘ E.symm)

def RenameIntNum.Statement : Prop :=
  ∀ (F : Type u) [Field F] (S K' : Type) [DecidableEq S] [DecidableEq K'] (κ : S → Type)
    (ι' : K' → Type) (E : S ≃ K') (σ : (Σ s, κ s) ≃ (Σ k', ι' k')), (∀ v, (σ v).1 = E v.1) →
    ∀ (P : Ideal (MRing ι' F)) (n : ℕ) (bs : Fin n → S → ℤ),
      intNum F (P.comap (rename σ)) bs = intNum F P (fun i => bs i ∘ E.symm)

def RenameMultiProjPrime.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (S K' : Type) [DecidableEq S] [DecidableEq K'] (κ : S → Type)
    (ι' : K' → Type) (E : S ≃ K') (σ : (Σ s, κ s) ≃ (Σ k', ι' k')), (∀ v, (σ v).1 = E v.1) →
    ∀ P : Ideal (MRing ι' R), IsMultiProjPrime P → IsMultiProjPrime (P.comap (rename σ))

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

