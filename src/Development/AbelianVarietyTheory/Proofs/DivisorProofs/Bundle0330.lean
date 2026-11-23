module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Formalism.SatakeDualWeyl.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0093
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0294

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexEqOfSurj
section
open GlobalTheory.LGrp GlobalTheory.BorelUMod Formalism.UG

noncomputable section
namespace GlobalTheory.BorelUMod.Cayley

theorem relIndex_eq_of_surj {G A : Type} [Group G] [AddGroup A] (H K : Subgroup G) (B D : AddSubgroup A)
    (f : K → D) (hf : Function.Surjective f)
    (h : ∀ u u' : K, (u : G)⁻¹ * u' ∈ H ↔ -(f u : A) + f u' ∈ B) : H.relIndex K = B.relIndex D := by
  have h' : ∀ u u' : K, (QuotientGroup.leftRel (H.subgroupOf K)) u u' ↔
      (QuotientAddGroup.leftRel (B.addSubgroupOf D)) (f u) (f u') := fun u u' => by
    rw [QuotientGroup.leftRel_apply, QuotientAddGroup.leftRel_apply]
    exact h u u'
  refine Nat.card_congr (Equiv.ofBijective (Quotient.map' f fun a b e => (h' a b).1 e) ⟨?_, ?_⟩)
  · intro x y
    refine Quotient.inductionOn₂' x y fun a b e => ?_
    exact Quotient.sound' ((h' a b).2 (Quotient.exact' e))
  · intro x
    refine Quotient.inductionOn' x fun a => ?_
    obtain ⟨b, rfl⟩ := hf a
    exact ⟨Quotient.mk'' b, rfl⟩

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem pow_apply_eq_zero {y : Matrix (Fin n) (Fin n) L} (hy : ∀ i j, j ≤ i → y i j = 0) (k : ℕ) :
    ∀ i j : Fin n, j.val < i.val + k → (y ^ k) i j = 0 := by
  first
  | exact @_root_.GlobalTheory.StrictUpperNilpotent.pow_apply_eq_zero_of_strictUpper
  | exact _root_.GlobalTheory.StrictUpperNilpotent.pow_apply_eq_zero_of_strictUpper
  | (apply _root_.GlobalTheory.StrictUpperNilpotent.pow_apply_eq_zero_of_strictUpper <;> assumption)
  | (intros; apply _root_.GlobalTheory.StrictUpperNilpotent.pow_apply_eq_zero_of_strictUpper <;> assumption)
  | (intros; apply @_root_.GlobalTheory.StrictUpperNilpotent.pow_apply_eq_zero_of_strictUpper <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.StrictUpperNilpotent.pow_apply_eq_zero_of_strictUpper ..)

theorem pow_succ_mem {c : Fin n → Fin n → ℤ} (hc : IsWeight c) {y : Matrix (Fin n) (Fin n) L}
    (hy : y ∈ upLat L c) (k : ℕ) : y ^ (k + 1) ∈ upLat L c := by
  induction k with
  | zero => simpa using hy
  | succ k ih => rw [pow_succ]; exact mul_mem_upLat hc.2 ih hy

theorem exists_inv {c : Fin n → Fin n → ℤ} (hc : IsWeight c) {y : Matrix (Fin n) (Fin n) L}
    (hy : y ∈ upLat L c) : ∃ z ∈ upLat L c, (1 + y) * (1 + z) = 1 ∧ (1 + z) * (1 + y) = 1 := by
  have hy' : -y ∈ upLat L c := neg_mem hy
  have h0 : (-y) ^ (n + 1) = 0 := by
    ext i j
    exact pow_apply_eq_zero hy'.1 _ i j (by have := j.2; omega)
  have h1 : (1 + y) * (1 + ∑ k ∈ Finset.range n, (-y) ^ (k + 1)) = 1 := by
    have := mul_neg_geom_sum (-y) (n + 1)
    rw [h0, sub_zero, sub_neg_eq_add, Finset.sum_range_succ', pow_zero, add_comm _ (1 : Matrix (Fin n) (Fin n) L)] at this
    simpa [add_comm] using this
  exact ⟨_, sum_mem fun k _ => pow_succ_mem hc hy' k, h1, mul_eq_one_comm.1 h1⟩

theorem unit_mul_mem {c C : Fin n → Fin n → ℤ} (hI : IsIdealWeight c C) {a b x : Matrix (Fin n) (Fin n) L}
    (ha : a ∈ upLat L c) (hb : b ∈ upLat L c) (hx : x ∈ upLat L C) : (1 + a) * x * (1 + b) ∈ upLat L C := by
  have h1 : (1 + a) * x ∈ upLat L C := by
    rw [add_mul, one_mul]; exact add_mem hx (mul_mem_upLat hI.2.1 ha hx)
  rw [mul_add, mul_one]
  exact add_mem h1 (mul_mem_upLat hI.2.2 h1 hb)

theorem unit_mul_mem_iff {c C : Fin n → Fin n → ℤ} (hc : IsWeight c) (hI : IsIdealWeight c C)
    {a b x : Matrix (Fin n) (Fin n) L} (ha : a ∈ upLat L c) (hb : b ∈ upLat L c) :
    (1 + a) * x * (1 + b) ∈ upLat L C ↔ x ∈ upLat L C := by
  refine ⟨fun hx => ?_, unit_mul_mem hI ha hb⟩
  obtain ⟨a', ha', -, e1⟩ := exists_inv hc ha
  obtain ⟨b', hb', e2, -⟩ := exists_inv hc hb
  have := unit_mul_mem hI ha' hb' hx
  rwa [← mul_assoc, ← mul_assoc, e1, one_mul, mul_assoc, e2, mul_one] at this

def cay (t : L) (u : Matrix (Fin n) (Fin n) L) : Matrix (Fin n) (Fin n) L := (1 + t • (u - 1))⁻¹ * (u - 1)

theorem cay_eq {c : Fin n → Fin n → ℤ} (hc : IsWeight c) {t : L} (ht : Valued.v t ≤ 1)
    {u : Matrix (Fin n) (Fin n) L} (hu : u - 1 ∈ upLat L c) :
    ∃ z ∈ upLat L c, (1 + t • (u - 1)) * (1 + z) = 1 ∧ (1 + z) * (1 + t • (u - 1)) = 1 ∧
      cay t u = (1 + z) * (u - 1) := by
  obtain ⟨z, hz, e1, e2⟩ := exists_inv hc (smul_mem_upLat ht hu)
  exact ⟨z, hz, e1, e2, by rw [cay, Matrix.inv_eq_right_inv e1]⟩

theorem cay_mem {c : Fin n → Fin n → ℤ} (hc : IsWeight c) {t : L} (ht : Valued.v t ≤ 1)
    {u : Matrix (Fin n) (Fin n) L} (hu : u - 1 ∈ upLat L c) : cay t u ∈ upLat L c := by
  obtain ⟨z, hz, -, -, e⟩ := cay_eq hc ht hu
  rw [e, add_mul, one_mul]
  exact add_mem hu (mul_mem_upLat hc.2 hz hu)

theorem cay_skew {c : Fin n → Fin n → ℤ} (hc : IsWeight c) {σ : L →+* L} {t : L} (ht : Valued.v t ≤ 1)
    (hσ : t + σ t = 1) {u : Matrix (Fin n) (Fin n) L} (hu : u - 1 ∈ upLat L c) (huv : u * adjJ σ u = 1) :
    cay t u ∈ skewJ σ n := by
  obtain ⟨z, -, e1, e2, e⟩ := cay_eq hc ht hu
  have e3 := congrArg (adjJ σ) e2
  rw [adjJ_mul, adjJ_one, adjJ_add, adjJ_smul, adjJ_sub, adjJ_one] at e3
  rw [mem_skewJ, e, adjJ_mul, adjJ_sub, adjJ_one]
  set v := adjJ σ u
  set W := 1 + z
  set W' := adjJ σ W
  have hs : σ t = 1 - t := by linear_combination hσ
  have key : (1 + t • (u - 1)) * (v - 1) = -((u - 1) * (1 + σ t • (v - 1))) := by
    simp only [hs, add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, huv]
    module
  calc (v - 1) * W' = W * ((1 + t • (u - 1)) * (v - 1)) * W' := by rw [← mul_assoc W, e2, one_mul]
    _ = -(W * (u - 1)) := by
      rw [key, mul_neg, neg_mul, mul_assoc, mul_assoc, e3, mul_one]

theorem cay_sub_mem_iff {c C : Fin n → Fin n → ℤ} (hc : IsWeight c) (hI : IsIdealWeight c C) {t : L}
    (ht : Valued.v t ≤ 1) {u u' : Matrix (Fin n) (Fin n) L} (hu : u - 1 ∈ upLat L c) (hu' : u' - 1 ∈ upLat L c) :
    -cay t u + cay t u' ∈ upLat L C ↔ u' - u ∈ upLat L C := by
  obtain ⟨z, hz, e1, e2, e⟩ := cay_eq hc ht hu
  obtain ⟨z', hz', e1', e2', e'⟩ := cay_eq hc ht hu'
  rw [← unit_mul_mem_iff hc hI hz hz' (x := u' - u)]
  have hcomm : (1 + z') * (u' - 1) = (u' - 1) * (1 + z') := by
    have : (u' - 1) * (1 + t • (u' - 1)) = (1 + t • (u' - 1)) * (u' - 1) := by
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    calc (1 + z') * (u' - 1) = (1 + z') * ((u' - 1) * (1 + t • (u' - 1))) * (1 + z') := by
          rw [mul_assoc, mul_assoc, e1', mul_one]
      _ = _ := by rw [this, ← mul_assoc, e2', one_mul]
  have key : u' - u = (1 + t • (u - 1)) * (u' - 1) - (u - 1) * (1 + t • (u' - 1)) := by
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    abel
  have : (1 + z) * (u' - u) * (1 + z') = -cay t u + cay t u' := by
    rw [key, mul_sub, sub_mul, ← mul_assoc, e2, one_mul, mul_assoc, mul_assoc, e1', mul_one, e, e', hcomm]
    abel
  rw [this]

theorem cay_surj {c : Fin n → Fin n → ℤ} (hc : IsWeight c) {σ : L →+* L} (hσσ : ∀ x, σ (σ x) = x) {t : L}
    (ht : Valued.v t ≤ 1) (hσ : t + σ t = 1) {X : Matrix (Fin n) (Fin n) L} (hX : X ∈ upLat L c)
    (hs : X ∈ skewJ σ n) : ∃ u, u - 1 ∈ upLat L c ∧ adjJ σ u * u = 1 ∧ cay t u = X := by
  obtain ⟨z, hz, e1, e2⟩ := exists_inv hc (neg_mem (smul_mem_upLat ht hX))
  rw [mem_skewJ] at hs
  have hst : σ t = 1 - t := by linear_combination hσ
  have e3 := congrArg (adjJ σ) e1
  rw [← sub_eq_add_neg] at e1 e2 e3
  rw [adjJ_mul, adjJ_one, adjJ_sub, adjJ_smul, adjJ_one, hs, smul_neg, sub_neg_eq_add] at e3
  set T := 1 + z with hT
  have h1 : (1 + σ t • X) * T - 1 = X * T := by
    have : (1 + σ t • X) = X + (1 - t • X) := by rw [hst]; module
    rw [this, add_mul, e1, add_sub_cancel_right]
  refine ⟨(1 + σ t • X) * T, ?_, ?_, ?_⟩
  · rw [h1, hT, mul_add, mul_one]
    exact add_mem hX (mul_mem_upLat hc.2 hX hz)
  · rw [adjJ_mul, adjJ_add σ 1 (σ t • X), adjJ_smul, adjJ_one, hs, hσσ, smul_neg, ← sub_eq_add_neg]
    have : (1 - t • X) * (1 + σ t • X) = (1 + σ t • X) * (1 - t • X) := by
      simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
      module
    rw [mul_assoc, ← mul_assoc (1 - t • X), this, mul_assoc, e1, mul_one, e3]
  · have h2 : 1 + t • (X * T) = T := by
      have := e1
      rw [sub_mul, one_mul, smul_mul_assoc] at this
      rw [← this]; abel
    have h3 : (1 - t • X) * X = X * (1 - t • X) := by
      simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    rw [cay, h1, h2, Matrix.inv_eq_left_inv e1, ← mul_assoc, h3, mul_assoc, e1, mul_one]

theorem relIndex_unipLat (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ)
    (h : IsUnramInv ϖ σ q) (c C : Fin n → Fin n → ℤ) (hc : IsWeight c) (hC : IsWeight C) (hI : IsIdealWeight c C) :
    (unipLat h.2.1 hC).relIndex (unipLat h.2.1 hc) =
      (upLat L C ⊓ skewJ σ n).relIndex (upLat L c ⊓ skewJ σ n) := by
  obtain ⟨⟨t, ht, hσ⟩, -⟩ := exists_trace_one h
  have hadj : ∀ u : (borelU σ n).U, (u.1.1⁻¹).val = adjJ σ u.1.1.val := fun u => (mem_GU_iff_adjJ σ _).1 u.1.2
  have hsk : ∀ u : unipLat h.2.1 hc, cay t u.1.1.1.val ∈ skewJ σ n := fun u =>
    cay_skew hc ht hσ u.2 (by rw [← hadj, Units.mul_inv])
  refine relIndex_eq_of_surj _ _ _ _ (fun u => ⟨cay t u.1.1.1.val, cay_mem hc ht u.2, hsk u⟩) ?_ ?_
  · rintro ⟨X, hX, hs⟩
    obtain ⟨u, hu, e1, e⟩ := cay_surj hc h.1 ht hσ hX hs
    let g : GL (Fin n) L := ⟨u, adjJ σ u, mul_eq_one_comm.1 e1, e1⟩
    have hg : g ∈ GU σ n := (mem_GU_iff_adjJ σ g).2 rfl
    have hU : (⟨g, hg⟩ : GU σ n) ∈ (borelU σ n).U := by
      rw [mem_borelU_U]
      refine ⟨fun i j e => ?_, fun i => ?_⟩
      · have := hu.1 i j (le_of_lt e)
        rw [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_gt e), sub_zero] at this
        exact this
      · have := hu.1 i i le_rfl
        rw [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] at this
        exact this
    exact ⟨⟨⟨⟨g, hg⟩, hU⟩, hu⟩, Subtype.ext e⟩
  · intro u u'
    have h1 : (u.1.1.1⁻¹).val - 1 ∈ upLat L c := (unipLat h.2.1 hc).inv_mem u.2
    have h2 := unit_mul_mem_iff hc hI (x := u'.1.1.1.val - u.1.1.1.val) h1 (zero_mem _)
    rw [add_zero, mul_one, add_sub_cancel, mul_sub, Units.inv_mul] at h2
    show (u.1.1.1⁻¹).val * u'.1.1.1.val - 1 ∈ upLat L C ↔
      -cay t u.1.1.1.val + cay t u'.1.1.1.val ∈ upLat L C ⊓ skewJ σ n
    rw [h2, AddSubgroup.mem_inf, cay_sub_mem_iff hc hI ht u.2 u'.2]
    exact ⟨fun e => ⟨e, add_mem (neg_mem (hsk u)) (hsk u')⟩, fun e => e.1⟩

end GlobalTheory.BorelUMod.Cayley
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomPowerSeriesEqOfRescale
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem coeff_mul_of_coeff_lt_eq_zero {R : Type} [CommRing R] (φ δ : PowerSeries R) (j : ℕ)
    (h : ∀ i < j, PowerSeries.coeff i δ = 0) :
    PowerSeries.coeff j (φ * δ) = PowerSeries.constantCoeff φ * PowerSeries.coeff j δ := by
  rw [PowerSeries.coeff_mul, Finset.sum_eq_single (0, j)]
  · simp
  · rintro ⟨a, b⟩ hp hne
    have hp : a + b = j := by simpa using hp
    have hb : b < j := by
      by_contra hb
      have ha : a = 0 := by omega
      have hb' : b = j := by omega
      subst ha hb'
      exact hne rfl
    rw [h _ hb, mul_zero]
  · intro hn
    exact absurd (by simp) hn

theorem ringHom_powerSeries_eq_of_rescale :
    ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (c : R) (n : ℕ), ε.comp π = RingHom.id B → m.comp π = π → ε.comp m = ε → (∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2) → 0 < n → (∀ j, n ≤ j → IsUnit (c ^ j - 2)) → ∀ γ γ' : A →+* PowerSeries R, γ.comp π = PowerSeries.C.comp β → γ'.comp π = PowerSeries.C.comp β → PowerSeries.constantCoeff.comp γ = β.comp ε → PowerSeries.constantCoeff.comp γ' = β.comp ε → (PowerSeries.rescale c).comp γ = γ.comp m → (PowerSeries.rescale c).comp γ' = γ'.comp m → (∀ j < n, ∀ f, PowerSeries.coeff j (γ f) = PowerSeries.coeff j (γ' f)) → γ = γ' := by
  intro A B R _ _ _ π ε m β c n hεπ hmπ _hεm hm hn hc γ γ' hγπ hγ'π hγ0 hγ'0 hγm hγ'm hlow
  have hεπ' : ∀ b, ε (π b) = b := fun b => by simpa using RingHom.congr_fun hεπ b
  have hmπ' : ∀ b, m (π b) = π b := fun b => by simpa using RingHom.congr_fun hmπ b
  have hγπ' : ∀ b, γ (π b) = PowerSeries.C (β b) := fun b => by simpa using RingHom.congr_fun hγπ b
  have hγ'π' : ∀ b, γ' (π b) = PowerSeries.C (β b) := fun b => by simpa using RingHom.congr_fun hγ'π b
  have hc0 : ∀ f, PowerSeries.constantCoeff (γ f) = β (ε f) := fun f => by
    simpa using RingHom.congr_fun hγ0 f
  have hc0' : ∀ f, PowerSeries.constantCoeff (γ' f) = β (ε f) := fun f => by
    simpa using RingHom.congr_fun hγ'0 f
  have hγm' : ∀ f, γ (m f) = PowerSeries.rescale c (γ f) := fun f => by
    simpa using (RingHom.congr_fun hγm f).symm
  have hγ'm' : ∀ f, γ' (m f) = PowerSeries.rescale c (γ' f) := fun f => by
    simpa using (RingHom.congr_fun hγ'm f).symm
  have hcoeff : ∀ j, ∀ f, PowerSeries.coeff j (γ f) = PowerSeries.coeff j (γ' f) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
    rcases lt_or_ge j n with hj | hj
    · exact hlow j hj
    have hj0 : j ≠ 0 := by omega
    obtain ⟨D, hD⟩ : ∃ D : A → R, ∀ f, D f = PowerSeries.coeff j (γ f) - PowerSeries.coeff j (γ' f) :=
      ⟨_, fun _ => rfl⟩
    have hlowδ : ∀ f, ∀ i < j, PowerSeries.coeff i (γ f - γ' f) = 0 := by
      intro f i hi; rw [map_sub, ih i hi f, sub_self]
    have Dadd : ∀ f g, D (f + g) = D f + D g := by
      intro f g; simp only [hD, map_add (f := _)]; ring
    have Dsub : ∀ f g, D (f - g) = D f - D g := by
      intro f g; simp only [hD, map_sub]; ring
    have Dmul : ∀ f g, D (f * g) = β (ε f) * D g + β (ε g) * D f := by
      intro f g
      have e : γ (f * g) - γ' (f * g) = γ f * (γ g - γ' g) + γ' g * (γ f - γ' f) := by
        rw [map_mul, map_mul]; ring
      have h1 := coeff_mul_of_coeff_lt_eq_zero (γ f) _ j (hlowδ g)
      have h2 := coeff_mul_of_coeff_lt_eq_zero (γ' g) _ j (hlowδ f)
      have h3 : D (f * g) = PowerSeries.coeff j (γ (f * g) - γ' (f * g)) := by
        rw [hD, map_sub]
      rw [h3, e, map_add (f := _), h1, h2, hc0, hc0', map_sub, map_sub, hD, hD]
    have Dπ : ∀ b, D (π b) = 0 := by
      intro b; rw [hD, hγπ', hγ'π', PowerSeries.coeff_C, if_neg hj0, sub_self]
    have Dsq : ∀ x ∈ RingHom.ker ε ^ 2, D x = 0 := by
      intro x hx
      rw [pow_two] at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro a ha b hb
        rw [RingHom.mem_ker] at ha hb
        rw [Dmul, ha, hb, map_zero, zero_mul, zero_mul, add_zero]
      · intro x y hx hy
        rw [Dadd, hx, hy, add_zero]
    have Dm2 : ∀ f, D (m f) = 2 * D f := by
      intro f
      set f0 := f - π (ε f) with hf0
      have hf0k : f0 ∈ RingHom.ker ε := by
        rw [RingHom.mem_ker, hf0, map_sub, hεπ', sub_self]
      have hmf : m f = π (ε f) + m f0 := by
        rw [hf0, map_sub, hmπ']; ring
      have hff : f = π (ε f) + f0 := by rw [hf0]; ring
      have hDf : D f = D f0 := by
        conv_lhs => rw [hff]
        rw [Dadd, Dπ, zero_add]
      have hsplit : m f0 = (m f0 - 2 * f0) + (f0 + f0) := by ring
      rw [hmf, Dadd, Dπ, zero_add, hsplit, Dadd, Dsq _ (hm f0 hf0k), Dadd, hDf]
      ring
    have Dmc : ∀ f, D (m f) = c ^ j * D f := by
      intro f
      rw [hD, hD, hγm', hγ'm', PowerSeries.coeff_rescale, PowerSeries.coeff_rescale]
      ring
    intro f
    have h0 : (c ^ j - 2) * D f = 0 := by
      have := (Dmc f).symm.trans (Dm2 f)
      rw [sub_mul, this, sub_self]
    have hDf0 : D f = 0 := (hc j hj).mul_right_eq_zero.mp h0
    rw [hD] at hDf0
    exact sub_eq_zero.mp hDf0
  exact RingHom.ext fun f => PowerSeries.ext fun j => hcoeff j f

end GlobalTheory.Nef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecEqZeroOfLoc
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.KummerSplit

def unitsT : CommRingCat.{0} ⥤ Type where
  obj A := (A : Type)ˣ
  map {A B} f := TypeCat.ofHom fun (u : (A : Type)ˣ) => Units.map f.hom.toMonoidHom u
  map_id A := by ext u; rfl
  map_comp f g := by ext u; rfl

structure Trip (q : ℕ) (A : Type) [CommRing A] where
  root : Prim q A
  src : Aˣ
  tgt : Aˣ
  tgt_eq : (tgt : A) = root.1 * src

def Trip.map {q : ℕ} {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x : Trip q A) : Trip q B :=
  ⟨x.root.map f, Units.map f.toMonoidHom x.src, Units.map f.toMonoidHom x.tgt, by
    change f (x.tgt : A) = f x.root.1 * f (x.src : A)
    rw [x.tgt_eq, map_mul]⟩

def tripT (q : ℕ) : CommRingCat.{0} ⥤ Type where
  obj A := Trip q A
  map f := TypeCat.ofHom (Trip.map f.hom)
  map_id A := by
    ext x
    cases x
    rfl
  map_comp f g := by
    ext x
    cases x
    rfl

def unitsP : PSh := Scheme.Γ ⋙ unitsT

def tripP (q : ℕ) : PSh := Scheme.Γ ⋙ tripT q

def unitsP.mk {U : Scheme.{0}} (v : (Γ(U, ⊤))ˣ) : unitsP.obj (op U) := v

def tripP.mk {q : ℕ} {U : Scheme.{0}} (x : Trip q Γ(U, ⊤)) : (tripP q).obj (op U) := x

def tripP.get {q : ℕ} {U : Scheme.{0}} (x : (tripP q).obj (op U)) : Trip q Γ(U, ⊤) := x

theorem unitsP.map_mk {V U : Scheme.{0}} (g : V ⟶ U) (v : (Γ(U, ⊤))ˣ) :
    unitsP.map g.op (unitsP.mk v) = unitsP.mk (Units.map g.appTop.hom.toMonoidHom v) := rfl

theorem smap_sum {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} {ι : Type} (c : ι →₀ ULift.{1} R) (f : ι → Sec F U) :
    Sec.map φ (c.sum fun x r => r • f x) = c.sum fun x r => r • Sec.map φ (f x) := by
  simp only [Sec.map, map_finsuppSum, map_smul]

theorem res_sum {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) {ι : Type} (c : ι →₀ ULift.{1} R) (f : ι → Sec F U) :
    Sec.res g (c.sum fun x r => r • f x) = c.sum fun x r => r • Sec.res g (f x) := by
  simp only [Sec.res, map_finsuppSum, map_smul]

theorem smap_sub {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a - b) = Sec.map φ a - Sec.map φ b := map_sub _ _ _

theorem res_sub {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (a b : Sec F U) :
    Sec.res g (a - b) = Sec.res g a - Sec.res g b := map_sub _ _ _

theorem res_zero' {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) :
    Sec.res g (0 : Sec F U) = 0 := map_zero _

theorem sec_eq_zero_of_loc {R : Type} [CommRing R] (F : Shv R) {U : Scheme.{0}} (s : Sec F U)
    (h : Loc U fun _ g => Sec.res g s = 0) : s = 0 := by
  obtain ⟨S, hS, hS'⟩ := h
  exact Sheaf.isSeparated F U S hS s 0 (fun V g hg => (hS' V g hg).trans (map_zero _).symm)

theorem sec_res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  change ((φ.hom.app (op U)) ≫ G.obj.map g.op).hom x = (F.obj.map g.op ≫ φ.hom.app (op V)).hom x
  rw [φ.hom.naturality]

theorem sec_map_comp {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

end GlobalTheory.EtC.KummerSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecSigmaBijective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem ofArrows_sigmaι_mem_etale {ι : Type} (V : ι → Scheme.{0}) :
    Presieve.ofArrows V (Sigma.ι V) ∈ Scheme.etalePrecoverage (∐ V) := by
  refine (Scheme.ofArrows_mem_precoverage_iff _).2 ⟨fun x => ?_, fun i => inferInstance⟩
  obtain ⟨i, y, hy⟩ := (sigmaOpenCover V).exists_eq x
  exact ⟨i, y, hy⟩

theorem sec_subsingleton_of_isEmpty {R : Type} [CommRing R] (F : Shv R) (Z : Scheme.{0}) [IsEmpty Z] :
    Subsingleton (Sec F Z) := by
  have hF : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget _) :=
    (isSheaf_iff_isSheaf_of_type _ _).1 ((sheafCompose Scheme.etaleTopology (forget (ModuleCat.{1} (ULift.{1} R)))).obj F).property
  have hmem : (⊥ : Sieve Z) ∈ Scheme.etaleTopology Z := Scheme.bot_mem_grothendieckTopology (P := @Etale) Z
  refine ⟨fun a b => (hF _ hmem).isSeparatedFor.ext fun _ _ hf => ?_⟩
  simp at hf

theorem sec_sigma_bijective : ∀ (R : Type) [CommRing R] (F : Shv R) {ι : Type} (V : ι → Scheme.{0}), Function.Bijective fun (a : Sec F (∐ V)) (i : ι) => Sec.res (Sigma.ι V i) a := by
  intro R _ F ι V
  have hF : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget _) :=
    (isSheaf_iff_isSheaf_of_type _ _).1 ((sheafCompose Scheme.etaleTopology (forget (ModuleCat.{1} (ULift.{1} R)))).obj F).property
  have h := hF.isSheafFor _ (Precoverage.generate_mem_toGrothendieck (ofArrows_sigmaι_mem_etale V))
  rw [Presieve.isSheafFor_arrows_iff] at h
  have hc : ∀ x : ∀ i, Sec F (V i), Presieve.Arrows.Compatible (F.obj ⋙ forget _) (Sigma.ι V) x := by
    intro x i j Z gi gj hij
    by_cases e : i = j
    · subst e
      obtain rfl := (cancel_mono (Sigma.ι V i)).1 hij
      rfl
    · have : IsEmpty Z := ⟨fun z => (isEmpty_pullback_sigmaι_of_ne V e).false ((pullback.lift gi gj hij).base z)⟩
      have := sec_subsingleton_of_isEmpty F Z
      exact Subsingleton.elim _ _
  refine ⟨fun a b hab => ?_, fun x => ?_⟩
  · obtain ⟨t, -, ht⟩ := h (fun i => Sec.res (Sigma.ι V i) a) (hc _)
    exact (ht a fun i => rfl).trans (ht b fun i => (congrFun hab i).symm).symm
  · obtain ⟨t, ht, -⟩ := h x (hc x)
    exact ⟨t, funext ht⟩

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionInverseIntoSlice
section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory.RankFibreKer

theorem eq_of_isFirstMax_of_isFirstMax {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a d : ℕ} {Y : Matrix (Fin a) (Fin d) k} {J J' : Fin a ↪ Fin d} (h : IsFirstMax Y J) (h' : IsFirstMax Y J') :
    J = J' := by
  apply idx.injective
  rcases lt_trichotomy (idx J) (idx J') with hl | he | hl
  · exact absurd ((h'.2 J).2 hl) (not_lt.2 (h.2 J').1)
  · exact he
  · exact absurd ((h.2 J').2 hl) (not_lt.2 (h'.2 J).1)

theorem sec_inv_mul_mem_slice : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Y : Matrix (Fin a) (Fin d) k) (J : Fin a ↪ Fin d), IsFirstMax Y J →
    ((GlobalTheory.RankFibreKer.sec Y)⁻¹).val * Y ∈ slice (k := k) a d := by
  intro k _ _ _ _ a d Y J hJ
  have hex : ∃ J, IsFirstMax Y J := ⟨J, hJ⟩
  have hc : hex.choose = J := eq_of_isFirstMax_of_isFirstMax hex.choose_spec hJ
  have hs : (sec Y).val = Y.submatrix id J := by
    unfold sec
    rw [dite_eq_left hex]
    show Y.submatrix id hex.choose = _
    rw [hc]
  have hsub : (((sec Y)⁻¹).val * Y).submatrix id J = ((sec Y)⁻¹).val * Y.submatrix id J := by
    ext i j; simp [Matrix.mul_apply]
  have hdet : (((sec Y)⁻¹).val).det = (minor Y J)⁻¹ := by
    have e := congrArg Matrix.det (sec Y).inv_mul
    rw [Matrix.det_mul, Matrix.det_one, hs] at e
    exact eq_inv_of_mul_eq_one_left e
  refine ⟨J, ?_, fun J' => ?_⟩
  · rw [hsub, ← hs]; exact (sec Y).inv_mul
  · rw [minor_mul, hdet, map_mul, map_inv₀]
    have h0 : valuation k (minor Y J) ≠ 0 := by simpa using hJ.1
    constructor
    · rw [inv_mul_le_iff₀ (zero_lt_iff.2 h0), mul_one]; exact (hJ.2 J').1
    · intro hl
      rw [inv_mul_lt_iff₀ (zero_lt_iff.2 h0), mul_one]; exact (hJ.2 J').2 hl

end GlobalTheory.RankFibreKer
end

