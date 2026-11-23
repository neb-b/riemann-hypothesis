module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0126
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0022

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardHilbertEisensteinFourierFiberLeNorm
section
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

noncomputable section

namespace GlobalTheory.QFiber

open FractionalIdeal

variable {F : Type} [Field F] [NumberField F]

def toIdeal (K : FractionalIdeal (𝓞 F)⁰ F) : Ideal (𝓞 F) :=
  open Classical in if h : K ≤ 1 then (le_one_iff_exists_coeIdeal.mp h).choose else ⊥

theorem coe_toIdeal {K : FractionalIdeal (𝓞 F)⁰ F} (h : K ≤ 1) :
    ((toIdeal K : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = K := by
  unfold toIdeal
  rw [dite_eq_left h]
  exact (le_one_iff_exists_coeIdeal.mp h).choose_spec

theorem nrm_nonneg (𝔞 : Frac F) : 0 ≤ nrm 𝔞 := by
  unfold nrm; exact_mod_cast absNorm_nonneg _

theorem emb_nonempty [IsTotallyReal F] : Nonempty (Emb F) := by
  obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
  exact ⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding⟩

theorem card_le_norm : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔞 𝔟 : Frac F) (ξ : F)
    (s : Finset (Quotient (qRel 𝔞 𝔟))), (∀ c ∈ s, c.out.1.1 * c.out.1.2 = ξ) →
    (s.card : ℝ) ≤ |(Algebra.norm ℚ ξ : ℝ)| / (nrm 𝔞 * nrm 𝔟) := by
  intro F _ _ _ 𝔞 𝔟 ξ s hs
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨c0, hc0⟩
  · simp only [Finset.card_empty, Nat.cast_zero]
    exact div_nonneg (abs_nonneg _) (mul_nonneg (nrm_nonneg 𝔞) (nrm_nonneg 𝔟))
  have hA : ((𝔞 : FractionalIdeal (𝓞 F)⁰ F)) ≠ 0 := 𝔞.ne_zero
  have hB : ((𝔟 : FractionalIdeal (𝓞 F)⁰ F)) ≠ 0 := 𝔟.ne_zero
  have hξ : ξ ≠ 0 := by
    obtain ⟨τ⟩ := emb_nonempty (F := F)
    have h := c0.out.2.2.2 τ
    rw [hs c0 hc0] at h
    intro h0
    rw [h0, map_zero] at h
    exact lt_irrefl _ h
  have hle : ∀ c : Quotient (qRel 𝔞 𝔟),
      spanSingleton (𝓞 F)⁰ c.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ ≤ 1 := fun c => by
    calc _ ≤ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ :=
          by gcongr; exact spanSingleton_le_iff_mem.mpr c.out.2.1
      _ = 1 := mul_inv_cancel₀ hA
  have hIle : ∀ c ∈ s, spanSingleton (𝓞 F)⁰ ξ * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ * (𝔟 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ ≤
      spanSingleton (𝓞 F)⁰ c.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ := by
    intro c hc
    have hb : spanSingleton (𝓞 F)⁰ c.out.1.2 * (𝔟 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ ≤ 1 := by
      calc _ ≤ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) * (𝔟 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ :=
            by gcongr; exact spanSingleton_le_iff_mem.mpr c.out.2.2.1
        _ = 1 := mul_inv_cancel₀ hB
    rw [← hs c hc, ← spanSingleton_mul_spanSingleton]
    calc spanSingleton (𝓞 F)⁰ c.out.1.1 * spanSingleton (𝓞 F)⁰ c.out.1.2 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ *
          (𝔟 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ =
          (spanSingleton (𝓞 F)⁰ c.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹) *
          (spanSingleton (𝓞 F)⁰ c.out.1.2 * (𝔟 : FractionalIdeal (𝓞 F)⁰ F)⁻¹) := by ring
      _ ≤ (spanSingleton (𝓞 F)⁰ c.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹) * 1 := by gcongr
      _ = _ := mul_one _
  have hI1 := (hIle c0 hc0).trans (hle c0)
  set I := toIdeal (spanSingleton (𝓞 F)⁰ ξ * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ * (𝔟 : FractionalIdeal (𝓞 F)⁰ F)⁻¹) with hIdef
  let f : Quotient (qRel 𝔞 𝔟) → Ideal (𝓞 F) := fun c =>
    toIdeal (spanSingleton (𝓞 F)⁰ c.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹)
  have hIJ : ∀ c ∈ s, I ≤ f c := by
    intro c hc
    rw [← coeIdeal_le_coeIdeal F, coe_toIdeal hI1, coe_toIdeal (hle c)]
    exact hIle c hc
  have hI0 : I ≠ ⊥ := by
    intro h
    have h' := coe_toIdeal hI1
    rw [← hIdef, h, coeIdeal_bot] at h'
    have := h'.symm
    simp only [mul_eq_zero, spanSingleton_eq_zero_iff, inv_eq_zero] at this
    tauto
  have hinj : Set.InjOn f s := by
    intro c hc c' hc' hcc
    have h1 : spanSingleton (𝓞 F)⁰ c.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ =
        spanSingleton (𝓞 F)⁰ c'.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ := by
      rw [← coe_toIdeal (hle c), ← coe_toIdeal (hle c')]
      exact congrArg _ hcc
    have h2 := mul_right_cancel₀ (inv_ne_zero hA) h1
    obtain ⟨u, hu⟩ := spanSingleton_eq_spanSingleton.mp h2
    rw [Units.smul_def, Algebra.smul_def] at hu
    have hν : c.out.1.1 ≠ 0 := left_ne_zero_of_mul (by rw [hs c hc]; exact hξ)
    have hu0 : algebraMap (𝓞 F) F (u : 𝓞 F) ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]; exact u.ne_zero
    have h4 : algebraMap (𝓞 F) F (u : 𝓞 F) * (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) = 1 := by
      rw [mul_comm]; exact unit_inv_mul u
    have e1 := hs c hc
    have e2 := hs c' hc'
    rw [← hu] at e2
    have hb : c'.out.1.2 = (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * c.out.1.2 := by
      apply mul_left_cancel₀ (mul_ne_zero hu0 hν)
      linear_combination e2 - e1 - c.out.1.1 * c.out.1.2 * h4
    rw [← Quotient.out_eq c, ← Quotient.out_eq c']
    apply Quotient.sound
    refine ⟨u⁻¹, ?_, hb⟩
    rw [inv_inv, ← hu]
  have key : (FractionalIdeal.absNorm ((I : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) : ℚ) =
      |Algebra.norm ℚ ξ| / (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) *
        FractionalIdeal.absNorm (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) := by
    rw [coe_toIdeal hI1, map_mul, map_mul, map_inv₀, map_inv₀, absNorm_span_singleton]
    ring
  rw [coeIdeal_absNorm] at key
  calc (s.card : ℝ) = ((s.image f).card : ℝ) := by rw [Finset.card_image_of_injOn hinj]
    _ ≤ (Ideal.absNorm I : ℝ) := by
      exact_mod_cast _root_.GlobalTheory.card_le_absNorm_of_forall_le F I hI0 (s.image f) (by
        intro J hJ
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hJ
        exact hIJ c hc)
    _ = _ := by
      unfold nrm
      have := congrArg (Rat.cast : ℚ → ℝ) key
      push_cast at this
      exact this

end GlobalTheory.QFiber
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechAndTotalDifferentialAdditiveSquareZero
section
set_option autoImplicit false

namespace GlobalTheory.DI

variable {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E]

theorem delta_add (c c' : Finset ι → E) : delta (c + c') = delta c + delta c' := by
  funext t
  simp only [delta, Pi.add_apply, smul_add, Finset.sum_add_distrib]

theorem delta_sub (c c' : Finset ι → E) : delta (c - c') = delta c - delta c' := by
  funext t
  simp only [delta, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]

theorem delta_delta (c : Finset ι → E) : delta (delta c) = 0 := by
  funext t
  let f : ι × ι → E := fun q =>
    (cubeSign t q.1 * cubeSign (t.erase q.1) q.2) • c ((t.erase q.1).erase q.2)
  have h1 : delta (delta c) t = ∑ q ∈ t.offDiag, f q := by
    show ∑ i ∈ t, cubeSign t i • delta c (t.erase i) = _
    rw [Finset.sum_finset_product t.offDiag t (fun i => t.erase i)
      (fun q => by simp only [Finset.mem_offDiag, Finset.mem_erase]; tauto)]
    refine Finset.sum_congr rfl fun i _ => ?_
    show cubeSign t i • ∑ j ∈ t.erase i, cubeSign (t.erase i) j • c ((t.erase i).erase j) = _
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [f, smul_smul]
  rw [h1, Pi.zero_apply]
  refine Finset.sum_involution (fun q _ => q.swap) (fun q hq => ?_) (fun q hq _ h => ?_)
    (fun q hq => ?_) (fun q _ => rfl)
  · rw [Finset.mem_offDiag] at hq
    simp only [f, Prod.fst_swap, Prod.snd_swap]
    rw [cubeSign_mul_erase hq.1 hq.2.1 hq.2.2, Finset.erase_right_comm (a := q.1) (b := q.2),
      neg_smul, neg_add_cancel]
  · rw [Finset.mem_offDiag] at hq
    exact hq.2.2 (congrArg Prod.snd h)
  · rw [Finset.mem_offDiag] at hq ⊢
    exact ⟨hq.2.1, hq.1, hq.2.2.symm⟩

theorem Dtot_add (d : E →+ E) (c c' : Finset ι → E) : Dtot d (c + c') = Dtot d c + Dtot d c' := by
  funext t
  simp only [Dtot, delta_add, Pi.add_apply, map_add (f := _), smul_add]
  abel

theorem Dtot_sub (d : E →+ E) (c c' : Finset ι → E) : Dtot d (c - c') = Dtot d c - Dtot d c' := by
  funext t
  simp only [Dtot, delta_sub, Pi.sub_apply, map_sub, smul_sub]
  abel

theorem Dtot_Dtot (d : E →+ E) (hd : ∀ x, d (d x) = 0) (c : Finset ι → E) :
    Dtot d (Dtot d c) = 0 := by
  funext t
  have hDt : ∀ s, Dtot d c s = delta c s + (-1 : ℤ) ^ s.card • d (c s) := fun s => rfl
  have e1 : delta (Dtot d c) t = delta (delta c) t +
      ∑ i ∈ t, cubeSign t i • ((-1 : ℤ) ^ (t.erase i).card • d (c (t.erase i))) := by
    show ∑ i ∈ t, cubeSign t i • Dtot d c (t.erase i) = delta (delta c) t + _
    simp only [hDt, smul_add, Finset.sum_add_distrib]
    rfl
  have e2 : d (delta c t) = ∑ i ∈ t, cubeSign t i • d (c (t.erase i)) := by
    show d (∑ i ∈ t, cubeSign t i • c (t.erase i)) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_zsmul d _ _
  show delta (Dtot d c) t + (-1 : ℤ) ^ t.card • d (Dtot d c t) = 0
  rw [e1, delta_delta, hDt, map_add (f := _), map_zsmul, hd, smul_zero, add_zero, e2, Finset.smul_sum,
    Pi.zero_apply, zero_add, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hc : (-1 : ℤ) ^ (t.erase i).card = -(-1 : ℤ) ^ t.card := by
    rw [← Finset.card_erase_add_one hi, pow_succ]; ring
  rw [hc, neg_smul, smul_neg, smul_comm, neg_add_cancel]

theorem delta_Dtot_props : ∀ {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] (d : E →+ E),
    (∀ c c' : Finset ι → E, delta (c + c') = delta c + delta c') ∧
    (∀ c c' : Finset ι → E, delta (c - c') = delta c - delta c') ∧
    (∀ c c' : Finset ι → E, Dtot d (c + c') = Dtot d c + Dtot d c') ∧
    (∀ c c' : Finset ι → E, Dtot d (c - c') = Dtot d c - Dtot d c') ∧
    (∀ c : Finset ι → E, delta (delta c) = 0) ∧
    ((∀ x, d (d x) = 0) → ∀ c : Finset ι → E, Dtot d (Dtot d c) = 0) :=
  fun d => ⟨delta_add, delta_sub, Dtot_add d, Dtot_sub d, delta_delta, fun hd => Dtot_Dtot d hd⟩

end GlobalTheory.DI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechAntisymmetrizedCupProductVanishAboveDegree
section
open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem prodL_eq_zero_of_card {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type}
    [LinearOrder ι] (f : ι → V →+ V) (h : ι → ι → V →+ K) (vs : List V) (t : Finset ι)
    (ht : vs.length + 1 < t.card) : prodL f h vs t = 0 := by
  induction vs generalizing t with
  | nil =>
    simp only [prodL, List.foldr_nil, oneC]
    simp only [List.length_nil] at ht
    rw [if_neg (by omega)]
  | cons v vs ih =>
    change Lop f h v (prodL f h vs) t = 0
    simp only [List.length_cons] at ht
    unfold Lop
    split_ifs with h1 h2
    · have e1 := ih t (by omega)
      have e2 := ih (t.erase (t.min' h1))
        (by rw [Finset.card_erase_of_mem (Finset.min'_mem _ _)]; omega)
      rw [e1, e2, mul_zero, smul_zero, smul_zero, add_zero]
    · have e1 := ih t (by omega)
      rw [e1, mul_zero, smul_zero, add_zero]
    · rfl

theorem alt_and_phi_vanish_above_degree : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) (f : ι → V →+ V) (h : ι → ι → V →+ K), (∀ (a : ℕ) (v : Fin a → V) (t : Finset ι), a + 1 < t.card → alt f h a v t = 0) ∧ ∀ (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)), IsPhi p f h Φ → ∀ a, ∀ x ∈ forms (Set.univ : Set K) (Set.univ : Set V) a, ∀ t : Finset ι, a + 1 < t.card → Φ x t = 0 := by
  intro K _ V _ _ ι _ p f h
  have halt : ∀ (a : ℕ) (v : Fin a → V) (t : Finset ι), a + 1 < t.card → alt f h a v t = 0 := by
    intro a v t ht
    simp only [alt, Finset.sum_apply, Pi.smul_apply]
    apply Finset.sum_eq_zero
    intro σ _
    rw [prodL_eq_zero_of_card f h _ t (by simpa using ht), smul_zero]
  refine ⟨halt, ?_⟩
  intro Φ hΦ a x hx t ht
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, -, v, -, rfl⟩ := hx
    rw [hΦ, Pi.smul_apply, halt a v t ht, smul_zero]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | neg x _ hx => simp [hx]

end GlobalTheory.DI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeltaCupProduct
section
open GlobalTheory GlobalTheory.DI

set_option autoImplicit false

namespace GlobalTheory.DI

section CupDelta

variable {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E]

theorem sum_alt_filter_lt_le (F : Finset ι → E) (u : Finset ι) :
    ∑ j ∈ u, (-1 : ℤ) ^ (u.filter (· < j)).card • (F (u.filter (· < j)) + F (u.filter (· ≤ j))) =
      F ∅ - (-1 : ℤ) ^ u.card • F u := by
  induction u using Finset.induction_on_max with
  | empty => simp
  | insert m u hm ih =>
    have hmu : m ∉ u := fun h => lt_irrefl m (hm m h)
    rw [Finset.sum_insert hmu]
    rw [Finset.sum_congr rfl (g := fun j => (-1 : ℤ) ^ (u.filter (· < j)).card •
        (F (u.filter (· < j)) + F (u.filter (· ≤ j)))) (fun j hj => by
      rw [Finset.filter_insert, if_neg (not_lt.2 (hm j hj).le), Finset.filter_insert,
        if_neg (not_le.2 (hm j hj))]), ih]
    have e1 : (insert m u).filter (· < m) = u := by
      ext x; simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hx, hxm⟩
        · exact absurd hxm (lt_irrefl _)
        · exact hx
      · intro hx; exact ⟨Or.inr hx, hm x hx⟩
    have e2 : (insert m u).filter (· ≤ m) = insert m u := by
      ext x; simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · exact fun h => h.1
      · rintro (rfl | hx)
        · exact ⟨Or.inl rfl, le_rfl⟩
        · exact ⟨Or.inr hx, (hm x hx).le⟩
    rw [e1, e2, Finset.card_insert_of_notMem hmu, pow_succ, smul_add, mul_neg_one, neg_smul]
    abel

theorem delta_cup_eq : ∀ {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E]
    (Φ : E →+ (Finset ι → E)) (c : Finset ι → E), (∀ x, Φ x ∅ = 0) → c ∅ = 0 → ∀ u,
    delta (cup Φ c) u = cup Φ (delta c) u + ∑ j ∈ u, (-1 : ℤ) ^ (u.filter (· < j)).card •
      delta (Φ (c (u.filter (· ≤ j)))) (u.filter (j ≤ ·)) := by
  intro ι _ E _ Φ c hΦ hc u

  have sL : ∀ {i j : ι}, i < j → cubeSign u i = cubeSign (u.filter (· ≤ j)) i := by
    intro i j hij
    have : (u.filter (· ≤ j)).filter (· < i) = u.filter (· < i) := by
      ext x; simp only [Finset.mem_filter]; grind
    unfold cubeSign; rw [this]
  have sR : ∀ {i j : ι}, j < i → cubeSign u i =
      (-1 : ℤ) ^ (u.filter (· < j)).card * cubeSign (u.filter (j ≤ ·)) i := by
    intro i j hji
    have hd : Disjoint (u.filter (· < j)) ((u.filter (j ≤ ·)).filter (· < i)) := by
      rw [Finset.disjoint_left]; intro x h1 h2
      simp only [Finset.mem_filter] at h1 h2
      exact absurd h1.2 (not_lt.2 h2.1.2)
    have : u.filter (· < i) = u.filter (· < j) ∪ (u.filter (j ≤ ·)).filter (· < i) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_union]; grind
    unfold cubeSign; rw [← pow_add, ← Finset.card_union_of_disjoint hd, this]

  have hL : delta (cup Φ c) u = ∑ j ∈ u, ∑ i ∈ u.erase j,
      cubeSign u i • Φ (c ((u.erase i).filter (· ≤ j))) ((u.erase i).filter (j ≤ ·)) := by
    simp only [delta, cup, Finset.smul_sum]
    exact Finset.sum_comm' (fun i j => by simp only [Finset.mem_erase]; tauto)

  have key : ∀ j ∈ u, Φ (delta c (u.filter (· ≤ j))) (u.filter (j ≤ ·)) +
      (-1 : ℤ) ^ (u.filter (· < j)).card • delta (Φ (c (u.filter (· ≤ j)))) (u.filter (j ≤ ·)) =
      ∑ i ∈ u.erase j,
        cubeSign u i • Φ (c ((u.erase i).filter (· ≤ j))) ((u.erase i).filter (j ≤ ·)) +
      (-1 : ℤ) ^ (u.filter (· < j)).card • (Φ (c (u.filter (· < j))) (u.filter (j ≤ ·)) +
        Φ (c (u.filter (· ≤ j))) (u.filter (j < ·))) := by
    intro j hj
    have eL : (u.erase j).filter (· < j) = u.filter (· < j) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_erase]; grind
    have eG : (u.erase j).filter (fun x => ¬ x < j) = u.filter (j < ·) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_erase]; grind
    have eLeL : (u.filter (· ≤ j)).filter (· < j) = u.filter (· < j) := by
      ext x; simp only [Finset.mem_filter]; grind
    have eLeJ : (u.filter (· ≤ j)).filter (fun x => ¬ x < j) = {j} := by
      ext x; simp only [Finset.mem_filter, Finset.mem_singleton]; grind
    have eGeG : (u.filter (j ≤ ·)).filter (j < ·) = u.filter (j < ·) := by
      ext x; simp only [Finset.mem_filter]; grind
    have eGeJ : (u.filter (j ≤ ·)).filter (fun x => ¬ j < x) = {j} := by
      ext x; simp only [Finset.mem_filter, Finset.mem_singleton]; grind
    have eLeE : (u.filter (· ≤ j)).erase j = u.filter (· < j) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_erase]; grind
    have eGeE : (u.filter (j ≤ ·)).erase j = u.filter (j < ·) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_erase]; grind

    rw [← Finset.sum_filter_add_sum_filter_not (u.erase j) (· < j), eL, eG]

    have h1 : Φ (delta c (u.filter (· ≤ j))) (u.filter (j ≤ ·)) =
        ∑ i ∈ u.filter (· < j), cubeSign (u.filter (· ≤ j)) i •
          Φ (c ((u.filter (· ≤ j)).erase i)) (u.filter (j ≤ ·)) +
        (-1 : ℤ) ^ (u.filter (· < j)).card • Φ (c (u.filter (· < j))) (u.filter (j ≤ ·)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [delta, map_sum, map_zsmul, Finset.sum_apply, Pi.smul_apply]
      rw [← Finset.sum_filter_add_sum_filter_not (u.filter (· ≤ j)) (· < j), eLeL, eLeJ,
        Finset.sum_singleton, eLeE]
      congr 2
      unfold cubeSign; rw [eLeL]

    have h2 : delta (Φ (c (u.filter (· ≤ j)))) (u.filter (j ≤ ·)) =
        ∑ i ∈ u.filter (j < ·), cubeSign (u.filter (j ≤ ·)) i •
          Φ (c (u.filter (· ≤ j))) ((u.filter (j ≤ ·)).erase i) +
        Φ (c (u.filter (· ≤ j))) (u.filter (j < ·)) := by
      simp only [delta]
      rw [← Finset.sum_filter_add_sum_filter_not (u.filter (j ≤ ·)) (j < ·), eGeG, eGeJ,
        Finset.sum_singleton, eGeE, cubeSign_eq_one_of_forall_le (by simp), one_smul]
    rw [h1, h2, smul_add, Finset.smul_sum]
    have hA : ∑ i ∈ u.filter (· < j), cubeSign u i •
          Φ (c ((u.erase i).filter (· ≤ j))) ((u.erase i).filter (j ≤ ·)) =
        ∑ i ∈ u.filter (· < j), cubeSign (u.filter (· ≤ j)) i •
          Φ (c ((u.filter (· ≤ j)).erase i)) (u.filter (j ≤ ·)) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hij : i < j := (Finset.mem_filter.1 hi).2
      rw [sL hij, Finset.filter_erase, Finset.filter_erase,
        Finset.erase_eq_of_notMem (s := u.filter (j ≤ ·)) (by simp [hij])]
    have hB : ∑ i ∈ u.filter (j < ·), cubeSign u i •
          Φ (c ((u.erase i).filter (· ≤ j))) ((u.erase i).filter (j ≤ ·)) =
        ∑ i ∈ u.filter (j < ·), (-1 : ℤ) ^ (u.filter (· < j)).card •
          cubeSign (u.filter (j ≤ ·)) i • Φ (c (u.filter (· ≤ j))) ((u.filter (j ≤ ·)).erase i) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hji : j < i := (Finset.mem_filter.1 hi).2
      rw [sR hji, Finset.filter_erase, Finset.filter_erase,
        Finset.erase_eq_of_notMem (s := u.filter (· ≤ j)) (by simp [hji]), mul_smul]
    rw [hA, hB]
    simp only [smul_add]
    abel

  have tele := sum_alt_filter_lt_le (fun s => Φ (c s) (u \ s)) u
  simp only [Finset.sdiff_self, hΦ, Finset.sdiff_empty, hc, map_zero, Pi.zero_apply, smul_zero,
    sub_zero] at tele
  have hT : ∑ j ∈ u, (-1 : ℤ) ^ (u.filter (· < j)).card • (Φ (c (u.filter (· < j))) (u.filter (j ≤ ·)) +
      Φ (c (u.filter (· ≤ j))) (u.filter (j < ·))) = 0 := by
    rw [← tele]
    refine Finset.sum_congr rfl fun j _ => ?_
    have a1 : u \ u.filter (· < j) = u.filter (j ≤ ·) := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_filter]; grind
    have a2 : u \ u.filter (· ≤ j) = u.filter (j < ·) := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_filter]; grind
    rw [a1, a2]
  rw [hL]
  show _ = ∑ j ∈ u, Φ (delta c (u.filter (· ≤ j))) (u.filter (j ≤ ·)) + _
  rw [← Finset.sum_add_distrib, Finset.sum_congr rfl key, Finset.sum_add_distrib, hT, add_zero]

end CupDelta

end GlobalTheory.DI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfMemSchA
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.WeilM

namespace GlobalTheory.ThKOp


open scoped Classical in
theorem continuous_of_mem_schA {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schA F κ) : Continuous Φ := by
  have hr : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
    have : (InfiniteAdeleRing.ringEquiv_mixedSpace F : InfiniteAdeleRing F → mixedEmbedding.mixedSpace F) =
        fun x => ((fun v : {w : InfinitePlace F // InfinitePlace.IsReal w} =>
            InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
          (fun v : {w : InfinitePlace F // InfinitePlace.IsComplex w} =>
            InfinitePlace.Completion.extensionEmbedding v.1 (x v))) := by
      funext x; exact InfiniteAdeleRing.ringEquiv_mixedSpace_apply F x
    rw [this]
    refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
    · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
        (continuous_apply _)
    · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
        (continuous_apply _)
  induction hΦ using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    have h1 : Continuous fun x : κ → AdeleRing (𝓞 F) F => fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 :=
      continuous_pi fun i => hr.comp (continuous_fst.comp (continuous_apply i))
    have h2 : Continuous fun x : κ → AdeleRing (𝓞 F) F => fun i => (x i).2 :=
      continuous_pi fun i => continuous_snd.comp (continuous_apply i)
    exact (f.continuous.comp h1).mul (hg.1.continuous.comp h2)
  | zero => exact continuous_const
  | add _ _ _ _ h h' => exact h.add h'
  | smul c _ _ h => exact continuous_const.mul h

end GlobalTheory.ThKOp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscrIsUnit
section
open IsLocalRing

open TensorProduct

namespace GlobalTheory.EtaleCoker

theorem discr_isUnit (S A : Type) [CommRing S] [IsLocalRing S] [CommRing A] [Algebra S A]
    [Algebra.Etale S A] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι S A) :
    IsUnit (Algebra.discr S b) := by
  have h := GlobalTheory.PurityDisc.discr_ne_zero_of_etale (ResidueField S) (ResidueField S ⊗[S] A)
    (Algebra.TensorProduct.basis (ResidueField S) b)
  rw [GlobalTheory.PurityDisc.discr_baseChange] at h
  by_contra hn
  exact h ((residue_eq_zero_iff _).mpr ((mem_maximalIdeal _).mpr hn))

end GlobalTheory.EtaleCoker
end

