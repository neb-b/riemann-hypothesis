module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0046

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowMulMemAdd
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def MemE (c : Coef l) (x : Qbar l) : Prop := ∃ k : ℕ, (l : Qbar l) ^ k * x ∈ c.O

def VecE (c : Coef l) (y : Fin 2 → Qbar l) : Prop := ∃ k : ℕ, ∀ i, (l : Qbar l) ^ k * y i ∈ c.O

theorem natPow_mem (c : Coef l) (k : ℕ) : (l : Qbar l) ^ k ∈ c.O :=
  c.O.pow_mem (c.O.natCast_mem l) k

theorem pow_mul_mem_add (c : Coef l) {x : Qbar l} {k : ℕ} (h : (l : Qbar l) ^ k * x ∈ c.O) (j : ℕ) :
    (l : Qbar l) ^ (k + j) * x ∈ c.O := by
  rw [pow_add, mul_comm ((l : Qbar l) ^ k), mul_assoc]
  exact c.O.mul_mem (natPow_mem c j) h

theorem memE_add {c : Coef l} {x y : Qbar l} (hx : MemE c x) (hy : MemE c y) : MemE c (x + y) := by
  obtain ⟨k, hk⟩ := hx
  obtain ⟨j, hj⟩ := hy
  refine ⟨k + j, ?_⟩
  have h2 := pow_mul_mem_add c hj k
  rw [add_comm j k] at h2
  rw [mul_add]
  exact c.O.add_mem (pow_mul_mem_add c hk j) h2

theorem memE_neg {c : Coef l} {x : Qbar l} (hx : MemE c x) : MemE c (-x) := by
  obtain ⟨k, hk⟩ := hx
  exact ⟨k, by rw [mul_neg]; exact c.O.neg_mem hk⟩

theorem vecE_add {c : Coef l} {x y : Fin 2 → Qbar l} (hx : VecE c x) (hy : VecE c y) : VecE c (x + y) := by
  obtain ⟨k, hk⟩ := hx
  obtain ⟨j, hj⟩ := hy
  refine ⟨k + j, fun i => ?_⟩
  have h2 := pow_mul_mem_add c (hj i) k
  rw [add_comm j k] at h2
  rw [Pi.add_apply, mul_add]
  exact c.O.add_mem (pow_mul_mem_add c (hk i) j) h2

theorem vecE_neg {c : Coef l} {x : Fin 2 → Qbar l} (hx : VecE c x) : VecE c (-x) := by
  obtain ⟨k, hk⟩ := hx
  exact ⟨k, fun i => by rw [Pi.neg_apply, mul_neg]; exact c.O.neg_mem (hk i)⟩

def divSelCoc (c : Coef l) (W : R2 Ω l) (S : Finset Pl) (A : ValuationSubring Ω) :
    AddSubgroup (G ℚ Ω → Fin 2 → Qbar l) where
  carrier := {z | (∃ k : ℕ, ∀ s i, (l : Qbar l) ^ k * z s i ∈ c.O) ∧
    (∀ s t i, z (s * t) i - z s i - (mat W s *ᵥ z t) i ∈ c.O) ∧
    (∀ s, ∀ᶠ t in nhds s, ∀ i, z t i - z s i ∈ c.O) ∧
    (∀ a ∈ (toGS Ω (S : Set Pl)).ker, ∀ i, z a i ∈ c.O) ∧
    (∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B q →
      ∃ y : Fin 2 → Qbar l, VecE c y ∧ ∀ s ∈ Ine (F := ℚ) B, ∀ i, z s i - (mat W s *ᵥ y - y) i ∈ c.O) ∧
    (∃ y : Qbar l, MemE c y ∧ ∀ s ∈ Dec (F := ℚ) A, z s 1 - (mat W s 1 1 * y - y) ∈ c.O)}
  add_mem' := by
    rintro z w ⟨⟨k, hk⟩, h2, h3, h4, h5, ⟨y, hy, h6⟩⟩ ⟨⟨k', hk'⟩, h2', h3', h4', h5', ⟨y', hy', h6'⟩⟩
    refine ⟨⟨k + k', fun s i => ?_⟩, fun s t i => ?_, fun s => ?_, fun a ha i => ?_, fun q hq hl B hB => ?_,
      ⟨y + y', memE_add hy hy', fun s hs => ?_⟩⟩
    · have h := pow_mul_mem_add c (hk' s i) k
      rw [add_comm k' k] at h
      rw [Pi.add_apply, Pi.add_apply, mul_add]
      exact c.O.add_mem (pow_mul_mem_add c (hk s i) k') h
    · have e : (z + w) (s * t) i - (z + w) s i - (mat W s *ᵥ (z + w) t) i =
          (z (s * t) i - z s i - (mat W s *ᵥ z t) i) + (w (s * t) i - w s i - (mat W s *ᵥ w t) i) := by
        simp only [Pi.add_apply, Matrix.mulVec_add]; ring
      rw [e]; exact c.O.add_mem (h2 s t i) (h2' s t i)
    · filter_upwards [h3 s, h3' s] with t ht ht' i
      have e : (z + w) t i - (z + w) s i = (z t i - z s i) + (w t i - w s i) := by
        simp only [Pi.add_apply]; ring
      rw [e]; exact c.O.add_mem (ht i) (ht' i)
    · rw [Pi.add_apply, Pi.add_apply]; exact c.O.add_mem (h4 a ha i) (h4' a ha i)
    · obtain ⟨u, hu, hu'⟩ := h5 q hq hl B hB
      obtain ⟨u', hv, hv'⟩ := h5' q hq hl B hB
      refine ⟨u + u', vecE_add hu hv, fun s hs i => ?_⟩
      have e : (z + w) s i - (mat W s *ᵥ (u + u') - (u + u')) i =
          (z s i - (mat W s *ᵥ u - u) i) + (w s i - (mat W s *ᵥ u' - u') i) := by
        simp only [Pi.add_apply, Pi.sub_apply, Matrix.mulVec_add]; ring
      rw [e]; exact c.O.add_mem (hu' s hs i) (hv' s hs i)
    · have e : (z + w) s 1 - (mat W s 1 1 * (y + y') - (y + y')) =
          (z s 1 - (mat W s 1 1 * y - y)) + (w s 1 - (mat W s 1 1 * y' - y')) := by
        simp only [Pi.add_apply]; ring
      rw [e]; exact c.O.add_mem (h6 s hs) (h6' s hs)
  zero_mem' := by
    refine ⟨⟨0, fun s i => by simp⟩, fun s t i => by simp, fun s => Filter.Eventually.of_forall fun t i => by simp,
      fun a _ i => by simp, fun q _ _ B _ => ⟨0, ⟨0, fun i => by simp⟩, fun s _ i => by simp⟩, ⟨0, ⟨0, by simp⟩, fun s _ => by simp⟩⟩
  neg_mem' := by
    rintro z ⟨⟨k, hk⟩, h2, h3, h4, h5, ⟨y, hy, h6⟩⟩
    refine ⟨⟨k, fun s i => ?_⟩, fun s t i => ?_, fun s => ?_, fun a ha i => ?_, fun q hq hl B hB => ?_,
      ⟨-y, memE_neg hy, fun s hs => ?_⟩⟩
    · rw [Pi.neg_apply, Pi.neg_apply, mul_neg]; exact c.O.neg_mem (hk s i)
    · have e : (-z) (s * t) i - (-z) s i - (mat W s *ᵥ (-z) t) i = -(z (s * t) i - z s i - (mat W s *ᵥ z t) i) := by
        simp only [Pi.neg_apply, Matrix.mulVec_neg]; ring
      rw [e]; exact c.O.neg_mem (h2 s t i)
    · filter_upwards [h3 s] with t ht i
      have e : (-z) t i - (-z) s i = -(z t i - z s i) := by simp only [Pi.neg_apply]; ring
      rw [e]; exact c.O.neg_mem (ht i)
    · rw [Pi.neg_apply, Pi.neg_apply]; exact c.O.neg_mem (h4 a ha i)
    · obtain ⟨u, hu, hu'⟩ := h5 q hq hl B hB
      refine ⟨-u, vecE_neg hu, fun s hs i => ?_⟩
      have e : (-z) s i - (mat W s *ᵥ (-u) - (-u)) i = -(z s i - (mat W s *ᵥ u - u) i) := by
        simp only [Pi.neg_apply, Pi.sub_apply, Matrix.mulVec_neg]; ring
      rw [e]; exact c.O.neg_mem (hu' s hs i)
    · have e : (-z) s 1 - (mat W s 1 1 * (-y) - (-y)) = -(z s 1 - (mat W s 1 1 * y - y)) := by
        simp only [Pi.neg_apply]; ring
      rw [e]; exact c.O.neg_mem (h6 s hs)

def divCob (c : Coef l) (W : R2 Ω l) : AddSubgroup (G ℚ Ω → Fin 2 → Qbar l) where
  carrier := {z | ∃ y : Fin 2 → Qbar l, VecE c y ∧ ∀ s i, z s i - (mat W s *ᵥ y - y) i ∈ c.O}
  add_mem' := by
    rintro z w ⟨u, hu, hu'⟩ ⟨u', hv, hv'⟩
    refine ⟨u + u', vecE_add hu hv, fun s i => ?_⟩
    have e : (z + w) s i - (mat W s *ᵥ (u + u') - (u + u')) i =
        (z s i - (mat W s *ᵥ u - u) i) + (w s i - (mat W s *ᵥ u' - u') i) := by
      simp only [Pi.add_apply, Pi.sub_apply, Matrix.mulVec_add]; ring
    rw [e]; exact c.O.add_mem (hu' s i) (hv' s i)
  zero_mem' := ⟨0, ⟨0, fun i => by simp⟩, fun s i => by simp⟩
  neg_mem' := by
    rintro z ⟨u, hu, hu'⟩
    refine ⟨-u, vecE_neg hu, fun s i => ?_⟩
    have e : (-z) s i - (mat W s *ᵥ (-u) - (-u)) i = -(z s i - (mat W s *ᵥ u - u) i) := by
      simp only [Pi.neg_apply, Pi.sub_apply, Matrix.mulVec_neg]; ring
    rw [e]; exact c.O.neg_mem (hu' s i)

abbrev DivSel (c : Coef l) (W : R2 Ω l) (S : Finset Pl) (A : ValuationSubring Ω) : Type :=
  ↥(divSelCoc c W S A) ⧸ (divCob c W).addSubgroupOf (divSelCoc c W S A)

theorem divSel_torsion (c : Coef l) (W : R2 Ω l) (S : Finset Pl) (A : ValuationSubring Ω) :
    ∀ x : DivSel c W S A, ∃ n : ℕ, l ^ n • x = 0 := by
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    obtain ⟨k, hk⟩ := z.2.1
    refine ⟨k, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    refine ⟨0, ⟨0, fun i => by simp⟩, fun s i => ?_⟩
    simp only [AddSubgroup.coe_nsmul, Pi.smul_apply, nsmul_eq_mul, Matrix.mulVec_zero, sub_zero, Pi.zero_apply]
    push_cast
    exact hk s i

end GlobalTheory.Ord2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TargetAlt
section
open Formalism.MainNotions.N

namespace GlobalTheory.ConjugateIrreducibility

private theorem isIrrSub_of_conj {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (H H' : Subgroup Γ)
    (hHH : ∀ s ∈ H, s ∈ H') (r r' : Γ →* GL (Fin n) k) (g : GL (Fin n) k)
    (hconj : ∀ s : Γ, (r' : Γ → GL (Fin n) k) s = g * (r : Γ → GL (Fin n) k) s * g⁻¹)
    (hne : (⊤ : Submodule k (Fin n → k)) ≠ ⊥)
    (hmin : ∀ W : Submodule k (Fin n → k), W ≤ ⊤ → IsInv (MonoidHom.comp r (Subgroup.subtype H)) W →
      W = ⊥ ∨ W = ⊤) :
    IsIrrSub (MonoidHom.comp r' (Subgroup.subtype H')) ⊤ := by
  refine ⟨hne, fun _ _ _ => Submodule.mem_top, fun W _ hinv => ?_⟩

  let W₀ : Submodule k (Fin n → k) := W.comap (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k))
  have hmem : ∀ v, v ∈ W₀ ↔ (g : Matrix (Fin n) (Fin n) k).mulVec v ∈ W := fun v => by
    simp [W₀, Matrix.toLin'_apply]
  have hinv₀ : IsInv (MonoidHom.comp r (Subgroup.subtype H)) W₀ := by
    intro s v hv
    rw [hmem] at hv ⊢
    have key : (g : Matrix (Fin n) (Fin n) k).mulVec ((r s.1 : Matrix (Fin n) (Fin n) k).mulVec v) =
        (r' s.1 : Matrix (Fin n) (Fin n) k).mulVec ((g : Matrix (Fin n) (Fin n) k).mulVec v) := by
      simp [hconj, Matrix.mulVec_mulVec, mul_assoc]
    have h1 := hinv ⟨s, hHH s s.2⟩ _ hv
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at h1 ⊢
    rw [key]
    exact h1
  have hback : ∀ w, ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec w ∈ W₀ ↔ w ∈ W := fun w => by
    rw [hmem, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  rcases hmin W₀ le_top hinv₀ with h0 | htop
  · left
    rw [eq_bot_iff]
    intro w hw
    have h1 := (hback w).mpr hw
    rw [h0, Submodule.mem_bot] at h1
    have h2 := congrArg (Matrix.mulVec (g : Matrix (Fin n) (Fin n) k)) h1
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.mulVec_zero] at h2
    rw [h2]
    exact Submodule.zero_mem _
  · right
    rw [eq_top_iff]
    intro w _
    exact (hback w).mp (htop ▸ Submodule.mem_top)

theorem target : ∀ {Γ k : Type} [inst : Group Γ] [inst_1 : Field k] {n : ℕ} (H H' : Subgroup Γ), (∀ s ∈ H, s ∈ H') → ∀ (r r' : Γ →* GL (Fin n) k) (g : GL (Fin n) k), (∀ (s : Γ), (r' : Γ → GL (Fin n) k) s = g * (r : Γ → GL (Fin n) k) s * g⁻¹) → Formalism.MainNotions.N.IsIrrSub (MonoidHom.comp r (Subgroup.subtype H)) ⊤ → Formalism.MainNotions.N.IsIrrSub (MonoidHom.comp r' (Subgroup.subtype H')) ⊤ := by
  intro Γ k _ _ n H H' hHH r r' g hconj hirr
  obtain ⟨hne, -, hmin⟩ := hirr
  exact isIrrSub_of_conj H H' hHH r r' g hconj hne hmin

end GlobalTheory.ConjugateIrreducibility
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceFormNeZeroOfStableLineIrreducible
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
open GlobalTheory.Sl2Ad

namespace GlobalTheory.Sl2Ad

theorem form_ne_zero_of_isIrr : ∀ {K : Type} [Field K] [CharZero K] {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin 2) K), IsIrr ρ →
    ∀ y : Fin 3 → K, y ≠ 0 → (∀ g, ∃ c : K, ad (ρ g) *ᵥ y = c • y) → form y y ≠ 0 := by
  intro K _ _ Γ _ ρ hirr y hy hstab hform
  have hq : y 0 * y 1 + y 2 * y 2 = 0 := by
    rw [form_apply] at hform
    have h2 : (2 : K) * (y 0 * y 1 + y 2 * y 2) = 0 := by linear_combination hform
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h two_ne_zero
    · exact h
  have hconj : ∀ g, ∃ c : K, ofCoord y * (ρ g : Matrix (Fin 2) (Fin 2) K) = (ρ g : Matrix (Fin 2) (Fin 2) K) * (c • ofCoord y) := by
    intro g
    obtain ⟨c, hc⟩ := hstab g⁻¹
    refine ⟨c, ?_⟩
    have h1 := coord_conj_ofCoord (ρ g⁻¹) y
    rw [hc] at h1
    have htr : ((ρ g⁻¹ : Matrix (Fin 2) (Fin 2) K) * ofCoord y * (((ρ g⁻¹)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).trace = 0 := by
      rw [trace_conj, trace_ofCoord]
    have h2 := ofCoord_coord htr
    rw [h1] at h2
    have h3 : ofCoord (c • y) = c • ofCoord y := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [ofCoord]
    rw [h3, map_inv, inv_inv] at h2
    have hu : (ρ g : Matrix (Fin 2) (Fin 2) K) * (((ρ g)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hu, Matrix.one_mul]
  let Wk : Submodule K (Fin 2 → K) := LinearMap.ker (Matrix.mulVecLin (ofCoord y))
  have hmem : ∀ x, x ∈ Wk ↔ ofCoord y *ᵥ x = 0 := fun x => by
    simp [Wk, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  have hinv : IsInv ρ Wk := by
    intro g x hx
    rw [hmem] at hx ⊢
    obtain ⟨c, hc⟩ := hconj g
    have hs : (c • ofCoord y) *ᵥ x = c • (ofCoord y *ᵥ x) := by
      ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
    rw [Matrix.mulVec_mulVec, hc, ← Matrix.mulVec_mulVec, hs, hx, smul_zero, Matrix.mulVec_zero]
  have hy0 : ∀ a b c : K, a = 0 → b = 0 → c = 0 → y 0 = a → y 1 = b → y 2 = c → False := by
    intro a b c ha hb hc h0 h1 h2
    apply hy
    ext i; fin_cases i
    · simpa [ha] using h0
    · simpa [hb] using h1
    · simpa [hc] using h2
  rcases hirr.2.2 Wk le_top hinv with h | h
  · have hv1 : (![y 0, -y 2] : Fin 2 → K) ∈ Wk := by
      rw [hmem]; ext i; fin_cases i <;> simp [ofCoord, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> first | linear_combination | linear_combination hq | linear_combination -hq
    have hv2 : (![y 2, y 1] : Fin 2 → K) ∈ Wk := by
      rw [hmem]; ext i; fin_cases i <;> simp [ofCoord, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> first | linear_combination | linear_combination hq | linear_combination -hq
    rw [h, Submodule.mem_bot] at hv1 hv2
    have a0 := congrFun hv1 0
    have a1 := congrFun hv1 1
    have b1 := congrFun hv2 1
    simp at a0 a1 b1
    exact hy0 0 0 0 rfl rfl rfl a0 b1 a1
  · have hv1 : (Pi.single 0 1 : Fin 2 → K) ∈ Wk := h ▸ Submodule.mem_top
    have hv2 : (Pi.single 1 1 : Fin 2 → K) ∈ Wk := h ▸ Submodule.mem_top
    rw [hmem] at hv1 hv2
    have a0 := congrFun hv1 0
    have a1 := congrFun hv1 1
    have b0 := congrFun hv2 0
    simp [ofCoord, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at a0 a1 b0
    exact hy0 0 0 0 rfl rfl rfl b0 a1 a0

end GlobalTheory.Sl2Ad
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedOfLevelAwayInertiaCharacters
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem unramified_of_levelAway : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (M : ℕ), 1 ≤ M → LevelAway l M W → ∃ S : Finset Pl, ContainsAbove S l ∧ ∀ w, w ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ W.ker := by
  intro l _ Ω _ _ _ W M hM hL
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hne : Ideal.span {((l * M : ℕ) : 𝓞 ℚ)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.mpr (Nat.mul_ne_zero hl0 (by omega))
  have hfin := Ideal.finite_factors hne
  have hmem : ∀ v : Pl, v ∈ hfin.toFinset ↔ ((l * M : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    intro v
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · intro v hv
    rw [hmem, Nat.cast_mul]
    exact v.asIdeal.mul_mem_right _ hv
  · intro w hw B hB s hs
    rw [hmem, Nat.cast_mul] at hw
    have hlw : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h => hw (w.asIdeal.mul_mem_right _ h)
    have hMw : ((M : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h => hw (w.asIdeal.mul_mem_left _ h)
    obtain ⟨A, hA, χ, hχ, g, hg⟩ := hL w hlw
    have hMA : ¬ A.valuation (M : Ω) < 1 := by
      intro h
      apply hMw
      apply (hA (M : 𝓞 ℚ)).1
      simpa using h
    have key : ∀ u ∈ Ine (F := ℚ) A, W u = 1 := by
      intro u hu
      have h1 : ∀ i, χ i u = 1 := fun i => hχ i u fun ζ hζ => GlobalTheory.TameTau.ine_fix_root hu M hMA hζ
      have h2 := hg u hu
      have h3 : g * W u * g⁻¹ = 1 := by
        apply Units.ext
        rw [h2]
        simp [h1]
      have h4 : W u = g⁻¹ * (g * W u * g⁻¹) * g := by group
      rw [h4, h3]; group
    obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hA hB
    have h5 := key _ (GlobalTheory.ParamRepCompare.conj_mem_Ine_of_smul_eq hσ hs)
    have h6 : s = σ * (σ⁻¹ * s * σ) * σ⁻¹ := by group
    rw [MonoidHom.mem_ker, h6, map_mul, map_mul, h5, mul_one, ← map_mul, mul_inv_cancel, map_one]

end GlobalTheory.Ord2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.VanishOrdOfKatoUse
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.VanishKato

theorem cont_of_ker {Γ H : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (f : Γ →* H) (U : Set Γ) (hU : IsOpen U) (h1 : 1 ∈ U)
    (h : ∀ s ∈ U, f s = 1) : Continuous f := by
  refine continuous_of_continuousAt_one f ?_
  refine (continuousAt_const (y := (1 : H))).congr ?_
  filter_upwards [hU.mem_nhds h1] with s hs
  exact (h s hs).symm

theorem cont_kills {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (M : ℕ) (hM : 1 ≤ M) (φ : G ℚ Ω →* (Qbar l)ˣ) (hφ : KillsMu M φ) : Continuous φ := by
  have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
    classical
    refine (Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
    simpa [Polynomial.mem_nthRoots hM] using hζ
  refine cont_of_ker φ (⋂ ζ ∈ {ζ : Ω | ζ ^ M = 1}, (MulAction.stabilizer (Ω ≃ₐ[ℚ] Ω) ζ : Set (Ω ≃ₐ[ℚ] Ω)))
    (hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral ζ) ?_ ?_
  · simp only [Set.mem_iInter]
    exact fun ζ _ => Subgroup.one_mem _
  · intro s hs
    simp only [Set.mem_iInter] at hs
    exact hφ s fun ζ hζ => hs ζ hζ

end GlobalTheory.Ord2.VanishKato

namespace GlobalTheory.Ord2

end GlobalTheory.Ord2

end
end

