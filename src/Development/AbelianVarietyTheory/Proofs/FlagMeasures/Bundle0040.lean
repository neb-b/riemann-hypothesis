module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0029
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameUnipotentExchangingDualIsotropic
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.FrameDual

open GlobalTheory.HL.Eichler

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)

theorem hf_sum_l {ι : Type} (s : Finset ι) (a : ι → Fin n → E) (y : Fin n → E) :
    hf L Hm (∑ i ∈ s, a i) y = ∑ i ∈ s, hf L Hm (a i) y := by
  induction s using Finset.induction_on with
  | empty => simp [hf]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hf_add_l, ih]

theorem hf_sum_r {ι : Type} (s : Finset ι) (a : ι → Fin n → E) (y : Fin n → E) :
    hf L Hm y (∑ i ∈ s, a i) = ∑ i ∈ s, hf L Hm y (a i) := by
  induction s using Finset.induction_on with
  | empty => simp [hf]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hf_add_r, ih]

end

theorem exists_unip_change_dual : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k) (g : Fin (r + 1) → S.V) (t : E) (gs gs2 : Fin r → S.V), (∀ a b, hf L S.Hm (g a) (g b) = if a = Fin.last r ∧ b = Fin.last r then t else 0) → (∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0) → (∀ a j, hf L S.Hm (g a) (gs2 j) = if a = j.castSucc then 1 else 0) → (∀ i j, hf L S.Hm (gs i) (gs j) = 0) → (∀ i j, hf L S.Hm (gs2 i) (gs2 j) = 0) → ∃ m ∈ S.Nof g, (∀ a, m (g a) = g a) ∧ (∀ j, m (gs j) = gs2 j) ∧ ∀ A : Submodule L.O S.V, (∀ x ∈ S.spanTo g r, x ∈ A) → (∀ x ∈ A, x ∈ perp L S.Hm (S.spanTo g r)) → m • (A ⊓ (perp L S.Hm (Submodule.span E (Set.range gs))).restrictScalars L.O) = A ⊓ (perp L S.Hm (Submodule.span E (Set.range gs2))).restrictScalars L.O := by
  intro F _ _ _ _ _ E _ _ _ L r k S g t gs gs2 hg hd hd2 hi hi2
  have hcj := hf_cj L S.herm.1
  obtain ⟨G, hG⟩ : ∃ G : Fin r → S.V, ∀ j, G j = g j.castSucc := ⟨_, fun _ => rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : Fin r → S.V, ∀ j, w j = gs2 j - gs j := ⟨_, fun _ => rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : Fin r → S.V, ∀ j, u j = w j + ∑ i, hf L S.Hm (gs j) (w i) • G i :=
    ⟨_, fun _ => rfl⟩
  have hGa : ∀ i a, hf L S.Hm (G i) (g a) = 0 := fun i a => by
    rw [hG, hg, if_neg]; rintro ⟨h, -⟩; exact Fin.castSucc_ne_last i h
  have haG : ∀ a i, hf L S.Hm (g a) (G i) = 0 := fun a i => by
    rw [hG, hg, if_neg]; rintro ⟨-, h⟩; exact Fin.castSucc_ne_last i h
  have hGG : ∀ i j, hf L S.Hm (G i) (G j) = 0 := fun i j => by rw [hG j]; exact hGa i _
  have hgw : ∀ a i, hf L S.Hm (g a) (w i) = 0 := fun a i => by rw [hw, hf_sub_r, hd, hd2, sub_self]
  have hwg : ∀ i a, hf L S.Hm (w i) (g a) = 0 := fun i a => by rw [← hcj, hgw, map_zero]
  have hGw : ∀ i j, hf L S.Hm (G i) (w j) = 0 := fun i j => by rw [hG i]; exact hgw _ _
  have hwG : ∀ i j, hf L S.Hm (w i) (G j) = 0 := fun i j => by rw [hG j]; exact hwg _ _
  have hGu : ∀ i j, hf L S.Hm (G i) (u j) = 0 := fun i j => by
    simp only [hu, hf_add_r, hf_sum_r, hf_smul_r, hGw, hGG, mul_zero, Finset.sum_const_zero, add_zero]
  have huG : ∀ j i, hf L S.Hm (u j) (G i) = 0 := fun j i => by
    simp only [hu, hf_add_l, hf_sum_l, hf_smul_l, hwG, hGG, mul_zero, Finset.sum_const_zero, add_zero]
  have huw : ∀ j i, hf L S.Hm (u j) (w i) = hf L S.Hm (w j) (w i) := fun j i => by
    simp only [hu, hf_add_l, hf_sum_l, hf_smul_l, hGw, mul_zero, Finset.sum_const_zero, add_zero]
  have huu : ∀ j l, hf L S.Hm (u j) (u l) = hf L S.Hm (w j) (w l) := fun j l => by
    conv_lhs => rw [hu l]
    simp only [hf_add_r, hf_sum_r, hf_smul_r, huG, huw, mul_zero, Finset.sum_const_zero, add_zero]
  have hgsG : ∀ j l, hf L S.Hm (gs j) (G l) = if l = j then 1 else 0 := fun j l => by
    rw [← hcj, hG, hd]
    by_cases h : l = j
    · subst h; simp
    · rw [if_neg (fun e => h (Fin.castSucc_injective _ e)), if_neg h, map_zero]
  have K : ∀ j i, hf L S.Hm (gs j) (w i) + hf L S.Hm (w j) (gs i) + hf L S.Hm (w j) (w i) = 0 := by
    intro j i
    have e : ∀ j, gs2 j = gs j + w j := fun j => by rw [hw]; abel
    have h2 := hi2 j i
    rw [e, e, hf_add_l, hf_add_r, hf_add_r, hi] at h2
    linear_combination h2

  obtain ⟨ff, hff⟩ : ∃ ff : S.V → S.V, ∀ v, ff v = v + ∑ j, hf L S.Hm v (G j) • u j -
      ∑ i, hf L S.Hm v (w i) • G i := ⟨_, fun _ => rfl⟩
  obtain ⟨fi, hfi⟩ : ∃ fi : S.V → S.V, ∀ v, fi v = v - ∑ j, hf L S.Hm v (G j) • u j +
      ∑ i, (hf L S.Hm v (w i) - ∑ j, hf L S.Hm v (G j) * hf L S.Hm (w j) (w i)) • G i :=
    ⟨_, fun _ => rfl⟩
  have hff_l : ∀ v y, hf L S.Hm (ff v) y = hf L S.Hm v y + ∑ j, hf L S.Hm v (G j) * hf L S.Hm (u j) y -
      ∑ i, hf L S.Hm v (w i) * hf L S.Hm (G i) y := fun v y => by
    rw [hff]; simp only [hf_add_l, hf_sub_l, hf_sum_l, hf_smul_l]
  have hff_r : ∀ y v, hf L S.Hm y (ff v) = hf L S.Hm y v + ∑ j, hf L S.Hm (G j) v * hf L S.Hm y (u j) -
      ∑ i, hf L S.Hm (w i) v * hf L S.Hm y (G i) := fun y v => by
    rw [hff]; simp only [hf_add_r, hf_sub_r, hf_sum_r, hf_smul_r, hcj]
  have hfi_l : ∀ v y, hf L S.Hm (fi v) y = hf L S.Hm v y - ∑ j, hf L S.Hm v (G j) * hf L S.Hm (u j) y +
      ∑ i, (hf L S.Hm v (w i) - ∑ j, hf L S.Hm v (G j) * hf L S.Hm (w j) (w i)) * hf L S.Hm (G i) y :=
    fun v y => by
    rw [hfi]; simp only [hf_add_l, hf_sub_l, hf_sum_l, hf_smul_l]
  have h1 : ∀ v, ff (fi v) = v := fun v => by
    have eG : ∀ l, hf L S.Hm (fi v) (G l) = hf L S.Hm v (G l) := fun l => by
      simp only [hfi_l, huG, hGG, mul_zero, Finset.sum_const_zero, sub_zero, add_zero]
    have ew : ∀ l, hf L S.Hm (fi v) (w l) =
        hf L S.Hm v (w l) - ∑ j, hf L S.Hm v (G j) * hf L S.Hm (w j) (w l) := fun l => by
      simp only [hfi_l, huw, hGw, mul_zero, Finset.sum_const_zero, add_zero]
    rw [hff]; simp only [eG, ew]; rw [hfi]; abel
  have h2 : ∀ v, fi (ff v) = v := fun v => by
    have eG : ∀ l, hf L S.Hm (ff v) (G l) = hf L S.Hm v (G l) := fun l => by
      simp only [hff_l, huG, hGG, mul_zero, Finset.sum_const_zero, sub_zero, add_zero]
    have ew : ∀ l, hf L S.Hm (ff v) (w l) =
        hf L S.Hm v (w l) + ∑ j, hf L S.Hm v (G j) * hf L S.Hm (w j) (w l) := fun l => by
      simp only [hff_l, huw, hGw, mul_zero, Finset.sum_const_zero, sub_zero]
    rw [hfi]; simp only [eG, ew, add_sub_cancel_right]; rw [hff]; abel
  obtain ⟨m, hm⟩ : ∃ m : S.GLV, ∀ v, m v = ff v := by
    refine ⟨{ toFun := ff, invFun := fi, left_inv := h2, right_inv := h1, map_add' := ?_, map_smul' := ?_ }, fun _ => rfl⟩
    · intro x y; simp only [hff, hf_add_l, add_smul, Finset.sum_add_distrib]; abel
    · intro c x; simp only [hff, hf_smul_l, smul_add, smul_sub, Finset.smul_sum, mul_smul, RingHom.id_apply]
  have iso : ∀ v v', hf L S.Hm (ff v) (ff v') = hf L S.Hm v v' := by
    intro v v'
    rw [hff_l]
    simp only [hff_r, huu, huG, hGu, hGG, mul_zero, Finset.sum_const_zero, sub_zero, add_zero]

    have hvu : ∀ j, hf L S.Hm v (u j) = hf L S.Hm v (w j) + ∑ i, hf L S.Hm (w i) (gs j) * hf L S.Hm v (G i) := by
      intro j; rw [hu, hf_add_r, hf_sum_r]; simp only [hf_smul_r, hcj]
    have huv : ∀ j, hf L S.Hm (u j) v' = hf L S.Hm (w j) v' + ∑ i, hf L S.Hm (gs j) (w i) * hf L S.Hm (G i) v' := by
      intro j; rw [hu, hf_add_l, hf_sum_l]; simp only [hf_smul_l]
    simp only [hvu, huv]
    have e1 : ∑ j, hf L S.Hm (G j) v' * (hf L S.Hm v (w j) + ∑ i, hf L S.Hm (w i) (gs j) * hf L S.Hm v (G i)) =
        ∑ j, hf L S.Hm v (w j) * hf L S.Hm (G j) v' +
          ∑ j, ∑ i, hf L S.Hm v (G j) * hf L S.Hm (G i) v' * hf L S.Hm (w j) (gs i) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
      · rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have e2 : ∑ x, hf L S.Hm v (G x) * (hf L S.Hm (w x) v' + ∑ i, hf L S.Hm (gs x) (w i) * hf L S.Hm (G i) v' +
          ∑ l, hf L S.Hm (G l) v' * hf L S.Hm (w x) (w l)) =
        ∑ x, hf L S.Hm (w x) v' * hf L S.Hm v (G x) +
          ∑ j, ∑ i, hf L S.Hm v (G j) * hf L S.Hm (G i) v' * (hf L S.Hm (gs j) (w i) + hf L S.Hm (w j) (w i)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [mul_add, mul_add, mul_comm (hf L S.Hm v (G x)), add_assoc]
      congr 1
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    have key : (∑ j, ∑ i, hf L S.Hm v (G j) * hf L S.Hm (G i) v' * hf L S.Hm (w j) (gs i)) +
        ∑ j, ∑ i, hf L S.Hm v (G j) * hf L S.Hm (G i) v' * (hf L S.Hm (gs j) (w i) + hf L S.Hm (w j) (w i)) = 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun i _ => ?_
      linear_combination hf L S.Hm v (G j) * hf L S.Hm (G i) v' * K j i
    rw [e1, e2]
    linear_combination key

  have hiso : ∀ x y, hf L S.Hm (m x) (m y) = hf L S.Hm x y := by simp only [hm]; exact iso
  have hmg : ∀ a, m (g a) = g a := fun a => by
    rw [hm, hff]; simp only [haG, hgw, zero_smul, Finset.sum_const_zero, add_zero, sub_zero]
  have hmgs : ∀ j, m (gs j) = gs2 j := fun j => by
    rw [hm, hff]
    simp only [hgsG, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hu, hw]; abel
  have hX : ∀ i, G i ∈ S.spanTo g r := fun i => by
    rw [hG]; exact Submodule.subset_span ⟨i.castSucc, by simp, rfl⟩
  have hfix : ∀ J, ∀ v ∈ S.spanTo g J, m v = v := by
    intro J v hv
    induction hv using Submodule.span_induction with
    | mem y hy => obtain ⟨a, -, rfl⟩ := hy; exact hmg a
    | zero => exact map_zero m
    | add a b _ _ ha hb => rw [map_add (f := _), ha, hb]
    | smul c a _ ha => rw [map_smul, ha]
  have hspan : ∀ J v, m v ∈ S.spanTo g J ↔ v ∈ S.spanTo g J := fun J v =>
    ⟨fun h => by
      have e : m (m v) = m v := hfix J _ h
      rw [m.injective e] at h; exact h,
     fun h => by rw [hfix J v h]; exact h⟩
  have hmperp : ∀ v ∈ perp L S.Hm (S.spanTo g r), m v = v - ∑ i, hf L S.Hm v (w i) • G i := by
    intro v hv
    rw [hm, hff]
    simp only [hv _ (hX _), zero_smul, Finset.sum_const_zero, add_zero]
  have hperp : ∀ v, m v ∈ perp L S.Hm (S.spanTo g r) ↔ v ∈ perp L S.Hm (S.spanTo g r) := fun v =>
    ⟨fun h y hy => by
      have := h y hy
      rwa [← hfix r y hy, hiso] at this,
     fun h y hy => by
      rw [← hfix r y hy, hiso]; exact h y hy⟩
  have hpspan : ∀ (f : Fin r → S.V) x,
      x ∈ perp L S.Hm (Submodule.span E (Set.range f)) ↔ ∀ l, hf L S.Hm x (f l) = 0 := fun f x =>
    ⟨fun h l => h _ (Submodule.subset_span ⟨l, rfl⟩),
     fun h => GlobalTheory.FramePsi.hf_span_right L S.Hm x _ (by rintro _ ⟨l, rfl⟩; exact h l)⟩
  refine ⟨m, ?_, hmg, hmgs, ?_⟩
  · simp only [Frames.Nof, Subgroup.mem_inf, Subgroup.mem_iInf]
    refine ⟨⟨hiso, fun j => ⟨fun v => hspan _ v, fun v hv => ?_⟩⟩, hperp, fun v hv => ?_⟩
    · rw [hfix _ v hv, sub_self]; exact Submodule.zero_mem _
    · rw [hmperp v hv, sub_sub_cancel_left]
      exact Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hX i))
  · intro A hXA hAp
    have hsum : ∀ x, ∑ i, hf L S.Hm x (w i) • G i ∈ A := fun x =>
      hXA _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hX i))
    have hAm : ∀ x, m x ∈ A ↔ x ∈ A := fun x =>
      ⟨fun h => by
        have hp : x ∈ perp L S.Hm (S.spanTo g r) := (hperp x).1 (hAp _ h)
        have e : x = m x + ∑ i, hf L S.Hm x (w i) • G i := by rw [hmperp x hp]; abel
        rw [e]; exact A.add_mem h (hsum x),
       fun h => by rw [hmperp x (hAp x h)]; exact A.sub_mem h (hsum x)⟩
    have hPm : ∀ x, m x ∈ perp L S.Hm (Submodule.span E (Set.range gs2)) ↔
        x ∈ perp L S.Hm (Submodule.span E (Set.range gs)) := fun x => by
      rw [hpspan, hpspan]
      simp only [← hmgs, hiso]
    have hsm : ∀ (Λ : Submodule L.O S.V) x, m x ∈ m • Λ ↔ x ∈ Λ := fun Λ x => by
      rw [Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨fun ⟨y, hy, e⟩ => (m.injective e) ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
    ext y
    obtain ⟨x, rfl⟩ := m.surjective y
    rw [hsm]
    simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, hAm, hPm]

end GlobalTheory.FrameDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryNearIdentityCloseTuples
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CloseTuples

open GlobalTheory.HL.Eichler GlobalTheory.HL.DualInter

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E}

theorem mem_jac [IsNonarchimedeanLocalField F] (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : ¬ IsUnit ϖ)
    (p : L.O) (hp : (p : E) = algebraMap F E ϖ) : p ∈ Ideal.jacobson (⊥ : Ideal L.O) := by
  have hm : ∀ c : 𝒪[F], algebraMap 𝒪[F] E c ∈ L.O := fun c =>
    (L.O_def _).2 isIntegral_algebraMap
  let f : 𝒪[F] →+* L.O := (algebraMap 𝒪[F] E).codRestrict L.O hm
  have hf : f.IsIntegral := fun x => by
    obtain ⟨p, hp, h⟩ := (L.O_def x).1 x.2
    refine ⟨p, hp, Subtype.ext ?_⟩
    change L.O.subtype _ = 0
    rw [Polynomial.hom_eval₂]
    exact h
  rw [Ideal.jacobson, Ideal.mem_sInf]
  rintro m ⟨-, hm⟩
  have h := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' f hf m
  have h2 : ϖ ∈ m.comap f := by
    rw [IsLocalRing.eq_maximalIdeal h]; exact hϖ
  have h3 : p = f ϖ := Subtype.ext hp
  rw [h3]
  exact h2

theorem exists_pow_denom [IsNonarchimedeanLocalField F] (L : LocE F E) {ϖ : 𝒪[F]}
    (hϖ : Irreducible ϖ) (x : E) : ∃ k : ℕ, algebraMap F E ϖ ^ k * x ∈ L.O := by
  have := L.free
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; omega)
  have hx : IsAlgebraic 𝒪[F] x :=
    (IsFractionRing.isAlgebraic_iff 𝒪[F] F E).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨d, hd0, hd⟩ := hx.exists_integral_multiple
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd0 hϖ
  refine ⟨k, (L.O_def _).2 ?_⟩
  have h2 := hd.smul ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F])
  rw [smul_smul, Units.inv_mul_cancel_left, Algebra.smul_def, map_pow] at h2
  exact h2

theorem one_add_onto {Λ : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) (p : L.O)
    (hp : p ∈ Ideal.jacobson (⊥ : Ideal L.O)) (A : (Fin n → E) →ₗ[E] (Fin n → E))
    (hA : ∀ v ∈ Λ, A v ∈ Λ) :
    Function.Bijective (LinearMap.id + (p : E) • A : (Fin n → E) →ₗ[E] (Fin n → E)) ∧
      ∀ v ∈ Λ, ∃ u ∈ Λ, u + (p : E) • A u = v := by
  set T : (Fin n → E) →ₗ[E] (Fin n → E) := LinearMap.id + (p : E) • A with hT
  have key : Λ ≤ Λ.map (T.restrictScalars L.O) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot hΛ.1 le_rfl fun z hz => ?_
    have hz' : z = T z + (-p) • A z := by
      change z = (z + (p : E) • A z) + (-(p : E)) • A z
      module
    rw [hz']
    exact Submodule.add_mem_sup ⟨z, hz, rfl⟩
      (Submodule.smul_mem_smul (Submodule.neg_mem _ hp) (hA z hz))
  have hs : Function.Surjective T := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hΛ.2, Submodule.span_le]
    intro v hv
    obtain ⟨u, -, hu⟩ := key hv
    exact ⟨u, hu⟩
  exact ⟨⟨OrzechProperty.injective_of_surjective_endomorphism T hs, hs⟩, fun v hv => key hv⟩

noncomputable def rk (L : LocE F E) (Hm : Matrix (Fin n) (Fin n) E) {m : ℕ}
    (t d : Fin m → Fin n → E) : (Fin n → E) →ₗ[E] (Fin n → E) :=
  ∑ a, (hfL L Hm (t a)).smulRight (d a)

theorem rk_apply {m : ℕ} (t d : Fin m → Fin n → E) (v : Fin n → E) :
    rk L Hm t d v = ∑ a, hf L Hm v (t a) • d a := by
  rw [rk, LinearMap.sum_apply]
  rfl

theorem rk_mem {Λ : Submodule L.O (Fin n → E)} (hΛ : IsSD L Hm Λ) {m : ℕ}
    {t d : Fin m → Fin n → E} (ht : ∀ a, t a ∈ Λ) (hd : ∀ a, d a ∈ Λ) {v : Fin n → E}
    (hv : v ∈ Λ) : rk L Hm t d v ∈ Λ := by
  rw [rk_apply]
  exact Λ.sum_mem fun a _ => Λ.smul_mem ⟨_, (hΛ.2 _).2 (ht a) _ hv⟩ (hd a)

theorem rk_adj (h : IsHermND L Hm) {m : ℕ} (t d : Fin m → Fin n → E) (v w : Fin n → E) :
    hf L Hm (rk L Hm t d v) w = hf L Hm v (rk L Hm d t w) := by
  simp only [rk_apply, sum_l, sum_r, smul_l, smul_r, cj_hf h, mul_comm]

theorem rk_dual {m : ℕ} {s t : Fin m → Fin n → E} {q : E}
    (hst : ∀ a b, hf L Hm (s a) (t b) = if a = b then q else 0) (d : Fin m → Fin n → E)
    (c : Fin m) : rk L Hm t d (s c) = q • d c := by
  simp [rk_apply, hst]

theorem exists_skew (h : IsHermND L Hm) {Λ : Submodule L.O (Fin n → E)} (hΛ : IsSD L Hm Λ) {m : ℕ}
    {s t d : Fin m → Fin n → E} (hs : ∀ a, s a ∈ Λ) (ht : ∀ a, t a ∈ Λ) (hd : ∀ a, d a ∈ Λ)
    {q : E} (hq : q ∈ L.O) (hq' : L.cj q = q)
    (hst : ∀ a b, hf L Hm (s a) (t b) = if a = b then q else 0)
    (hsk : ∀ a b, hf L Hm (s a) (d b) = - hf L Hm (d a) (s b)) :
    ∃ Z : (Fin n → E) →ₗ[E] (Fin n → E), (∀ v ∈ Λ, Z v ∈ Λ) ∧
      (∀ v w, hf L Hm (Z v) w = - hf L Hm v (Z w)) ∧ ∀ c, Z (s c) = (q * q) • d c := by
  have e1 : ∀ c, rk L Hm d t (s c) = - rk L Hm s t (d c) := fun c => by
    simp [rk_apply, hsk]
  have e3 : ∀ v w, hf L Hm (rk L Hm t d v) (rk L Hm t s w)
      = - hf L Hm (rk L Hm t s v) (rk L Hm t d w) := fun v w => by
    simp only [rk_apply, sum_l, sum_r, smul_l, smul_r, hsk, Finset.mul_sum, mul_neg,
      Finset.sum_neg_distrib, neg_neg]
  refine ⟨q • rk L Hm t d - q • rk L Hm d t - rk L Hm s t ∘ₗ rk L Hm t d, fun v hv => ?_,
    fun v w => ?_, fun c => ?_⟩
  · exact Λ.sub_mem (Λ.sub_mem (Λ.smul_mem ⟨q, hq⟩ (rk_mem hΛ ht hd hv))
      (Λ.smul_mem ⟨q, hq⟩ (rk_mem hΛ hd ht hv))) (rk_mem hΛ hs ht (rk_mem hΛ ht hd hv))
  · simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, sub_l, sub_r,
      smul_l, smul_r, hq']
    rw [rk_adj h s t, e3, ← rk_adj h t s v, rk_adj h t d v w, rk_adj h d t v w]
    ring
  · simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, rk_dual hst, e1,
      map_smul]
    module

theorem exists_cayley {Λ : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) (p : L.O)
    (hp : p ∈ Ideal.jacobson (⊥ : Ideal L.O)) (hp' : L.cj p = p)
    (Z : (Fin n → E) →ₗ[E] (Fin n → E)) (hZ : ∀ v ∈ Λ, Z v ∈ Λ)
    (hsk : ∀ v w, hf L Hm (Z v) w = - hf L Hm v (Z w)) :
    ∃ g ∈ isomG L Hm, (∀ v ∈ Λ, ∃ w ∈ Λ, g v - v = (p : E) • w) ∧
      ∀ x y, (p : E) • Z (x + y) = y - x → g x = y := by
  obtain ⟨b1, -⟩ := one_add_onto hΛ p hp Z hZ
  obtain ⟨b2, o2⟩ := one_add_onto hΛ p hp (-Z) fun v hv => Λ.neg_mem (hZ v hv)
  let g := (LinearEquiv.ofBijective _ b1).trans (LinearEquiv.ofBijective _ b2).symm
  have hg : ∀ x y, x + (p : E) • Z x = y - (p : E) • Z y → g x = y := fun x y e => by
    refine (LinearEquiv.symm_apply_eq _).2 ?_
    change x + (p : E) • Z x = y + (p : E) • (-Z y)
    rw [e]; module
  have hg' : ∀ u, g (u + (p : E) • (-Z u)) = u + (p : E) • Z u := fun u => hg _ _ (by
    simp only [map_add (f := _), map_smul, map_neg]; module)
  refine ⟨g, fun v w => ?_, fun v hv => ?_, fun x y e => hg x y ?_⟩
  · obtain ⟨v, rfl⟩ := b2.2 v
    obtain ⟨w, rfl⟩ := b2.2 w
    change hf L Hm (g (v + (p : E) • (-Z v))) (g (w + (p : E) • (-Z w)))
      = hf L Hm (v + (p : E) • (-Z v)) (w + (p : E) • (-Z w))
    rw [hg', hg']
    simp only [hf_add_l, hf_add_r, hf_smul_l, hf_smul_r, hf_neg_l, hf_neg_r, hp', hsk v w]
    ring
  · obtain ⟨u, hu, rfl⟩ := o2 v hv
    refine ⟨Z u + Z u, Λ.add_mem (hZ u hu) (hZ u hu), ?_⟩
    change g (u + (p : E) • (-Z u)) - (u + (p : E) • (-Z u)) = _
    rw [hg']; module
  · rw [map_add (f := _), smul_add] at e
    linear_combination (exp := 1) e

theorem exists_isometry_close : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λ, IsSD L Hm Λ → ∀ (m : ℕ) (Γ : Matrix (Fin m) (Fin m) E), IsUnit Γ.det → ∀ N : ℕ, ∃ N' : ℕ, ∀ x y : Fin m → Fin n → E, (∀ a, x a ∈ Λ) → gramT L Hm x = Γ → gramT L Hm y = Γ → (∀ a, ∃ w ∈ Λ, y a - x a = algebraMap F E ((ϖ : F) ^ N') • w) → ∃ g ∈ isomG L Hm, CongId L ϖ Λ N g ∧ ∀ a, g (x a) = y a := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n Hm h Λ hΛ m Γ hΓ N
  set π : E := algebraMap F E ϖ with hπ
  have hπO : π ∈ L.O := (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 ϖ.2
  have hπc : L.cj π = π := L.cj.commutes _
  have hπu : IsUnit π :=
    (IsUnit.mk0 (ϖ : F) fun e => hϖ.ne_zero (Subtype.ext e)).map _
  have hπj := mem_jac L hϖ.not_isUnit ⟨π, hπO⟩ rfl
  set hf2 : E := algebraMap F E 2⁻¹ with hhf2
  have h2 : hf2 * 2 = 1 := by
    rw [hhf2, ← map_ofNat (algebraMap F E) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  choose k hk using fun ab : Fin m × Fin m => exists_pow_denom L hϖ (hf2 * Γ⁻¹ ab.1 ab.2)
  obtain ⟨c, hc⟩ : ∃ c, ∀ ab, k ab ≤ c := ⟨Finset.univ.sup k, fun ab => Finset.le_sup (Finset.mem_univ ab)⟩
  set q : E := π ^ c with hq
  have hqO : q ∈ L.O := L.O.pow_mem hπO c
  have hqc : L.cj q = q := by rw [hq, map_pow, hπc]
  have hqΓ : ∀ a b, q * (hf2 * Γ⁻¹ a b) ∈ L.O := fun a b => by
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le' (hc (a, b))
    rw [hq, hj, pow_add, mul_assoc]
    exact L.O.mul_mem (L.O.pow_mem hπO j) (hk (a, b))
  let p : L.O := ⟨π, hπO⟩ ^ (N + 1)
  have hpe : (p : E) = π ^ (N + 1) := rfl
  have hpj : p ∈ Ideal.jacobson (⊥ : Ideal L.O) := Ideal.pow_mem_of_mem _ hπj _ (Nat.succ_pos N)
  have hpc : L.cj p = p := by rw [hpe, map_pow, hπc]
  refine ⟨N + 1 + (c + c), fun x y hx gx gy hxy => ?_⟩
  choose d hd hxy using hxy
  have hxy' : ∀ a, y a = x a + ((p : E) * (q * q)) • d a := fun a => by
    rw [← sub_eq_iff_eq_add', hxy, map_pow, pow_add, pow_add _ c c]; rfl
  have hu : IsUnit ((p : E) * (q * q)) := (hπu.pow _).mul ((hπu.pow _).mul (hπu.pow _))
  have huc : L.cj ((p : E) * (q * q)) = p * (q * q) := by simp only [map_mul, hpc, hqc]
  have hy : ∀ a, y a ∈ Λ := fun a => by
    rw [hxy']
    exact Λ.add_mem (hx a) (Λ.smul_mem ⟨_, L.O.mul_mem p.2 (L.O.mul_mem hqO hqO)⟩ (hd a))
  have gx' : ∀ a b, hf L Hm (x b) (x a) = Γ a b := fun a b => congrFun (congrFun gx a) b
  have gy' : ∀ a b, hf L Hm (y b) (y a) = Γ a b := fun a b => congrFun (congrFun gy a) b
  have hsk : ∀ a b, hf L Hm (x a + y a) (d b) = - hf L Hm (d a) (x b + y b) := fun a b => by
    refine hu.mul_left_cancel ?_
    have e : ∀ a, ((p : E) * (q * q)) • d a = y a - x a := fun a => by rw [hxy' a]; abel
    rw [mul_neg, ← smul_l L Hm _ (d a), e]
    conv_lhs => rw [← huc, ← smul_r, e]
    simp only [hf_add_l, hf_add_r, sub_l, sub_r, gx', gy']
    ring
  let t0 : Fin m → Fin n → E := fun b => ∑ a, L.cj (q * (hf2 * Γ⁻¹ b a)) • x a
  have ht0 : ∀ b, t0 b ∈ Λ := fun b => Λ.sum_mem fun a _ =>
    Λ.smul_mem ⟨_, GlobalTheory.UnramOrder.cj_mem L (hqΓ b a)⟩ (hx a)
  have hxt : ∀ a b, hf L Hm (x a + x a) (t0 b) = if a = b then q else 0 := fun a b => by
    have e : ∑ j, Γ⁻¹ b j * Γ j a = if a = b then 1 else 0 := by
      rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ hΓ, Matrix.one_apply]
      simp only [eq_comm]
    have e' : hf L Hm (x a) (t0 b) = q * hf2 * ∑ j, Γ⁻¹ b j * Γ j a := by
      simp only [t0, sum_r, smul_r, L.cj_cj, gx', Finset.mul_sum, mul_assoc]
    rw [hf_add_l, e', e]
    split_ifs
    · linear_combination q * h2
    · ring
  obtain ⟨-, o⟩ := one_add_onto hΛ.1 p hpj (q • rk L Hm d t0) fun v hv =>
    Λ.smul_mem ⟨q, hqO⟩ (rk_mem hΛ hd ht0 hv)
  choose t ht et using fun b => o _ (ht0 b)
  have hst : ∀ a b, hf L Hm (x a + y a) (t b) = if a = b then q else 0 := fun a b => by
    rw [← hxt, ← et b, hf_add_r, LinearMap.smul_apply, smul_r, smul_r, ← rk_adj h,
      rk_dual (s := fun a => x a + x a) hxt, hxy', ← add_assoc, hf_add_l _ _ (x a + x a), smul_l,
      smul_l, hpc, hqc]
    ring
  obtain ⟨Z, hZ, hZs, hZd⟩ := exists_skew h hΛ (s := fun a => x a + y a)
    (fun a => Λ.add_mem (hx a) (hy a)) ht hd hqO hqc hst hsk
  obtain ⟨g, hg, hgΛ, hgx⟩ := exists_cayley (Hm := Hm) hΛ.1 p hpj hpc Z hZ hZs
  refine ⟨g, hg, fun v hv => ?_, fun a => hgx _ _ ?_⟩
  · obtain ⟨w, hw, e⟩ := hgΛ v hv
    refine ⟨π • w, Λ.smul_mem ⟨π, hπO⟩ hw, ?_⟩
    rw [e, hpe, map_pow, smul_smul, pow_succ]
  · rw [hZd a, smul_smul, eq_sub_iff_add_eq', ← hxy']

end GlobalTheory.HL.CloseTuples
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemSpanSingleIff
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Glue

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}


open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} in
theorem _root_.GlobalTheory.HL.Glue.mem_span_single_iff {R : Type} [CommRing R] (O : Subring R) (n : ℕ)
    (v : Fin n → R) :
    v ∈ Submodule.span O (Set.range fun i => (Pi.single i 1 : Fin n → R)) ↔ ∀ i, v i ∈ O := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨j, rfl⟩ := hw
      intro i
      by_cases h : i = j
      · subst h; simp [O.one_mem]
      · simp [Pi.single_apply, h, O.zero_mem]
    | zero => intro i; simpa using O.zero_mem
    | add a b _ _ ha hb => intro i; simpa using O.add_mem (ha i) (hb i)
    | smul c a _ ha => intro i; simpa [Subring.smul_def] using O.mul_mem c.2 (ha i)
  · intro hv
    have hsum : v = ∑ i, (⟨v i, hv i⟩ : O) • (Pi.single i 1 : Fin n → R) := by
      ext j
      simp [Subring.smul_def, Finset.sum_apply, Pi.single_apply]
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)


open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} in
theorem _root_.GlobalTheory.HL.Glue.ιE_mem (A : _root_.GlobalTheory.HL.Places F E sig)
    (p : HeightOneSpectrum (𝓞 F)) (x : E) (hx : IsIntegral ℤ x) :
    (A.loc p).ιE x ∈ (A.L p).O := by
  rw [_root_.Formalism.MainNotions.S.Loc.LocE.O_def]
  exact (hx.map (A.loc p).ιE.toIntAlgHom).tower_top

end GlobalTheory.HL.Glue
end

