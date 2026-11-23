module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.DifB
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

theorem UpperTheory.V.Z.Kato.Sym.difB :
    UpperTheory.V.Z.Kato.Sym.DifB := by
  classical
  intro Ω _ _ _ ε X m hm u v P Q hP hQ
  obtain ⟨-, -, l3, l4, -, l6, -⟩ := lgB Ω ε X m hm
  have K := kaB Ω ε X m hm
  have hu := hP.hu
  have hv := hP.hv
  have nz : ∀ (θ : Kb X) (w : X.K), w ≠ 0 → θ ^ m = io X w → θ ≠ 0 := by
    rintro θ w hw h rfl
    rw [zero_pow hm.ne'] at h
    exact hw ((map_eq_zero (io X)).1 h.symm)
  have self0 : ∀ a : Kb X, a ≠ 0 → lg X m a a = 0 := fun a ha => l3 a a 0 ha (by simp)
  refine ⟨fun g h hg hh => ?_, ?_, ?_, fun R hR h hh => ?_, fun h hh => ?_, fun σ hσ h hh => ?_,
    fun τ s hτ σ hσ h hh => ?_⟩
  · have e1 := hP.cob g h hg hh
    have e2 := hQ.cob g h hg hh
    rw [(K Q.a u hu.1 hQ.ha).2.1 P.a hP.ha g hg, (K Q.b v hv.1 hQ.hb).2.1 P.b hP.hb h hh] at e1
    simp only [dif]
    rw [(K Q.a u hu.1 hQ.ha).1 g h hg hh, (K Q.b v hv.1 hQ.hb).1 g h hg hh]
    linear_combination e1 - e2
  · obtain ⟨B1, h1⟩ := hP.lc
    obtain ⟨B2, h2⟩ := hQ.lc
    obtain ⟨B3, h3⟩ := (K Q.a u hu.1 hQ.ha).2.2.1
    obtain ⟨B4, h4⟩ := (K Q.b v hv.1 hQ.hb).2.2.1
    refine ⟨B1 ∪ B2 ∪ B3 ∪ B4, fun h h' hh hh' hB => ?_⟩
    simp only [dif]
    rw [h1 h h' hh hh' fun b hb => hB b (by simp [hb]), h2 h h' hh hh' fun b hb => hB b (by simp [hb]),
      h3 h h' hh hh' fun b hb => hB b (by simp [hb]), h4 h h' hh hh' fun b hb => hB b (by simp [hb])]
  · intro B h hB hh hi
    simp only [dif]
    rw [hP.unr B h hB hh hi, hQ.unr B h hB hh hi, (K Q.a u hu.1 hQ.ha).2.2.2.1 hu B h hB hh hi,
      (K Q.b v hv.1 hQ.hb).2.2.2.1 hv B h hB hh hi]
    ring
  · simp only [dif]
    rw [l4 P.a Q.a R.a (nz _ _ hu.1 hR.ha) (hP.ha.trans hQ.ha.symm) (hQ.ha.trans hR.ha.symm),
      l4 P.b Q.b R.b (nz _ _ hv.1 hR.hb) (hP.hb.trans hQ.hb.symm) (hQ.hb.trans hR.hb.symm),
      (K R.a u hu.1 hR.ha).2.1 Q.a hQ.ha h hh, (K R.b v hv.1 hR.hb).2.1 Q.b hQ.hb h hh]
    ring
  · simp only [dif]
    rw [self0 _ (nz _ _ hu.1 hP.ha), self0 _ (nz _ _ hv.1 hP.hb)]
    ring
  · have hk : InD X (σ⁻¹ * h * σ) := fun f => by
      have : (σ⁻¹ * h * σ) (io X f) = σ.symm (h (σ (io X f))) := rfl
      rw [this, hσ f, hh f, RingEquiv.symm_apply_eq, hσ f]
    have hm' : σ * (σ⁻¹ * h * σ) = h * σ := by group
    have e1 := hP.cob σ _ hσ hk
    have e2 := hP.cob h σ hh hσ
    have e3 := (K P.b v hv.1 hP.hb).1 σ _ hσ hk
    have e4 := (K P.b v hv.1 hP.hb).1 h σ hh hσ
    rw [hm'] at e1 e3
    have e5 : ka X m P.b (σ⁻¹ * h * σ) = ka X m P.b h := by linear_combination e4 - e3
    rw [e5] at e1
    change 1 ^ 2 * P.η (σ⁻¹ * h * σ) - P.η h + ka X m P.a h * ka X m P.b σ - ka X m P.a σ * ka X m P.b h = 0
    linear_combination e2 - e1
  · simp only [dif, Pt.mv]
    rw [((K Q.a u hu.1 hQ.ha).2.2.2.2.1 σ τ s hτ hσ h hh).2, ((K Q.b v hv.1 hQ.hb).2.2.2.2.1 σ τ s hτ hσ h hh).2,
      l6 σ τ s hτ hσ P.a Q.a (nz _ _ hu.1 hQ.ha) (hP.ha.trans hQ.ha.symm),
      l6 σ τ s hτ hσ P.b Q.b (nz _ _ hv.1 hQ.hb) (hP.hb.trans hQ.hb.symm)]
    ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.PtOfDif
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

namespace UpperTheory.V.Z.Kato.Sym

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} {X : Tower Ω ε} {m : ℕ}

private theorem lc_add {φ ψ : RingAut (Kb X) → ZMod m} (h1 : LC X φ) (h2 : LC X ψ) :
    LC X fun h => φ h + ψ h := by
  classical
  obtain ⟨B, hB⟩ := h1
  obtain ⟨C, hC⟩ := h2
  refine ⟨B ∪ C, fun h h' a b e => ?_⟩
  show φ h + ψ h = φ h' + ψ h'
  rw [hB h h' a b fun z hz => e z (Finset.mem_union_left _ hz),
    hC h h' a b fun z hz => e z (Finset.mem_union_right _ hz)]

private theorem lc_mul {φ : RingAut (Kb X) → ZMod m} (c : ZMod m) (h1 : LC X φ) :
    LC X fun h => c * φ h := by
  obtain ⟨B, hB⟩ := h1
  refine ⟨B, fun h h' a b e => ?_⟩
  show c * φ h = c * φ h'
  rw [hB h h' a b e]

private theorem lc_congr {φ ψ : RingAut (Kb X) → ZMod m} (h1 : LC X φ) (e : ∀ h, InD X h → ψ h = φ h) :
    LC X ψ := by
  obtain ⟨B, hB⟩ := h1
  exact ⟨B, fun h h' a b c => by rw [e h a, e h' b, hB h h' a b c]⟩

private theorem lc_sum {I : Type} (A : Finset I) (φ : I → RingAut (Kb X) → ZMod m) (h1 : ∀ i ∈ A, LC X (φ i)) :
    LC X fun h => ∑ i ∈ A, φ i h := by
  classical
  induction A using Finset.induction_on with
  | empty => exact ⟨∅, fun _ _ _ _ _ => by simp⟩
  | insert i A hi ih =>
    refine lc_congr (lc_add (h1 i (Finset.mem_insert_self _ _))
      (ih fun j hj => h1 j (Finset.mem_insert_of_mem hj))) fun h _ => ?_
    simp only [Finset.sum_insert hi]

private theorem isU_prod {I : Type} (A : Finset I) (u : I → X.K) (h1 : ∀ i ∈ A, IsU X (u i)) :
    IsU X (∏ i ∈ A, u i) :=
  ⟨Finset.prod_ne_zero_iff.2 fun i hi => (h1 i hi).1, fun W hW => by
    rw [map_prod]; exact Finset.prod_eq_one fun i hi => (h1 i hi).2 W hW⟩

variable [IsAlgClosure ℚ Ω]

private theorem ka_prod (hm : 0 < m) {I : Type} (A : Finset I) (u : I → X.K) (α : I → Kb X)
    (h1 : ∀ i ∈ A, u i ≠ 0 ∧ α i ^ m = io X (u i)) (h : RingAut (Kb X)) (hh : InD X h) :
    ka X m (∏ i ∈ A, α i) h = ∑ i ∈ A, ka X m (α i) h := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    have := (kaB Ω ε X m hm 1 1 one_ne_zero (by simp)).2.2.2.2.2 1 1 one_ne_zero (by simp) h hh
    simpa using this
  | insert i A hi ih =>
    have h2 : ∀ j ∈ A, u j ≠ 0 ∧ α j ^ m = io X (u j) := fun j hj => h1 j (Finset.mem_insert_of_mem hj)
    have h3 := h1 i (Finset.mem_insert_self _ _)
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ← ih h2]
    refine (kaB Ω ε X m hm _ _ h3.1 h3.2).2.2.2.2.2 _ (∏ j ∈ A, u j)
      (Finset.prod_ne_zero_iff.2 fun j hj => (h2 j hj).1) ?_ h hh
    rw [map_prod, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun j hj => (h2 j hj).2

private theorem pt_of_dif (hm : 0 < m) {u v : X.K} {P : Pt X m} (hP : IsPt X m u v P) {α β : Kb X}
    {η : RingAut (Kb X) → ZMod m} (ha : α ^ m = P.a ^ m) (hb : β ^ m = P.b ^ m)
    (hd : ∀ h, InD X h → dif X P ⟨α, β, η⟩ h = 0) : IsPt X m u v ⟨α, β, η⟩ := by
  rw [hP.ha] at ha
  rw [hP.hb] at hb
  obtain ⟨a1, a2, a3, a4, -⟩ := kaB Ω ε X m hm α u hP.hu.1 ha
  obtain ⟨b1, b2, b3, b4, -⟩ := kaB Ω ε X m hm β v hP.hv.1 hb
  have e : ∀ h, InD X h →
      η h = P.η h + (lg X m P.b β * ka X m α h + -lg X m P.a α * ka X m β h) := fun h hh => by
    have := hd h hh
    simp only [dif] at this
    linear_combination -this
  refine ⟨hP.hu, hP.hv, ha, hb, fun g h hg hh => ?_,
    lc_congr (lc_add hP.lc (lc_add (lc_mul _ a3) (lc_mul _ b3))) e, fun B h c hh d => ?_⟩
  · have hgh : InD X (g * h) := fun f => by
      show g (h (io X f)) = io X f
      rw [hh f, hg f]
    have c := hP.cob g h hg hh
    rw [a2 _ hP.ha g hg, b2 _ hP.hb h hh] at c
    show ka X m α g * ka X m β h = η h - η (g * h) + η g
    rw [e g hg, e h hh, e _ hgh, a1 g h hg hh, b1 g h hg hh]
    linear_combination c
  · show η h = 0
    rw [e h hh, hP.unr B h c hh d, a4 hP.hu B h c hh d, b4 hP.hv B h c hh d]
    simp

end UpperTheory.V.Z.Kato.Sym

theorem UpperTheory.V.Z.Kato.Sym.sumB :
    UpperTheory.V.Z.Kato.Sym.SumB := by
  intro Ω _ _ _ ε X m hm I J A B u v P ⟨i0, hi0⟩ ⟨j0, hj0⟩ hP
  refine ⟨⟨_, fun i => (P i j0).a, fun j => (P i0 j).b,
    fun i j h => (P i j).η h + ka X m (P i j0).a h * lg X m (P i j).b (P i0 j).b -
      lg X m (P i j).a (P i j0).a * ka X m (P i0 j).b h, fun i hi j hj => ⟨?_, ?_, fun h _ => ?_⟩, rfl⟩, ?_⟩
  · rw [(hP i hi j0 hj0).ha, (hP i hi j hj).ha]
  · rw [(hP i0 hi0 j hj).hb, (hP i hi j hj).hb]
  · simp only [dif]
    ring
  rintro _ ⟨α, β, η, H, rfl⟩
  have Q : ∀ i ∈ A, ∀ j ∈ B, IsPt X m (u i) (v j) ⟨α i, β j, η i j⟩ := fun i hi j hj =>
    pt_of_dif hm (hP i hi j hj) (H i hi j hj).1 (H i hi j hj).2.1 (H i hi j hj).2.2
  refine ⟨isU_prod A u fun i hi => (Q i hi j0 hj0).hu, isU_prod B v fun j hj => (Q i0 hi0 j hj).hv, ?_, ?_,
    fun g h hg hh => ?_, lc_sum A _ fun i hi => lc_sum B _ fun j hj => (Q i hi j hj).lc, fun W h c hh d => ?_⟩
  · rw [map_prod, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i hi => (Q i hi j0 hj0).ha
  · rw [map_prod, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun j hj => (Q i0 hi0 j hj).hb
  · show ka X m (∏ i ∈ A, α i) g * ka X m (∏ j ∈ B, β j) h =
      ∑ i ∈ A, ∑ j ∈ B, η i j h - ∑ i ∈ A, ∑ j ∈ B, η i j (g * h) + ∑ i ∈ A, ∑ j ∈ B, η i j g
    rw [ka_prod hm A u α (fun i hi => ⟨(Q i hi j0 hj0).hu.1, (Q i hi j0 hj0).ha⟩) g hg,
      ka_prod hm B v β (fun j hj => ⟨(Q i0 hi0 j hj).hv.1, (Q i0 hi0 j hj).hb⟩) h hh, Finset.sum_mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j hj => (Q i hi j hj).cob g h hg hh
  · exact Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => (Q i hi j hj).unr W h c hh d
end

