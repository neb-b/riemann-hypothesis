module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0028
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0031

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AevalChartSubstMemOfMemBlowUpOf
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

noncomputable section

section Chart

variable {K : Type*} {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

def chartSubst (a : J → MRing ι R) : (Σ o, extIdx ι J o) → Polynomial (MRing ι R)
  | ⟨none, j⟩ => Polynomial.C (a j) * Polynomial.X
  | ⟨some k, i⟩ => Polynomial.C (X ⟨k, i⟩)

theorem aeval_chartSubst_liftForm (a : J → MRing ι R) (p : MRing ι R) :
    aeval (chartSubst a) (liftForm p) = Polynomial.C p := by
  have e : (aeval (chartSubst a)).comp (liftForm : MRing ι R →ₐ[R] MRing (extIdx ι J) R) =
      Polynomial.CAlgHom := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [liftForm, chartSubst]
  exact DFunLike.congr_fun e p

theorem aeval_chartSubst_mem_of_mem_blowUpOf {P : Ideal (MRing ι R)} (hP : P.IsPrime)
    {u a : J → MRing ι R} {u₀ g : MRing ι R} (hg : g ∉ P) (h : ∀ j, u₀ * u j - g * a j ∈ P)
    {F : MRing (extIdx ι J) R} (hF : F ∈ blowUpOf P u) :
    aeval (chartSubst a) F ∈ Ideal.map (Polynomial.C : MRing ι R →+* Polynomial (MRing ι R)) P := by
  let π := Polynomial.mapRingHom (Ideal.Quotient.mk P)
  have key : (Polynomial.compRingHom (Polynomial.C (Ideal.Quotient.mk P g) * Polynomial.X)).comp
        (π.comp (aeval (R := R) (chartSubst a)).toRingHom) =
      (Polynomial.compRingHom (Polynomial.C (Ideal.Quotient.mk P u₀) * Polynomial.X)).comp
        (aeval (R := R) (blowUpSubst P u)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [π, Polynomial.compRingHom]
      rfl
    · rintro ⟨_ | k, i⟩
      · have e : Ideal.Quotient.mk P (u₀ * u i) = Ideal.Quotient.mk P (g * a i) :=
          Ideal.Quotient.eq.mpr (h i)
        simp only [map_mul] at e
        simp [π, chartSubst, blowUpSubst, Polynomial.compRingHom]
        have e' : Polynomial.C (Ideal.Quotient.mk P (a i)) * Polynomial.C (Ideal.Quotient.mk P g) =
            Polynomial.C (Ideal.Quotient.mk P (u i)) * Polynomial.C (Ideal.Quotient.mk P u₀) := by
          rw [← Polynomial.C_mul, ← Polynomial.C_mul, mul_comm (Ideal.Quotient.mk P (u i)), e, mul_comm]
        rw [← mul_assoc, ← mul_assoc, e']
      · simp [π, chartSubst, blowUpSubst, Polynomial.compRingHom]
  have hF' : π (aeval (chartSubst a) F) = 0 := by
    have e := DFunLike.congr_fun key F
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at e
    rw [show aeval (blowUpSubst P u) F = 0 from RingHom.mem_ker.mp hF, map_zero] at e
    have hg' : Ideal.Quotient.mk P g ∈ nonZeroDivisors (MRing ι R ⧸ P) :=
      mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
    exact (Polynomial.comp_C_mul_X_eq_zero_iff hg').mp e
  have hk : aeval (chartSubst a) F ∈ RingHom.ker π := hF'
  rwa [Polynomial.ker_mapRingHom, Ideal.mk_ker] at hk

theorem mem_of_aeval_chartSubst_mem {a : J → MRing ι R} {H : Ideal (MRing (extIdx ι J) R)}
    (hH : H.IsPrime) {P' : Ideal (MRing ι R)} (hP'H : P' ≤ H.comap (liftForm (J := J))) (j₀ : J)
    (ha : liftForm (a j₀) ∉ H)
    (hrel : ∀ j, newVar j * liftForm (a j₀) - newVar j₀ * liftForm (a j) ∈ H)
    {F : MRing (extIdx ι J) R}
    (hF : aeval (chartSubst a) F ∈ Ideal.map (Polynomial.C : MRing ι R →+* Polynomial (MRing ι R)) P') :
    F ∈ H := by
  let L := FractionRing (MRing (extIdx ι J) R ⧸ H)
  let q : MRing (extIdx ι J) R →+* L := (algebraMap _ L).comp (Ideal.Quotient.mk H)
  have hq : ∀ y, q y = 0 ↔ y ∈ H := by
    intro y
    simp only [q, RingHom.comp_apply]
    rw [map_eq_zero_iff _ (IsFractionRing.injective _ L), Ideal.Quotient.eq_zero_iff_mem]
  have ha' : q (liftForm (a j₀)) ≠ 0 := fun h0 => ha ((hq _).mp h0)
  let ε : Polynomial (MRing ι R) →+* L :=
    Polynomial.eval₂RingHom (q.comp (liftForm (J := J) : MRing ι R →ₐ[R] _).toRingHom)
      (q (newVar j₀) / q (liftForm (a j₀)))
  have key : ε.comp (aeval (R := R) (chartSubst a)).toRingHom = q := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [ε, liftForm_C]
    · rintro ⟨_ | k, i⟩
      · have h1 := (hq _).mpr (hrel i)
        rw [map_sub, map_mul, map_mul, sub_eq_zero] at h1
        simp only [ε, chartSubst, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
          aeval_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_mul, Polynomial.eval₂_C,
          Polynomial.eval₂_X]
        rw [← mul_div_assoc, div_eq_iff ha', mul_comm]
        exact h1.symm
      · simp [ε, chartSubst, liftForm]
  have hε : Ideal.map (Polynomial.C : MRing ι R →+* Polynomial (MRing ι R)) P' ≤ RingHom.ker ε := by
    rw [Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap, RingHom.mem_ker]
    simp only [ε, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    exact (hq _).mpr (hP'H hp)
  have h2 := RingHom.mem_ker.mp (hε hF)
  have h3 := DFunLike.congr_fun key F
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at h3
  rw [h3] at h2
  exact (hq F).mp h2

end Chart

theorem BlowUpStrictTransform.proof : BlowUpStrictTransform.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD s hsP e m H hϖH hH
  set Q := blowUpOf P (blowUpGens s g f m e) with hQ
  have hPp : P.IsPrime := hP.multiProj.isPrime

  obtain ⟨x, hx, hHmin⟩ : ∃ x : MRing (extIdx ι (BlowUpIdx ι)) O,
      (x = liftForm s ∨ x = newVar none) ∧ H ∈ (Q ⊔ Ideal.span {x}).minimalPrimes := by
    have hm : ∀ {F}, divCycle Q F H ≠ 0 → H ∈ (Q ⊔ Ideal.span {F}).minimalPrimes := by
      intro F hF
      unfold divCycle at hF
      split_ifs at hF with hW
      · exact hW.1
      · exact absurd rfl hF
    rcases hH with hH | hH
    · exact ⟨_, Or.inl rfl, hm hH⟩
    · exact ⟨_, Or.inr rfl, hm hH⟩
  obtain ⟨hHp, hQH, hHrel⟩ : H.IsPrime ∧ Q ≤ H ∧ IsRelevant H := by
    rcases hH with hH | hH
    · exact le_and_isRelevant_of_divCycle_ne_zero hH
    · exact le_and_isRelevant_of_divCycle_ne_zero hH
  have mnm : ∀ {y z}, y ∉ H → z ∉ H → y * z ∉ H := fun hy hz hyz => (hHp.mem_or_mem hyz).elim hy hz
  have hxH : x ∈ H := hHmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))
  set H₀ := H.comap (liftForm (J := BlowUpIdx ι)) with hH₀
  obtain ⟨hH₀p, hPH₀, hrel₀, -⟩ := comap_liftForm_facts hHp hQH hHrel
  have hϖH₀ : (C ϖ : MRing ι O) ∉ H₀ := by rw [Ideal.mem_comap, liftForm_C]; exact hϖH

  obtain ⟨u₀, v₀, hu, hv, h⟩ := hD.unit_off_special H₀ hH₀p hPH₀ hrel₀ hϖH₀
  obtain ⟨i, hpm, hYi, -⟩ := blowUp_offSpecial hPp e hD.den_not_mem hHp hQH hHrel (u₀ := u₀) hv h
  set a := blowUpCof s m e u₀ v₀ with ha_def
  have haS : liftForm (a (some (some i))) ∉ H := by
    show liftForm (v₀ * powMonomial e i) ∉ H
    rw [map_mul]; exact mnm hv hpm
  have hrelH : ∀ j, newVar j * liftForm (a (some (some i))) -
      newVar (some (some i)) * liftForm (a j) ∈ H :=
    fun j => hQH (blowUpCof_relation hPp e hD.den_not_mem h j _)

  have hsH₀ : s ∈ H₀ := by
    rcases hx with rfl | rfl
    · exact hxH
    · have h3 := H.sub_mem (H.mul_mem_right (liftForm (a (some (some i)))) hxH) (hrelH none)
      rw [sub_sub_cancel] at h3
      have h4 : liftForm (u₀ * s) ∈ H := (hHp.mem_or_mem h3).resolve_left hYi
      rw [map_mul] at h4
      exact (hHp.mem_or_mem h4).resolve_left hu

  have hmin₀ : H₀ ∈ (P ⊔ Ideal.span {s}).minimalPrimes := by
    refine ⟨⟨hH₀p, sup_le hPH₀ ((Ideal.span_singleton_le_iff_mem _).mpr hsH₀)⟩,
      fun P' hP' hP'H₀ => ?_⟩
    have := hP'.1
    have hsP' : s ∈ P' := hP'.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
    let Q' := (Ideal.map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) P').comap
      (aeval (R := O) (chartSubst a))
    have hQ'p : Q'.IsPrime := Ideal.comap_isPrime _ _
    have hQQ' : Q ⊔ Ideal.span {x} ≤ Q' := by
      refine sup_le (fun F hF => ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
      · exact Ideal.map_mono (le_sup_left.trans hP'.2)
          (aeval_chartSubst_mem_of_mem_blowUpOf hPp hD.den_not_mem (fun j => blowUpCof_spec e h j) hF)
      · rw [Ideal.mem_comap]
        rcases hx with rfl | rfl
        · rw [aeval_chartSubst_liftForm]
          exact Ideal.mem_map_of_mem _ hsP'
        · simp only [newVar, aeval_X, chartSubst]
          exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (P'.mul_mem_left _ hsP'))
    have hQ'H : Q' ≤ H := fun F hF => mem_of_aeval_chartSubst_mem hHp hP'H₀ _ haS hrelH hF
    have hHQ' := hHmin.2 ⟨hQ'p, hQQ'⟩ hQ'H
    intro p hp
    have h5 : Polynomial.C p ∈ Ideal.map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) P' := by
      rw [← aeval_chartSubst_liftForm a p]
      exact hHQ' hp
    simpa using Ideal.mem_map_C_iff.mp h5 0

  have := hH₀p
  unfold divCycle
  rw [dite_eq_left ⟨hmin₀, hrel₀⟩]
  have hne := length_localizedQuot_ne_top (P ⊔ Ideal.span {s}) H₀ hmin₀
  have hnz : multAt (P ⊔ Ideal.span {s}) H₀ ≠ 0 := by
    unfold multAt
    rw [Ne, Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]
    intro hs
    obtain ⟨r, hr, hr0⟩ := hs (Ideal.Quotient.mk _ 1)
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, mul_one,
      Ideal.Quotient.eq_zero_iff_mem] at hr0
    exact hr (hmin₀.1.2 hr0)
  have htn : (multAt (P ⊔ Ideal.span {s}) H₀).toNat ≠ 0 :=
    fun h0 => (ENat.toNat_eq_zero.mp h0).elim hnz hne
  exact_mod_cast htn

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBridgeFull
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem IntNumIsFieldIntersection.full : IntNumIsFieldIntersection.Statement.{u} :=
  IntNumIsFieldIntersection.of_intNumBase_cutRational FieldNumbers.IntNumBase.full
    FieldNumbers.CutRational.full

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.DivCycleEqZeroOfNotMem
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

noncomputable section

section Helpers

variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

private theorem divCycle_eq_zero_of_not_mem' {P W : Ideal (MRing ι R)} {x : MRing ι R} (h : x ∉ W) :
    divCycle P x W = 0 := by
  by_contra h'
  exact h (form_mem_of_divCycle_ne_zero h')

private theorem divCycle_nonneg' (P : Ideal (MRing ι R)) (x : MRing ι R) (W : Ideal (MRing ι R)) :
    0 ≤ divCycle P x W := by
  unfold divCycle
  split_ifs <;> positivity

private theorem facts_of_divCycle_ne_zero' {P W : Ideal (MRing ι R)} {x : MRing ι R}
    (h : divCycle P x W ≠ 0) : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes ∧ IsRelevant W := by
  unfold divCycle at h
  split_ifs at h with hc
  · exact hc
  · exact absurd rfl h

end Helpers

section Rel

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {R : Type u} [CommRing R]
  [IsNoetherianRing R]

private theorem ratDiv_eq_of_rel {P W : Ideal (MRing ι R)} (hP : P.IsPrime) (hPW : P ≤ W)
    {f g a v : MRing ι R} (hf : f ∉ P) (hg : g ∉ P) (ha : a ∉ W) (h : a * f - v * g ∈ P) :
    v ∉ P ∧ ratDiv P f g W = divCycle P v W := by
  have haP : a ∉ P := fun h' => ha (hPW h')
  have hv : v ∉ P := by
    intro hv
    have e : a * f = (a * f - v * g) + v * g := by ring
    have h1 : a * f ∈ P := by rw [e]; exact P.add_mem h (P.mul_mem_right _ hv)
    exact (hP.mem_or_mem h1).elim haP hf
  refine ⟨hv, ?_⟩
  have e1 := congrFun (divCycle_congr_of_sub_mem h) W
  rw [DivCycleMul.proof R K ι P a f hP haP hf, DivCycleMul.proof R K ι P v g hP hv hg] at e1
  simp only [Pi.add_apply] at e1
  rw [divCycle_eq_zero_of_not_mem' ha] at e1
  unfold ratDiv
  linarith

end Rel

section Proof

theorem ExceptionalComparison.proof (h₁ : BlowUpDecomposition.Statement.{u}) (h₂ : BlowUpOrderLe.Statement.{u})
    (h₃ : ExceptionalContraction.Statement.{u}) : ExceptionalComparison.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hH e hce m hm hmP hmH G' hϖG' hY₀ hE
  obtain ⟨hQm, -, hsQ, hY₀Q, hD₁, -, -, -⟩ :=
    h₁ O ϖ hϖ K ι P d hP b f g hD c s hs hsP hH e hce m hm hmP hmH
  have hG := h₃ O ϖ hϖ K ι P d hP b f g hD c s hs hsP hH e hce m hm hmP hmH G' hϖG' hY₀ hE
  set Q := blowUpOf P (blowUpGens s g f m e) with hQdef
  set G := G'.comap (liftForm (J := BlowUpIdx ι)) with hGdef
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hQp : Q.IsPrime := hQm.multiProj.isPrime
  obtain ⟨hG'min, hG'rel⟩ := facts_of_divCycle_ne_zero' hY₀.ne'
  have hGp : G.IsPrime := hG.1.1
  have hPG : P ≤ G := le_sup_left.trans hG.1.2
  have hGrel : IsRelevant G := by
    intro k
    obtain ⟨i, hi⟩ := hG'rel (some k)
    refine ⟨i, fun h => hi ?_⟩
    rw [hGdef, Ideal.mem_comap] at h
    simpa [liftForm, rename_X] using h
  have hlift : ∀ {p : MRing ι O}, p ∉ P → liftForm (J := BlowUpIdx ι) p ∉ Q := by
    intro p hp h
    rw [hQdef, blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_liftForm, Polynomial.C_eq_zero,
      Ideal.Quotient.eq_zero_iff_mem] at h
    exact hp h
  have hliftP : ∀ {p : MRing ι O}, p ∈ P → liftForm (J := BlowUpIdx ι) p ∈ Q := by
    intro p hp
    rw [hQdef, blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_liftForm,
      Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
  have hfP : f ∉ P := hD.1.num_not_mem
  have hgP : g ∉ P := hD.1.den_not_mem
  have hY₁Q : (newVar (some none) : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ Q := hD₁.1.num_not_mem
  have hmul := DivCycleMul.proof O (Option K) (extIdx ι (BlowUpIdx ι)) Q
  have hnm : ∀ {x y}, x ∉ Q → y ∉ Q → x * y ∉ Q := fun hx hy h => (hQp.mem_or_mem h).elim hx hy

  have e1 := congrFun (divCycle_congr_of_sub_mem (blowUp_relation P s g f m e)) G'
  rw [map_mul, hmul _ _ hQp (hnm (hlift hsP) (hlift hgP)) hY₁Q, hmul _ _ hQp (hlift hsP) (hlift hgP),
    hmul _ _ hQp (hlift (fun h => (hPp.mem_or_mem h).elim hfP hmP)) hY₀Q] at e1
  simp only [Pi.add_apply] at e1
  have eE : ratDiv Q (liftForm (f * m)) (liftForm g * newVar (some none)) G' =
      ratDiv Q (liftForm f) (liftForm g) G' - ratDiv Q (newVar (some none)) (liftForm m) G' := by
    unfold ratDiv
    rw [map_mul, hmul _ _ hQp (hlift hfP) (hlift hmP), hmul _ _ hQp (hlift hgP) hY₁Q]
    simp only [Pi.add_apply]
    ring
  have eE' : ratDiv Q (liftForm (f * m)) (liftForm g * newVar (some none)) G' =
      divCycle Q (liftForm s) G' - divCycle Q (newVar none) G' := by
    unfold ratDiv
    rw [hmul _ _ hQp (hlift hgP) hY₁Q]
    simp only [Pi.add_apply]
    linarith

  have hD₁G' : 0 ≤ ratDiv Q (newVar (some none)) (liftForm m) G' := by
    by_cases h0 : ratDiv Q (newVar (some none)) (liftForm m) G' = 0
    · exact h0.ge
    have hW : G' ∈ (Q ⊔ Ideal.span {newVar (some none)}).minimalPrimes ∧ IsRelevant G' ∨
        G' ∈ (Q ⊔ Ideal.span {liftForm m}).minimalPrimes ∧ IsRelevant G' := by
      unfold ratDiv at h0
      by_cases h1 : divCycle Q (newVar (some none)) G' = 0
      · right; exact facts_of_divCycle_ne_zero' (fun h2 => h0 (by rw [h1, h2, sub_zero]))
      · left; exact facts_of_divCycle_ne_zero' h1
    have hW' : G'.IsPrime ∧ Q ≤ G' ∧ IsRelevant G' := by
      rcases hW with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨h1.1.1, le_sup_left.trans h1.1.2, h2⟩
      · exact ⟨h1.1.1, le_sup_left.trans h1.1.2, h2⟩
    obtain ⟨a, v, ha, hrel⟩ := hD₁.2 G' hW'.1 hW'.2.1 hW'.2.2
    have := ratDiv_eq_of_rel hQp hW'.2.1 hY₁Q (hlift hmP) ha hrel
    rw [this.2]
    exact divCycle_nonneg' _ _ _

  obtain ⟨a, v, haG, hrelP⟩ := hD.2 G hGp hPG hGrel
  obtain ⟨hvP, hfgG⟩ := ratDiv_eq_of_rel hPp hPG hfP hgP haG hrelP
  have hrelQ : liftForm a * liftForm f - liftForm v * liftForm g ∈ Q := by
    have := hliftP hrelP
    rwa [map_sub, map_mul, map_mul] at this
  have haG' : liftForm (J := BlowUpIdx ι) a ∉ G' := fun h => haG (by rw [hGdef, Ideal.mem_comap]; exact h)
  have hQG' : Q ≤ G' := le_sup_left.trans hG'min.1.2
  obtain ⟨-, hfgG'⟩ := ratDiv_eq_of_rel hQp hQG' (hlift hfP) (hlift hgP) haG' hrelQ

  have hs' := h₂ O K ι (BlowUpIdx ι) P hPp (blowUpGens s g f m e) G' (newVar none) hY₀Q hG'min hG'rel
    s hsP hG s hsP
  have hv' := h₂ O K ι (BlowUpIdx ι) P hPp (blowUpGens s g f m e) G' (newVar none) hY₀Q hG'min hG'rel
    s hsP hG v hvP
  refine ⟨G, ?_, ?_, ?_⟩
  · rw [hGdef, Ideal.mem_comap]
    simpa [liftForm] using hϖG'
  · rw [eE']
    linarith
  · rw [eE, hfgG', hfgG]
    linarith

end Proof

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisMore
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)

def FlagFrameOfFullFlag.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (K : Type) [Fintype K]
    (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (e : ℕ),
    ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal F x) e →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B : ChartBundle F (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) N E)
      (fl : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FullFlag F x B),
      ∃ w : Module.Basis (Fin N) Ω E, IsFlagFrame x B w fl.deg

end GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsLast
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def ResidualContractionComponent.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
    ∀ e : K → ℕ, (∀ k, (c k : ℤ) = b k + e k) →
    ∀ m : MRing ι O, IsMultiHomog m e → m ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → m ∉ H) →
    ∀ G' : Ideal (MRing (extIdx ι (BlowUpIdx ι)) O),
      (C ϖ : MRing (extIdx ι (BlowUpIdx ι)) O) ∈ G' →
      0 < divCycle (blowUpOf P (blowUpGens s g f m e)) (liftForm s) G' →
      0 < ratDiv (blowUpOf P (blowUpGens s g f m e)) (newVar (some none)) (liftForm m) G' →
      G'.comap (liftForm (J := BlowUpIdx ι)) ∈ (P ⊔ Ideal.span {s}).minimalPrimes

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalQuotRing
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem LocalQuotRing.proof : LocalQuotRing.Statement.{u} := by
  intro R _ P U _ hP hPU
  have hdisj : Disjoint (U.primeCompl : Set R) (P : Set R) :=
    Set.disjoint_left.mpr fun x hx hxP => hx (hPU hxP)
  have hPS : (P.map (algebraMap R (Localization.AtPrime U))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint U.primeCompl (Localization.AtPrime U) P hP hdisj
  have hker : (P.map (algebraMap R (Localization.AtPrime U))).comap
      (algebraMap R (Localization.AtPrime U)) = P :=
    IsLocalization.under_map_of_isPrime_disjoint U.primeCompl (Localization.AtPrime U) hP hdisj
  haveI := hPS
  have hdom : IsDomain (localQuot P U) := Ideal.Quotient.isDomain _
  have hloc : IsLocalRing (localQuot P U) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hmax : U.map (localQuotMap P U) = IsLocalRing.maximalIdeal (localQuot P U) := by
    rw [localQuotMap, ← Ideal.map_map, Localization.AtPrime.map_eq_maximalIdeal]
    exact IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  refine ⟨hdom, hloc, fun y => ?_, fun x => ?_⟩
  · rw [hmax, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  · rw [localQuotMap, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, hker]

end GroundTheory.Heights₂.Heights.NumbersDVR
end

