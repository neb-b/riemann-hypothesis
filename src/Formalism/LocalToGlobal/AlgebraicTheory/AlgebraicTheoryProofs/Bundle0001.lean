module

public import Formalism.LocalToGlobal.AlgebraicTheory.Bundle0002
public import ReciprocityTheory.EigenFrames.EigenSt
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.Bundle0006

@[expose] public section

-- bundled from Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.EigenFrameDualOf
section
noncomputable section
open scoped BigOperators
open NumberField

namespace Formalism.L2.AlgTh

open Formalism.L2.Th1.GD (InMul frameM)
open Formalism.L2.Col (Fields Sp)
open Formalism.L2.Ker (Amb DVar)

namespace CapelliMinorMembership

theorem norm_natCast (p : ℕ) [Fact p.Prime] {N : ℕ} (h : ¬ p ∣ N) : ‖(N : ℂ_[p])‖ = 1 := by
  have hq : ‖(N : ℚ_[p])‖ = 1 := by
    exact Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd (Fact.out)).2 h)
  have e1 : ‖(N : PadicAlgCl p)‖ = 1 := by
    rw [← hq, ← PadicAlgCl.norm_extends]
    simp
  rw [← e1, ← PadicComplex.norm_extends]
  simp

end CapelliMinorMembership

theorem eigenFrameDual_of (h : ReciprocityTheory.EigenFramesTheory.EigenFrameDual.{0, 0}) : EigenFrameDual := by
  intro E _ _ p _ ι hd τ₀
  exact h p E _ (NumberField.RingOfIntegers.basis E) ι hd τ₀

theorem CapelliMinorMembership.key_term {X : Fields} (A : Amb X) {a b : ℕ} {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) {n₀ : ℕ}
    (hn0 : (n₀ : ℂ_[p]) ≠ 0) (r : X.Tau → Module.Free.ChooseBasisIndex ℤ (𝓞 X.E) → ℂ_[p])
    (τ₁ τ : X.Tau) (β₁ β' β : Fin b) (α₁ α' α : Fin a) (i : Module.Free.ChooseBasisIndex ℤ (𝓞 X.E)) :
    (ι : ℂ →+* ℂ_[p]) (((n₀ : ℂ) • vecE A.σ₀ ((NumberField.RingOfIntegers.basis X.E i : 𝓞 X.E) : X.E) β α)
        (τ₁, β₁, α₁)) *
      (if β = β' ∧ α = α' then ι (A.cD τ) * r τ i * (n₀ : ℂ_[p])⁻¹ else 0) =
    if α = α₁ then (if β = β₁ then
      (if β₁ = β' ∧ α₁ = α' then ι (A.cD τ) *
        (r τ i * ι (X.embC A.σ₀ τ₁ ((NumberField.RingOfIntegers.basis X.E i : 𝓞 X.E) : X.E))) else 0)
      else 0) else 0 := by
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hα : α = α₁
  · subst hα
    by_cases hβ : β = β₁
    · subst hβ
      by_cases h' : β = β' ∧ α = α'
      · simp only [vecE, h', and_self, if_true]
        rw [map_mul, map_natCast]
        field_simp
        simp only [RingEquiv.coe_toRingHom]
        ring
      · simp [vecE, h']
    · simp [vecE, hβ, Ne.symm hβ]
  · simp [vecE, hα, Ne.symm hα]

theorem CapelliMinorMembership.collapse {K κ B C : Type} [AddCommMonoid K] [Fintype κ] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] (g : κ → K) (β₁ : B) (α₁ : C) :
    ∑ i, ∑ β : B, ∑ α : C, (if α = α₁ then (if β = β₁ then g i else 0) else 0) = ∑ i, g i := by
  simp [Finset.sum_ite_eq', Finset.sum_ite_eq]

theorem kerFrame_of (h : EigenFrameDual) : KerFrame := by
  intro X A a b N N' L p _ ι hd hinj hcD hn
  obtain ⟨n₀, hn₀, hv⟩ := hn
  choose r hr1 hr2 using fun τ : X.Tau => h X.E p ι hd (X.embC A.σ₀ τ)
  have hn0 : (n₀ : ℂ_[p]) ≠ 0 := by
    intro h0
    have := CapelliMinorMembership.norm_natCast p hn₀
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  refine ⟨Module.Free.ChooseBasisIndex ℤ (𝓞 X.E) × Fin b × Fin a, inferInstance,
    fun j => (n₀ : ℂ) • vecE A.σ₀ ((NumberField.RingOfIntegers.basis X.E j.1 : 𝓞 X.E) : X.E) j.2.1 j.2.2,
    fun j k => if j.2.1 = k.2.1 ∧ j.2.2 = k.2.2 then ι (A.cD k.1) * r k.1 j.1 * (n₀ : ℂ_[p])⁻¹ else 0,
    fun j => hv _ _ _, ?_, ?_⟩
  · intro j k
    dsimp only
    split_ifs
    · rw [norm_mul, norm_mul, norm_inv, CapelliMinorMembership.norm_natCast p hn₀, inv_one, mul_one]
      first
      | exact mul_le_one₀ (hcD _) (norm_nonneg _) (hr1 _ _)
      | nlinarith [norm_nonneg (ι (A.cD k.1)), norm_nonneg (r k.1 j.1), hcD k.1, hr1 k.1 j.1]
    · simp
  · intro i k
    obtain ⟨τ₁, β₁, α₁⟩ := i
    obtain ⟨τ, β', α'⟩ := k
    unfold frameM
    simp only [Fintype.sum_prod_type]
    simp only [CapelliMinorMembership.key_term A ι hn0 r]
    refine (CapelliMinorMembership.collapse _ β₁ α₁).trans ?_
    by_cases hc : β₁ = β' ∧ α₁ = α'
    · refine (Finset.sum_congr rfl (fun i _ => if_pos hc)).trans ?_
      rw [← Finset.mul_sum, hr2 τ (X.embC A.σ₀ τ₁)]
      obtain ⟨rfl, rfl⟩ := hc
      by_cases ht : τ₁ = τ
      · subst ht
        simp
      · have hne : X.embC A.σ₀ τ₁ ≠ X.embC A.σ₀ τ := fun e => ht (hinj e)
        rw [if_neg hne, mul_zero, if_neg]
        intro he
        exact ht (Prod.mk.inj he).1
    · refine (Finset.sum_congr rfl (fun i _ => if_neg hc)).trans ?_
      rw [Finset.sum_const_zero, if_neg]
      intro he
      have h2 := (Prod.mk.inj he).2
      exact hc ⟨(Prod.mk.inj h2).1, (Prod.mk.inj h2).2⟩

end Formalism.L2.AlgTh
end
end

-- bundled from Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.KerJet
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.AlgTh

open Formalism.L2.Th1.H (taylorMv cntVec cntVec_apply taylorMv_coeff)
open Formalism.L2.Ker (DVar VCx coordX derivAt0)
open Formalism.DworkPowerSeriesWeights (mfact)

namespace KerJet

variable {n : Type} [Fintype n] [DecidableEq n]

theorem card_fib {k : ℕ} (f : Fin k → n) (i : n) :
    Fintype.card {a // f a = i} = cntVec f i := by
  rw [cntVec_apply, Fintype.card_subtype]

theorem perm_of_cnt {k : ℕ} (f g : Fin k → n) (h : cntVec f = cntVec g) :
    ∃ σ : Equiv.Perm (Fin k), g ∘ σ = f := by
  refine ⟨Equiv.ofFiberEquiv (f := f) (g := g) (fun i => Fintype.equivOfCardEq (by rw [card_fib, card_fib, h])), ?_⟩
  funext a
  exact Equiv.ofFiberEquiv_map _ a

theorem cnt_comp_perm {k : ℕ} (g : Fin k → n) (σ : Equiv.Perm (Fin k)) : cntVec (g ∘ σ) = cntVec g := by
  ext i
  rw [cntVec_apply, cntVec_apply, ← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (σ.subtypeEquiv (fun a => Iff.rfl))

theorem card_cnt {k : ℕ} (g : Fin k → n) :
    (Finset.univ.filter fun f : Fin k → n => cntVec f = cntVec g).card * ∏ i, (cntVec g i).factorial =
      k.factorial := by
  classical
  set t := Finset.univ.filter fun f : Fin k → n => cntVec f = cntVec g with ht
  have hstab : (Finset.univ.filter fun τ : Equiv.Perm (Fin k) => g ∘ τ = g).card = ∏ i, (cntVec g i).factorial := by
    rw [← Fintype.card_subtype, DomMulAct.stabilizer_card]
    exact Finset.prod_congr rfl fun i _ => by rw [card_fib]
  have hfib : ∀ f ∈ t, ((Finset.univ : Finset (Equiv.Perm (Fin k))).filter fun σ : Equiv.Perm (Fin k) => g ∘ ⇑σ = f).card =
      (Finset.univ.filter fun τ : Equiv.Perm (Fin k) => g ∘ τ = g).card := by
    intro f hf
    obtain ⟨σ₀, hσ₀⟩ := perm_of_cnt f g (Finset.mem_filter.1 hf).2
    refine Finset.card_bij' (fun (σ : Equiv.Perm (Fin k)) _ => σ * σ₀⁻¹) (fun (τ : Equiv.Perm (Fin k)) _ => τ * σ₀) ?_ ?_ ?_ ?_
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      funext x
      have h1 := congrFun hσ (σ₀⁻¹ x)
      have h2 := congrFun hσ₀ (σ₀⁻¹ x)
      simp only [Function.comp_apply, Equiv.Perm.mul_apply] at h1 h2 ⊢
      rw [h1, ← h2]; simp
    · intro τ hτ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      funext x
      have h1 := congrFun hτ (σ₀ x)
      simp only [Function.comp_apply, Equiv.Perm.mul_apply] at h1 ⊢
      rw [h1, ← hσ₀]; rfl
    · intro σ _; simp
    · intro τ _; simp
  have hall : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin k))), g ∘ σ ∈ t := by
    intro σ _
    rw [ht, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, cnt_comp_perm g σ⟩
  have hsum := Finset.card_eq_sum_card_fiberwise hall
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, hstab] at hsum
  exact hsum.symm

end KerJet

open KerJet

theorem flat_single (T : Type) [Fintype T] [DecidableEq T] (a b : ℕ) (k : DVar T a b) :
    flat T a b (Pi.single k (1 : ℂ)) = coordX k := by
  funext τ i j
  simp only [flat, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, coordX, Pi.single_apply]
  by_cases h : τ = k.1 ∧ i = k.2.1 ∧ j = k.2.2
  · rw [if_pos h, if_pos]
    obtain ⟨h1, h2, h3⟩ := h
    subst h1 h2 h3; rfl
  · rw [if_neg h, if_neg]
    rintro rfl
    exact h ⟨rfl, rfl, rfl⟩

theorem taylor_jet_expansion : TaylorJet := by
  intro T _ _ a b G hG m
  set K := Multiset.card m.toMultiset with hKdef
  set l := m.toMultiset.toList with hldef
  have hl : l.length = K := by simp [hldef, hKdef]
  let g0 : Fin K → DVar T a b := fun i => l.get ⟨i, by simp [hl]⟩
  have hof : List.ofFn g0 = l := by
    refine List.ext_get (by simp [hl]) fun i h1 h2 => ?_
    simp [g0]
  have hg0 : cntVec g0 = m := by
    ext i
    have h1 : (Finset.univ.filter fun j => g0 j = i).card = Multiset.count i ((Finset.univ : Finset (Fin K)).val.map g0) := by
      rw [Multiset.count_map, Finset.card_def, Finset.filter_val]
      congr 1
      exact Multiset.filter_congr fun x _ => eq_comm
    rw [cntVec_apply, h1, Fin.univ_val_map, hof, hldef, Multiset.coe_toList, Finsupp.count_toMultiset]
  have hdeg : m.degree = K := by
    rw [Finsupp.degree_eq_sum, hKdef, Finsupp.card_toMultiset, Finsupp.sum_fintype _ _ (fun _ => rfl)]
    rfl
  have hGc : ContDiff ℂ ⊤ G := hG.contDiff
  let L : (DVar T a b → ℂ) →L[ℂ] VCx T a b := ((flat T a b).toContinuousLinearEquiv : (DVar T a b → ℂ) →L[ℂ] VCx T a b)
  have hFL : (fun z => G (flat T a b z)) = G ∘ L := rfl
  have hterm : ∀ f : Fin K → DVar T a b, cntVec f = m →
      iteratedFDeriv ℂ K (fun z => G (flat T a b z)) 0 (fun j => Pi.single (f j) (1 : ℂ)) = derivAt0 G m := by
    intro f hf
    obtain ⟨σ, hσ⟩ := perm_of_cnt f g0 (hf.trans hg0.symm)
    rw [hFL, L.iteratedFDeriv_comp_right hGc 0 (by exact_mod_cast le_top),
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
    have hv : (fun j => L (Pi.single (f j) (1 : ℂ))) = (fun i => coordX (g0 i)) ∘ σ := by
      funext j
      simp only [Function.comp_apply]
      rw [← hσ]
      exact flat_single T a b _
    rw [map_zero, hv, (hGc.contDiffAt).iteratedFDeriv_comp_perm]
    rfl
  rw [taylorMv_coeff _ K m hdeg, Finset.sum_congr rfl fun f hf => hterm f (Finset.mem_filter.1 hf).2,
    Finset.sum_const, nsmul_eq_mul]
  have hc := card_cnt g0
  rw [hg0] at hc
  have hmf : mfact m = ∏ i, (m i).factorial := Finsupp.prod_fintype _ _ (fun _ => rfl)
  rw [← hmf] at hc
  have hc' : (((Finset.univ.filter fun f : Fin K → DVar T a b => cntVec f = m).card : ℕ) : ℂ) * (mfact m : ℂ) =
      (K.factorial : ℂ) := by exact_mod_cast hc
  have hK0 : (K.factorial : ℂ) ≠ 0 := by exact_mod_cast K.factorial_ne_zero
  calc _ = ((K.factorial : ℂ))⁻¹ * ((((Finset.univ.filter fun f : Fin K → DVar T a b => cntVec f = m).card : ℕ) : ℂ) *
        (mfact m : ℂ)) * derivAt0 G m := by ring
    _ = _ := by rw [hc', inv_mul_cancel₀ hK0, one_mul]

end Formalism.L2.AlgTh
end
end

