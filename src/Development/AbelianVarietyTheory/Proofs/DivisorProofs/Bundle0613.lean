module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0584
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0578
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0585
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0573

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCob1WittLiftModP
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WittStart

theorem eq_zero_or_single {ι : Type} [Fintype ι] [DecidableEq ι] (γ : ι →₀ ℕ) (h : γ.degree < 2) :
    γ = 0 ∨ ∃ s, γ = Finsupp.single s 1 := by
  by_cases h0 : γ = 0
  · exact Or.inl h0
  right
  obtain ⟨s, hs⟩ : ∃ s, γ s ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h0 (Finsupp.ext hc)
  rw [Finsupp.degree_eq_sum] at h
  have hsum : ∑ i, γ i = γ s + ∑ i ∈ Finset.univ.erase s, γ i :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ s)).symm
  refine ⟨s, Finsupp.ext fun t => ?_⟩
  by_cases hts : t = s
  · subst hts
    have : ∑ i ∈ Finset.univ.erase t, γ i ≥ 0 := Nat.zero_le _
    simp only [Finsupp.single_eq_same]
    omega
  · simp only [Finsupp.single_apply, Ne.symm hts, if_false]
    have : γ t ≤ ∑ i ∈ Finset.univ.erase s, γ i :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨hts, Finset.mem_univ t⟩)
    omega

variable {R : Type} [CommRing R] {d : ℕ}

theorem coeff_single_linear_substitution_pair {τ : Type} (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    (u v : Fin d → MvPowerSeries τ R) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (t : τ) :
    coeff (Finsupp.single t 1) (at2 c u v) =
      ∑ i, coeff (Finsupp.single (Sum.inl i) 1) c * coeff (Finsupp.single t 1) (u i) +
      ∑ i, coeff (Finsupp.single (Sum.inr i) 1) c * coeff (Finsupp.single t 1) (v i) := by
  unfold at2
  rw [GlobalTheory.FormalCalc.coeff_single_subst, Fintype.sum_sum_type]
  · rfl
  · rintro (i | i)
    · exact hu i
    · exact hv i

theorem constantCoeff_subst0 {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries σ R) :
    constantCoeff (subst a f) = constantCoeff f := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have h1 : f = (f - C (constantCoeff f)) + C (constantCoeff f) := by ring
  conv_lhs => rw [h1]
  rw [subst_add hs, map_add (f := _), constantCoeff_subst_eq_zero hs ha (by simp), subst_C, zero_add]
  simp

theorem constantCoeff_op {τ : Type} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ0 : ∀ i, constantCoeff (μ i) = 0) (u v : Fin d → MvPowerSeries τ R)
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) :
    constantCoeff (op μ u v i) = 0 := by
  unfold op at2
  rw [constantCoeff_subst0 (fun s => by cases s with | inl s => exact hu s | inr s => exact hv s)]
  exact hμ0 i

theorem coeff_single_op {τ : Type} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i s, coeff (Finsupp.single s 1) (μ i) = coeff (Finsupp.single s 1) (addLaw R d i))
    (u v : Fin d → MvPowerSeries τ R)
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) (t : τ) :
    coeff (Finsupp.single t 1) (op μ u v i) =
      coeff (Finsupp.single t 1) (u i) + coeff (Finsupp.single t 1) (v i) := by
  classical
  unfold op
  rw [coeff_single_linear_substitution_pair _ _ _ hu hv]
  simp only [hμ, addLaw, map_add (f := _), GlobalTheory.FormalCalc.coeff_single_X]
  simp [add_mul, Finset.sum_add_distrib]

theorem coeff_single_coc {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ0 : ∀ i, constantCoeff (μ i) = 0)
    (hμ : ∀ i s, coeff (Finsupp.single s 1) (μ i) = coeff (Finsupp.single s 1) (addLaw R d i))
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) (hc : IsCoc μ c) (s : Fin d ⊕ Fin d) :
    coeff (Finsupp.single s 1) c = 0 := by
  classical
  have hx1 : ∀ i, constantCoeff (x1 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
  have hx2 : ∀ i, constantCoeff (x2 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
  have hx3 : ∀ i, constantCoeff (x3 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
  have hinl : ∀ j, coeff (Finsupp.single (Sum.inl j) 1) c = 0 := by
    intro j
    have h := congrArg (coeff (Finsupp.single (Sum.inl j : Fin d ⊕ (Fin d ⊕ Fin d)) 1)) hc.1
    unfold cob2 at h
    rw [map_sub, map_add (f := _), map_sub, map_zero,
      coeff_single_linear_substitution_pair _ _ _ hx2 hx3,
      coeff_single_linear_substitution_pair _ _ _ (constantCoeff_op hμ0 _ _ hx1 hx2) hx3,
      coeff_single_linear_substitution_pair _ _ _ hx1 (constantCoeff_op hμ0 _ _ hx2 hx3),
      coeff_single_linear_substitution_pair _ _ _ hx1 hx2] at h
    simp only [coeff_single_op hμ _ _ hx1 hx2, coeff_single_op hμ _ _ hx2 hx3, x1, x2, x3,
      GlobalTheory.FormalCalc.coeff_single_X] at h
    simpa using h
  cases s with
  | inl j => exact hinl j
  | inr j =>
    have h := congrArg (coeff (Finsupp.single (Sum.inr j) 1)) hc.2
    unfold swap at h
    rw [coeff_single_linear_substitution_pair _ _ _ (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _)] at h
    simp only [GlobalTheory.FormalCalc.coeff_single_X] at h
    simp only [Sum.inr.injEq, reduceCtorEq, if_false, mul_zero, Finset.sum_const_zero, zero_add,
      mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    rw [← h]
    simp [hinl]

end GlobalTheory.WittStart

namespace GlobalTheory.WittStart

theorem start : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), IsLaw μ → ∀ c, IsCoc μ c →
    ∀ w : Fin d → k, ∃ f ∈ intBy p k (Fin d) 1, RedV p (lin f) w ∧
      ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree < 2 → ∃ w : WittVector p k,
        coeff γ (cob1 (fun i => Katz.lift p (μ i)) f - Katz.lift p c) =
          algebraMap (WittVector p k) (Fr p k) (p * w) := by
  intro p _ k _ _ _ d μ hμ c hc w
  classical
  have hL := GlobalTheory.T.formal_group_law_linear_coeff_additive p k d μ hμ
  have hdeg : ∀ s : Fin d ⊕ Fin d, (Finsupp.single s 1).degree ≤ 1 := fun s => by
    rw [Finsupp.degree_single]
  have hμk : ∀ i s, coeff (Finsupp.single s 1) (μ i) = coeff (Finsupp.single s 1) (addLaw k d i) :=
    fun i s => (hL i _ (hdeg s)).1
  have hμF : ∀ i s, coeff (Finsupp.single s 1) (Katz.lift p (μ i)) =
      coeff (Finsupp.single s 1) (addLaw (Fr p k) d i) := fun i s => (hL i _ (hdeg s)).2
  have hμ0F : ∀ i, constantCoeff (Katz.lift p (μ i)) = 0 := fun i => constantCoeff_lift p (hμ.const i)
  have hclin := coeff_single_coc hμ.const hμk c hc
  set T : k → Fr p k := fun x => algebraMap (WittVector p k) (Fr p k) (WittVector.teichmuller p x)
    with hT
  set f : MvPowerSeries (Fin d) (Fr p k) :=
    (-(WittVector.teichmuller p (constantCoeff c))) • (1 : MvPowerSeries (Fin d) (Fr p k)) +
      ∑ i, WittVector.teichmuller p (w i) • (X i : MvPowerSeries (Fin d) (Fr p k)) with hf
  have hcoeff : ∀ α, coeff α f = (if α = 0 then -T (constantCoeff c) else 0) +
      ∑ i, if α = Finsupp.single i 1 then T (w i) else 0 := by
    intro α
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hf, map_add (f := _), map_sum]
    have e : ∀ (r : WittVector p k) (g : MvPowerSeries (Fin d) (Fr p k)),
        coeff α (r • g) = algebraMap (WittVector p k) (Fr p k) r * coeff α g := fun r g => by
      rw [← algebraMap_smul (Fr p k) r g, coeff_smul]
    simp only [e, coeff_one, coeff_X, hT, map_neg]
    congr 1
    · split_ifs <;> simp
    · refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp
  refine ⟨f, ?_, ?_, ?_⟩
  · intro α
    rw [hcoeff α]
    refine ⟨(if α = 0 then -WittVector.teichmuller p (constantCoeff c) else 0) +
      ∑ i, if α = Finsupp.single i 1 then WittVector.teichmuller p (w i) else 0, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [one_mul, map_add (f := _), map_sum]
    congr 1
    · split_ifs <;> simp [hT]
    · refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp [hT]
  · intro i
    refine ⟨WittVector.teichmuller p (w i), ?_, ?_⟩
    · show coeff _ f = _
      rw [hcoeff]
      simp [Finsupp.single_eq_single_iff, hT]
    · rw [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
  · intro γ hγ
    refine ⟨0, ?_⟩
    rw [mul_zero, map_zero]
    rcases eq_zero_or_single γ hγ with rfl | ⟨s, rfl⟩
    · have h0s : ∀ i : Fin d, (0 : Fin d →₀ ℕ) ≠ Finsupp.single i 1 :=
        fun i => (Finsupp.single_ne_zero.mpr one_ne_zero).symm
      rw [coeff_zero_eq_constantCoeff_apply, map_sub]
      unfold cob1 inL inR
      rw [map_sub, map_sub, constantCoeff_subst0 hμ0F, constantCoeff_subst0 (fun _ => constantCoeff_X _),
        constantCoeff_subst0 (fun _ => constantCoeff_X _), ← coeff_zero_eq_constantCoeff_apply,
        ← coeff_zero_eq_constantCoeff_apply, coeff_lift, hcoeff]
      simp [hT, coeff_zero_eq_constantCoeff_apply, h0s]
    · rw [map_sub, coeff_lift, hclin, WittVector.teichmuller_zero, map_zero, sub_zero]
      unfold cob1 inL inR
      rw [map_sub, map_sub, GlobalTheory.FormalCalc.coeff_single_subst hμ0F,
        GlobalTheory.FormalCalc.coeff_single_subst (fun _ => constantCoeff_X _),
        GlobalTheory.FormalCalc.coeff_single_subst (fun _ => constantCoeff_X _)]
      simp only [hμF, addLaw, map_add (f := _), mul_add, Finset.sum_add_distrib]
      ring

end GlobalTheory.WittStart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalGroupLawLiftOfSurjective
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftLaw

def cmap {σ R S : Type} [CommRing R] [CommRing S] (g : R → S) (f : MvPowerSeries σ R) : MvPowerSeries σ S :=
  fun α => g (coeff α f)

theorem coeff_cmap {σ R S : Type} [CommRing R] [CommRing S] (g : R → S) (f : MvPowerSeries σ R) (α : σ →₀ ℕ) :
    coeff α (cmap g f) = g (coeff α f) := rfl

theorem swap_cmap {R S : Type} [CommRing R] [CommRing S] {d : ℕ} (g : R → S)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) : swap (cmap g c) = cmap g (swap c) := by
  ext α
  obtain ⟨⟨a, e⟩, rfl⟩ := (Finsupp.sumFinsuppEquivProdFinsupp : (Fin d ⊕ Fin d →₀ ℕ) ≃ (Fin d →₀ ℕ) × (Fin d →₀ ℕ)).symm.surjective α
  have h : (Finsupp.sumFinsuppEquivProdFinsupp : (Fin d ⊕ Fin d →₀ ℕ) ≃ (Fin d →₀ ℕ) × (Fin d →₀ ℕ)).symm (a, e) = Finsupp.sumElim a e := rfl
  rw [h, coeff_cmap, SwapCoeff.coeff_swap, SwapCoeff.coeff_swap, coeff_cmap]

theorem coeff_subst_elim_zero {R : Type} [CommRing R] {d : ℕ}
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) (β : Fin d →₀ ℕ) :
    coeff β (subst (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) R)) fun (_ : Fin d) => 0) c) =
      coeff (Finsupp.embDomain (Function.Embedding.inl : Fin d ↪ Fin d ⊕ Fin d) β) c := by
  classical
  have ha : HasSubst (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) R)) fun (_ : Fin d) => 0) :=
    hasSubst_of_constantCoeff_zero fun s => by rcases s with i | i <;> simp
  have hb : HasSubst (X ∘ (Function.Embedding.inl : Fin d ↪ Fin d ⊕ Fin d) :
      Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) :=
    hasSubst_of_constantCoeff_zero fun s => by simp
  have hr : rename (Function.Embedding.inl : Fin d ↪ Fin d ⊕ Fin d)
      (subst (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) R)) fun (_ : Fin d) => 0) c) =
      subst (fun s : Fin d ⊕ Fin d => if s.isLeft then (X s : MvPowerSeries (Fin d ⊕ Fin d) R) else 0) c := by
    rw [rename_eq_subst, subst_comp_subst_apply ha hb]
    congr 1
    funext s
    rcases s with i | i
    · simp [subst_X hb]
    · simp only [Sum.elim_inr, Sum.isLeft_inr]
      rw [← coe_substAlgHom hb, map_zero]
      rfl
  rw [← coeff_embDomain_rename (Function.Embedding.inl : Fin d ↪ Fin d ⊕ Fin d), hr,
    OnePair.coeff_subst_kill]
  rw [if_pos]
  rintro (i | i) hi
  · simp at hi
  · simp [Finsupp.embDomain_apply]

theorem exists_isLift : ∀ (B O : Type) [CommRing B] [CommRing O] (θ : B →+* O), Function.Surjective θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∃ μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B, IsLift θ μ' ∧ ∀ i, map θ (μ' i) = μ i := by
  intro B O _ _ θ hθ d μ hμ
  classical
  by_cases h1 : (1 : O) = 0
  ·
    haveI : Subsingleton O := subsingleton_of_zero_eq_one h1.symm
    have hm : ∀ i, map θ (addLaw B d i) = μ i := fun i => by
      ext α
      exact Subsingleton.elim _ _
    have ha : HasSubst (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) B)) fun (_ : Fin d) => 0) :=
      hasSubst_of_constantCoeff_zero fun s => by rcases s with i | i <;> simp
    have hs : HasSubst (Sum.elim (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) B))
        fun i => X (Sum.inl i)) :=
      hasSubst_of_constantCoeff_zero fun s => by rcases s with i | i <;> simp
    refine ⟨addLaw B d, ⟨fun i => by simp [addLaw], ?_, fun i => ?_, ?_⟩, hm⟩
    · funext i
      simp only [op, at2, addLaw]
      rw [subst_add ha, subst_X ha, subst_X ha]
      simp
    · simp only [swap, at2, addLaw]
      rw [subst_add hs, subst_X hs, subst_X hs]
      simp [add_comm]
    · have : (fun i => map θ (addLaw B d i)) = μ := funext hm
      rw [this]
      exact hμ
  ·
    let s : O → B := fun x => if x = 0 then 0 else if x = 1 then 1 else (hθ x).choose
    have hs : ∀ x, θ (s x) = x := fun x => by
      simp only [s]
      split_ifs with h h'
      · rw [map_zero, h]
      · rw [map_one, h']
      · exact (hθ x).choose_spec
    have hs0 : s 0 = 0 := by simp [s]
    have hs1 : s 1 = 1 := by simp [s, h1]
    refine ⟨fun i => cmap s (μ i), ⟨fun i => ?_, ?_, fun i => ?_, ?_⟩, fun i => ?_⟩
    · rw [← coeff_zero_eq_constantCoeff_apply, coeff_cmap, coeff_zero_eq_constantCoeff_apply,
        hμ.const i, hs0]
    · funext i
      ext β
      have hu := congrArg (coeff β) (congrFun hμ.unit i)
      simp only [op, at2] at hu ⊢
      rw [coeff_subst_elim_zero] at hu ⊢
      rw [coeff_cmap, hu, coeff_X, coeff_X]
      split_ifs
      · exact hs1
      · exact hs0
    · rw [swap_cmap, hμ.comm i]
    · have : (fun i => map θ (cmap s (μ i))) = μ := funext fun i => by
        ext α
        rw [coeff_map, coeff_cmap, hs]
      rw [this]
      exact hμ
    · ext α
      rw [coeff_map, coeff_cmap, hs]

end GlobalTheory.LiftLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorRigidifiedLocallyTrivial
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.RigTriv

variable {T X : Scheme.{0}}

theorem exists_lift (W : X.Opens) {Z : Scheme.{0}} (f : Z ⟶ X) (h : ∀ z, f z ∈ W) :
    ∃ g : Z ⟶ W.toScheme, g ≫ W.ι = f :=
  ⟨IsOpenImmersion.lift W.ι f (by rintro _ ⟨z, rfl⟩; rw [Scheme.Opens.range_ι]; exact h z),
    IsOpenImmersion.lift_fac _ _ _⟩

theorem ι_mem (W : X.Opens) (x : W.toScheme) : W.ι x ∈ W := by
  have h : W.ι x ∈ Set.range W.ι := ⟨x, rfl⟩
  rw [W.range_ι] at h; exact h

theorem surj_restrict (A : Over T) [GrpObj A] (hA : IsAbelianScheme A) (U : T.Opens) :
    Function.Surjective (A.hom ∣_ U).appTop.hom := by
  have h1 : Function.Surjective (pullback.snd A.hom U.ι).appTop.hom :=
    (GlobalTheory.SemiRigid.globalFns _ _ (Out.TLinPf.isAb_pullback U.ι A hA)).2
  have e : A.hom ∣_ U = (pullbackRestrictIsoRestrict A.hom U).inv ≫ pullback.snd A.hom U.ι := rfl
  rw [e, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso
    ((pullbackRestrictIsoRestrict A.hom U).inv.app ⊤)).2.comp h1

theorem normalize (p : X ⟶ T) (e : T ⟶ X) {N : LB X} (hN : N.IsLB)
    (t : LB.Gen (N.pull e)) (ht : t.IsGen) (W : X.Opens) (hW : ∀ x ∈ W, e (p x) ∈ W)
    (s : LB.Gen (N.pull W.ι)) (hs : s.IsGen) :
    ∃ n : LB.Gen (LB.LinComb N (fun _ : PUnit => W.ι ≫ 𝟙 X) (fun _ => 1)), n.IsGen ∧
      ∀ (Z : Scheme.{0}) (m : Z ⟶ W.toScheme) (z : Z) (J), Good N z J →
        m ≫ W.ι ≫ p ≫ e = m ≫ W.ι → val n m z J = val t (m ≫ W.ι ≫ p) z J := by
  obtain ⟨q, hq⟩ := exists_lift W (W.ι ≫ p ≫ e) (fun z => by
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]; exact hW _ (ι_mem W z))
  let n₀ := LB.mulGen N _ _ _ _ (LB.mulGen N _ _ _ _ s (LB.invGen N _ _ (LB.pullGen N _ _ s q)))
    (LB.pullGen N (fun _ : PUnit => e) (fun _ => 1) t (W.ι ≫ p))
  have hn₀ : n₀.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hs
    (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hs _))) (DVR.pullGen_isGen _ _ _ _ ht _)
  obtain ⟨n, hn, hv⟩ := exists_gen hN (φ' := fun _ : PUnit => W.ι ≫ 𝟙 X) (ε' := fun _ => 1)
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, zpow_one,
        zpow_neg, hq, Category.assoc, Category.comp_id]
      exact _root_.inv_mul_cancel_right _ _) n₀ hn₀
  refine ⟨n, hn, fun Z m z J hJ hm => ?_⟩
  have hmq : m ≫ q = m := by
    rw [← cancel_mono W.ι, Category.assoc, hq, hm]
  rw [hv Z m z J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, hmq, mul_inv_cancel, _root_.one_mul]

theorem exists_gen_of_local (p : X ⟶ T) (e : T ⟶ X) (he : e ≫ p = 𝟙 T)
    (hsurj : ∀ U : T.Opens, Function.Surjective (p ∣_ U).appTop.hom) {N : LB X} (hN : N.IsLB)
    (t : LB.Gen (N.pull e)) (ht : t.IsGen)
    (hloc : ∀ τ : T, ∃ V : T.Opens, τ ∈ V ∧ ∃ s : LB.Gen (N.pull (p ⁻¹ᵁ V).ι), s.IsGen) :
    ∃ s : LB.Gen N, s.IsGen := by
  choose V hV s hs using hloc
  have hep : ∀ x : T, p (e x) = x := fun x => by rw [← Scheme.Hom.comp_apply, he]; rfl
  have hW : ∀ τ, ∀ x ∈ p ⁻¹ᵁ V τ, e (p x) ∈ p ⁻¹ᵁ V τ := fun τ x hx => by
    show p (e (p x)) ∈ V τ
    rw [hep]; exact hx
  choose n hn hnv using fun τ => normalize p e hN t ht (p ⁻¹ᵁ V τ) (hW τ) (s τ) (hs τ)
  have agree : ∀ (τ τ' : T) (Z : Scheme.{0}) (r : Z ⟶ (p ⁻¹ᵁ V τ).toScheme)
      (r' : Z ⟶ (p ⁻¹ᵁ V τ').toScheme) (z : Z) (J), Good N z J →
      r ≫ (p ⁻¹ᵁ V τ).ι = r' ≫ (p ⁻¹ᵁ V τ').ι → val (n τ) r z J = val (n τ') r' z J := by
    intro τ τ' Z r r' z J hJ hrr
    set U := V τ ⊓ V τ' with hUdef
    have l₁ : p ⁻¹ᵁ U ≤ p ⁻¹ᵁ V τ := fun x hx => hx.1
    have l₂ : p ⁻¹ᵁ U ≤ p ⁻¹ᵁ V τ' := fun x hx => hx.2
    let i₁ := X.homOfLE l₁
    let i₂ := X.homOfLE l₂
    have hi₁ : i₁ ≫ (p ⁻¹ᵁ V τ).ι = (p ⁻¹ᵁ U).ι := X.homOfLE_ι _
    have hi₂ : i₂ ≫ (p ⁻¹ᵁ V τ').ι = (p ⁻¹ᵁ U).ι := X.homOfLE_ι _
    obtain ⟨e₂, he₂⟩ := exists_lift (p ⁻¹ᵁ U) (U.ι ≫ e) (fun y => by
      show p ((U.ι ≫ e) y) ∈ U
      rw [Scheme.Hom.comp_apply, hep]; exact ι_mem U y)
    have hs₂ : e₂ ≫ (p ∣_ U) = 𝟙 _ := by
      rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, he₂, Category.assoc, he,
        Category.comp_id, Category.id_comp]
    obtain ⟨ρ, hρ⟩ := exists_lift (p ⁻¹ᵁ U) (r ≫ (p ⁻¹ᵁ V τ).ι) (fun y => by
      refine ⟨ι_mem (p ⁻¹ᵁ V τ) (r y), ?_⟩
      have h := ι_mem (p ⁻¹ᵁ V τ') (r' y)
      rw [← Scheme.Hom.comp_apply, ← hrr, Scheme.Hom.comp_apply] at h
      exact h)
    have hρ₁ : ρ ≫ i₁ = r := by rw [← cancel_mono (p ⁻¹ᵁ V τ).ι, Category.assoc, hi₁, hρ]
    have hρ₂ : ρ ≫ i₂ = r' := by rw [← cancel_mono (p ⁻¹ᵁ V τ').ι, Category.assoc, hi₂, hρ, hrr]
    have hφ : i₂ ≫ (p ⁻¹ᵁ V τ').ι ≫ 𝟙 X = i₁ ≫ (p ⁻¹ᵁ V τ).ι ≫ 𝟙 X := by
      rw [← Category.assoc, hi₂, ← Category.assoc, hi₁]
    obtain ⟨b', hb', hbv⟩ := exists_gen hN (φ' := fun _ : PUnit => i₁ ≫ (p ⁻¹ᵁ V τ).ι ≫ 𝟙 X)
      (ε' := fun _ => 1) (fun U _ h => by simp only [hφ]) (LB.pullGen N _ _ (n τ') i₂)
      (DVR.pullGen_isGen _ _ _ _ (hn τ') _)
    have sec : ∀ (σ : T) (l : p ⁻¹ᵁ U ≤ p ⁻¹ᵁ V σ), X.homOfLE l ≫ (p ⁻¹ᵁ V σ).ι = (p ⁻¹ᵁ U).ι →
        (e₂ ≫ X.homOfLE l) ≫ (p ⁻¹ᵁ V σ).ι ≫ p ≫ e = (e₂ ≫ X.homOfLE l) ≫ (p ⁻¹ᵁ V σ).ι := by
      intro σ l hl
      simp only [Category.assoc, reassoc_of% hl, reassoc_of% he₂, reassoc_of% he, hl, he₂]
    have key := gen_unique hN (p ∣_ U) e₂ hs₂ (hsurj U) (u := LB.pullGen N _ _ (n τ) i₁) (u' := b')
      (DVR.pullGen_isGen _ _ _ _ (hn τ) _) hb' (fun y J hJ => by
        rw [hbv _ _ y J hJ, val_pull hJ, val_pull hJ, hnv τ _ (e₂ ≫ i₁) y J hJ (sec τ l₁ hi₁),
          hnv τ' _ (e₂ ≫ i₂) y J hJ (sec τ' l₂ hi₂)]
        simp only [Category.assoc, reassoc_of% hi₁, reassoc_of% hi₂]) Z ρ z J hJ
    rw [val_pull hJ, hρ₁, hbv _ _ z J hJ, val_pull hJ, hρ₂] at key
    exact key
  obtain ⟨u, hu, -⟩ := glue_gen hN (fun _ : PUnit => 𝟙 X) (fun _ => 1) (fun τ => p ⁻¹ᵁ V τ)
    (fun x => ⟨p x, hV (p x)⟩) n hn agree
  have hle : ∀ i, N.U i ≤ LB.wchart N (fun _ : PUnit => 𝟙 X) (fun _ => i) := fun i x hx =>
    Set.mem_iInter.2 fun _ => hx
  refine ⟨⟨fun i => res (hle i) (u.s (fun _ => i))⟩, fun i j => unit_ext fun x hx => ?_⟩
  have h1 : (𝟙 X : X ⟶ X) x ∈ LB.wchart N (fun _ : PUnit => 𝟙 X) (fun _ => i) := hle i hx.1
  have h2 : (𝟙 X : X ⟶ X) x ∈ LB.wchart N (fun _ : PUnit => 𝟙 X) (fun _ => j) := hle j hx.2
  have key := gen_trans hu (𝟙 X) x h1 h2
  simp only [trF, Fintype.prod_unique, zpow_one, Category.comp_id] at key
  dsimp only
  rw [map_mul, gm_res (𝟙 X) x _ hx, gm_res (𝟙 X) x _ hx]
  exact (gm_res (𝟙 X) x (hle i) hx.1 _).trans (key.trans (congrArg _ (gm_res (𝟙 X) x (hle j) hx.2 _).symm))

theorem exists_gen_of_locally_trivial : ∀ (T : Scheme.{0}) (A' : Over T) [GrpObj A'] (N : LB A'.left), IsAbelianScheme A' → N.IsLB → Out.Rigidified A' N → (∀ τ : T, ∃ V : T.Opens, τ ∈ V ∧ ∃ s : (N.pull (A'.hom ⁻¹ᵁ V).ι).Gen, s.IsGen) → ∃ s : N.Gen, s.IsGen := by
  intro T A' _ N hA hN ⟨t, ht⟩ hloc
  exact exists_gen_of_local A'.hom (eSec A') (Over.w η[A']) (surj_restrict A' hA) hN t ht hloc

end GlobalTheory.RigTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupSchemeBaseChangeHomOfGrpPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_groupScheme_baseChange_hom_of_grpPullback : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G A : Over S) [GrpObj G] [GrpObj A] (G' A' : Over S') [GrpObj G'] [GrpObj A'] (φG : G'.left ⟶ G.left) (φA : A'.left ⟶ A.left) (p : G ⟶ A), IsGrpPullback G' G f φG → IsGrpPullback A' A f φA → IsMonHom p → ∃ p' : G' ⟶ A', IsMonHom p' ∧ p'.left ≫ φA = φG ≫ p.left := by
  first | (exact @GlobalTheory.GrpBC.exists_baseChange_hom) | (exact GlobalTheory.GrpBC.exists_baseChange_hom) | (intros; apply GlobalTheory.GrpBC.exists_baseChange_hom  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpPullbackPowObjProjectionsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_grpPullback_powObj_projections : ∀ (S T : Scheme.{0}) (t : T ⟶ S) (A : Over S) [GrpObj A] (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left) (B' : Over T) [GrpObj B'] (r : ℕ) (φB : B'.left ⟶ (Out.powObj A r).left), IsGrpPullback A' A t φ' → IsGrpPullback B' (Out.powObj A r) t φB → ∃ pr' : Fin r → (B' ⟶ A'), (∀ u, IsMonHom (pr' u)) ∧ (∀ u, (pr' u).left ≫ φ' = φB ≫ (Out.powPr A u).left) ∧ ∀ (X : Over T) (y : Fin r → (X ⟶ A')), ∃! x : X ⟶ B', ∀ u, x ≫ pr' u = y u := by
  first | (exact @GlobalTheory.ActFin.exists_powPr_of_isGrpPullback) | (exact GlobalTheory.ActFin.exists_powPr_of_isGrpPullback) | (intros; apply GlobalTheory.ActFin.exists_powPr_of_isGrpPullback  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundlePowerIsoReindexedChartsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundlePower_iso_reindexed_charts : ∀ {X Y Z₁ Z₂ : Scheme.{0}} (L : LB Z₁) (M : LB Z₂) (f : X ⟶ Z₁) (h : X ⟶ Y) (m : Y ⟶ Z₂) (k : ℕ) (w : LB.Gen (LB.div ((M.pull m).pull h) (L.pull f))), w.IsGen → ∃ α : LB.Gen (LB.div (powPull M (h ≫ m) (k : ℤ)) (powPull L f (k : ℤ))), α.IsGen := by
  first | (exact @GlobalTheory.PowIsoRe.exists_powIso) | (exact GlobalTheory.PowIsoRe.exists_powIso) | (intros; apply GlobalTheory.PowIsoRe.exists_powIso  <;> assumption)
end

