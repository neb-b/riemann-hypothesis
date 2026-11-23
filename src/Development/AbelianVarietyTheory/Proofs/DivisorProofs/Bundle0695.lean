module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0595
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0681
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0598
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0648
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0677
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0680
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0667
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0669
public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0670
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0671
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0631
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0683
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0361

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogarithmIntegersAdaptedBasisNoLieComponents
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.RedO

theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (k : ℕ) (e0 : Fin d ⊕ Fin k → MvPowerSeries (Fin d) C) (lb : Module.Basis (Fin k) O G.dual.Lie), IsBasis c.μ e0 → IsAdapted (RingHom.id O) c.μ e0 → (∀ j, c.IsLie (e0 (Sum.inr j)) (lb j)) → ∀ h : MvPowerSeries (Fin d) C, QL c.μ ⊤ h → cob1 (up C c.μ) h = 0 → ∀ a : Fin d ⊕ Fin k → O, In (⊤ : Ideal O) (h - comb a e0) → (∀ j, a (Sum.inr j) = 0) ∧ ∀ i, lin h i = algebraMap O C (a (Sum.inl i)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c k e0 lb hB hA hL h hh hcob a ha
  have hF : IsFrame p C (RingHom.id O) := GlobalTheory.FrameIntegers.isFrame_integers p C v O hv
  have hμ : ∀ i, constantCoeff (up C c.μ i) = 0 := fun i => by
    simp [up, constantCoeff_map, c.isLaw.const i]

  have lie0 : ∀ f : MvPowerSeries (Fin d) C, cob1 (up C c.μ) f = 0 → c.IsLie f 0 := by
    intro f hf
    have hd : ∀ n : ℕ, defect c.μ (p ^ n) f = defect c.μ (p ^ n) (0 : MvPowerSeries (Fin d) C) := fun n => by
      rw [defect, GlobalTheory.LieZero.subst_nmul_of_cob1_eq_zero c.μ c.isLaw.const f hf, sub_self, defect,
        ← coe_substAlgHom (hasSubst_up_nmul c.isLaw.const _), map_zero, smul_zero, sub_zero]
    have e : c.IsLie f 0 ↔ c.IsLie (0 : MvPowerSeries (Fin d) C) 0 := by
      unfold Chart.IsLie
      simp only [hd]
    exact e.2 (c.isLie_zero hv.hom_inj)

  have hcobE : ∀ i, cob1 (up C c.μ) (e0 (Sum.inl i)) = 0 := fun i => by
    ext α
    obtain ⟨b, hb, hb'⟩ := (hA i).1 α
    rw [RingHom.mem_ker, RingHom.id_apply] at hb
    rw [hb', hb, map_zero, map_zero]
  let L : Fin d ⊕ Fin k → G.dual.Lie := Sum.elim (fun _ => 0) lb
  have hLe : ∀ x, c.IsLie (e0 x) (L x) := by
    rintro (i | j)
    · exact lie0 _ (hcobE i)
    · exact hL j

  let e' : Unit ⊕ (Fin d ⊕ Fin k) → MvPowerSeries (Fin d) C := Sum.elim (fun _ => h) e0
  let b' : Unit ⊕ (Fin d ⊕ Fin k) → O := Sum.elim (fun _ => 1) (-a)
  have hcomb : comb b' e' = h - comb a e0 := by
    simp only [comb, Fintype.sum_sum_type, e', b', Sum.elim_inl, Sum.elim_inr, Pi.neg_apply,
      map_neg, neg_smul, Finset.sum_neg_distrib, map_one, one_smul, Finset.univ_unique,
      Finset.sum_singleton]
    abel
  have hQL : ∀ x, QL c.μ ⊤ (e' x) := by
    rintro (_ | x)
    · exact hh
    · exact hB.1 x
  have hLie' : ∀ x, c.IsLie (e' x) (Sum.elim (fun _ => (0 : G.dual.Lie)) L x) := by
    rintro (_ | x)
    · exact lie0 h hcob
    · exact hLe x
  have hs := GlobalTheory.QLog.Chart.isLie_comb p O C hF G d c _ e' _ b' hQL hLie'
  rw [hcomb] at hs
  have hc0 : constantCoeff (h - comb a e0) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, hh.1, comb, map_sum]
    simp [← coeff_zero_eq_constantCoeff_apply, coeff_smul,
      coeff_zero_eq_constantCoeff_apply, (hB.1 _).1]
  have hl0 := (GlobalTheory.LieZero.lie_eq_zero p O C hF G d c _ _ hs).1 ha hc0
  simp only [Fintype.sum_sum_type, b', Sum.elim_inl, Sum.elim_inr, smul_zero, Finset.sum_const_zero,
    zero_add, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, neg_eq_zero, L] at hl0
  have hinr : ∀ j, a (Sum.inr j) = 0 :=
    Fintype.linearIndependent_iff.1 lb.linearIndependent (fun j => a (Sum.inr j)) hl0
  refine ⟨hinr, fun i => ?_⟩

  have hcobc : cob1 (up C c.μ) (h - comb a e0) = 0 := by
    have hadd : ∀ f g, cob1 (up C c.μ) (f + g) = cob1 (up C c.μ) f + cob1 (up C c.μ) g :=
      formalCoboundary_add hμ
    let Φ : MvPowerSeries (Fin d) C →+ MvPowerSeries (Fin d ⊕ Fin d) C :=
      AddMonoidHom.mk' (cob1 (up C c.μ)) hadd
    have e1 : cob1 (up C c.μ) (comb a e0) = 0 := by
      change Φ (comb a e0) = 0
      set_option synthInstance.maxHeartbeats 100000 in
        rw [comb, map_sum]
      refine Finset.sum_eq_zero fun x _ => ?_
      change cob1 (up C c.μ) (algebraMap O C (a x) • e0 x) = 0
      rw [formalCoboundary_smul hμ]
      rcases x with i' | j
      · rw [hcobE i', smul_zero]
      · rw [hinr j, map_zero, zero_smul]
    rw [sub_eq_add_neg, ← neg_one_smul C (comb a e0), hadd, formalCoboundary_smul hμ, e1, smul_zero, hcob,
      add_zero]
  obtain ⟨s, hs'⟩ := In.top_iff.1 ha
  have hs0 : s = 0 :=
    GlobalTheory.QLog.IntAdd.eq_zero_of_cob1_eq_zero p C v O hv G d c C hF s (by rw [hs']; exact hcobc)
  rw [hs0, map_zero] at hs'
  have hEq : h = comb a e0 := sub_eq_zero.1 hs'.symm
  rw [hEq]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [lin, comb, Fintype.sum_sum_type, map_add (f := _), map_sum, coeff_smul, smul_eq_mul]
  have h2 : ∀ j, algebraMap O C (a (Sum.inr j)) * coeff (Finsupp.single i 1) (e0 (Sum.inr j)) = 0 :=
    fun j => by rw [hinr j, map_zero, zero_mul]
  have h1 : ∀ i', coeff (Finsupp.single i 1) (e0 (Sum.inl i')) = (Pi.single i' (1 : C) : Fin d → C) i :=
    fun i' => congrFun (hA i').2 i
  simp only [h2, h1, Finset.sum_const_zero, add_zero, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end GlobalTheory.QLog.RedO
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupIdempotentSplitFieldStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pDivGroup_idempotent_split_field : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (G : PDivGroup p k) (u v : G ⟶ G), u + v = 𝟙 G → u ≫ v = 0 → v ≫ u = 0 → ∃ (K : PDivGroup p k) (i : K ⟶ G) (q : G ⟶ K), i ≫ q = 𝟙 K ∧ q ≫ i = v ∧ ∀ n : ℕ, Function.Surjective (i.app n) ∧ RingHom.ker (i.app n) = kerIdeal (u.app n) := by
  first | exact @GlobalTheory.PDivGroup.idempotent_split | exact GlobalTheory.PDivGroup.idempotent_split | (intros; apply GlobalTheory.PDivGroup.idempotent_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodConstExt
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem period_const_ext : ∀ {I₀ : Type} [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam I₀ g Λ} (K₀ : Charts F₀) {R : Type} [CommRing R] (et : Hol F₀.V →+* R) (M : Ideal R) {B₀ D : Type} [CommRing B₀] [CommRing D] {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp B₀} {σ₀ : B₀ →+* Hol F₀.V} (r₀ : GlobalTheory.AnPer.Real K₀ s₀ σ₀) {J : Ideal D} (dl : DividedPowers J) {s' : X₀ ⟶ Sp D} {π : D →+* B₀} {io : D →+* R} (H : IsOver et M s₀ σ₀ J s' π io) (j : B₀ →+* D) (φ₀ : X₀ ⟶ X₀) (n : IsMor (dp0 B₀) s₀ dl s' j φ₀), φ₀ = 𝟙 X₀ → (∀ b, et (σ₀ b) = io (j b)) → ∀ (c : FirstDeRham s₀) (per : Λ →+ Hol F₀.V), r₀.coef.pull1 c = K₀.perCl per → (r₀.coefD dl H).pull1 (n.pull1 c) = K₀.perClD et M (et.toAddMonoidHom.comp per) := by
  intro I₀ _ g Λ _ F₀ K₀ R _ et M B₀ D _ _ X₀ s₀ σ₀ r₀ J dl s' π io H j φ₀ n hφ hj c per hc
  refine _root_.GlobalTheory.AnPer.period_restrict_family K₀ K₀ et M et id (fun h ↦ h) (fun _ ↦ RingHom.id _) (fun S ↦ S.T.ρ)
    (fun S f ↦ (S.T.ρ_cst f).trans (S.compat f)) (fun S h ↦ ?_) (fun S S' f ↦ Charts.Hom.close f.1)
    r₀ r₀ dl H j φ₀ n hj (fun k ↦ ?_) c per hc
  · exact (sub_self (S.T.ρ h)).symm ▸ S.T.J.zero_mem
  · subst hφ
    have e : spMap (RingHom.id (Hol (K₀.W k))) = 𝟙 _ := Spec.map_id _
    exact (congrArg (· ≫ r₀.x k) e).trans ((Category.id_comp _).trans (Category.comp_id _).symm)

end GlobalTheory.AnPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodPullbackEqOfChartMapClass
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.CatCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.ChartMap

variable {I₁ : Type} [Fintype I₁] {g₁ : ℕ} {Λ₁ : Type} [AddCommGroup Λ₁] {F₁ : Fam I₁ g₁ Λ₁}
  {I₂ : Type} [Fintype I₂] {g₂ : ℕ} {Λ₂ : Type} [AddCommGroup Λ₂] {F₂ : Fam I₂ g₂ Λ₂}

def Φc (b : (I₁ → ℂ) → I₂ → ℂ) (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) {K₁ : Charts F₁} {K₂ : Charts F₂}
    (κ : K₁.K → K₂.K) (hΦ : ∀ k, AnalyticOnNhd ℂ (fun p : Tot I₁ g₁ ↦ ((b p.1, M p.2) : Tot I₂ g₂)) (K₁.W k))
    (hW : ∀ k, ∀ p ∈ K₁.W k, ((b p.1, M p.2) : Tot I₂ g₂) ∈ K₂.W (κ k)) (k : K₁.K) :
    Hol (K₂.W (κ k)) →+* Hol (K₁.W k) :=
  (Hol.comap _ (hΦ k) (hW k)).toRingHom

theorem Φc_cst (b : (I₁ → ℂ) → I₂ → ℂ) (hb : AnalyticOnNhd ℂ b F₁.V) (hbV : ∀ z ∈ F₁.V, b z ∈ F₂.V)
    (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) {K₁ : Charts F₁} {K₂ : Charts F₂}
    (κ : K₁.K → K₂.K) (hΦ : ∀ k, AnalyticOnNhd ℂ (fun p : Tot I₁ g₁ ↦ ((b p.1, M p.2) : Tot I₂ g₂)) (K₁.W k))
    (hW : ∀ k, ∀ p ∈ K₁.W k, ((b p.1, M p.2) : Tot I₂ g₂) ∈ K₂.W (κ k)) (k : K₁.K) (f : Hol F₂.V) :
    Φc b M κ hΦ hW k (K₂.cst (κ k) f) = K₁.cst k (Hol.comap b hb hbV f) :=
  Hol.ext_fn fun p hp ↦ by
    change (Hol.comap _ (hΦ k) (hW k) (K₂.cst (κ k) f)).fn p = _
    rw [Hol.fn_comap _ _ _ _ hp, Charts.fn_cst _ _ _ (hW k p hp), Charts.fn_cst _ _ _ hp,
      Hol.fn_comap _ _ _ _ (K₁.base k p hp)]

theorem Φc_sh (b : (I₁ → ℂ) → I₂ → ℂ) (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) (A : Λ₁ →+ Λ₂)
    (hτ : ∀ l, ∀ z ∈ F₁.V, F₂.τ (A l) (b z) = M (F₁.τ l z)) {K₁ : Charts F₁} {K₂ : Charts F₂}
    (κ : K₁.K → K₂.K) (hΦ : ∀ k, AnalyticOnNhd ℂ (fun p : Tot I₁ g₁ ↦ ((b p.1, M p.2) : Tot I₂ g₂)) (K₁.W k))
    (hW : ∀ k, ∀ p ∈ K₁.W k, ((b p.1, M p.2) : Tot I₂ g₂) ∈ K₂.W (κ k)) {l : Λ₁} {k k' : K₁.K}
    (h : K₁.le l k' k) (h₂ : K₂.le (A l) (κ k') (κ k)) (f : Hol (K₂.W (κ k))) :
    Φc b M κ hΦ hW k' (Charts.sh h₂ f) = Charts.sh h (Φc b M κ hΦ hW k f) :=
  Hol.ext_fn fun p hp ↦ by
    change (Hol.comap _ (hΦ k') (hW k') (Charts.sh h₂ f)).fn p =
      (Charts.sh h (Hol.comap _ (hΦ k) (hW k) f)).fn p
    rw [Hol.fn_comap _ _ _ _ hp, Charts.fn_sh _ _ (hW k' p hp), Charts.fn_sh _ _ hp,
      Hol.fn_comap _ _ _ _ (K₁.maps h p hp)]
    congr 1
    simp [Fam.shift, map_add (f := _), hτ l p.1 (K₁.base k' p hp)]

theorem dw_Φc (b : (I₁ → ℂ) → I₂ → ℂ) (hb : AnalyticOnNhd ℂ b F₁.V)
    (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) {K₁ : Charts F₁} {K₂ : Charts F₂}
    (κ : K₁.K → K₂.K) (hΦ : ∀ k, AnalyticOnNhd ℂ (fun p : Tot I₁ g₁ ↦ ((b p.1, M p.2) : Tot I₂ g₂)) (K₁.W k))
    (hW : ∀ k, ∀ p ∈ K₁.W k, ((b p.1, M p.2) : Tot I₂ g₂) ∈ K₂.W (κ k)) (k : K₁.K) (a : Fin g₁)
    (f : Hol (K₂.W (κ k))) :
    dw a (Φc b M κ hΦ hW k f) = ∑ c, M (Pi.single a 1) c • Φc b M κ hΦ hW k (dw c f) :=
  dw_comap_linear b M (fun p hp ↦ hb _ (K₁.base k p hp)) (hΦ k) (hW k) a f

end GlobalTheory.AnPer.ChartMap

namespace GlobalTheory.AnPer.ChartMap

variable {I₁ : Type} [Fintype I₁] {g₁ : ℕ} {Λ₁ : Type} [AddCommGroup Λ₁] {F₁ : Fam I₁ g₁ Λ₁}
  {I₂ : Type} [Fintype I₂] {g₂ : ℕ} {Λ₂ : Type} [AddCommGroup Λ₂] {F₂ : Fam I₂ g₂ Λ₂}

@[reducible] def objMap (b : (I₁ → ℂ) → I₂ → ℂ) (hb : AnalyticOnNhd ℂ b F₁.V) (hbV : ∀ z ∈ F₁.V, b z ∈ F₂.V)
    (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) {K₁ : Charts F₁} {K₂ : Charts F₂}
    (κ : K₁.K → K₂.K) (hΦ : ∀ k, AnalyticOnNhd ℂ (fun p : Tot I₁ g₁ ↦ ((b p.1, M p.2) : Tot I₂ g₂)) (K₁.W k))
    (hW : ∀ k, ∀ p ∈ K₁.W k, ((b p.1, M p.2) : Tot I₂ g₂) ∈ K₂.W (κ k)) (T : K₁.Obj) : K₂.Obj where
  k := κ T.k
  C := T.C
  ring := T.ring
  alg := ((algebraMap (Hol F₁.V) T.C).comp (Hol.comap b hb hbV).toRingHom).toAlgebra
  J := T.J
  nil := T.nil
  ρ := T.ρ.comp (Φc b M κ hΦ hW T.k)
  ρ_cst f := by
    change T.ρ (Φc b M κ hΦ hW T.k (K₂.cst (κ T.k) f)) = algebraMap (Hol F₁.V) T.C (Hol.comap b hb hbV f)
    rw [Φc_cst b hb hbV M κ hΦ hW, T.ρ_cst]

def homMap (b : (I₁ → ℂ) → I₂ → ℂ) (hb : AnalyticOnNhd ℂ b F₁.V) (hbV : ∀ z ∈ F₁.V, b z ∈ F₂.V)
    (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) (A : Λ₁ →+ Λ₂)
    (hτ : ∀ l, ∀ z ∈ F₁.V, F₂.τ (A l) (b z) = M (F₁.τ l z)) {K₁ : Charts F₁} {K₂ : Charts F₂}
    (κ : K₁.K → K₂.K) (hΦ : ∀ k, AnalyticOnNhd ℂ (fun p : Tot I₁ g₁ ↦ ((b p.1, M p.2) : Tot I₂ g₂)) (K₁.W k))
    (hW : ∀ k, ∀ p ∈ K₁.W k, ((b p.1, M p.2) : Tot I₂ g₂) ∈ K₂.W (κ k))
    (hle : ∀ l k' k, K₁.le l k' k → K₂.le (A l) (κ k') (κ k)) {T T' : K₁.Obj} (f : T ⟶ T') :
    Charts.Hom (objMap b hb hbV M κ hΦ hW T) (objMap b hb hbV M κ hΦ hW T') where
  φ := { (f.φ : T.C →+* T'.C) with commutes' := fun r ↦ f.φ.commutes (Hol.comap b hb hbV r) }
  deg := A f.deg
  le := hle _ _ _ (Charts.Hom.le f)
  mem := f.mem
  close := by
    have h := Close.comap_linear T'.J _ _ (Φc b M κ hΦ hW T.k) (fun c a ↦ M (Pi.single a 1) c)
      (dw_Φc b hb M κ hΦ hW T.k) f.close
    convert h using 1
    · exact RingHom.ext fun x ↦ congrArg T'.ρ (Φc_sh b M A hτ κ hΦ hW (Charts.Hom.le f) (hle _ _ _ (Charts.Hom.le f)) x)
    · rfl

def functor (b : (I₁ → ℂ) → I₂ → ℂ) (hb : AnalyticOnNhd ℂ b F₁.V) (hbV : ∀ z ∈ F₁.V, b z ∈ F₂.V)
    (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) (A : Λ₁ →+ Λ₂)
    (hτ : ∀ l, ∀ z ∈ F₁.V, F₂.τ (A l) (b z) = M (F₁.τ l z)) (K₁ : Charts F₁) (K₂ : Charts F₂)
    (κ : K₁.K → K₂.K) (hΦ : ∀ k, AnalyticOnNhd ℂ (fun p : Tot I₁ g₁ ↦ ((b p.1, M p.2) : Tot I₂ g₂)) (K₁.W k))
    (hW : ∀ k, ∀ p ∈ K₁.W k, ((b p.1, M p.2) : Tot I₂ g₂) ∈ K₂.W (κ k))
    (hle : ∀ l k' k, K₁.le l k' k → K₂.le (A l) (κ k') (κ k)) : K₁.Obj ⥤ K₂.Obj where
  obj := objMap b hb hbV M κ hΦ hW
  map f := homMap b hb hbV M A hτ κ hΦ hW hle f
  map_id _ := Charts.hom_ext (fun _ ↦ rfl) (map_zero A)
  map_comp _ _ := Charts.hom_ext (fun _ ↦ rfl) (map_add A _ _)

def coef (b : (I₁ → ℂ) → I₂ → ℂ) (hb : AnalyticOnNhd ℂ b F₁.V) (hbV : ∀ z ∈ F₁.V, b z ∈ F₂.V)
    (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) (A : Λ₁ →+ Λ₂)
    (hτ : ∀ l, ∀ z ∈ F₁.V, F₂.τ (A l) (b z) = M (F₁.τ l z)) (K₁ : Charts F₁) (K₂ : Charts F₂)
    (κ : K₁.K → K₂.K) (hΦ : ∀ k, AnalyticOnNhd ℂ (fun p : Tot I₁ g₁ ↦ ((b p.1, M p.2) : Tot I₂ g₂)) (K₁.W k))
    (hW : ∀ k, ∀ p ∈ K₁.W k, ((b p.1, M p.2) : Tot I₂ g₂) ∈ K₂.W (κ k))
    (hle : ∀ l k' k, K₁.le l k' k → K₂.le (A l) (κ k') (κ k)) :
    CoefMap (Hol.comap b hb hbV).toRingHom K₂.Oc K₁.Oc where
  G := functor b hb hbV M A hτ K₁ K₂ κ hΦ hW hle
  α T := RingHom.id T.C
  naturality _ _ := rfl
  smul T r c := (Algebra.smul_def (A := T.C) (Hol.comap b hb hbV r) c).symm

end GlobalTheory.AnPer.ChartMap

namespace GlobalTheory.AnPer

theorem period_pullback_eq_of_chartMap : ∀ {I₁ : Type} [Fintype I₁] {g₁ : ℕ} {Λ₁ : Type} [AddCommGroup Λ₁] {F₁ : Fam I₁ g₁ Λ₁} {B₁ : Type} [CommRing B₁] {X₁ : Scheme.{0}} {s₁ : X₁ ⟶ Sp B₁} {σ₁ : B₁ →+* Hol F₁.V} {I₂ : Type} [Fintype I₂] {g₂ : ℕ} {Λ₂ : Type} [AddCommGroup Λ₂] {F₂ : Fam I₂ g₂ Λ₂} {B₂ : Type} [CommRing B₂] {X₂ : Scheme.{0}} {s₂ : X₂ ⟶ Sp B₂} {σ₂ : B₂ →+* Hol F₂.V} (b : (I₁ → ℂ) → I₂ → ℂ) (hb : AnalyticOnNhd ℂ b F₁.V) (hbV : ∀ z ∈ F₁.V, b z ∈ F₂.V) (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) (A : Λ₁ →+ Λ₂), (∀ l, ∀ z ∈ F₁.V, F₂.τ (A l) (b z) = M (F₁.τ l z)) → ∀ (K₁ : Charts F₁) (K₂ : Charts F₂) (κ : K₁.K → K₂.K) (hΦ : ∀ k, AnalyticOnNhd ℂ (fun p : Tot I₁ g₁ ↦ ((b p.1, M p.2) : Tot I₂ g₂)) (K₁.W k)) (hW : ∀ k, ∀ p ∈ K₁.W k, ((b p.1, M p.2) : Tot I₂ g₂) ∈ K₂.W (κ k)), (∀ l k' k, K₁.le l k' k → K₂.le (A l) (κ k') (κ k)) → ∀ (r₁ : Real K₁ s₁ σ₁) (r₂ : Real K₂ s₂ σ₂) (β : B₂ →+* B₁) (φ : X₁ ⟶ X₂) (m : IsMor (dp0 B₂) s₂ (dp0 B₁) s₁ β φ), (∀ x, σ₁ (β x) = Hol.comap b hb hbV (σ₂ x)) → (∀ k, spMap (Hol.comap _ (hΦ k) (hW k)).toRingHom ≫ r₂.x (κ k) = r₁.x k ≫ φ) → ∀ (c : FirstDeRham s₂) (per₂ : Λ₂ →+ Hol F₂.V) (per₁ : Λ₁ →+ Hol F₁.V), (∀ l, per₁ l = Hol.comap b hb hbV (per₂ (A l))) → r₂.coef.pull1 c = K₂.perCl per₂ → r₁.coef.pull1 (m.pull1 c) = K₁.perCl per₁ := by
  intro I₁ _ g₁ Λ₁ _ F₁ B₁ _ X₁ s₁ σ₁ I₂ _ g₂ Λ₂ _ F₂ B₂ _ X₂ s₂ σ₂ b hb hbV M A hτ K₁ K₂ κ hΦ hW hle r₁ r₂ β φ m
    hσ hx c per₂ per₁ hper hc
  let n := ChartMap.coef b hb hbV M A hτ K₁ K₂ κ hΦ hW hle
  let θ : (m.coef.comp r₁.coef).G ⟶ (r₂.coef.comp n).G :=
    { app := fun T ↦
        { φ := { RingHom.id T.C with
            commutes' := fun r ↦ congrArg (algebraMap (Hol F₁.V) T.C) (hσ r) }
          φ₀ := RingHom.id (T.C ⧸ T.J)
          comm := fun _ ↦ rfl
          dp := letI := T.ratAlg
            isDPMorphism_of_rat T.δ (ChartMap.objMap b hb hbV M κ hΦ hW T).δ (RingHom.id T.C) fun _ h ↦ h
          pt := by
            change spMap (RingHom.id (T.C ⧸ T.J)) ≫ (spMap ((Ideal.Quotient.mk T.J).comp T.ρ) ≫ r₁.x T.k) ≫ φ =
              spMap (((Ideal.Quotient.mk T.J).comp T.ρ).comp (Hol.comap _ (hΦ T.k) (hW T.k)).toRingHom) ≫
                r₂.x (κ T.k)
            rw [Cris.spMap_id, Category.id_comp, Category.assoc, ← hx T.k,
              Cris.spMap_comp (Hol.comap _ (hΦ T.k) (hW T.k)).toRingHom, Category.assoc] }
      naturality := fun _ _ _ ↦ Thick.Hom.ext' (AlgHom.ext fun _ ↦ rfl) }
  have e₁ : r₁.coef.pull1 (m.pull1 c) = (m.coef.comp r₁.coef).pull1 c := (m.coef.pullCohomologyOne_comp r₁.coef c).symm
  have e₂ : (m.coef.comp r₁.coef).pull1 c = (r₂.coef.comp n).pull1 c :=
    CoefMap.pullCohomologyOne_eq_of_natTrans _ _ θ (fun _ _ ↦ rfl) c
  have e₃ : n.pullbackOneCocycle (K₂.perZ per₂) = K₁.perZ per₁ := by
    refine Subtype.ext ?_
    funext T T' f
    exact (congrArg (algebraMap (Hol F₁.V) T'.C) (hper f.deg)).symm
  rw [e₁, e₂, r₂.coef.pullCohomologyOne_comp n c, hc, Charts.perCl, CoefMap.pullCohomologyOne_class, e₃, Charts.perCl]

end GlobalTheory.AnPer

namespace GlobalTheory.AnPer.CmpCore

theorem period_pullback_eq_of_chartMap_class_alt : ∀ {I₁ : Type} [Fintype I₁] {g₁ : ℕ} {Λ₁ : Type} [AddCommGroup Λ₁] {F₁ : Fam I₁ g₁ Λ₁} {B₁ : Type} [CommRing B₁] {X₁ : Scheme.{0}} {s₁ : X₁ ⟶ Sp B₁} {σ₁ : B₁ →+* Hol F₁.V} {I₂ : Type} [Fintype I₂] {g₂ : ℕ} {Λ₂ : Type} [AddCommGroup Λ₂] {F₂ : Fam I₂ g₂ Λ₂} {B₂ : Type} [CommRing B₂] {X₂ : Scheme.{0}} {s₂ : X₂ ⟶ Sp B₂} {σ₂ : B₂ →+* Hol F₂.V} (b : (I₁ → ℂ) → I₂ → ℂ) (hb : AnalyticOnNhd ℂ b F₁.V) (hbV : ∀ z ∈ F₁.V, b z ∈ F₂.V) (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) (A : Λ₁ →+ Λ₂), (∀ l, ∀ z ∈ F₁.V, F₂.τ (A l) (b z) = M (F₁.τ l z)) → ∀ (K₁ : Charts F₁) (K₂ : Charts F₂) (κ : K₁.K → K₂.K) (hΦ : ∀ k, AnalyticOnNhd ℂ (fun p : Tot I₁ g₁ ↦ ((b p.1, M p.2) : Tot I₂ g₂)) (K₁.W k)) (hW : ∀ k, ∀ p ∈ K₁.W k, ((b p.1, M p.2) : Tot I₂ g₂) ∈ K₂.W (κ k)), (∀ l k' k, K₁.le l k' k → K₂.le (A l) (κ k') (κ k)) → ∀ (r₁ : Real K₁ s₁ σ₁) (r₂ : Real K₂ s₂ σ₂) (β : B₂ →+* B₁) (φ : X₁ ⟶ X₂) (m : IsMor (dp0 B₂) s₂ (dp0 B₁) s₁ β φ), (∀ x, σ₁ (β x) = Hol.comap b hb hbV (σ₂ x)) → (∀ k, spMap (Hol.comap _ (hΦ k) (hW k)).toRingHom ≫ r₂.x (κ k) = r₁.x k ≫ φ) → ∀ (c : FirstDeRham s₂) (per₂ : Λ₂ →+ Hol F₂.V) (per₁ : Λ₁ →+ Hol F₁.V), (∀ l, per₁ l = Hol.comap b hb hbV (per₂ (A l))) → r₂.coef.pull1 c = K₂.perCl per₂ → r₁.coef.pull1 (m.pull1 c) = K₁.perCl per₁ :=
  @GlobalTheory.AnPer.period_pullback_eq_of_chartMap

end GlobalTheory.AnPer.CmpCore
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientSubDPIdeal
section
open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.DPQuot

theorem quotient_subDPIdeal : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J),
    (∀ 𝔟 : Ideal B, δ.IsSubDPIdeal 𝔟 → ∃ δ' : DividedPowers (J.map (Ideal.Quotient.mk 𝔟)),
      IsDPMorphism δ δ' (Ideal.Quotient.mk 𝔟) ∧
      ∀ (C : Type) [CommRing C] (J'' : Ideal C) (δ'' : DividedPowers J'') (g : B ⧸ 𝔟 →+* C),
        IsDPMorphism δ δ'' (g.comp (Ideal.Quotient.mk 𝔟)) → IsDPMorphism δ' δ'' g) ∧
    ∀ s : Set B, s ⊆ J →
      δ.IsSubDPIdeal (Ideal.span {y | ∃ n : ℕ, n ≠ 0 ∧ ∃ x ∈ s, y = δ.dpow n x}) := by
  intro B _ J δ
  refine ⟨fun 𝔟 h𝔟 ↦ ?_, fun s hs ↦ ?_⟩
  · have hinf : δ.IsSubDPIdeal (𝔟 ⊓ J) := by
      rw [inf_eq_left.mpr h𝔟.isSubideal]; exact h𝔟
    refine ⟨Quotient.dividedPowers δ hinf, Quotient.isDPMorphism δ hinf, ?_⟩
    intro C _ J'' δ'' g hg
    refine ⟨?_, fun {n} y hy ↦ ?_⟩
    · rw [Ideal.map_map]; exact hg.1
    · obtain ⟨a, ha, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hy
      rw [Quotient.dpow_apply δ hinf ha]
      exact hg.2 a ha
  · have hset : {y | ∃ n : ℕ, n ≠ 0 ∧ ∃ x ∈ s, y = δ.dpow n x} =
        {y : B | ∃ (n : ℕ) (_ : n ≠ 0) (x : B) (_ : x ∈ s), y = δ.dpow n x} := by
      ext y; simp only [Set.mem_setOf_eq, exists_prop]
    rw [hset, ← SubDPIdeal.span_carrier_eq_dpow_span δ hs]
    exact (SubDPIdeal.span δ s).toIsSubDPIdeal

end GlobalTheory.DPQuot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RoughHormanderEstimateCompactManifold
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.rough_hormander_compact : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ C : Cover A, ∃ K t0 : ℝ, 0 ≤ K ∧ ∀ (la : La) (t : ℝ), t0 ≤ t → CurvGe C la t → ∀ F0 : ι → Y → ℂ, A.IsSSec (A.kap + la) F0 → ∃ F : ι → Y → ℂ, A.IsSec (A.kap + la) F ∧ n0 A la (F0 - F) ≤ ENNReal.ofReal K * n1 C la F0 := by
  intro n Y _ _ _ _ _ _ ι La _ A C
  obtain ⟨K4, hK4, h4⟩ := _root_.GlobalTheory.hormander_step n Y ι La A C
  refine ⟨4, 4 * K4 + 1, by norm_num, ?_⟩
  intro la t ht hC F0 hF0
  have tpos : 0 < t := by linarith
  have hq : K4 / t ≤ 1 / 4 := by rw [div_le_iff₀ tpos]; linarith
  have step : ∀ F : {F : ι → Y → ℂ // A.IsSSec (A.kap + la) F},
      ∃ G : {F : ι → Y → ℂ // A.IsSSec (A.kap + la) F},
        n0 A la (F.1 - G.1) ≤ ENNReal.ofReal (1 / 4) * n1 C la F.1 ∧
        n1 C la G.1 ≤ ENNReal.ofReal (1 / 4) * n1 C la F.1 := by
    intro F
    obtain ⟨G, hG, h1, h2⟩ := h4 la t tpos hC F.1 F.2
    have hq' : ENNReal.ofReal (K4 / t) ≤ ENNReal.ofReal (1 / 4) := ENNReal.ofReal_le_ofReal hq
    exact ⟨⟨G, hG⟩, h1.trans (by gcongr), h2.trans (by gcongr)⟩
  choose g hg using step
  let S : ℕ → {F : ι → Y → ℂ // A.IsSSec (A.kap + la) F} := fun m => g^[m] ⟨F0, hF0⟩
  have hS : ∀ m, S (m + 1) = g (S m) := fun m => Function.iterate_succ_apply' g m _
  have hN : n1 C la F0 < ⊤ := _root_.GlobalTheory.n1_lt_infty_of_isSSec n Y ι La A C la F0 hF0
  have hq1 : ENNReal.ofReal (1 / 4) ≤ 1 := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num)
  have h1 : ∀ m, n1 C la (S m).1 ≤ ENNReal.ofReal ((1 / 4) ^ m) * n1 C la F0 := by
    intro m
    induction m with
    | zero => simp [S]
    | succ m ih =>
      rw [hS]
      refine (hg (S m)).2.trans ?_
      calc ENNReal.ofReal (1 / 4) * n1 C la (S m).1
          ≤ ENNReal.ofReal (1 / 4) * (ENNReal.ofReal ((1 / 4) ^ m) * n1 C la F0) := by
            gcongr
        _ = ENNReal.ofReal ((1 / 4) ^ (m + 1)) * n1 C la F0 := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num), pow_succ']
  have h0 : ∀ m, n0 A la ((S m).1 - (S (m + 1)).1) ≤
      ENNReal.ofReal ((n1 C la F0).toReal / 4 ^ m) := by
    intro m
    rw [hS]
    refine (hg (S m)).1.trans ?_
    refine (mul_le_of_le_one_left (zero_le) hq1).trans ((h1 m).trans (le_of_eq ?_))
    rw [show (n1 C la F0).toReal / 4 ^ m = (1 / 4) ^ m * (n1 C la F0).toReal by
        rw [one_div, inv_pow]; ring,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hN.ne]
  have hT : Tendsto (fun m => n1 C la (S m).1) atTop (𝓝 0) := by
    have hp : Tendsto (fun m : ℕ => ENNReal.ofReal ((1 / 4 : ℝ) ^ m)) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal
        (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num) (by norm_num))
      simpa using this
    have hl := ENNReal.Tendsto.mul_const hp (Or.inr hN.ne)
    rw [zero_mul] at hl
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl
      (fun _ => zero_le) h1
  obtain ⟨G, hG, hfin⟩ := _root_.GlobalTheory.OTY.exists_isSec_of_rapid_cauchy n Y ι La A C la t (n1 C la F0).toReal (fun m => (S m).1)
    tpos hC ENNReal.toReal_nonneg (fun m => (S m).2) h0 hT
  refine ⟨G, hG, hfin.trans (le_of_eq ?_)⟩
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hN.ne]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfNilpotentReduction
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftDim

theorem surjective_spMap_of_nilpotent {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hπ : Function.Surjective π) (hnil : IsNilpotent (RingHom.ker π)) : Surjective (spMap π) := by
  refine ⟨fun P => ?_⟩
  have : P ∈ Set.range (PrimeSpectrum.comap π) := by
    rw [range_comap_of_surjective _ _ hπ]
    intro x hx
    obtain ⟨n, hn⟩ := hnil
    refine (P : PrimeSpectrum R).2.mem_of_pow_mem n ?_
    have h : x ^ n ∈ RingHom.ker π ^ n := Ideal.pow_mem_pow hx n
    rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at h
    rw [h]; exact zero_mem _
  exact this

theorem smoothOfRelativeDimension_of_reduction : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (g : ℕ) (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left), IsPullback i X₀.hom X.hom (spMap π) → Smooth X.hom →
    SmoothOfRelativeDimension g X₀.hom → SmoothOfRelativeDimension g X.hom := by
  intro R R₀ _ _ π hπ hnil g X X₀ i hpb hsm hg
  have hs : Surjective (spMap π) := surjective_spMap_of_nilpotent π hπ hnil
  have hi : Surjective i := MorphismProperty.of_isPullback hpb.flip hs
  have key : ∀ x : X.left, ∃ W : X.left.Opens, x ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ X.hom) := by
    intro x
    obtain ⟨n, W, hx, hW⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim X.hom x
    obtain ⟨x₀, hx₀⟩ := hi.surj x
    have hn : n = g := ReciprocityTheory.ChartRestriction.G.H1.dim_base hpb hW hg x₀ (by rw [hx₀]; exact hx)
    subst hn
    exact ⟨W, hx, hW⟩
  choose W hW hd using key
  haveI : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} g) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) W ?_ hd
  exact top_unique fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩

end GlobalTheory.LiftDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfNoetherianCase
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_of_noetherian_case : ∀ (q : ℕ) [NeZero q], (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ i : ℤ, Function.Surjective (gmPhi q A i)) → ∀ (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ i : ℤ, Function.Surjective (gmPhi q A i) := by
  first | (exact @GlobalTheory.EtC.gmPhi_surjective_of_noetherian) | (exact GlobalTheory.EtC.gmPhi_surjective_of_noetherian) | (intros; apply GlobalTheory.EtC.gmPhi_surjective_of_noetherian  <;> assumption)
end

