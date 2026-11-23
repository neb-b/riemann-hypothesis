module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0068
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmulLatMatOf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0081
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
public import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0054

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConstantCoeffBivariateSeriesSubstPair
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU GlobalTheory.OnePlace Classical

noncomputable section

namespace GlobalTheory.OnePlacePairs

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime]

theorem expS_zero {κ : Type} : product_zeroth_first_parts.expS ℂ_[p] (0 : MvPowerSeries κ ℂ_[p]) = 1 := by
  have h := ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add (k := ℂ_[p]) (a := (0 : MvPowerSeries κ ℂ_[p])) (b := 0)
    (by simp) (by simp)
  rw [add_zero] at h
  have hu : IsUnit (PowerSeries.subst (0 : MvPowerSeries κ ℂ_[p]) (PowerSeries.exp ℂ_[p])) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.constantCoeff_exp (by simp)]
    exact isUnit_one
  unfold product_zeroth_first_parts.expS
  exact hu.mul_left_cancel (h.symm.trans (mul_one _).symm)

theorem expS_add {κ : Type} {f g : MvPowerSeries κ ℂ_[p]} (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
    product_zeroth_first_parts.expS ℂ_[p] (f + g) = product_zeroth_first_parts.expS ℂ_[p] f * product_zeroth_first_parts.expS ℂ_[p] g :=
  ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add hf hg

theorem expS_sum {κ ι : Type} (s : Finset ι) (f : ι → MvPowerSeries κ ℂ_[p]) (hf : ∀ i, constantCoeff (f i) = 0) :
    product_zeroth_first_parts.expS ℂ_[p] (∑ i ∈ s, f i) = ∏ i ∈ s, product_zeroth_first_parts.expS ℂ_[p] (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [expS_zero]
  | insert i s hi ih =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_insert hi, Finset.prod_insert hi, expS_add (hf i) (by rw [map_sum]; exact Finset.sum_eq_zero fun j _ => hf j), ih]

theorem padicExpSeries_doubleSum {κ α β : Type} [Fintype α] [Fintype β] (f : α → β → MvPowerSeries κ ℂ_[p])
    (hf : ∀ a b, constantCoeff (f a b) = 0) :
    product_zeroth_first_parts.expS ℂ_[p] (∑ a, ∑ b, f a b) = ∏ a, ∏ b, product_zeroth_first_parts.expS ℂ_[p] (f a b) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [expS_sum _ _ (fun a => by rw [map_sum]; exact Finset.sum_eq_zero fun b _ => hf a b)]
  exact Finset.prod_congr rfl fun a _ => expS_sum _ _ (hf a)

theorem cc_logF : PowerSeries.constantCoeff (Formalism.MainNotions.GL3Theta.logF p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Formalism.MainNotions.GL3Theta.logF, PowerSeries.coeff_mk]
  simp

theorem cc_plog {κ : Type} {u : MvPowerSeries κ ℂ_[p]} (hu : constantCoeff u = 0) :
    constantCoeff (PowerSeries.subst u (Formalism.MainNotions.GL3Theta.logF p)) = 0 := by
  rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.constantCoeff_psubst hu, cc_logF]

theorem constantCoeff_bivariateSeriesSubstPair {κ : Type} {b0 : MvPowerSeries (Fin 2) ℂ_[p]} (hb0 : constantCoeff b0 = 0)
    {u v : MvPowerSeries κ ℂ_[p]} (hu : constantCoeff u = 0) (hv : constantCoeff v = 0) :
    constantCoeff (GlobalTheory.ThBe0.at2 b0 u v) = 0 := by
  have h : ∀ i : Fin 2, constantCoeff (if i = 0 then u else v) = 0 := fun i => by split_ifs <;> assumption
  exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h) h hb0

theorem subst_powerSeriesEvalTwoGroups {κ κ' : Type} {φ : κ → MvPowerSeries κ' ℂ_[p]} (hφ : HasSubst φ) (b0 : MvPowerSeries (Fin 2) ℂ_[p])
    {u v : MvPowerSeries κ ℂ_[p]} (hu : constantCoeff u = 0) (hv : constantCoeff v = 0) :
    subst φ (GlobalTheory.ThBe0.at2 b0 u v) = GlobalTheory.ThBe0.at2 b0 (subst φ u) (subst φ v) := by
  have h : ∀ i : Fin 2, constantCoeff (if i = 0 then u else v) = 0 := fun i => by split_ifs <;> assumption
  unfold GlobalTheory.ThBe0.at2
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero h) hφ]
  congr 1
  funext i
  split_ifs <;> rfl

variable {n' : ℕ} [NeZero n']

theorem hasSubst_pair {r0 r1 : ℕ} (a : Fin r0) (b : Fin r1) :
    HasSubst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem cc_jet {r0 r1 : ℕ} (v : ZMod n' × Fin r0 × Fin r1) : constantCoeff (jetLogG p n' v) = 0 := by
  rw [← GlobalTheory.BiextInhab.bridge p n' v.2 v.1]
  exact GlobalTheory.BeProps.constantCoeff_laAt _ _

theorem hasSubst_jet' {r0 r1 : ℕ} : HasSubst (jetLogG p n' (β := Fin r0 × Fin r1)) :=
  hasSubst_of_constantCoeff_zero cc_jet

theorem pair_eq {r0 r1 : ℕ} (b0 : MvPowerSeries (Fin 2) ℂ_[p]) (bv : MvPowerSeries (ZMod n') ℂ_[p])
    (x : Fin (n' / 2) ⊕ Fin (n' / 2) → MvPowerSeries (ZMod n') ℂ_[p]) (V : MvPowerSeries (ZMod n') ℂ_[p])
    (hb0 : constantCoeff b0 = 0) (hbv : constantCoeff bv = 0) (hx : ∀ r, constantCoeff (x r) = 0)
    (H : product_zeroth_first_parts.expS ℂ_[p] (-(∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (PowerSeries.subst (x (Sum.inl r)) (Formalism.MainNotions.GL3Theta.logF p))
      (PowerSeries.subst (x (Sum.inr r)) (Formalism.MainNotions.GL3Theta.logF p)))) = V * product_zeroth_first_parts.expS ℂ_[p] (-(subst (GlobalTheory.ThStr.laS p n') bv)))
    (a : Fin r0) (b : Fin r1) :
    product_zeroth_first_parts.expS ℂ_[p] (-(∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0
                               (PowerSeries.subst (xiE x (Sum.inl ((r, a, b) : Eidx n' r0 r1))) (Formalism.MainNotions.GL3Theta.logF p))
                               (PowerSeries.subst (xiE x (Sum.inr ((r, a, b) : Eidx n' r0 r1))) (Formalism.MainNotions.GL3Theta.logF p)))) =
      subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) V *
        product_zeroth_first_parts.expS ℂ_[p] (-(subst (fun s : ZMod n' => jetLogG p n' (s, a, b)) bv)) := by
  have hψ := hasSubst_pair (p := p) (n' := n') a b
  have hcL : constantCoeff (-(∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (PowerSeries.subst (x (Sum.inl r)) (Formalism.MainNotions.GL3Theta.logF p))
      (PowerSeries.subst (x (Sum.inr r)) (Formalism.MainNotions.GL3Theta.logF p)))) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_neg, map_sum, Finset.sum_eq_zero fun r _ => constantCoeff_bivariateSeriesSubstPair hb0 (cc_plog (hx _)) (cc_plog (hx _)), neg_zero]
  have hLa : HasSubst (GlobalTheory.ThStr.laS p n') := hasSubst_of_constantCoeff_zero GlobalTheory.BeProps.constantCoeff_laS
  have hcR : constantCoeff (-(subst (GlobalTheory.ThStr.laS p n') bv)) = 0 := by
    rw [map_neg, constantCoeff_subst_eq_zero hLa GlobalTheory.BeProps.constantCoeff_laS hbv, neg_zero]
  have e1 : subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p]))
      (product_zeroth_first_parts.expS ℂ_[p] (-(∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (PowerSeries.subst (x (Sum.inl r)) (Formalism.MainNotions.GL3Theta.logF p))
        (PowerSeries.subst (x (Sum.inr r)) (Formalism.MainNotions.GL3Theta.logF p))))) =
      product_zeroth_first_parts.expS ℂ_[p] (-(∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0
        (PowerSeries.subst (xiE x (Sum.inl ((r, a, b) : Eidx n' r0 r1))) (Formalism.MainNotions.GL3Theta.logF p))
        (PowerSeries.subst (xiE x (Sum.inr ((r, a, b) : Eidx n' r0 r1))) (Formalism.MainNotions.GL3Theta.logF p)))) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [product_zeroth_first_parts.expS, product_zeroth_first_parts.expS, GlobalTheory.BeProps.subst_psubst hψ hcL, ← substAlgHom_apply hψ, map_neg, map_sum]
    congr 2
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [substAlgHom_apply, subst_powerSeriesEvalTwoGroups hψ b0 (cc_plog (hx _)) (cc_plog (hx _)),
      GlobalTheory.BeProps.subst_psubst hψ (hx _), GlobalTheory.BeProps.subst_psubst hψ (hx _)]
    rfl
  have e2 : subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p]))
      (V * product_zeroth_first_parts.expS ℂ_[p] (-(subst (GlobalTheory.ThStr.laS p n') bv))) =
      subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) V *
        product_zeroth_first_parts.expS ℂ_[p] (-(subst (fun s : ZMod n' => jetLogG p n' (s, a, b)) bv)) := by
    have hn : subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p]))
        (-(subst (GlobalTheory.ThStr.laS p n') bv)) = -(subst (fun s : ZMod n' => jetLogG p n' (s, a, b)) bv) := by
      rw [← substAlgHom_apply hψ, map_neg, substAlgHom_apply, subst_comp_subst_apply hLa hψ]
      congr 2
      funext s
      exact GlobalTheory.BiextInhab.bridge p n' (a, b) s
    rw [product_zeroth_first_parts.expS, product_zeroth_first_parts.expS, ← substAlgHom_apply hψ, map_mul]
    simp only [substAlgHom_apply]
    rw [GlobalTheory.BeProps.subst_psubst hψ hcR, hn]
  rw [← e1, ← e2, H]

theorem integralW_pair {r0 r1 : ℕ} (a : Fin r0) (b : Fin r1) {V : MvPowerSeries (ZMod n') ℂ_[p]}
    (hV : Formalism.MainNotions.GL3Theta.IntegralW V) :
    Formalism.MainNotions.GL3Theta.IntegralW (subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) V) := by
  let e : ZMod n' ↪ ZMod n' × Fin r0 × Fin r1 := ⟨fun s => (s, a, b), fun x y h => (Prod.mk.inj h).1⟩
  have he : subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) V =
      rename e V := by
    rw [rename_eq_subst]; rfl
  rw [he]
  intro m
  by_cases hm : m ∈ Set.range (Finsupp.mapDomain (e : ZMod n' → ZMod n' × Fin r0 × Fin r1))
  · obtain ⟨n, rfl⟩ := hm
    rw [← Finsupp.embDomain_eq_mapDomain, coeff_embDomain_rename]
    exact hV n
  · rw [coeff_rename_eq_zero _ _ hm]
    exact zero_mem _

theorem cc_xiE {r0 r1 : ℕ} {x : Fin (n' / 2) ⊕ Fin (n' / 2) → MvPowerSeries (ZMod n') ℂ_[p]}
    (hx : ∀ r, constantCoeff (x r) = 0) (e : Eidx n' r0 r1 ⊕ Eidx n' r0 r1) : constantCoeff (xiE x e) = 0 := by
  rcases e with ⟨r, a, b⟩ | ⟨r, a, b⟩
  · exact constantCoeff_subst_eq_zero (hasSubst_pair a b) (fun _ => constantCoeff_X _) (hx _)
  · exact constantCoeff_subst_eq_zero (hasSubst_pair a b) (fun _ => constantCoeff_X _) (hx _)

theorem sum_reorder {r0 r1 : ℕ} {M : Type*} [AddCommMonoid M] (f : Eidx n' r0 r1 → M) :
    ∑ e, f e = ∑ a : Fin r0, ∑ b : Fin r1, ∑ r : Fin (n' / 2), f (r, a, b) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm, Fintype.sum_prod_type]

theorem neg_doubleSum_eq_doubleSum_neg {α β M : Type*} [Fintype α] [Fintype β] [AddCommGroup M] (g : α → β → M) :
    -(∑ a, ∑ b, g a b) = ∑ a, ∑ b, -g a b := by
  simp [Finset.sum_neg_distrib]

theorem rhs_eq {r0 r1 : ℕ} (bv : MvPowerSeries (ZMod n') ℂ_[p]) (hbv : constantCoeff bv = 0) :
    subst (jetLogG p n' (β := Fin r0 × Fin r1)) (product_zeroth_first_parts.expS ℂ_[p] ((-1 : ℂ_[p]) • ∑ a : Fin r0, ∑ b : Fin r1,
      subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) bv)) =
      ∏ a : Fin r0, ∏ b : Fin r1, product_zeroth_first_parts.expS ℂ_[p] (-(subst (fun s : ZMod n' => jetLogG p n' (s, a, b)) bv)) := by
  have hJ := hasSubst_jet' (p := p) (n' := n') (r0 := r0) (r1 := r1)
  have hc : constantCoeff (-(∑ a : Fin r0, ∑ b : Fin r1,
      subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) bv)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_neg, map_sum, Finset.sum_eq_zero fun a _ => ?_, neg_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero fun b _ => constantCoeff_subst_eq_zero (hasSubst_pair a b) (fun _ => constantCoeff_X _) hbv
  have e : subst (jetLogG p n' (β := Fin r0 × Fin r1)) (-(∑ a : Fin r0, ∑ b : Fin r1,
      subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) bv)) =
      ∑ a : Fin r0, ∑ b : Fin r1, -(subst (fun s : ZMod n' => jetLogG p n' (s, a, b)) bv) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← substAlgHom_apply hJ, map_neg, map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [substAlgHom_apply, subst_comp_subst_apply (hasSubst_pair a b) hJ]
    congr 2
    funext s
    rw [subst_X hJ]
  rw [neg_one_smul, product_zeroth_first_parts.expS, GlobalTheory.BeProps.subst_psubst hJ hc, e]
  exact padicExpSeries_doubleSum _ fun a b => by
    rw [map_neg, constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun s => cc_jet _) (fun s => cc_jet _) hbv,
      neg_zero]

end GlobalTheory.OnePlacePairs

namespace GlobalTheory.OnePlacePairs

open MvPowerSeries

theorem pairs_all : ∀ {p : ℕ} [Fact p.Prime] {n' : ℕ} [NeZero n'] (b0 : MvPowerSeries (Fin 2) ℂ_[p]) (bv : MvPowerSeries (ZMod n') ℂ_[p]) (x : Fin (n' / 2) ⊕ Fin (n' / 2) → MvPowerSeries (ZMod n') ℂ_[p]) (V : MvPowerSeries (ZMod n') ℂ_[p]), MvPowerSeries.constantCoeff b0 = 0 → MvPowerSeries.constantCoeff bv = 0 → (∀ r, MvPowerSeries.constantCoeff (x r) = 0) → Formalism.MainNotions.GL3Theta.IntegralW V → product_zeroth_first_parts.expS ℂ_[p] (-(∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (PowerSeries.subst (x (Sum.inl r)) (Formalism.MainNotions.GL3Theta.logF p)) (PowerSeries.subst (x (Sum.inr r)) (Formalism.MainNotions.GL3Theta.logF p)))) = V * product_zeroth_first_parts.expS ℂ_[p] (-(MvPowerSeries.subst (GlobalTheory.ThStr.laS p n') bv)) → ∀ (r0 r1 : ℕ), ∃ U2 : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p], (∀ m, ‖MvPowerSeries.coeff m U2‖ ≤ 1) ∧ product_zeroth_first_parts.expS ℂ_[p] (-(∑ e : Eidx n' r0 r1, GlobalTheory.ThBe0.at2 b0 (PowerSeries.subst (xiE x (Sum.inl e)) (Formalism.MainNotions.GL3Theta.logF p)) (PowerSeries.subst (xiE x (Sum.inr e)) (Formalism.MainNotions.GL3Theta.logF p)))) = U2 * MvPowerSeries.subst (jetLogG p n' (β := Fin r0 × Fin r1)) (product_zeroth_first_parts.expS ℂ_[p] ((-1 : ℂ_[p]) • ∑ a : Fin r0, ∑ b : Fin r1, MvPowerSeries.subst (fun s : ZMod n' => (MvPowerSeries.X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) bv)) := by
  intro p _ n' _ b0 bv x V hb0 hbv hx hV H r0 r1
  refine ⟨∏ a : Fin r0, ∏ b : Fin r1,
    subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) V, fun m => ?_, ?_⟩
  · have hmem : (∏ a : Fin r0, ∏ b : Fin r1,
        subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) V) ∈
        GlobalTheory.BiextInhab.serW p (ZMod n' × Fin r0 × Fin r1) :=
      Subring.prod_mem _ fun a _ => Subring.prod_mem _ fun b _ => GlobalTheory.BiextInhab.mem_serW.2 (integralW_pair a b hV)
    exact GlobalTheory.BeProps.norm_le_one_of_mem_Wp (GlobalTheory.BiextInhab.mem_serW.1 hmem m)
  · rw [rhs_eq bv hbv, ← Finset.prod_mul_distrib]
    simp only [← Finset.prod_mul_distrib]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [sum_reorder, neg_doubleSum_eq_doubleSum_neg, padicExpSeries_doubleSum _ fun a b => by
      rw [map_neg, map_sum, Finset.sum_eq_zero fun r _ => constantCoeff_bivariateSeriesSubstPair hb0 (cc_plog (cc_xiE hx _)) (cc_plog (cc_xiE hx _)),
        neg_zero]]
    exact Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => pair_eq b0 bv x V hb0 hbv hx H a b

end GlobalTheory.OnePlacePairs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetUnitaryStabiliserSelfDualLatticeNormOne
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory NumberField IsDedekindDomain

namespace GlobalTheory.DetFields

open GlobalTheory.Mem.Col2.JetEx.VacEqPf

theorem iE_det {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (γ : Sp X.E n ≃ₗ[X.E] Sp X.E n) :
    s.iE ((LinearEquiv.det γ : X.Eˣ) : X.E) = (matOf s γ).det := by
  rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix']
  rw [show s.iE (LinearMap.toMatrix' (γ : Sp X.E n →ₗ[X.E] Sp X.E n)).det = _ from
    RingHom.map_det (s.iE : X.E →+* D.host.E) _]
  congr 1

theorem det_of_stab : ∀ (D : D7) (X : Fields) (s : Seam D X) (χ : TaylorLogMetric.IdE D → ℂ), s.Ok → TaylorLogMetric.IsChi D χ → ∀ (n : ℕ) (N' : Submodule (𝓞 X.E) (Sp X.E n)), IsSDLat D.host.E n (s.lat N') → ∀ γ : UF X.E n, gmap γ.1 N' = N' → ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) * star ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) = 1 ∧ IsIntegral ℤ ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) ∧ ∏ τ, TaylorLogMetric.embT D τ (s.iE ((LinearEquiv.det γ.1 : X.Eˣ) : X.E)) = 1 := by
  intro D X s χ hok hχ n N' hL γ hγ
  have hd := iE_det s γ.1
  have hSD : Formalism.MainNotions.StandardLatticesGL3.SD D (s.lat N') := hL
  have hfg : (s.lat N').FG := hL.1
  have hsp : Submodule.span D.host.E ((s.lat N' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) = ⊤ := hL.2.1
  have hU := matOf_unitary s hok γ
  set M := matOf s γ.1 with hM

  have hMM : GlobalTheory.RatEqui.adj D M * M = 1 ∧ M * GlobalTheory.RatEqui.adj D M = 1 := by
    letI := D.host.cmStar
    have e : star M = GlobalTheory.RatEqui.adj D M := by
      ext i j
      simp [GlobalTheory.RatEqui.adj, Matrix.star_apply, star_conj]
    rw [← e]
    exact ⟨Unitary.star_mul_self_of_mem hU, Unitary.mul_star_self_of_mem hU⟩
  have hadj : M * GlobalTheory.RatEqui.adj D M = 1 := hMM.2

  have hs : ∀ v, v ∈ s.lat N' ↔ M.mulVec v ∈ s.lat N' := by
    intro v
    constructor
    · intro hv
      obtain ⟨x, hx, rfl⟩ := (mem_lat s N' v).1 hv
      refine (mem_lat s N' _).2 ⟨γ.1 x, ?_, (matOf_mulVec s γ.1 x).symm⟩
      rw [← hγ]
      exact ⟨x, hx, rfl⟩
    · intro hv
      obtain ⟨y, hy, hyv⟩ := (mem_lat s N' _).1 hv
      rw [← hγ] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      have hx' : M.mulVec (vec s x) = M.mulVec v := by
        rw [← hyv]
        exact matOf_mulVec s γ.1 x
      have hinj : vec s x = v := by
        have := congrArg (fun w => (GlobalTheory.RatEqui.adj D M).mulVec w) hx'
        simpa only [Matrix.mulVec_mulVec, hMM.1, Matrix.one_mulVec] using this
      rw [← hinj]
      exact (mem_lat s N' _).2 ⟨x, hx, rfl⟩

  have hdet : M.det * D.host.conj M.det = 1 := by
    have h1 : (GlobalTheory.RatEqui.adj D M).det = D.host.conj M.det := by
      unfold GlobalTheory.RatEqui.adj
      rw [Matrix.det_transpose]
      exact (RingHom.map_det (D.host.conj : D.host.E →+* D.host.E) M).symm
    rw [← h1, ← Matrix.det_mul, hMM.2, Matrix.det_one]
  refine ⟨?_, ?_, ?_⟩
  · apply s.iE.injective
    rw [map_mul, hok.2, hd, map_one]
    exact hdet
  · have i1 := GlobalTheory.DetStab.isIntegral_det_of_stable (s.lat N') hfg hsp M fun v hv => (hs v).1 hv
    have i2 : IsIntegral ℤ M.det := isIntegral_trans (R := ℤ) _ i1
    have i3 := map_isIntegral_int s.iE.symm.toRingHom i2
    rw [← hd] at i3
    simpa using i3
  · rw [hd]
    exact GlobalTheory.DetStab.prod_emb_det_eq_one D χ hχ n (s.lat N') hSD M hadj hs

end GlobalTheory.DetFields
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualIsoDetGenMNeZero
section
noncomputable section

namespace GlobalTheory.ValCmp

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.MainNotions.G

theorem dualIso_det_genM_ne_zero (R : Type) [CommRing R] [Nontrivial R] (n : ℕ) : (genM R n).det ≠ 0 := by
  intro h
  have h1 := congrArg (MvPolynomial.eval fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) R) v.1 v.2) h
  rw [RingHom.map_det, map_zero] at h1
  have h2 : (MvPolynomial.eval fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) R) v.1 v.2).mapMatrix
      (genM R n) = 1 := by
    ext a b
    simp [genM]
  rw [h2, Matrix.det_one] at h1
  exact one_ne_zero h1

theorem dualIso_cofRel_unique {R : Type} [CommRing R] [IsDomain R] {m : ℕ} {ν : Fin (m + 1) → ℕ}
    {f g g' : MP R (m + 1)} (h : CofRel R m ν f g) (h' : CofRel R m ν f g') : g = g' :=
  mul_left_cancel₀ (pow_ne_zero _ (dualIso_det_genM_ne_zero R (m + 1))) (h.trans h'.symm)

theorem dualIso_cofRel_add {R : Type} [CommRing R] {m : ℕ} {ν : Fin (m + 1) → ℕ}
    {f g f' g' : MP R (m + 1)} (h : CofRel R m ν f g) (h' : CofRel R m ν f' g') :
    CofRel R m ν (f + f') (g + g') := by
  unfold CofRel at *
  rw [mul_add, map_add (f := _), h, h']

theorem dualIso_cofRel_smul {R : Type} [CommRing R] {m : ℕ} {ν : Fin (m + 1) → ℕ}
    {f g : MP R (m + 1)} (c : R) (h : CofRel R m ν f g) : CofRel R m ν (c • f) (c • g) := by
  unfold CofRel at *
  rw [mul_smul_comm, map_smul, h]

theorem dualIso_cofRel_zsmul {R : Type} [CommRing R] {m : ℕ} {ν : Fin (m + 1) → ℕ}
    {f g : MP R (m + 1)} (c : ℤ) (h : CofRel R m ν f g) : CofRel R m ν (c • f) (c • g) := by
  unfold CofRel at *
  rw [mul_smul_comm, map_zsmul, h]

theorem dualIso_map_genM {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ) :
    (MvPolynomial.map φ).mapMatrix (genM R n) = genM S n := by
  ext1 a b
  simp [genM]

theorem dualIso_map_cofAct {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ) (f : MP R n) :
    MvPolynomial.map φ (cofAct R n f) = cofAct S n (MvPolynomial.map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [cofAct]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp only [cofAct, aeval_X]
    rw [← dualIso_map_genM φ n, ← RingHom.map_adjugate]
    rfl

theorem dualIso_cofRel_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {m : ℕ} {ν : Fin (m + 1) → ℕ}
    {f g : MP R (m + 1)} (h : CofRel R m ν f g) :
    CofRel S m ν (MvPolynomial.map φ f) (MvPolynomial.map φ g) := by
  unfold CofRel at *
  rw [← dualIso_map_cofAct, ← h, map_mul, map_pow, RingHom.map_det, dualIso_map_genM]

theorem dualIso_nuDual_antitone {m : ℕ} {ν : Fin (m + 1) → ℕ} (hν : Antitone ν) : Antitone (nuDual ν) := by
  intro i j hij
  have := hν (Fin.rev_le_rev.2 hij)
  simp only [nuDual]
  omega

theorem dualIso_nuDual_last {m : ℕ} (ν : Fin (m + 1) → ℕ) : nuDual ν (Fin.last m) = 0 := by
  simp [nuDual]

theorem dualIso_nuDual_nuDual {m : ℕ} {ν : Fin (m + 1) → ℕ} (hν : Antitone ν) (hl : ν (Fin.last m) = 0) :
    nuDual (nuDual ν) = ν := by
  funext i
  have := hν (Fin.zero_le i)
  simp only [nuDual, Fin.rev_rev, Fin.rev_zero, hl]
  omega

theorem dualIso_units_smul_smul {M : Type} [AddCommGroup M] (ε : ℤˣ) (x : M) : (ε : ℤ) • (ε : ℤ) • x = x := by
  rw [smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]

theorem dualIso_exists_map (K : Type) [Field K] (m : ℕ) (ν : Fin (m + 1) → ℕ) (hν : Antitone ν)
    (hl : ν (Fin.last m) = 0) :
    ∃ Ψ : MP K (m + 1) →ₗ[K] MP K (m + 1), ∀ f ∈ dualWeyl K (m + 1) (m + 1) ν, CofRel K m ν f (Ψ f) := by
  choose G hG using _root_.GlobalTheory.ValCmp.exists_cofRel_dualWeyl K m ν hν hl
  let Ψ₀ : dualWeyl K (m + 1) (m + 1) ν →ₗ[K] MP K (m + 1) :=
    { toFun := fun f => G f.1 f.2
      map_add' := fun f g =>
        dualIso_cofRel_unique (hG _ (f + g).2).2 (dualIso_cofRel_add (hG _ f.2).2 (hG _ g.2).2)
      map_smul' := fun c f =>
        dualIso_cofRel_unique (hG _ (c • f).2).2 (dualIso_cofRel_smul c (hG _ f.2).2) }
  obtain ⟨Ψ, hΨ⟩ := LinearMap.exists_extend Ψ₀
  refine ⟨Ψ, fun f hf => ?_⟩
  have h1 : Ψ f = G f hf := LinearMap.congr_fun hΨ ⟨f, hf⟩
  rw [h1]
  exact (hG f hf).2

theorem dualIso_lattice (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] (m : ℕ)
    (ν : Fin (m + 1) → ℕ) (hν : Antitone ν) (hl : ν (Fin.last m) = 0)
    (Ψ : MP Kf (m + 1) →ₗ[Kf] MP Kf (m + 1))
    (hΨ : ∀ f ∈ dualWeyl Kf (m + 1) (m + 1) ν, CofRel Kf m ν f (Ψ f))
    (A B : Submodule O (MP O (m + 1))) (hA : A ≤ dualWeyl O (m + 1) (m + 1) ν)
    (hB : B ≤ dualWeyl O (m + 1) (m + 1) (nuDual ν))
    (hAB : ∀ f ∈ A, ∃ g ∈ B, CofRel O m ν f g) (hBA : ∀ g ∈ B, ∃ f ∈ A, CofRel O m (nuDual ν) g f) :
    (A.map (mapAlgHom (Algebra.ofId O Kf)).toLinearMap).map (Ψ.restrictScalars O) =
      B.map (mapAlgHom (Algebra.ofId O Kf)).toLinearMap := by
  have key : ∀ f ∈ A, ∀ g, CofRel O m ν f g →
      Ψ (MvPolynomial.map (algebraMap O Kf) f) = MvPolynomial.map (algebraMap O Kf) g := fun f hf g hfg =>
    dualIso_cofRel_unique (hΨ _ (dualWeylMap O Kf _ _ _ _ _ (hA hf))) (dualIso_cofRel_map _ hfg)
  apply le_antisymm
  · rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    obtain ⟨g, hg, hfg⟩ := hAB f hf
    exact ⟨g, hg, (key f hf g hfg).symm⟩
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨f, hf, hgf⟩ := hBA g hg
    obtain ⟨ε, hε⟩ := GlobalTheory.T.cofactorTwistRelation_dualWeight_involutive O m (nuDual ν) (dualIso_nuDual_antitone hν) (dualIso_nuDual_last ν)
    have h1 := hε g (hB hg) f hgf
    rw [dualIso_nuDual_nuDual hν hl] at h1
    have h2 := dualIso_cofRel_zsmul (ε : ℤ) h1
    rw [dualIso_units_smul_smul] at h2
    have h3 : (ε : ℤ) • f ∈ A := A.toAddSubgroup.zsmul_mem hf _
    exact ⟨_, ⟨_, h3, rfl⟩, key _ h3 g h2⟩

theorem exists_posOk_dual (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] (m : ℕ)
    (ν : Fin (m + 1) → ℕ) (hν : Antitone ν) (hl : ν (Fin.last m) = 0) (e c : ℤ) :
    ∃ Ψ : MP Kf (m + 1) →ₗ[Kf] MP Kf (m + 1),
      PosOk O Kf (m + 1) ν (nuDual ν) e (-(e + ν 0 + c)) c (fun h => (h⁻¹).transpose) Ψ := by
  obtain ⟨Ψ, hΨ⟩ := dualIso_exists_map Kf m ν hν hl
  have hν' := dualIso_nuDual_antitone hν
  have hl' := dualIso_nuDual_last ν
  have hdd := dualIso_nuDual_nuDual hν hl
  refine ⟨Ψ, fun f hf h0 => ?_, ?_, fun h hh f hf => ?_, ?_, ?_⟩
  · obtain ⟨ε, hε⟩ := GlobalTheory.T.cofactorTwistRelation_dualWeight_involutive Kf m ν hν hl
    have h1 := hε f hf _ (hΨ f hf)
    rw [h0] at h1
    have h2 : CofRel Kf m (nuDual ν) 0 0 := by simp [CofRel]
    have h3 := dualIso_cofRel_unique h1 h2
    rw [← dualIso_units_smul_smul ε f, h3, smul_zero]
  · apply le_antisymm
    · rintro _ ⟨f, hf, rfl⟩
      obtain ⟨g, hg, hfg⟩ := _root_.GlobalTheory.ValCmp.exists_cofRel_dualWeyl Kf m ν hν hl f hf
      rw [dualIso_cofRel_unique (hΨ f hf) hfg]
      exact hg
    · intro g hg
      obtain ⟨f, hf, hgf⟩ := _root_.GlobalTheory.ValCmp.exists_cofRel_dualWeyl Kf m _ hν' hl' g hg
      obtain ⟨ε, hε⟩ := GlobalTheory.T.cofactorTwistRelation_dualWeight_involutive Kf m _ hν' hl'
      have h1 := hε g hg f hgf
      rw [hdd] at h1 hf
      have h2 := dualIso_cofRel_zsmul (ε : ℤ) h1
      rw [dualIso_units_smul_smul] at h2
      have h3 : (ε : ℤ) • f ∈ dualWeyl Kf (m + 1) (m + 1) ν :=
        (dualWeyl Kf (m + 1) (m + 1) ν).toAddSubgroup.zsmul_mem hf _
      exact ⟨_, h3, dualIso_cofRel_unique (hΨ _ h3) h2⟩
  · have h1 := _root_.GlobalTheory.ValCmp.Eqv.cofRel_rowAct Kf m ν h hh f hf _ (hΨ f hf)
    have h2 := dualIso_cofRel_unique (hΨ _ (dualWeylRowStable Kf _ _ _ h⁻¹ f hf)) h1
    have h3 : (h⁻¹).transpose⁻¹ = h.transpose := by
      rw [← Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ hh]
    have h4 : (h⁻¹).transpose.det = (h.det)⁻¹ := by
      rw [Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    simp only [rnd, LinearMap.smul_apply, map_smul, AlgHom.toLinearMap_apply, h2, h3, h4, smul_smul, inv_zpow']
    rw [← zpow_add₀ hh.ne_zero, ← zpow_add₀ hh.ne_zero]
    congr 2
    ring
  · refine dualIso_lattice O Kf m ν hν hl Ψ hΨ _ _ le_rfl le_rfl (_root_.GlobalTheory.ValCmp.exists_cofRel_dualWeyl O m ν hν hl) fun g hg => ?_
    have := _root_.GlobalTheory.ValCmp.exists_cofRel_dualWeyl O m _ hν' hl' g hg
    rwa [hdd] at this
  · refine dualIso_lattice O Kf m ν hν hl Ψ hΨ _ _ (weylLeDual O _ _ _ _ hν) (weylLeDual O _ _ _ _ hν')
      (_root_.GlobalTheory.ValCmp.weyl_exists_cofRel O m ν hν hl) fun g hg => ?_
    have := _root_.GlobalTheory.ValCmp.weyl_exists_cofRel O m _ hν' hl' g hg
    rwa [hdd] at this

end GlobalTheory.ValCmp
end
end

