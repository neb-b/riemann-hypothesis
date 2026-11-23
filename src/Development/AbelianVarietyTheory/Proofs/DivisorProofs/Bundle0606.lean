module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0571
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TensorPlaceNorm
public import Formalism.LocalToGlobal.Divisibility.CoefMod

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstLiftXPowFrob
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.Katz

variable (p : ℕ) [Fact p.Prime] {k k' k'' : Type} [Field k] [CharP k p] [Field k'] [CharP k' p]
  [Field k''] [CharP k'' p]

theorem wittMap_injective (σ : k →+* k') :
    Function.Injective ((algebraMap (WittVector p k') (Fr p k')).comp (WittVector.map σ)) :=
  (IsFractionRing.injective (WittVector p k') (Fr p k')).comp (WittVector.map_injective σ σ.injective)

def frMap (σ : k →+* k') : Fr p k →+* Fr p k' := IsFractionRing.lift (wittMap_injective p σ)

theorem frMap_algebraMap (σ : k →+* k') (w : WittVector p k) :
    frMap p σ (algebraMap _ _ w) = algebraMap _ _ (WittVector.map σ w) :=
  IsFractionRing.lift_algebraMap _ _

theorem frMap_id : frMap p (RingHom.id k) = RingHom.id (Fr p k) := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors (WittVector p k)) (RingHom.ext fun w => ?_)
  simp [frMap_algebraMap, WittVector.map_id]

theorem frMap_comp (σ : k →+* k') (τ : k' →+* k'') :
    frMap p (τ.comp σ) = (frMap p τ).comp (frMap p σ) := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors (WittVector p k)) (RingHom.ext fun w => ?_)
  simp only [RingHom.comp_apply, frMap_algebraMap]
  congr 1

theorem map_lift {ι : Type} (σ : k →+* k') (f : MvPowerSeries ι k) :
    MvPowerSeries.map (frMap p σ) (lift p f) = lift p (MvPowerSeries.map σ f) := by
  ext α
  rw [coeff_map, coeff_lift, coeff_lift, frMap_algebraMap, WittVector.map_teichmuller, coeff_map]

theorem map_subst_lift {d e : ℕ} (τ : k' →+* k'') (ψ : Fin d → MvPowerSeries (Fin e) k')
    (hψ : ∀ j, constantCoeff (ψ j) = 0) (g : MvPowerSeries (Fin d) (Fr p k')) :
    MvPowerSeries.map (frMap p τ) (subst (fun j => lift p (ψ j)) g) =
      subst (fun j => lift p (MvPowerSeries.map τ (ψ j))) (MvPowerSeries.map (frMap p τ) g) := by
  rw [map_subst (hasSubst_of_constantCoeff_zero fun j => constantCoeff_lift p (hψ j))]
  simp only [map_lift]

theorem lift_X_pow {ι : Type} (i : ι) (n : ℕ) :
    lift p ((X i : MvPowerSeries ι k) ^ n) = X i ^ n := by
  classical
  ext α
  rw [coeff_lift, coeff_X_pow, coeff_X_pow]
  split_ifs <;> simp

theorem frobRing_eq (h : (p : k) = 0) : frobRing h = frobenius k p :=
  RingHom.ext fun r => by rw [frobRing_apply, frobenius_def]

theorem frMap_frobenius [PerfectRing k p] : frMap p (frobenius k p) = KatzF.sig p k := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors (WittVector p k)) (RingHom.ext fun w => ?_)
  simp only [RingHom.comp_apply, frMap_algebraMap, KatzF.sig, WittVector.FractionRing.frobenius]
  rw [RingEquiv.coe_toRingHom, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  congr 1
  rw [← WittVector.frobenius_eq_map_frobenius]
  rfl

theorem subst_lift_X_pow_frob [PerfectRing k p] (h : (p : k) = 0) {d : ℕ}
    (f : MvPowerSeries (Fin d) (Fr p k)) :
    subst (fun j => lift p ((X j : MvPowerSeries (Fin d) k) ^ p)) (MvPowerSeries.map (frMap p (frobRing h)) f) =
      KatzF.frobS p f := by
  simp only [lift_X_pow, frobRing_eq p h, frMap_frobenius, KatzF.frobS]
  rfl

theorem ringHom_eq_of_app {q : ℕ} {O O' O'' : Type} [CommRing O] [CommRing O'] [CommRing O'']
    {σ : O →+* O'} {τ : O' →+* O''} {υ : O →+* O''} {G : PDivGroup q O} {G' : PDivGroup q O'}
    {G'' : PDivGroup q O''} (s : SemiHom σ G' G) (t : SemiHom τ G'' G') (u : SemiHom υ G'' G)
    (h : ∀ n a, u.app n a = t.app n (s.app n a)) : υ = τ.comp σ := by
  ext r
  have e := h 0 (r • 1)
  rw [(u.app 0).smul_map, (s.app 0).smul_map, (t.app 0).smul_map, map_one, map_one, map_one] at e
  have := congrArg (Coalgebra.counit (R := O'')) e
  simpa [Algebra.smul_def] using this

end GlobalTheory.Katz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapVariableGroupsFormalGroupLawCoboundaryOneCom
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.CobSwap

theorem hasSubst_swapVars {R : Type} [CommRing R] {d : ℕ} :
    HasSubst (Sum.elim (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R))
      (fun i => X (Sum.inl i))) :=
  hasSubst_of_constantCoeff_zero fun j => by cases j <;> simp

theorem swap_map {B Q : Type} [CommRing B] [CommRing Q] (h : B →+* Q) {d : ℕ}
    (c : MvPowerSeries (Fin d ⊕ Fin d) B) : swap (map h c) = map h (swap c) := by
  unfold swap at2
  rw [map_subst hasSubst_swapVars]
  congr 1
  funext j
  cases j <;> simp

theorem swap_subst {R : Type} [CommRing R] {d : ℕ} (ν : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hν : ∀ i, constantCoeff (ν i) = 0) (f : MvPowerSeries (Fin d) R) :
    swap (subst ν f) = subst (fun i => swap (ν i)) f := by
  unfold swap at2
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hν) hasSubst_swapVars]

theorem swap_inL {R : Type} [CommRing R] {d : ℕ} (f : MvPowerSeries (Fin d) R) :
    swap (inL f) = inR f := by
  unfold swap at2 inL inR
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
    hasSubst_swapVars]
  congr 1
  funext i
  rw [subst_X hasSubst_swapVars]
  rfl

theorem swap_inR {R : Type} [CommRing R] {d : ℕ} (f : MvPowerSeries (Fin d) R) :
    swap (inR f) = inL f := by
  unfold swap at2 inL inR
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
    hasSubst_swapVars]
  congr 1
  funext i
  rw [subst_X hasSubst_swapVars]
  rfl

theorem swap_sub {R : Type} [CommRing R] {d : ℕ} (a b : MvPowerSeries (Fin d ⊕ Fin d) R) :
    swap (a - b) = swap a - swap b := by
  unfold swap at2
  exact subst_sub hasSubst_swapVars a b

theorem swap_cob1_eq_of_swap_eq : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), (∀ i, constantCoeff (μ i) = 0) →
    (∀ i, swap (μ i) = μ i) → ∀ g : MvPowerSeries (Fin d) Q,
    swap (cob1 (up Q μ) g) = cob1 (up Q μ) g := by
  intro B Q _ _ _ d μ h0 hs g
  have h0' : ∀ i, constantCoeff (up Q μ i) = 0 := fun i => by
    simp [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, h0 i]
  have hs' : ∀ i, swap (up Q μ i) = up Q μ i := fun i => by
    simp only [up]; rw [swap_map, hs i]
  unfold cob1
  rw [swap_sub, swap_sub, swap_subst _ h0', swap_inL, swap_inR]
  simp only [hs']
  abel

end GlobalTheory.CobSwap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricCocycleAdditiveEqCoboundaryAdd
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.SymCocAdd

variable {R : Type} [CommRing R] {d : ℕ}

theorem subst_zeroPt {σ τ : Type} [Finite σ] (f : MvPowerSeries σ R) :
    subst (fun _ : σ => (0 : MvPowerSeries τ R)) f = C (constantCoeff f) := by
  classical
  have hs : HasSubst (fun _ : σ => (0 : MvPowerSeries τ R)) :=
    hasSubst_of_constantCoeff_zero fun _ => map_zero _
  ext e
  rw [coeff_subst hs, finsum_eq_single _ 0]
  · rw [Finsupp.prod_zero_index, coeff_zero_eq_constantCoeff_apply, coeff_C, coeff_one, smul_eq_mul]
    split_ifs <;> simp
  · intro dd hdd
    obtain ⟨s, hs'⟩ := Finsupp.ne_iff.1 hdd
    have hmem : s ∈ dd.support := Finsupp.mem_support_iff.2 (by simpa using hs')
    rw [Finsupp.prod, Finset.prod_eq_zero hmem (zero_pow (Finsupp.mem_support_iff.1 hmem)), map_zero,
      smul_zero]

theorem hs2 {τ : Type} {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) : HasSubst (Sum.elim u v) :=
  hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp [hu, hv]

theorem subst_powerSeriesEvalTwoGroups {τ τ' : Type} [Finite τ] {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    {a : τ → MvPowerSeries τ' R} (ha : ∀ t, constantCoeff (a t) = 0)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    subst a (at2 c u v) = at2 c (fun i => subst a (u i)) (fun i => subst a (v i)) := by
  unfold at2
  rw [subst_comp_subst_apply (hs2 hu hv) (hasSubst_of_constantCoeff_zero ha)]
  congr 1
  funext s
  cases s <;> rfl

theorem op_addLaw {τ : Type} {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) : op (addLaw R d) u v = u + v := by
  funext i
  unfold op addLaw at2
  rw [subst_add (hs2 hu hv), subst_X (hs2 hu hv), subst_X (hs2 hu hv)]
  rfl

end GlobalTheory.SymCocAdd

namespace GlobalTheory.SymCocAdd

variable {R : Type} [CommRing R] {d : ℕ}

theorem coc_at {τ : Type} [Finite τ] {c : MvPowerSeries (Fin d ⊕ Fin d) R}
    (hc : cob2 (addLaw R d) c = 0) {u v w : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    (hw : ∀ i, constantCoeff (w i) = 0) :
    at2 c v w - at2 c (u + v) w + at2 c u (v + w) - at2 c u v = 0 := by
  set a : Fin d ⊕ (Fin d ⊕ Fin d) → MvPowerSeries τ R := Sum.elim u (Sum.elim v w) with ha_def
  have ha0 : ∀ t, constantCoeff (a t) = 0 := fun t => by
    rcases t with t | t | t <;> simp [a, hu, hv, hw]
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  have h1 : ∀ i, constantCoeff ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun i => by simp [x1]
  have h2 : ∀ i, constantCoeff ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun i => by simp [x2]
  have h3 : ∀ i, constantCoeff ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun i => by simp [x3]
  have e1 : (fun i => subst a ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i)) = u := by
    funext i; simp only [x1]; rw [subst_X ha]; rfl
  have e2 : (fun i => subst a ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i)) = v := by
    funext i; simp only [x2]; rw [subst_X ha]; rfl
  have e3 : (fun i => subst a ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i)) = w := by
    funext i; simp only [x3]; rw [subst_X ha]; rfl
  have hadd : ∀ p q : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R,
      (fun i => subst a ((p + q) i)) = (fun i => subst a (p i)) + (fun i => subst a (q i)) := by
    intro p q; funext i; simp only [Pi.add_apply]; rw [subst_add ha]
  have h12 : ∀ i, constantCoeff ((x1 + x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun i => by simp [h1, h2]
  have h23 : ∀ i, constantCoeff ((x2 + x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun i => by simp [h2, h3]
  have key := congrArg (subst a) hc
  unfold cob2 at key
  rw [op_addLaw h1 h2, op_addLaw h2 h3] at key
  rw [subst_sub ha, subst_add ha, subst_sub ha, subst_powerSeriesEvalTwoGroups h2 h3 ha0, subst_powerSeriesEvalTwoGroups h12 h3 ha0,
    subst_powerSeriesEvalTwoGroups h1 h23 ha0, subst_powerSeriesEvalTwoGroups h1 h2 ha0, hadd, hadd, e1, e2, e3] at key
  rw [key, ← coe_substAlgHom ha, map_zero]

end GlobalTheory.SymCocAdd

namespace GlobalTheory.SymCocAdd

variable {R : Type} [CommRing R] {d : ℕ}


variable (R d) in
def PtGrp (τ : Type) : AddSubgroup (Fin d → MvPowerSeries τ R) where
  carrier := {u | ∀ i, constantCoeff (u i) = 0}
  zero_mem' := fun i => by simp
  add_mem' := fun {u v} hu hv i => by simp [hu i, hv i]
  neg_mem' := fun {u} hu i => by simp [hu i]

theorem sum_single_apply {M : Type} [AddCommMonoid M] (s : Finset (Fin d)) (w : Fin d → M) (i : Fin d) :
    (∑ j ∈ s, Pi.single j (w j) : Fin d → M) i = if i ∈ s then w i else 0 := by
  classical
  rw [Finset.sum_apply]
  simp only [Pi.single_apply]
  rw [Finset.sum_ite_eq]

theorem subst_sum_single {τ : Type} {a : Fin d → MvPowerSeries τ R} (ha : ∀ t, constantCoeff (a t) = 0)
    (s : Finset (Fin d)) :
    (fun i => subst a ((∑ j ∈ s, Pi.single j (X j) : Fin d → MvPowerSeries (Fin d) R) i)) =
      ∑ j ∈ s, Pi.single j (a j) := by
  have hS : HasSubst a := hasSubst_of_constantCoeff_zero ha
  funext i
  rw [sum_single_apply, sum_single_apply]
  split_ifs
  · exact subst_X hS i
  · rw [← coe_substAlgHom hS, map_zero]

theorem cc_sum_single {τ : Type} (s : Finset (Fin d)) (w : Fin d → MvPowerSeries τ R)
    (hw : ∀ j, constantCoeff (w j) = 0) (i : Fin d) :
    constantCoeff ((∑ j ∈ s, Pi.single j (w j) : Fin d → MvPowerSeries τ R) i) = 0 := by
  rw [sum_single_apply]; split_ifs <;> simp [hw]

end GlobalTheory.SymCocAdd

namespace GlobalTheory.SymCocAdd

variable {R : Type} [CommRing R] {d : ℕ}

theorem subst_single {τ : Type} {a : Fin d → MvPowerSeries τ R} (ha : ∀ t, constantCoeff (a t) = 0)
    (m : Fin d) :
    (fun i => subst a ((Pi.single m (X m) : Fin d → MvPowerSeries (Fin d) R) i)) = Pi.single m (a m) := by
  classical
  have hS : HasSubst a := hasSubst_of_constantCoeff_zero ha
  funext i
  rw [Pi.single_apply, Pi.single_apply]
  split_ifs with h
  · subst h; exact subst_X hS i
  · rw [← coe_substAlgHom hS, map_zero]


variable (R) in
def corr (c : MvPowerSeries (Fin d ⊕ Fin d) R) : MvPowerSeries (Fin d) R :=
  ∑ m : Fin d, at2 c (∑ j ∈ Finset.univ.filter (· < m), Pi.single j (X j))
    (Pi.single m (X m) : Fin d → MvPowerSeries (Fin d) R)

theorem subst_corr {τ : Type} {a : Fin d → MvPowerSeries τ R} (ha : ∀ t, constantCoeff (a t) = 0)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    subst a (corr R c) = ∑ m : Fin d, at2 c (∑ j ∈ Finset.univ.filter (· < m), Pi.single j (a j))
      (Pi.single m (a m)) := by
  classical
  have hS : HasSubst a := hasSubst_of_constantCoeff_zero ha
  unfold corr
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← coe_substAlgHom hS, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coe_substAlgHom hS, subst_powerSeriesEvalTwoGroups (cc_sum_single _ _ (fun j => by simp))
    (fun i => by rw [Pi.single_apply]; split_ifs <;> simp) ha, subst_sum_single ha, subst_single ha]

end GlobalTheory.SymCocAdd

namespace GlobalTheory


open GlobalTheory.SymCocAdd in
theorem symmetricCocycle_additive_eq_coboundary_add_alt (R : Type) [CommRing R] (d : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    (hc : IsCoc (addLaw R d) c) (h0 : constantCoeff c = 0) :
    ∃ b : MvPowerSeries (Fin d) R, c = cob1 (addLaw R d) b +
      ∑ m : Fin d, at2 c (Pi.single m (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) R))
        (Pi.single m (X (Sum.inr m))) := by
  classical
  let τ := Fin d ⊕ Fin d
  let A := PtGrp R d τ
  let γ : A → A → MvPowerSeries τ R := fun u v => at2 c u.1 v.1
  have hsymm : ∀ u v, γ u v = γ v u := by
    intro u v
    have hX1 : ∀ i, constantCoeff ((fun i => (X (Sum.inr i) : MvPowerSeries τ R)) i) = 0 :=
      fun i => by simp
    have hX2 : ∀ i, constantCoeff ((fun i => (X (Sum.inl i) : MvPowerSeries τ R)) i) = 0 :=
      fun i => by simp
    have huv : ∀ t, constantCoeff (Sum.elim u.1 v.1 t) = 0 := fun t => by
      cases t with
      | inl t => exact u.2 t
      | inr t => exact v.2 t
    have := subst_powerSeriesEvalTwoGroups hX1 hX2 huv c
    change at2 (swap c) u.1 v.1 = _ at this
    rw [hc.2] at this
    simp only [γ]
    rw [this]
    have hS : HasSubst (Sum.elim u.1 v.1) := hasSubst_of_constantCoeff_zero huv
    congr 1 <;> funext i <;> rw [subst_X hS] <;> rfl
  have hcoc : ∀ x y z : A, γ y z - γ (x + y) z + γ x (y + z) - γ x y = 0 :=
    fun x y z => coc_at hc.1 x.2 y.2 z.2
  have hzero : γ 0 0 = 0 := by
    simp only [γ]
    unfold at2
    have : Sum.elim ((0 : A) : Fin d → MvPowerSeries τ R) ((0 : A) : Fin d → MvPowerSeries τ R) =
        fun _ => 0 := by funext t; cases t <;> rfl
    rw [this, subst_zeroPt, h0, map_zero]
  let x : Fin d → A := fun m => ⟨Pi.single m (X (Sum.inl m)), fun i => by
    rw [Pi.single_apply]; split_ifs <;> simp⟩
  let y : Fin d → A := fun m => ⟨Pi.single m (X (Sum.inr m)), fun i => by
    rw [Pi.single_apply]; split_ifs <;> simp⟩
  have key := _root_.GlobalTheory.symmCocycle_sum A (MvPowerSeries τ R) γ hsymm hcoc hzero d x y
  have coeA : ∀ (s : Finset (Fin d)) (f : Fin d → A),
      ((∑ j ∈ s, f j : A) : Fin d → MvPowerSeries τ R) = ∑ j ∈ s, (f j : Fin d → MvPowerSeries τ R) :=
    fun s f => map_sum A.subtype f s
  have hL : γ (∑ m, x m) (∑ m, y m) = c := by
    simp only [γ]
    rw [coeA, coeA]
    simp only [x, y]
    rw [Finset.univ_sum_single (fun m => (X (Sum.inl m) : MvPowerSeries τ R)),
      Finset.univ_sum_single (fun m => (X (Sum.inr m) : MvPowerSeries τ R))]
    unfold at2
    have : Sum.elim (fun m => (X (Sum.inl m) : MvPowerSeries τ R)) (fun m => X (Sum.inr m)) = X := by
      funext t; cases t <;> rfl
    rw [this, subst_self]; rfl
  have hT : ((∑ m, γ (∑ j ∈ Finset.univ.filter (· < m), (x j + y j)) (x m + y m)) -
      (∑ m, γ (∑ j ∈ Finset.univ.filter (· < m), x j) (x m)) -
      ∑ m, γ (∑ j ∈ Finset.univ.filter (· < m), y j) (y m)) = cob1 (addLaw R d) (corr R c) := by
    unfold cob1 inL inR
    rw [subst_corr (fun i => by simp [addLaw]), subst_corr (fun i => by simp),
      subst_corr (fun i => by simp)]
    simp only [γ, coeA]
    simp only [x, y, AddSubgroup.coe_add, ← Pi.single_add]
    rfl
  refine ⟨corr R c, ?_⟩
  calc c = γ (∑ m, x m) (∑ m, y m) := hL.symm
    _ = _ := key
    _ = _ := by rw [hT, add_comm]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorNormLeIffTensorNormBound
section
open MvPolynomial

noncomputable section

namespace GlobalTheory.TensorNormCompare

open Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.IndefiniteRowSideFullHecke

variable {ι : Type} [Fintype ι] {n n' : ℕ}

theorem fockS_re_nonneg {σ : Type} (f : MvPolynomial σ ℂ) : 0 ≤ (fockS f f).re := by
  obtain ⟨r, hr, h⟩ := TensorPlaceNorm.fockS_self_nonneg f
  rw [h, Complex.ofReal_re]; exact hr

theorem fockS_re_pos' {σ : Type} {f : MvPolynomial σ ℂ} (hf : f ≠ 0) : 0 < (fockS f f).re := by
  have : (fockS f f).re = ∑ m ∈ f.support, ‖f.coeff m‖ ^ 2 * (mfact m : ℝ) := by
    have e : fockS f f = ((∑ m ∈ f.support, ‖f.coeff m‖ ^ 2 * (mfact m : ℝ) : ℝ) : ℂ) := by
      unfold fockS
      push_cast
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← Complex.conj_mul']
      rfl
    rw [e, Complex.ofReal_re]
  rw [this]
  refine Finset.sum_pos (fun m hm => mul_pos (pow_pos (norm_pos_iff.mpr (mem_support_iff.mp hm)) 2) ?_)
    (support_nonempty.mpr hf)
  exact_mod_cast Finset.prod_pos fun k _ => Nat.factorial_pos _

theorem fockS_conj_symm {σ : Type} (f g : MvPolynomial σ ℂ) : (starRingEnd ℂ) (fockS g f) = fockS f g := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [fockS_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right,
    fockS_eq_sum f g (f.support ∪ g.support) Finset.subset_union_left, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [map_mul, map_natCast, Complex.star_def, Complex.conj_conj]
  ring

def fockCore (σ : Type) : InnerProductSpace.Core ℂ (MvPolynomial σ ℂ) where
  inner f g := fockS f g
  conj_inner_symm f g := fockS_conj_symm f g
  re_inner_nonneg f := fockS_re_nonneg f
  add_left f f' g := by
    change fockL (f + f') g = fockL f g + fockL f' g
    rw [map_add (f := _), LinearMap.add_apply]
  smul_left f g r := by
    change fockL (r • f) g = _ * fockL f g
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
  definite f h := by
    by_contra hf
    have h' : fockS f f = 0 := h
    have := fockS_re_pos' hf
    rw [h'] at this
    simp at this

theorem exists_norm_bound {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] (S : Submodule ℂ E) [FiniteDimensional ℂ S] (A : S →ₗ[ℂ] F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : S, (inner ℂ (A f) (A f)).re ≤ C * (inner ℂ f.1 f.1).re := by
  let B := LinearMap.toContinuousLinearMap A
  refine ⟨‖B‖ ^ 2, by positivity, fun f => ?_⟩
  have h1 : (inner ℂ (A f) (A f)).re = ‖A f‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) (A f)
  have h2 : (inner ℂ f.1 f.1).re = ‖f.1‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) f.1
  have h3 : ‖A f‖ ≤ ‖B‖ * ‖f.1‖ := B.le_opNorm f
  rw [h1, h2, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h3 2

theorem exists_fock_bound {σ σ' : Type} (S : Submodule ℂ (MvPolynomial σ ℂ)) [FiniteDimensional ℂ S]
    (A : S →ₗ[ℂ] MvPolynomial σ' ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : S, (fockS (A f) (A f)).re ≤ C * (fockS f.1 f.1).re := by
  exact @exists_norm_bound _ _ (fockCore σ).toNormedAddCommGroup (InnerProductSpace.ofCore (fockCore σ).toCore)
    (fockCore σ').toNormedAddCommGroup (InnerProductSpace.ofCore (fockCore σ').toCore) S ‹_› A

theorem finiteDimensional_nablaSq (lam : DomWeight n) : FiniteDimensional ℂ (nablaSq ℂ n lam) := by
  obtain ⟨b, ⟨-, hb, -⟩, -⟩ := Formalism.GradedWeylDivisibility.sSBasis ℂ n n lam.natW
  have : Finite (Formalism.GradedWeylDivisibility.ssIdx n n lam.natW) := (Formalism.GradedWeylDivisibility.sSIdxFinite n n _).to_subtype
  unfold nablaSq
  rw [← hb]
  exact FiniteDimensional.span_of_finite ℂ (Set.finite_range b)

theorem extremal_fock_pos (lam : DomWeight n) : 0 < (fockS (extremal ℂ n lam) (extremal ℂ n lam)).re :=
  fockS_re_pos' (Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl lam.natW)

end GlobalTheory.TensorNormCompare
end
end

