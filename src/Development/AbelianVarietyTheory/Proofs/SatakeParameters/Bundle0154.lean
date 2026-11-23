module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0314
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0126

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedBaseChangeEqOfSatakeEq
section
noncomputable section

namespace GlobalTheory.SatBcInj

open Formalism.UG GlobalTheory.InertThetaCompare GlobalTheory.LFun.Orbit Formalism.MainNotions.N
open GlobalTheory.IndefiniteRowSideFullHecke.InertPlaceSetting (labInd)
open GlobalTheory.LGrp (WeylConjU bcParam bcParam_of_weylConj)

variable {m : ℕ}

def monoJ (a : Fin m → ℤ) (γ : Fin m → ℂ) : ℂ := ∏ i, γ i ^ a i

def actJ (w : Sgn m) (γ : Fin m → ℂ) : Fin m → ℂ := fun i => γ (w.1 i) ^ (w.2 i : ℤ)

def evJ (c : (Fin m → ℤ) →₀ ℂ) (γ : Fin m → ℂ) : ℂ := ∑ a ∈ c.support, c a * monoJ a γ

def symJ (a : Fin m → ℤ) (γ : Fin m → ℂ) : ℂ := ∑ w : Sgn m, monoJ a (actJ w γ)

theorem monoJ_act (w : Sgn m) (a : Fin m → ℤ) (γ : Fin m → ℂ) : monoJ a (actJ w γ) = monoJ (coact w a) γ := by
  unfold monoJ
  rw [← Equiv.prod_comp w.1 fun i => γ i ^ coact w a i]
  simp [actJ, coact, zpow_mul]

def coinv (w : Sgn m) (b : Fin m → ℤ) : Fin m → ℤ := fun i => w.2 i * b (w.1 i)

theorem coact_coinv (w : Sgn m) (b : Fin m → ℤ) : coact w (coinv w b) = b := funext fun j => by
  simp only [coact, coinv, Equiv.apply_symm_apply, ← mul_assoc]
  rcases Int.units_eq_one_or (w.2 (w.1.symm j)) with h | h <;> simp [h]

theorem coinv_coact (w : Sgn m) (a : Fin m → ℤ) : coinv w (coact w a) = a := funext fun j => by
  simp only [coact, coinv, Equiv.symm_apply_apply, ← mul_assoc]
  rcases Int.units_eq_one_or (w.2 j) with h | h <;> simp [h]

theorem evJ_act {c : (Fin m → ℤ) →₀ ℂ} (hc : ∀ w a, c (coact w a) = c a) (w : Sgn m) (γ : Fin m → ℂ) :
    evJ c (actJ w γ) = evJ c γ := by
  unfold evJ
  simp only [monoJ_act]
  refine Finset.sum_nbij' (coact w) (coinv w) (fun a ha => ?_) (fun b hb => ?_) (fun a _ => coinv_coact w a)
    (fun b _ => coact_coinv w b) (fun a _ => by rw [hc])
  · rw [Finsupp.mem_support_iff, hc]; exact Finsupp.mem_support_iff.1 ha
  · rw [Finsupp.mem_support_iff, ← hc w, coact_coinv]; exact Finsupp.mem_support_iff.1 hb

theorem sum_symJ {c : (Fin m → ℤ) →₀ ℂ} (hc : ∀ w a, c (coact w a) = c a) (γ : Fin m → ℂ) :
    ∑ a ∈ c.support, c a * symJ a γ = Fintype.card (Sgn m) * evJ c γ := by
  simp only [symJ, Finset.mul_sum]
  have e : ∀ w : Sgn m, ∑ a ∈ c.support, c a * monoJ a (actJ w γ) = evJ c γ := fun w => evJ_act hc w γ
  rw [Finset.sum_comm, Finset.sum_congr rfl fun w _ => e w, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem symJ_coact (w : Sgn m) (a : Fin m → ℤ) (γ : Fin m → ℂ) : symJ (coact w a) γ = symJ a γ := by
  let φ : Sgn m → Sgn m := fun u => (u.1 * w.1, fun i => u.2 (w.1 i) * w.2 i)
  have hφ : Function.Injective φ := fun u u' h => Prod.ext (mul_right_cancel (congrArg Prod.fst h))
    (funext fun i => by simpa [φ] using congrFun (congrArg Prod.snd h) (w.1.symm i))
  refine Fintype.sum_bijective φ (Finite.injective_iff_bijective.1 hφ) _ _ fun u => ?_
  rw [← monoJ_act]
  congr 1
  funext i
  simp [actJ, φ, zpow_mul]

theorem eq_zero_of_triangular (H : (Fin m → ℤ) → ℕ) (c : (Fin m → ℤ) → (Fin m → ℤ) →₀ ℂ)
    (hcoef : ∀ d, Dom d → ∀ w a, c d (coact w a) = c d a) (hself : ∀ d, Dom d → c d d ≠ 0)
    (htri : ∀ d a, Dom d → Dom a → c d a ≠ 0 → a = d ∨ H a < H d) (S : (Fin m → ℤ) → ℂ)
    (hS : ∀ w a, S (coact w a) = S a) (h : ∀ d, Dom d → ∑ a ∈ (c d).support, c d a * S a = 0) :
    ∀ d, Dom d → S d = 0 := fun d => by
  classical
  induction hk : H d using Nat.strong_induction_on generalizing d with
  | _ k ih =>
    intro hd
    have h3 := h d hd
    rw [← Finset.sum_filter_ne_zero, Finset.sum_congr rfl (g := fun _ => c d d * S d),
      Finset.sum_const, smul_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h3
    · refine (mul_eq_zero.1 (h3.elim (fun h4 => ?_) id)).resolve_left (hself d hd)
      exact not_not.1 (h4 (Finsupp.mem_support_iff.2 (hself d hd)))
    · intro a ha
      obtain ⟨w, hw⟩ := exists_dom a
      have h5 := (Finset.mem_filter.1 ha).2
      rw [← hcoef d hd w a, ← hS w a] at h5 ⊢
      rcases htri d _ hd hw (left_ne_zero_of_mul h5) with e | e
      · rw [e]
      · exact absurd (ih _ (hk ▸ e) _ rfl hw) (right_ne_zero_of_mul h5)

theorem monoJ_single (i₀ : Fin m) (k : ℕ) (δ : Fin m → ℂ) : monoJ (Pi.single i₀ (k : ℤ)) δ = δ i₀ ^ k := by
  unfold monoJ
  rw [Finset.prod_eq_single i₀ (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
  simp

theorem dom_single (i₀ : Fin m) (h0 : (i₀ : ℕ) = 0) (k : ℕ) : Dom (Pi.single i₀ (k : ℤ)) := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · simp only [Pi.single_apply]
    have : a ≤ b := hab
    rw [Fin.le_def] at this
    split_ifs with h1 h2 h2 <;> first | rfl | omega | (subst h2; exfalso; exact h1 (Fin.ext (by omega)))
  · simp only [Pi.single_apply]; split_ifs <;> omega

theorem ne_zero_of_symJ (α : Fin m → ℂˣ) (α₀ : Fin m → ℂ) (i₀ : Fin m)
    (h : ∀ k : ℕ, symJ (Pi.single i₀ (k : ℤ)) α₀ = symJ (Pi.single i₀ (k : ℤ)) fun j => (α j : ℂ)) (i : Fin m) :
    α₀ i ≠ 0 := by
  classical
  intro hi
  have hli := (linearIndependent_monoidHom (Multiplicative ℕ) ℂ).comp _ (powersHom ℂ).injective
  have e : ∑ w : Sgn m, Finsupp.single (actJ w α₀ i₀) (1 : ℂ) =
      ∑ w : Sgn m, Finsupp.single (actJ w (fun j => (α j : ℂ)) i₀) (1 : ℂ) := by
    refine hli (funext fun k => ?_)
    have := h k.toAdd
    simp only [symJ, monoJ_single] at this
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, powersHom_apply] using this
  have h1 := DFunLike.congr_fun e 0
  rw [Finsupp.finsetSum_apply, Finsupp.finsetSum_apply, Finset.sum_eq_zero (s := Finset.univ)
    (f := fun w : Sgn m => (Finsupp.single (actJ w (fun j => (α j : ℂ)) i₀) (1 : ℂ)) 0) fun w _ =>
      Finsupp.single_eq_of_ne (zpow_ne_zero _ (Units.ne_zero _)).symm] at h1
  simp only [Finsupp.single_apply, Finset.sum_boole, Nat.cast_eq_zero, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff] at h1
  exact h1 (Finset.mem_univ (Equiv.swap i₀ i, 1)) (by simp [actJ, hi])

section Local

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n q : ℕ} {ϖ : L}
  [CompleteSpace L]

theorem ne_zero_of_dosetInd (hU : IsUnramInv ϖ σ q) (α : Fin (n / 2) → ℂˣ) (α₀ : Fin (n / 2) → ℂ)
    (h : ∀ (d : Fin n → ℤ) (t : GU σ n), Antitone d → t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) →
      SatU ϖ q (dosetInd ℂ (KU σ n) t) (fun i => (α i : ℂ)) = SatU ϖ q (dosetInd ℂ (KU σ n) t) α₀)
    (i : Fin (n / 2)) : α₀ i ≠ 0 := by
  classical
  have hq : (q : ℂ) ≠ 0 := by
    have := hU.2.2.2.2.2.1
    exact_mod_cast (by omega : q ≠ 0)
  let x : (Fin (n / 2) → ℤ) → ℂ := fun a => ∏ i, (q : ℂ) ^ (-(a i) * ((n : ℤ) - 1 - 2 * (i.val : ℤ)))
  have hx : ∀ a, x a ≠ 0 := fun a => Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ hq
  have hex : ∀ d : Fin (n / 2) → ℤ, ∃ c : (Fin (n / 2) → ℤ) →₀ ℂ, Dom d →
      ∀ a, c a = x a * cnt σ n ϖ (lab n d) a := fun d => by
    by_cases hd : Dom d
    · exact ⟨Finsupp.ofSupportFinite (fun a => x a * cnt σ n ϖ (lab n d) a)
        ((finite_cnt hU (good_lab hd)).subset fun a ha h0 => ha (by simp [h0])), fun _ _ => rfl⟩
    · exact ⟨0, fun h => absurd h hd⟩
  choose c hc using hex
  have hevJ : ∀ d, Dom d → ∀ γ : Fin (n / 2) → ℂ,
      evJ (c d) γ = SatU ϖ q (labInd σ n ϖ (lab n d)) γ := fun d hd γ => by
    rw [satU_labInd hU (good_lab hd), finsum_eq_sum_of_support_subset (s := (c d).support), evJ]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [hc d hd, Finset.prod_mul_distrib]
      simp only [monoJ, x]
      ring
    · intro a ha
      rw [Finset.mem_coe, Finsupp.mem_support_iff, hc d hd]
      exact mul_ne_zero (hx a) (right_ne_zero_of_mul ha)
  have hcoef : ∀ d, Dom d → ∀ w a, c d (coact w a) = c d a := fun d hd w a => by
    refine coeff_coact (fun γ => ?_) a
    obtain ⟨t, ht⟩ := exists_diag hU (good_lab hd)
    change evJ (c d) (fun i => ((act w γ i : ℂˣ) : ℂ)) = evJ (c d) (fun i => (γ i : ℂ))
    rw [hevJ d hd, hevJ d hd, labInd_eq_dosetInd ht]
    exact (GlobalTheory.LFun.satU_of_weylConj hU (Final.DosetIndMem _ _ _ _) (weylConj_act w γ)).symm
  have hJ : ∀ d, Dom d → evJ (c d) α₀ = evJ (c d) (fun i => (α i : ℂ)) := fun d hd => by
    obtain ⟨t, ht⟩ := exists_diag hU (good_lab hd)
    rw [hevJ d hd, hevJ d hd, labInd_eq_dosetInd ht]
    exact (h _ t (anti_getD (good_lab hd).1 (good_lab hd).2.1) ht).symm
  let T : (Fin (n / 2) → ℤ) → Fin n → ℤ := fun d k => ∑ i ∈ Finset.Ici k, (lab n d).getD i.1 0
  have h2 := eq_zero_of_triangular (fun d => (-∑ k, T d k).toNat) c hcoef (fun d hd => ?_)
    (fun d a hd ha h0 => ?_) (fun a => symJ a α₀ - symJ a fun j => (α j : ℂ))
    (fun w a => by simp only [symJ_coact]) (fun d hd => ?_)
  · have hi0 : 0 < n / 2 := Nat.pos_of_ne_zero fun h0 => (h0 ▸ i).elim0
    refine ne_zero_of_symJ α α₀ ⟨0, hi0⟩ (fun k => sub_eq_zero.1 (h2 _ (dom_single _ rfl k))) i
  · have := cnt_self hU (good_lab hd)
    rw [getD_lab] at this
    rw [hc d hd]
    exact mul_ne_zero (hx d) (by exact_mod_cast this)
  · rw [hc d hd] at h0
    have h1 : ∀ k, T d k ≤ T a k := tail_of_cnt hU (good_lab ha) (good_lab hd) (by
      rw [getD_lab]; exact_mod_cast right_ne_zero_of_mul h0)
    have h2 : ∑ k, T a k ≤ 0 := Finset.sum_nonpos fun k _ => tail_nonpos (good_lab ha) k
    rcases (Finset.sum_le_sum (s := Finset.univ) fun k _ => h1 k).eq_or_lt with e | e
    · have h3 := eq_of_tails fun k => (Finset.sum_eq_sum_iff_of_le fun k _ => h1 k).1 e k (Finset.mem_univ k)
      rw [← getD_lab a, ← getD_lab d, eq_of_getD (good_lab hd).1 (good_lab ha).1 (congrFun h3)]
      exact Or.inl rfl
    · exact Or.inr (by omega)
  · simp only [mul_sub, Finset.sum_sub_distrib, sum_symJ (hcoef d hd), hJ d hd, sub_self]

theorem bcParam_eq_ubc_of_satU_eq : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    (ϖ : L) (σ : L →+* L) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ (α : Fin (n / 2) → ℂˣ) (α₀ : Fin (n / 2) → ℂ),
    (∀ (d : Fin n → ℤ) (t : Formalism.UG.GU σ n), Antitone d → t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) →
      Formalism.UG.SatU ϖ q (Formalism.UG.dosetInd ℂ (Formalism.UG.KU σ n) t) (fun i => (α i : ℂ)) =
        Formalism.UG.SatU ϖ q (Formalism.UG.dosetInd ℂ (Formalism.UG.KU σ n) t) α₀) →
    (GlobalTheory.LGrp.bcParam n α).map (fun a : ℂˣ => (a : ℂ)) = ubc n (Finset.univ.val.map α₀) := by
  intro L _ _ _ ϖ σ q n hU α α₀ h
  let β : Fin (n / 2) → ℂˣ := fun i => Units.mk0 (α₀ i) (ne_zero_of_dosetInd hU α α₀ h i)
  have hβ : (fun i => ((β i : ℂˣ) : ℂ)) = α₀ := funext fun i => Units.val_mk0 _
  have e : bcParam n α = bcParam n β :=
    bcParam_of_weylConj (GlobalTheory.LFun.weylConj_of_dosetInd hU (by rw [hβ]; exact h))
  rw [e, bcParam, ubc]
  simp only [Multiset.map_add (f := _), Multiset.map_map, Function.comp_def, Units.val_inv_eq_inv_val, Multiset.map_replicate,
    Units.val_one]
  rw [← hβ]
  congr 1
  rcases Nat.mod_two_eq_zero_or_one n with h2 | h2
  · rw [h2, if_neg (Nat.not_odd_iff.2 h2)]; rfl
  · rw [h2, if_pos (Nat.odd_iff.2 h2)]; rfl

end Local

end GlobalTheory.SatBcInj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedLocalPairActsOnVacuaByHeisenbergComb
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

theorem locPair_extend_vac : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ φ : M →ₗ[ℂ] M, (∀ s, LocVac ρ s → LocVac ρ (φ s)) → ∃ B : Module.End ℂ M, (∀ x, B * ρ x = ρ x * B) ∧ ∀ s, LocVac ρ s → B s = φ s := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP φ hφ
  classical
  let V : Submodule ℂ M :=
    { carrier := {s | LocVac ρ s}
      add_mem' := by intro a b ha hb u hu; simp [ha u hu, hb u hu]
      zero_mem' := by intro u _; simp
      smul_mem' := by intro c a ha u hu; simp [ha u hu] }
  let T : (Matrix (Fin n') (Fin n) L →₀ V) →ₗ[ℂ] M := Finsupp.lsum ℂ (fun x => ρ x ∘ₗ V.subtype)
  let T' : (Matrix (Fin n') (Fin n) L →₀ V) →ₗ[ℂ] M := Finsupp.lsum ℂ (fun x => ρ x ∘ₗ φ ∘ₗ V.subtype)
  have hT : ∀ d, T d = d.sum fun x v => ρ x (v : M) := fun d => rfl
  have hT' : ∀ d, T' d = d.sum fun x v => ρ x (φ (v : M)) := fun d => rfl
  have hker : LinearMap.ker T ≤ LinearMap.ker T' := by
    intro d hd
    rw [LinearMap.mem_ker] at hd ⊢
    have key := _root_.GlobalTheory.Hk3.locVac_rel_map L ϖ σ q δ n n' JS JT ψ M ρ ω hP φ hφ (d.mapRange V.subtype (map_zero _))
      (fun x => by rw [Finsupp.mapRange_apply]; exact (d x).2)
    rw [Finsupp.sum_mapRange_index (fun x => map_zero _), Finsupp.sum_mapRange_index (fun x => by simp)] at key
    exact key hd
  have hsurj : Function.Surjective T := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hP.span, Submodule.span_le]
    rintro w ⟨x, s, hs, rfl⟩
    exact ⟨Finsupp.single x ⟨s, hs⟩, by rw [hT, Finsupp.sum_single_index (by simp)]⟩
  let B : Module.End ℂ M := (LinearMap.ker T).liftQ T' hker ∘ₗ (T.quotKerEquivOfSurjective hsurj).symm.toLinearMap
  have hB : ∀ d, B (T d) = T' d := by
    intro d
    have : (T.quotKerEquivOfSurjective hsurj).symm (T d) = Submodule.Quotient.mk d := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp only [B, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
  refine ⟨B, fun y => ?_, fun s hs => ?_⟩
  · let c : Matrix (Fin n') (Fin n) L → ℂ := fun x => ψ ((locH σ δ JS JT y x + σ (locH σ δ JS JT y x)) / 2)
    let Sh : (Matrix (Fin n') (Fin n) L →₀ V) →ₗ[ℂ] (Matrix (Fin n') (Fin n) L →₀ V) :=
      Finsupp.lsum ℂ (fun x => c x • Finsupp.lsingle (y + x))
    have h1 : ρ y ∘ₗ T = T ∘ₗ Sh := by
      apply Finsupp.lhom_ext
      intro x v
      simp only [LinearMap.comp_apply, Sh, T, Finsupp.lsum_single, LinearMap.smul_apply, Finsupp.lsingle_apply, map_smul]
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
      rw [← Module.End.mul_apply, hP.rho_mul]
      rfl
    have h2 : ρ y ∘ₗ T' = T' ∘ₗ Sh := by
      apply Finsupp.lhom_ext
      intro x v
      simp only [LinearMap.comp_apply, Sh, T', Finsupp.lsum_single, LinearMap.smul_apply, Finsupp.lsingle_apply, map_smul]
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
      rw [← Module.End.mul_apply, hP.rho_mul]
      rfl
    apply LinearMap.ext
    intro m
    obtain ⟨d, rfl⟩ := hsurj m
    have e1 := LinearMap.congr_fun h1 d
    have e2 := LinearMap.congr_fun h2 d
    simp only [LinearMap.comp_apply] at e1 e2
    rw [Module.End.mul_apply, Module.End.mul_apply, e1, hB, hB, e2]
  · have : T (Finsupp.single 0 ⟨s, hs⟩) = s := by
      rw [hT, Finsupp.sum_single_index (by simp), hP.rho_zero]; rfl
    calc B s = B (T (Finsupp.single 0 ⟨s, hs⟩)) := by rw [this]
      _ = φ s := by rw [hB, hT', Finsupp.sum_single_index (by simp), hP.rho_zero]; rfl

theorem locPair_act_vac_comb : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ p, ∃ c : Matrix (Fin n') (Fin n) L →₀ ℂ, ∀ s, LocVac ρ s → ω p s = c.sum fun x z => z • ρ x s := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP p
  classical
  by_cases h0 : ∃ s0, LocVac ρ s0 ∧ s0 ≠ 0
  swap
  · refine ⟨0, fun s hs => ?_⟩
    have : s = 0 := by by_contra h; exact h0 ⟨s, hs, h⟩
    subst this; simp
  obtain ⟨s0, hs0, hs0ne⟩ := h0

  let N : Subgroup (Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L)) :=
    { carrier := {p | ∀ B : Module.End ℂ M, (∀ x, B * ρ x = ρ x * B) → ω p * B = B * ω p}
      one_mem' := by intro B _; simp
      mul_mem' := by
        intro a b ha hb B hB
        rw [map_mul, mul_assoc, hb B hB, ← mul_assoc, ha B hB, mul_assoc]
      inv_mem' := by
        intro a ha B hB
        have h1 : ω a⁻¹ * ω a = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
        have h2 : ω a * ω a⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
        calc ω a⁻¹ * B = ω a⁻¹ * B * (ω a * ω a⁻¹) := by rw [h2, mul_one]
          _ = ω a⁻¹ * (ω a * B) * ω a⁻¹ := by rw [ha B hB]; noncomm_ring
          _ = B * ω a⁻¹ := by rw [← mul_assoc, h1, one_mul] }
  have hN : N.Normal := by
    constructor
    intro a ha g B hB
    have h1 : ω g⁻¹ * ω g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    have h2 : ω g * ω g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have hB' : ∀ x, (ω g⁻¹ * B * ω g) * ρ x = ρ x * (ω g⁻¹ * B * ω g) := by
      intro x
      have hn := hP.norm g.1 g.2 x
      set y := (((g.2 : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x *
        (((g.1 : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))
      have hn' : ω g * ρ x = ρ y * ω g := hn
      have hinv : ω g⁻¹ * ρ y = ρ x * ω g⁻¹ := by
        calc ω g⁻¹ * ρ y = ω g⁻¹ * ρ y * (ω g * ω g⁻¹) := by rw [h2, mul_one]
          _ = ω g⁻¹ * (ρ y * ω g) * ω g⁻¹ := by noncomm_ring
          _ = ω g⁻¹ * (ω g * ρ x) * ω g⁻¹ := by rw [hn']
          _ = (ω g⁻¹ * ω g) * ρ x * ω g⁻¹ := by noncomm_ring
          _ = ρ x * ω g⁻¹ := by rw [h1, one_mul]
      calc (ω g⁻¹ * B * ω g) * ρ x = ω g⁻¹ * B * (ω g * ρ x) := by noncomm_ring
        _ = ω g⁻¹ * (B * ρ y) * ω g := by rw [hn']; noncomm_ring
        _ = (ω g⁻¹ * ρ y) * B * ω g := by rw [hB y]; noncomm_ring
        _ = ρ x * (ω g⁻¹ * B * ω g) := by rw [hinv]; noncomm_ring
    have ha' := ha _ hB'
    calc ω (g * a * g⁻¹) * B = ω g * ω a * (ω g⁻¹ * B * ω g) * ω g⁻¹ := by
          rw [map_mul, map_mul]
          calc ω g * ω a * ω g⁻¹ * B = ω g * ω a * (ω g⁻¹ * B) * 1 := by noncomm_ring
            _ = _ := by rw [← h2]; noncomm_ring
      _ = ω g * (ω g⁻¹ * B * ω g) * ω a * ω g⁻¹ := by rw [mul_assoc (ω g) (ω a), ha']; noncomm_ring
      _ = (ω g * ω g⁻¹) * B * (ω g * ω a * ω g⁻¹) := by noncomm_ring
      _ = B * ω (g * a * g⁻¹) := by rw [h2, one_mul, map_mul, map_mul]

  have hInt : ∀ (g : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L)) (h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L)),
      (g : GL (Fin n) L) ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
      (g, h) ∈ N := by
    intro g h hg hh B hB
    apply LinearMap.ext_on hP.span
    rintro w ⟨x, s, hs, rfl⟩
    have hBs : ∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) → ρ u (B s) = B s := by
      intro u hu
      have := congrArg (fun F => F s) (hB u)
      simp only [Module.End.mul_apply] at this
      rw [← this, hs u hu]
    have hn := hP.norm g h x
    have e1 := congrArg (fun F => F (B s)) hn
    have e2 := congrArg (fun F => F s) hn
    have e3 := congrArg (fun F => F s) (hB x)
    have e4 := congrArg (fun F => F s) (hB (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x *
        (((g : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)))
    simp only [Module.End.mul_apply] at e1 e2 e3 e4 ⊢
    rw [e3, e1, hP.fix g h hg hh _ hBs, e2, hP.fix g h hg hh _ hs, e4]
  have hTop : N = ⊤ := by
    have hS := _root_.GlobalTheory.NormalHyp.normal_closure_hyp L ϖ σ q n JS hP.unr hP.odd hP.intS hP.hermS (N.comap (MonoidHom.inl _ _)) (hN.comap _)
      (fun g hg => Subgroup.mem_comap.mpr (hInt g 1 hg (by simpa using (Formalism.UG.GLint (Fin n') (Formalism.UG.intL L)).one_mem)))
    have hT := _root_.GlobalTheory.NormalHyp.normal_closure_hyp L ϖ σ q n' JT hP.unr hP.odd hP.intT hP.hermT (N.comap (MonoidHom.inr _ _)) (hN.comap _)
      (fun h hh => Subgroup.mem_comap.mpr (hInt 1 h (by simpa using (Formalism.UG.GLint (Fin n) (Formalism.UG.intL L)).one_mem) hh))
    rw [eq_top_iff]
    rintro ⟨g, h⟩ -
    have hg : (g, (1 : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L))) ∈ N := by
      have : g ∈ N.comap (MonoidHom.inl _ _) := by rw [hS]; trivial
      simpa using this
    have hh : ((1 : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L)), h) ∈ N := by
      have : h ∈ N.comap (MonoidHom.inr _ _) := by rw [hT]; trivial
      simpa using this
    have := N.mul_mem hg hh
    simpa using this
  have hpN : p ∈ N := by rw [hTop]; trivial

  obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ M, f s0 = 1 := by
    have := (Module.forall_dual_apply_eq_zero_iff ℂ s0).not.mpr hs0ne
    push_neg at this
    obtain ⟨f, hf⟩ := this
    exact ⟨(f s0)⁻¹ • f, by simp [hf]⟩
  have hline : ∀ t, LocVac ρ t → ∀ m, LocVac ρ (f.smulRight t m) := by
    intro t ht m u hu
    simp [ht u hu]
  obtain ⟨B0, hB0, hB0v⟩ := locPair_extend_vac L ϖ σ q δ n n' JS JT ψ M ρ ω hP (f.smulRight s0) (fun m _ => hline s0 hs0 m)

  have hspan : ∀ m : M, ∃ c : Matrix (Fin n') (Fin n) L →₀ ℂ, B0 m = c.sum fun x z => z • ρ x s0 := by
    intro m
    have hm : m ∈ Submodule.span ℂ {w | ∃ x s, (∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) → ρ u s = s) ∧ w = ρ x s} := by
      rw [hP.span]; trivial
    induction hm using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨x, s, hs, rfl⟩ := hw
      refine ⟨Finsupp.single x (f s), ?_⟩
      have := congrArg (fun F => F s) (hB0 x)
      simp only [Module.End.mul_apply] at this
      rw [this, hB0v s hs]
      simp
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨ca, hca⟩ := ha
      obtain ⟨cb, hcb⟩ := hb
      refine ⟨ca + cb, ?_⟩
      rw [map_add (f := _), hca, hcb, Finsupp.sum_add_index']
      · intro x; simp
      · intro x z z'; rw [add_smul]
    | smul a b _ hb =>
      obtain ⟨cb, hcb⟩ := hb
      refine ⟨a • cb, ?_⟩
      rw [map_smul, hcb, Finsupp.sum_smul_index' (h := fun x z => z • ρ x s0) (fun _ => zero_smul ℂ _), Finsupp.smul_sum]
      simp [Finsupp.sum, Finset.smul_sum, smul_smul]
  obtain ⟨c, hc⟩ := hspan (ω p s0)
  have hps0 : ω p s0 = c.sum fun x z => z • ρ x s0 := by
    have e := congrArg (fun F => F s0) (hpN B0 hB0)
    simp only [Module.End.mul_apply] at e
    rw [← hc, ← e, hB0v s0 hs0]
    simp [hf]
  refine ⟨c, fun s hs => ?_⟩
  obtain ⟨Bs, hBs, hBsv⟩ := locPair_extend_vac L ϖ σ q δ n n' JS JT ψ M ρ ω hP (f.smulRight s) (fun m _ => hline s hs m)
  have e1 : Bs s0 = s := by rw [hBsv s0 hs0]; simp [hf]
  have e := congrArg (fun F => F s0) (hpN Bs hBs)
  simp only [Module.End.mul_apply] at e
  rw [← e1, e, hps0, map_finsuppSum]
  refine Finsupp.sum_congr fun x _ => ?_
  have := congrArg (fun F => F s0) (hBs x)
  simp only [Module.End.mul_apply] at this
  rw [map_smul, this]

end GlobalTheory.Hk3
end

