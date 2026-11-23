module

public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0597
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0608
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0584
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.InductionG11
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace GeneralLinearInduction

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {ψ : AddChar (Ad E) ℂ}

theorem step (hψ : StdPsi ψ) (m : ℕ) (f : GA E a → ℂ) (hma : m + 1 < a) (hG : Good ψ (m + 1) f)
    (Z : Set (GA E a)) (hZ : ∀ γ, IsMir (m + 1) γ → ∀ g ∈ Z, ratGL E a γ * g ∈ Z)
    (hc : ∀ g ∈ Z, colT ψ (m + 1) f g = 0) : ∀ g ∈ Z, f g = 0 := by
  intro g₀ hg
  have hPer : Per (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1))) (fun x => f (blkU x * g₀)) :=
    per_blk hG.cont (fun c g => hG.left _ (isMir_blkU c) g) g₀
  have hΦ : (fun x : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E => f (blkU x * g₀)) = 0 := by
    refine _root_.GlobalTheory.CuspGeneric.eq_zero_of_avg_character_eq_zero E _ ψ hψ _ hPer fun ξ => ?_
    by_cases hξ0 : ξ = 0
    · subst hξ0
      have hv := hG.van (m + 1) (Nat.succ_pos m) le_rfl g₀
      have e : ∀ x : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E,
          ψ (-dot (0 : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E) x) = 1 := by
        intro x
        simp [dot]
      simp only [e, one_mul]
      exact hv
    · obtain ⟨γ, hγ, hγξ⟩ := _root_.GlobalTheory.CuspGeneric.mir_exists_row E a m hma ξ hξ0
      have h1 := hc _ (hZ γ hγ g₀ hg)
      simp only [colT] at h1
      rw [_root_.GlobalTheory.CuspGeneric.coefF_ratGL_mul E a ψ hψ m f hG.cont hG.left γ hγ (eLast a (m + 1)) g₀] at h1
      have e : (fun t : UnipotentBlockColumnIndex a (m + 1) (m + 1) =>
          ∑ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), eLast a (m + 1) s * γ.val s.1.1 t.1.1) = ξ := funext hγξ
      rw [e] at h1
      exact h1
  have h1 := congrFun hΦ 0
  simp only [Pi.zero_apply] at h1
  have e : (blkU (0 : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) : GA E a) = 1 := posU_zero _
  rw [e, one_mul] at h1
  exact h1

theorem main (hψ : StdPsi ψ) (m : ℕ) : ∀ (f : GA E a → ℂ), (m < a ∨ m = 0) → Good ψ m f →
    ∀ Z : Set (GA E a), (∀ γ, IsMir m γ → ∀ g ∈ Z, ratGL E a γ * g ∈ Z) →
      (∀ g ∈ Z, whit ψ m f g = 0) → ∀ g ∈ Z, f g = 0 := by
  induction m with
  | zero => intro f _ _ Z _ hw; exact hw
  | succ m ih =>
    intro f hm hG Z hZ hw
    have hma : m + 1 < a := by omega
    refine step hψ m f hma hG Z hZ ?_
    refine ih _ (Or.inl (by omega)) (_root_.GlobalTheory.CuspRep.Generic.good_colT hψ hma hG) Z
      (fun γ hγ g hg => hZ γ (fun i k h => hγ i k (by omega)) g hg) ?_
    intro g hg
    exact hw g hg

end GeneralLinearInduction

theorem induction_g11_holds : FourierUniquenessMirabolic := by
  intro E _ _ _ a ψ hψ m f hm hG Z hZ _ hw
  exact GeneralLinearInduction.main hψ m f hm hG Z hZ hw

end PositivityTheory.jumpWindows

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.InfiniteFiniteFactorization
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace InfiniteFiniteFactorization

open Classical

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem stepInf (h6 : G6) {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) {S : Finset (Pl E)}
    {Y Y' : Submodule ℂ (XB E a)} (hY : YOK ψ S Y) (hY' : YOK ψ S Y') (m : Pl E → ℕ)
    (h : St ψ S Y Y' 0 m) : ∀ n, n ≤ a - 1 → St ψ S Y Y' n m := by
  intro n
  induction n with
  | zero => intro _; exact h
  | succ n ih => intro hn; exact h6 E a ψ hψ S Y Y' hY hY' n m (by omega) (ih (by omega))

theorem stepFin (h7 : G7) {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) {S : Finset (Pl E)}
    {Y Y' : Submodule ℂ (XB E a)} (hY : YOK ψ S Y) (hY' : YOK ψ S Y') (w : Pl E) (hw : w ∈ S)
    (n : ℕ) (m : Pl E → ℕ) (hm : m w = 0) (h : St ψ S Y Y' n m) :
    ∀ k, k ≤ a - 1 → St ψ S Y Y' n (Function.update m w k) := by
  intro k
  induction k with
  | zero => intro _; rw [Function.update_eq_self_iff.mpr hm.symm]; exact h
  | succ k ih =>
    intro hk
    have h' := h7 E a ψ hψ S Y Y' hY hY' n (Function.update m w k) w hw
      (by simp only [Function.update_self]; omega) (ih (by omega))
    simpa only [Function.update_self, Function.update_idem] using h'

end InfiniteFiniteFactorization

open InfiniteFiniteFactorization in
theorem whittaker_factorization_places : G6 → G7 → FourierInductionSteps := by
  classical
  intro h6 h7 E _ _ _ a ψ hψ S Y Y' hY hY' h0
  have h1 := stepInf h6 hψ hY hY' (fun _ => 0) h0 (a - 1) le_rfl
  have key : ∀ T : Finset (Pl E), T ⊆ S →
      St ψ S Y Y' (a - 1) (fun w => if w ∈ T then a - 1 else 0) := by
    intro T
    refine Finset.induction_on T ?_ ?_
    · intro _
      simpa using h1
    · intro x T hx ih hT
      have h := stepFin h7 hψ hY hY' x (hT (Finset.mem_insert_self x T)) (a - 1)
        (fun w => if w ∈ T then a - 1 else 0) (by simp [hx])
        (ih (subset_trans (Finset.subset_insert x T) hT)) (a - 1) le_rfl
      convert h using 1
      funext w
      by_cases hw : w = x
      · subst hw; simp
      · simp [hw]
  exact key S subset_rfl

end PositivityTheory.jumpWindows

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.MirrorMap
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace MirrorMap

theorem mir_map {R S : Type} [CommRing R] [CommRing S] {a m : ℕ} (p : R →+* S) {γ : GL (Fin a) R}
    (h : Mir m γ) : Mir m (GeneralLinearGroup.map p γ) := by
  intro i k hik
  change p (γ.val i k) = _
  rw [h i k hik, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem mirS_mul (h10 : MirabolicColumnBlock) {S : Finset (Pl E)} {x g : GA E a} (hx : Mir (a - 1) x) (hg : MirS S g) :
    MirS S (x * g) := by
  refine ⟨?_, fun w hw => ?_⟩
  · rw [map_mul]
    exact (h10 _ a (a - 1)).2.2.2.2.1 _ _ (mir_map (pInf E) hx) hg.1
  · rw [map_mul]
    exact (h10 _ a (a - 1)).2.2.2.2.1 _ _ (mir_map ((pLoc E w).comp (pFin E)) hx) (hg.2 w hw)

end MirrorMap

theorem mirror_global_of : MirabolicColumnBlock → G0 → G5 → G9 → PlacewiseToOutsideS → FourierUniquenessMirabolic → WeakApproximationGL → WhittakerVanishingImpliesZero := by
  intro h10 h0 h5 h9 h9b h11 h12 E _ _ _ a ψ hψ S hcond φ hgood hleft hsat hvan
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hproj, -⟩ := h0 E a
  have hcont : Continuous (Wh ψ φ) := ((h5 E a ψ hψ).2.2.2 φ hgood).1
  have step1 : ∀ g, MirS S g → Wh ψ φ g = 0 := by
    intro g hg
    obtain ⟨g₀, e1, e2, e3⟩ := hproj S g
    refine h9b E a S (Wh ψ φ) hcont ?_ g g₀ e1 e2 e3 ?_
    · intro w hw h hh hz u
      obtain ⟨B, hB⟩ := hsat w hw
      exact h9 E a ψ hψ w (hcond w hw) B φ hgood hB h hh hz u
    · refine hvan g₀ ⟨?_, fun w hw => ?_⟩ e3
      · rw [e1]; exact hg.1
      · rw [e2 w hw]; exact hg.2 w hw
  have step2 : ∀ g, MirS S g → φ g = 0 := by
    intro g hg
    refine h11 E a ψ hψ (a - 1) φ (by omega) hgood {g | MirS S g} ?_ ?_ step1 g hg
    · intro γ hγ g hg
      exact MirrorMap.mirS_mul h10 (MirrorMap.mir_map (algebraMap E (Ad E)) hγ) hg
    · intro k hk y g hg
      exact MirrorMap.mirS_mul h10 ((h10 (Ad E) a (a - 1)).2.2.2.2.2.1 k y hk) hg
  have hEq : (⇑φ) = fun _ => (0 : ℂ) := by
    refine Continuous.ext_on (h12 E a S) φ.continuous continuous_const ?_
    rintro x ⟨γ, g, rfl, hg1, hg2⟩
    show φ (ratGL E a γ * g) = 0
    rw [hleft]
    refine step2 g ⟨?_, fun w hw => ?_⟩
    · rw [hg1]; exact (h10 _ a (a - 1)).2.2.1
    · rw [hg2 w hw]; exact (h10 _ a (a - 1)).2.2.1
  ext x
  simpa using congrFun hEq x

end PositivityTheory.jumpWindows

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.SmoothVectorOrbit
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace SmoothVectorOrbit

theorem orb_smul {ι : Type} [Fintype ι] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) (c : ℂ) (v : X) :
    orb ρ (c • v) = c • orb ρ v := by
  funext M
  simp only [PositivityTheory.jumpWindows.orb, Pi.smul_apply]
  split_ifs <;> simp

theorem smV_smul {ι : Type} [Fintype ι] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) (c : ℂ) (v : X) (h : SmV ρ v) : SmV ρ (c • v) := by
  unfold PositivityTheory.jumpWindows.SmV at h ⊢
  rw [PositivityTheory.jumpWindows.SmoothVectorOrbit.orb_smul]
  exact h.const_smul c

end SmoothVectorOrbit

theorem smooth_vector_orbit_invariance : G0 → G5 → G5b → G9 → PlacewiseToOutsideS → G8 := by
  intro hAC hSW hSP hWS hWV
  unfold PositivityTheory.jumpWindows.G8 PositivityTheory.jumpWindows.ForE
  intro E _ _ _ a ψ hψ S hS Y hY φ hφY hφ0 hφsm hφsph hφeig
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hreg, -⟩ := hAC E a
  obtain ⟨hΛ, htr, -, hW⟩ := hSW E a ψ hψ
  obtain ⟨hsmooth, hsph, hsph_smul, -, -⟩ := hSP E a S
  obtain ⟨-, hYtr, hYmir⟩ := hY
  obtain ⟨hWcont, hWne, -⟩ := hW φ (hYmir φ hφY)
  obtain ⟨g, hg⟩ := hWne hφ0
  obtain ⟨g₀, harch, hloc, hsupp⟩ := hreg S g
  have hg₀ : PositivityTheory.jumpWindows.Wh ψ φ g₀ ≠ 0 := by
    intro h0
    refine hg (hWV E a S _ hWcont ?_ g g₀ harch hloc hsupp h0)
    intro w hw h hh h0' u
    obtain ⟨B, hB⟩ := hφeig w hw
    exact hWS E a ψ hψ w (hS w hw) B φ (hYmir φ hφY) hB h hh h0' u
  have hφ'Y : PositivityTheory.jumpWindows.Rt E a g₀ φ ∈ Y := hYtr g₀ hsupp φ hφY
  have hW1 : PositivityTheory.jumpWindows.Wh ψ (PositivityTheory.jumpWindows.Rt E a g₀ φ) 1 ≠ 0 := by
    rw [htr, one_mul]
    exact hg₀
  refine ⟨(PositivityTheory.jumpWindows.Wh ψ (PositivityTheory.jumpWindows.Rt E a g₀ φ) 1)⁻¹ •
      PositivityTheory.jumpWindows.Rt E a g₀ φ, Y.smul_mem _ hφ'Y, ?_, ?_, ?_⟩
  · exact PositivityTheory.jumpWindows.SmoothVectorOrbit.smV_smul _ _ _ (hsmooth g₀ φ hφsm)
  · exact hsph_smul _ _ (hsph g₀ φ hφsph)
  · obtain ⟨Λ, hΛ1⟩ := hΛ 1
    rw [← hΛ1 _ (hYmir _ (Y.smul_mem _ hφ'Y)), map_smul, hΛ1 _ (hYmir _ hφ'Y), smul_eq_mul,
      inv_mul_cancel₀ hW1]

end PositivityTheory.jumpWindows

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.UnipotentCharacter
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace UnipotentCharacter

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def chi (ψ : AddChar (Ad E) ℂ) (w : Pl E) : AddChar (w.adicCompletion E) ℂ where
  toFun y := ψ (sFin E (sLoc E w y))
  map_zero_eq_one' := by simp only [map_zero, AddChar.map_zero_eq_one]
  map_add_eq_mul' x y := by simp only [map_add (f := _), AddChar.map_add_eq_mul]

theorem chi_apply (ψ : AddChar (Ad E) ℂ) (w : Pl E) (y : w.adicCompletion E) :
    chi ψ w y = ψ (sFin E (sLoc E w y)) := rfl

theorem chi_cont {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (w : Pl E) : Continuous (chi ψ w) :=
  hψ.cont.comp ((continuous_const.prodMk continuous_id : Continuous fun x : Af E =>
    ((0, x) : InfiniteAdeleRing E × Af E)).comp (CuspSub.continuous_sLoc w))

theorem lastE_loc (w : Pl E) {k : ℕ} (y : UnipotentBlockColumnIndex a k k → w.adicCompletion E) :
    lastE k (fun t => sFin E (sLoc E w (y t))) = sFin E (sLoc E w (lastE k y)) := by
  unfold lastE
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> simp

theorem sum_of {X : Type} [AddCommMonoid X] [Module ℂ X] (P : X → Prop) (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y)) (hsm : ∀ (c : ℂ) x, P x → P (c • x)) {ι : Type}
    (T : Finset ι) (c : ι → ℂ) (f : ι → X) (hf : ∀ t, P (f t)) : P (∑ t ∈ T, c t • f t) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using h0
  | insert t T ht ih => rw [Finset.sum_insert ht]; exact hadd _ _ (hsm _ _ (hf t)) ih

end UnipotentCharacter

open UnipotentCharacter in
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
theorem whittaker_expansion_cuspidal : S2 → S9 → MirabolicColumnBlock → G0 → G5 → G5b → G7 := by
  intro hS2 hS9 hS10 hG0 hG5 hG5b E _ _ _ a ψ hψ S Y Y' hY hY' n m w hw hmw hSt
  obtain ⟨φ, hφY, φ', hφY', hsm, hsm', hlev, hlev', h1, hWh⟩ := hSt
  obtain ⟨-, -, i3, i4, i5, -, -, i8, -, i10, -⟩ := hG0 E a
  obtain ⟨g5a, g5r, -, g5c⟩ := hG5 E a ψ hψ
  obtain ⟨b1, b2, b3, b4, b5⟩ := hG5b E a S
  obtain ⟨s10dec, -, -, s10blk1, -⟩ := hS10 (w.adicCompletion E) a (m w + 1)
  have hpoly : PolyBd (repI E a) := ⟨1, 0, zero_le_one, fun g x => by
    rw [pow_zero, mul_one, one_mul]
    exact le_of_eq (norm_Rt (infGL E a g) x)⟩
  obtain ⟨s0, sadd, ssmul, -, -, -⟩ := hS2 (InfinitePlace E) a (XB E a) (repI E a) hpoly
  let U : Set (GL (Fin a) (w.adicCompletion E)) := {u | repW a w u φ = φ} ∩ {u | repW a w u φ' = φ'}
  have hU : U ∈ 𝓝 (1 : GL (Fin a) (w.adicCompletion E)) := Filter.inter_mem (hlev w hw) (hlev' w hw)
  have hne : ∃ x, chi ψ w x ≠ 1 := by
    obtain ⟨y, hy⟩ := hψ.loc w
    exact ⟨y, hy⟩
  obtain ⟨T, c, η, r, hη1, hr1, hrMir, -, -, hmain⟩ :=
    hS9 (w.adicCompletion E) a (m w) hmw (chi ψ w) (chi_cont hψ w) hne (XB E a) (repW a w) U hU
  have inS : ∀ u, InS S (fl a w u : GA E a) := fun u v hv => i5 w v u (fun e => hv (e ▸ hw))
  have stab : ∀ Z : Submodule ℂ (XB E a), YOK ψ S Z → ∀ u, ∀ x ∈ Z, repW a w u x ∈ Z :=
    fun Z hZ u x hx => hZ.stable _ (inS u) x hx
  have memZ : ∀ Z : Submodule ℂ (XB E a), YOK ψ S Z → ∀ x ∈ Z, ∑ t ∈ T, c t • repW a w t x ∈ Z :=
    fun Z hZ x hx => Z.sum_mem fun t _ => Z.smul_mem _ (stab Z hZ t x hx)
  have smZ : ∀ x : XB E a, SmV (repI E a) x → SmV (repI E a) (∑ t ∈ T, c t • repW a w t x) :=
    fun x hx => sum_of _ s0 sadd ssmul T c _ fun t => b1 _ x hx
  have levZ : ∀ x : XB E a, Lev S x → Lev S (∑ t ∈ T, c t • repW a w t x) :=
    fun x hx => sum_of _ b5 b4 b3 T c _ fun t => b2 _ x hx

  have key : ∀ Z : Submodule ℂ (XB E a), YOK ψ S Z → ∀ x ∈ Z, (∀ u ∈ U, repW a w u x = x) →
      ∀ g' : GA E a, cLoc w g' = 1 → ∀ h, GlobalTheory (m w + 1) h →
      Wh ψ (∑ t ∈ T, c t • repW a w t x) (g' * fl a w h) = η h * Wh ψ x (g' * fl a w (r h)) := by
    intro Z hZ x hx hxU g' hg' h hh
    obtain ⟨Λ, hΛ⟩ := g5a g'
    have hcond : ∀ z ∈ Z, ∀ y : UnipotentBlockColumnIndex a (m w + 1) (m w + 1) → w.adicCompletion E,
        (Λ : XB E a →ₗ[ℂ] ℂ) (repW a w (blkU y) z) = chi ψ w (lastE (m w + 1) y) * (Λ : XB E a →ₗ[ℂ] ℂ) z := by
      intro z hz y
      show Λ _ = _ * Λ _
      rw [hΛ _ (hZ.good _ (stab Z hZ _ z hz)),
        hΛ _ (hZ.good _ hz), repW_apply, g5r, i8 w g' hg', i10,
        (g5c z (hZ.good _ hz)).2.2 (m w + 1) (Nat.succ_pos _), lastE_loc, chi_apply]
    have := hmain x hxU Z (stab Z hZ) hx (Λ : XB E a →ₗ[ℂ] ℂ) hcond h hh
    change Λ _ = η h * Λ _ at this
    rw [hΛ _ (hZ.good _ (stab Z hZ _ _ (memZ Z hZ x hx))), hΛ _ (hZ.good _ (stab Z hZ _ _ hx)),
      repW_apply, repW_apply, g5r, g5r] at this
    exact this
  refine ⟨_, memZ Y hY φ hφY, _, memZ Y' hY' φ' hφY', smZ φ hsm, smZ φ' hsm', levZ φ hlev, levZ φ' hlev', ?_, ?_⟩
  · have := key Y hY φ hφY (fun u hu => hu.1) 1 (map_one _) 1 s10blk1
    rw [hr1] at this
    simp only [map_one, mul_one] at this
    rw [this]
    exact mul_ne_zero hη1 h1
  · intro g hg
    obtain ⟨hgI, hgL⟩ := hg
    have hgw : Mir (m w + 1) (cLoc w g) := by simpa using hgL w
    obtain ⟨y, h, hh, hdec⟩ := s10dec _ hgw
    set g' : GA E a := g * (fl a w (cLoc w g))⁻¹ with hg'def
    have hg' : cLoc w g' = 1 := by rw [hg'def, map_mul, map_inv, i4, mul_inv_cancel]
    have red : ∀ Z : Submodule ℂ (XB E a), YOK ψ S Z → ∀ x ∈ Z, (∀ u ∈ U, repW a w u x = x) →
        Wh ψ (∑ t ∈ T, c t • repW a w t x) g =
          ψ (lastE (m w + 1) fun t => sFin E (sLoc E w (y t))) * (η h * Wh ψ x (g' * fl a w (r h))) := by
      intro Z hZ x hx hxU
      have e : g = blkU (fun t => sFin E (sLoc E w (y t))) * (g' * fl a w h) := by
        rw [← i10, ← mul_assoc, ← i8 w g' hg', mul_assoc, ← map_mul, ← hdec, hg'def, inv_mul_cancel_right]
      rw [e, (g5c _ (hZ.good _ (memZ Z hZ x hx))).2.2 (m w + 1) (Nat.succ_pos _), key Z hZ x hx hxU g' hg' h hh]
    rw [red Y hY φ hφY (fun u hu => hu.1), red Y' hY' φ' hφY' (fun u hu => hu.2)]
    by_cases hη : η h = 0
    · rw [hη]; simp
    congr 2
    refine hWh _ ⟨?_, fun v => ?_⟩
    · rw [map_mul, hg'def, map_mul, map_inv, i3, i3, inv_one, mul_one, mul_one]
      exact hgI
    · rcases eq_or_ne v w with rfl | hv
      · rw [map_mul, hg', i4, one_mul]
        exact hrMir h hh hη
      · rw [map_mul, hg'def, map_mul, map_inv, i5 w v _ hv, i5 w v _ hv, inv_one, mul_one, mul_one]
        simpa [hv] using hgL v

end PositivityTheory.jumpWindows

end
end

