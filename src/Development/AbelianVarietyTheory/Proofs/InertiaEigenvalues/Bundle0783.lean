module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0675
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0773
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0635
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0312
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0475
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0194
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0311

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceInvariantFormsSeparateThetaFunctions
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

namespace GlobalTheory.DownLift.SplitSep

open GlobalTheory.SplitScalar

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem symplO_nsmul_left (k : ℕ) (x y : WO S T) : symplO S T (k • x) y = k • symplO S T x y := by
  induction k with
  | zero => rw [zero_nsmul, zero_nsmul, symplO_zero_left]
  | succ n ih => rw [succ_nsmul, succ_nsmul, GlobalTheory.LatVac.symplO_add_left, ih]

theorem symplO_nsmul_swap (k : ℕ) (x y : WO S T) : symplO S T (k • x) y = symplO S T x (k • y) := by
  rw [symplO_nsmul_left, symplO_skew S T (k • y) x, symplO_nsmul_left, symplO_skew S T x y, neg_nsmul, neg_neg]

theorem symplO_neg_left (x y : WO S T) : symplO S T (-x) y = -symplO S T x y := by
  have h := symplO_sub_left S T 0 x y
  rwa [zero_sub, symplO_zero_left, zero_sub] at h

theorem nsmul_smul_comm (k : ℕ) (a : AE D) (v : WO S T) : k • (a • v) = a • (k • v) := by
  induction k with
  | zero => rw [zero_nsmul, zero_nsmul, smul_zero]
  | succ n ih => rw [succ_nsmul, succ_nsmul, smul_add, ih]

theorem isHalf_neg' {m n : ℕ} {e : AE D} {u : Mx D m n} (hu : IsHalf e u) : IsHalf e (-u) := by
  rw [isHalf_iff] at *
  rw [smul_neg, hu]

theorem smul_eq_zero_of_half_conj {a : AE D} (ha : IsSplitIdem D a) {u : WO S T} (hu : IsHalf (cA D a) u) :
    a • u = 0 := by
  rw [← (isHalf_iff _ _).1 hu, smul_smul, ha.2.1, zero_smul]

theorem conj_smul_eq_zero_of_half {a : AE D} (ha : IsSplitIdem D a) {u : WO S T} (hu : IsHalf a u) :
    cA D a • u = 0 := by
  rw [← (isHalf_iff _ _).1 hu, smul_smul, mul_comm, ha.2.1, zero_smul]

theorem exists_nsmul_subgroup (Λ : AddSubgroup (WO S T)) (k : ℕ) :
    ∃ K : AddSubgroup (WO S T), ∀ d, d ∈ K ↔ ∃ v ∈ Λ, d = k • v := by
  refine ⟨{ carrier := {d | ∃ v ∈ Λ, d = k • v}
            add_mem' := ?_, zero_mem' := ?_, neg_mem' := ?_ }, fun d => Iff.rfl⟩
  · rintro u w ⟨v, hv, rfl⟩ ⟨v', hv', rfl⟩
    exact ⟨v + v', add_mem hv hv', by rw [nsmul_add]⟩
  · exact ⟨0, zero_mem _, by rw [nsmul_zero]⟩
  · rintro u ⟨v, hv, rfl⟩
    exact ⟨-v, neg_mem hv, by rw [neg_nsmul]⟩

theorem exists_mixed_subgroup {a : AE D} (ha : IsSplitIdem D a) (Λ : AddSubgroup (WO S T)) (k : ℕ) :
    ∃ Λ' : AddSubgroup (WO S T), (∀ u, IsHalf a u → (u ∈ Λ' ↔ ∃ v ∈ Λ, u = k • v)) ∧
      ∀ u, IsHalf (cA D a) u → (u ∈ Λ' ↔ k • u ∈ Λ) := by
  obtain ⟨Λ', hΛ'⟩ : ∃ Λ' : AddSubgroup (WO S T),
      ∀ u, u ∈ Λ' ↔ (∃ v ∈ Λ, a • u = k • v) ∧ k • (cA D a • u) ∈ Λ := by
    refine ⟨{ carrier := {u | (∃ v ∈ Λ, a • u = k • v) ∧ k • (cA D a • u) ∈ Λ}
              add_mem' := ?_, zero_mem' := ?_, neg_mem' := ?_ }, fun u => Iff.rfl⟩
    · rintro u w ⟨⟨v, hv, huv⟩, hu⟩ ⟨⟨v', hv', hwv⟩, hw⟩
      refine ⟨⟨v + v', add_mem hv hv', by rw [smul_add, huv, hwv, nsmul_add]⟩, ?_⟩
      rw [smul_add, nsmul_add]
      exact add_mem hu hw
    · refine ⟨⟨0, zero_mem _, by rw [smul_zero, nsmul_zero]⟩, ?_⟩
      rw [smul_zero, nsmul_zero]
      exact zero_mem _
    · rintro u ⟨⟨v, hv, huv⟩, hu⟩
      refine ⟨⟨-v, neg_mem hv, by rw [smul_neg, huv, neg_nsmul]⟩, ?_⟩
      rw [smul_neg, neg_nsmul]
      exact neg_mem hu
  refine ⟨Λ', fun u hu => ?_, fun u hu => ?_⟩
  · rw [hΛ', (isHalf_iff _ _).1 hu, conj_smul_eq_zero_of_half ha hu, nsmul_zero]
    exact ⟨fun h => h.1, fun h => ⟨h, zero_mem _⟩⟩
  · have h0 : a • u = 0 := smul_eq_zero_of_half_conj ha hu
    have h1 : cA D a • u = u := (isHalf_iff _ _).1 hu
    rw [hΛ']
    constructor
    · rintro ⟨-, h⟩
      rwa [h1] at h
    · intro h
      exact ⟨⟨0, zero_mem _, by rw [h0, nsmul_zero]⟩, by rwa [h1]⟩

theorem rep_half {e : AE D} (he : e * e = e) {Λ : AddSubgroup (WO S T)} (hstab : ∀ u ∈ Λ, e • u ∈ Λ) {k : ℕ}
    {d : WO S T} (hd : IsHalf e d) (h : ∃ v ∈ Λ, d = k • v) : ∃ v ∈ Λ, IsHalf e v ∧ d = k • v := by
  obtain ⟨v, hv, h⟩ := h
  exact ⟨e • v, hstab v hv, isHalf_smul he v, by rw [nsmul_smul_comm, ← h, (isHalf_iff _ _).1 hd]⟩

theorem sum_average {a : AE D} (ha : IsSplitIdem D a) {Λ : AddSubgroup (WO S T)} {k : ℕ} {f : WO S T → ℂ}
    (hfix : ∀ u ∈ Λ, IsHalf (cA D a) u → heisO ψ S T (k • u) f = f)
    {Y X : Finset (WO S T)}
    (hY : ∀ y ∈ Y, IsHalf (cA D a) y ∧ k • y ∈ Λ)
    (hYu : ∀ y', IsHalf (cA D a) y' → k • y' ∈ Λ →
      ∃! y, y ∈ Y ∧ ∃ u ∈ Λ, IsHalf (cA D a) u ∧ y' - y = k • u)
    (hX : ∀ x ∈ X, IsHalf a x)
    (hXo : ∀ y, IsHalf (cA D a) y → k • y ∈ Λ →
      ((∃ u ∈ Λ, IsHalf (cA D a) u ∧ y = k • u) → ∀ x ∈ X, ψ (symplO S T y x) = 1) ∧
      ((¬ ∃ u ∈ Λ, IsHalf (cA D a) u ∧ y = k • u) → ∑ x ∈ X, ψ (symplO S T y x) = 0)) :
    ∑ x ∈ X, heisO ψ S T (-x) (∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f)) = (X.card : ℂ) • f := by
  have e1 : ∀ x ∈ X, heisO ψ S T (-x) (∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f)) =
      ∑ y ∈ Y, ψ (symplO S T y x) • heisO ψ S T y f := by
    intro x hx
    rw [heisO_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [heisO_comm, ← heisO_add_of_orth ψ S T (half_orth ha (isHalf_neg' (hX x hx)) (hX x hx)),
      neg_add_cancel, heisO_zero, symplO_neg_left, ← symplO_skew]
  rw [Finset.sum_congr rfl e1, Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  obtain ⟨y₀, ⟨hy₀Y, u₀, hu₀, hu₀h, hy₀⟩, huniq⟩ :=
    hYu 0 (isHalf_zero _) (by rw [nsmul_zero]; exact zero_mem _)
  rw [Finset.sum_eq_single_of_mem y₀ hy₀Y]
  · have hy₀' : y₀ = k • (-u₀) := by rw [neg_nsmul, ← hy₀, zero_sub, neg_neg]
    have hyy : ∃ u ∈ Λ, IsHalf (cA D a) u ∧ y₀ = k • u := ⟨-u₀, neg_mem hu₀, isHalf_neg' hu₀h, hy₀'⟩
    rw [Finset.sum_congr rfl ((hXo y₀ (hY y₀ hy₀Y).1 (hY y₀ hy₀Y).2).1 hyy), Finset.sum_const, nsmul_eq_mul,
      mul_one, hy₀', hfix _ (neg_mem hu₀) (isHalf_neg' hu₀h)]
  · intro y hy hne
    have hnot : ¬ ∃ u ∈ Λ, IsHalf (cA D a) u ∧ y = k • u := by
      rintro ⟨u, hu, huh, rfl⟩
      exact hne (huniq _ ⟨hy, -u, neg_mem hu, isHalf_neg' huh, by rw [zero_sub, neg_nsmul]⟩)
    rw [(hXo y (hY y hy).1 (hY y hy).2).2 hnot, zero_smul]

theorem sum_translates_eq_zero {a : AE D} (ha : IsSplitIdem D a) (hψ : IsStdChar D ψ (-1)) {Λ : AddSubgroup (WO S T)}
    (hdual : ∀ u : WO S T, u.map (infPart D) = 0 → (u ∈ Λ ↔ ∀ u' ∈ Λ, ψ (symplO S T u u') = 1))
    (hpair : ∀ u ∈ Λ, ∀ u' ∈ Λ, ψ (symplO S T u u') = 1)
    (hstab : ∀ e : AE D, e * e = e → ∀ u ∈ Λ, e • u ∈ Λ)
    {k : ℕ} {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hfix : ∀ u ∈ Λ, IsHalf a u ∨ IsHalf (cA D a) u → heisO ψ S T (k • u) f = f)
    {Y : Finset (WO S T)}
    (hY : ∀ y ∈ Y, IsHalf (cA D a) y ∧ k • y ∈ Λ)
    (hYu : ∀ y', IsHalf (cA D a) y' → k • y' ∈ Λ →
      ∃! y, y ∈ Y ∧ ∃ u ∈ Λ, IsHalf (cA D a) u ∧ y' - y = k • u)
    (hℓ : ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x → ℓ (heisO ψ S T x f) = 0)
    {x : WO S T} (hxa : IsHalf a x) (hkx : k • x ∈ Λ) :
    ∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f) = 0 := by
  have ha' := isSplitIdem_conj ha
  have hcc : cA D (cA D a) = a := GlobalTheory.DualPairCheck.cA_cA a
  obtain ⟨K, hK⟩ := exists_nsmul_subgroup Λ k
  obtain ⟨Λ', memA, memC⟩ := exists_mixed_subgroup ha Λ k
  have hYK : ∀ u', IsHalf (cA D a) u' → k • u' ∈ Λ → ∃! v, v ∈ Y ∧ u' - v ∈ K := by
    intro u' hu' hku'
    obtain ⟨y, ⟨hyY, w, hw, -, hyw⟩, huniq⟩ := hYu u' hu' hku'
    refine ⟨y, ⟨hyY, (hK _).2 ⟨w, hw, hyw⟩⟩, fun y' hy' => huniq y' ⟨hy'.1, ?_⟩⟩
    exact rep_half ha'.1 (hstab _ ha'.1) (isHalf_sub hu' (hY y' hy'.1).1) ((hK _).1 hy'.2)
  by_contra hn
  have hfx : IsThetaFunO ψ S T (heisO ψ S T x f) := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf x
  have hGx : ∀ d, IsHalf (cA D a) d → d ∈ K → heisO ψ S T d (heisO ψ S T x f) = heisO ψ S T x f := by
    intro d hdh hdK
    obtain ⟨v, hv, hvh, rfl⟩ := rep_half ha'.1 (hstab _ ha'.1) hdh ((hK d).1 hdK)
    rw [heisO_comm, symplO_nsmul_swap, hpair v hv _ hkx, one_smul, hfix v hv (Or.inr hvh)]
  have hd : ∀ y, IsHalf (cA D a) y → y ∉ Λ' → ∃ l ∈ Λ', IsHalf (cA D (cA D a)) l ∧ ψ (symplO S T l y) ≠ 1 := by
    intro y hy hyΛ'
    have hky : k • y ∉ Λ := fun h => hyΛ' ((memC y hy).2 h)
    obtain ⟨l, hl, hlh, hne⟩ := exists_dual_half ha' hdual (hstab _ (by rw [hcc]; exact ha.1))
      (isHalf_nsmul hy k) hky
    refine ⟨k • l, ?_, isHalf_nsmul hlh k, by rwa [symplO_nsmul_swap]⟩
    rw [hcc] at hlh
    exact (memA _ (isHalf_nsmul hlh k)).2 ⟨l, hl, rfl⟩
  have h1 : ∀ u ∈ Λ', IsHalf (cA D a) u →
      heisO ψ S T u (∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f)) = ∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f) :=
    fun u hu huh => sum_reps_invariant (ψ := ψ) (Λ := K) (Λ' := Λ') ha'
      (fun y hy => ⟨(memC y (hY y hy).1).2 (hY y hy).2, (hY y hy).1⟩)
      (fun u' hu' hu'h => hYK u' hu'h ((memC u' hu'h).1 hu')) (fun d hdK _ hdh => hGx d hdh hdK) hu huh
  have h2 : ∀ u ∈ Λ', IsHalf (cA D (cA D a)) u →
      heisO ψ S T u (∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f)) = ∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f) := by
    intro u hu huh
    rw [hcc] at huh
    obtain ⟨v, hv, hvh, rfl⟩ := rep_half ha.1 (hstab _ ha.1) huh ((memA u huh).1 hu)
    rw [heisO_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [heisO_comm, symplO_nsmul_swap, hpair v hv _ (hY y hy).2, one_smul, heisO_comm ψ S T (k • v) x,
      half_orth ha (isHalf_nsmul hvh k) hxa, AddChar.map_zero_eq_one, one_smul, hfix v hv (Or.inl hvh)]
  obtain ⟨ℓ, hℓ0, hℓinv⟩ := GlobalTheory.SplitHecke.exists_invariant_form' (Λ := Λ') (ψ := ψ) ha' hd hn h1 h2
  apply hℓ0
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_congr rfl fun y hy => hℓinv y (hY y hy).1 _ hfx, hℓ ℓ hℓinv x hxa,
    Finset.sum_const_zero]

theorem invForms_separate (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (hψ : IsStdChar D ψ (-1)) (a : AE D)
    (ha : IsSplitIdem D a) (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f)
    (hℓ : ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x → ℓ (heisO ψ S T x f) = 0) : f = 0 := by
  have hS := GlobalTheory.PlaceModel.isSelfDualC_latFrame S
  have hT := GlobalTheory.PlaceModel.isSelfDualC_latFrame T
  have ha' := isSplitIdem_conj ha
  obtain ⟨k, hk, hfix, -⟩ := (_root_.GlobalTheory.DownLift.SplitCoef.coef_isSBHalf_uniform D ψ S T hψ _ _ hS hT a ha f hf).1
  obtain ⟨Y, -, hY, hYu, -⟩ := _root_.GlobalTheory.DownLift.GenQuot.reps_orth D ψ S T hψ _ _ hS hT a ha.1 (infPart_splitIdem ha) k hk
  obtain ⟨X, hXne, hX, -, hXo⟩ := _root_.GlobalTheory.DownLift.GenQuot.reps_orth D ψ S T hψ _ _ hS hT (cA D a) ha'.1 (infPart_splitIdem ha') k hk
  rw [GlobalTheory.DualPairCheck.cA_cA] at hX
  have hdual : ∀ u : WO S T, u.map (infPart D) = 0 →
      (u ∈ latH S T (GlobalTheory.PlaceModel.latFrame S) (GlobalTheory.PlaceModel.latFrame T) ↔
        ∀ u' ∈ latH S T (GlobalTheory.PlaceModel.latFrame S) (GlobalTheory.PlaceModel.latFrame T), ψ (symplO S T u u') = 1) :=
    (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfinΛ : ∀ u ∈ latH S T (GlobalTheory.PlaceModel.latFrame S) (GlobalTheory.PlaceModel.latFrame T), u.map (infPart D) = 0 :=
    fun u hu => latO_fin hu
  have hstab : ∀ e : AE D, e * e = e → ∀ u ∈ latH S T (GlobalTheory.PlaceModel.latFrame S) (GlobalTheory.PlaceModel.latFrame T),
      e • u ∈ latH S T (GlobalTheory.PlaceModel.latFrame S) (GlobalTheory.PlaceModel.latFrame T) :=
    fun e he => idem_smul_mem he
  generalize latH S T (GlobalTheory.PlaceModel.latFrame S) (GlobalTheory.PlaceModel.latFrame T) = Λ at *
  have hpair : ∀ u ∈ Λ, ∀ u' ∈ Λ, ψ (symplO S T u u') = 1 := fun u hu => (hdual u (hfinΛ u hu)).1 hu
  have hB : ∀ x ∈ X, ∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f) = 0 := fun x hx =>
    sum_translates_eq_zero ha hψ hdual hpair hstab hf hfix hY hYu hℓ (hX x hx).1 (hX x hx).2
  have hA := sum_average (ψ := ψ) ha (fun u hu huh => hfix u hu (Or.inr huh)) hY hYu (fun x hx => (hX x hx).1) hXo
  have h0 : ∑ x ∈ X, heisO ψ S T (-x) (∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f)) = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [hB x hx]
    exact (heisL ψ S T (-x)).map_zero
  rw [h0] at hA
  have hc : (X.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 hXne)
  exact (smul_eq_zero.1 hA.symm).resolve_left hc

end GlobalTheory.DownLift.SplitSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UpwardVectorLiftMemRangeCoefficientExtension
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.AdjUp

noncomputable section

namespace GlobalTheory.AdjRange

open GlobalTheory.TraceIncl

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem inner_sum_eq {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ W) (Φ : W → ℂ) (hadd : ∀ w w', Φ (w + w') = Φ w + Φ w')
    (hsmul : ∀ (c : ℂ) w, Φ (c • w) = star c * Φ w) (w : W) :
    ⟪w, ∑ k, Φ (b k) • b k⟫_ℂ = Φ w := by
  have hsum : ∀ s : Finset (Fin n), Φ (∑ k ∈ s, ⟪b k, w⟫_ℂ • b k) = ∑ k ∈ s, star ⟪b k, w⟫_ℂ * Φ (b k) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have h0 := hsmul 0 0
      simp only [zero_smul, star_zero, zero_mul] at h0
      simpa using h0
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, hsmul, ih]
  conv_rhs => rw [← b.sum_repr' w]
  rw [hsum, inner_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_smul_right, mul_comm]
  congr 1
  exact (inner_conj_symm (𝕜 := ℂ) w (b k)).symm

theorem star_inv_of_finOrder (u : ℂˣ) (hu : IsOfFinOrder u) : star (((u⁻¹ : ℂˣ) : ℂ)) = (u : ℂ) := by
  obtain ⟨n, hn, hpow⟩ := hu.exists_pow_eq_one
  have h1 : ‖(u : ℂ)‖ = 1 := by
    have : ‖(u : ℂ)‖ ^ n = 1 := by
      rw [← norm_pow, ← Units.val_pow_eq_pow_val, hpow, Units.val_one, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
  have hne : (u : ℂ) ≠ 0 := u.ne_zero
  rw [Units.val_inv_eq_inv_val, star_inv₀, Complex.star_def, Complex.inv_def, Complex.normSq_eq_norm_sq,
    Complex.norm_conj, h1]
  simp

variable (R : RealDat D A Ks) (i : Fin D.R.m) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (y : (R.HW i (sg0 D A)).H)

def phi (K : (R.cV i).W →ₗ[ℂ] Ser R i) (w : (R.cV i).W) : ℂ :=
  ∫ g in R.fdW i, star (K w v g) * val R i v y g ∂(R.νW i)

def coVec {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W) (K : (R.cV i).W →ₗ[ℂ] Ser R i) : (R.cV i).W :=
  ∑ k, phi R i v y K (b k) • b k

theorem inner_coVec {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W) (K : (R.cV i).W →ₗ[ℂ] Ser R i)
    (hI : ∀ w, IntegrableOn (fun g => star (K w v g) * val R i v y g) (R.fdW i) (R.νW i)) (w : (R.cV i).W) :
    ⟪w, coVec R i v y b K⟫_ℂ = phi R i v y K w := by
  refine inner_sum_eq b _ (fun w w' => ?_) (fun c w => ?_) w
  · unfold phi
    rw [← integral_add (hI w) (hI w')]
    refine integral_congr_ae (.of_forall fun g => ?_)
    simp only [map_add (f := _), Pi.add_apply, star_add, add_mul]
  · unfold phi
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun g => ?_)
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, star_mul', mul_assoc]

end GlobalTheory.AdjRange

namespace GlobalTheory.AdjRange

open GlobalTheory.TraceIncl

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem integrable_kernA (hP : GlobalTheory.Published.CuspRapidDecay) (R : RealDat D A Ks) (F : Face D A) (hL : Laws R F)
    (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (y : (R.HW i (sg0 D A)).H) (h : GA D (Vc D i))
    (w : (R.cV i).W) :
    IntegrableOn (fun g => star (kernA R i t h w v g) * val R i v y g) (R.fdW i) (R.νW i) := by
  have hω := hL.thP.ωP i t
  have hf := hL.thP.pt_theta i t (R.ioP i (PiTensorProduct.tprod ℂ v) ((R.cV i).ρ h⁻¹ w))
  have hMem : (R.HW i (sg0 D A)).e y ∈ R.Wall i (sg0 D A) := by
    rw [← (hL.models.HW i (sg0 D A)).2.1]
    exact LinearMap.mem_range_self _ y
  have hMM := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hMem
  have hR : GlobalTheory.Grow.RapidDec (Wc D i) (val R i v y) :=
    GlobalTheory.Grow.rapidDec_of_cuspForm hP hL.models.inf (hMM.aut _) (hMM.cusp _)
  have : BorelSpace (GA D (Wc D i)) := ⟨rfl⟩
  have hm : GlobalTheory.Grow.ModGrowth (Wc D i) (fun g => star (thetaKO (R.ωP i t) h g
      (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) ((R.cV i).ρ h⁻¹ w))))) :=
    ((GlobalTheory.Core.Rk.ThetaGrowthBoth.thetaKO_modGrowth₂ D _ _ _ _ _ _ hω _ hf).right h).of_le
      (fun g => (norm_star _).le)
  have hl : ∀ γ ∈ GQ (Wc D i), ∀ g, star (thetaKO (R.ωP i t) h (γ * g)
      (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) ((R.cV i).ρ h⁻¹ w)))) =
      star (thetaKO (R.ωP i t) h g (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) ((R.cV i).ρ h⁻¹ w)))) :=
    fun γ hγ g => by rw [GlobalTheory.Chain.LiftConv.thetaKO_left hω hf h γ hγ g]
  have hms := ((GlobalTheory.Chain.LiftConv.thetaKO_continuous hω hf h).star).measurable.aestronglyMeasurable
    (μ := (R.νW i).restrict (R.fdW i))
  exact hR.integrableOn_modGrowth_mul (hL.models.νW i).1.1 (hL.models.νW i).2 hm hl hms

theorem integrable_kern (hP : GlobalTheory.Published.CuspRapidDecay) (R : RealDat D A Ks) (F : Face D A) (hL : Laws R F)
    (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (y : (R.HW i (sg0 D A)).H)
    (x : Formalism.IndefR.Bridge.Gf (Vc D i)) (w : (R.cV i).W) :
    IntegrableOn (fun g => star (kern R i t x w v g) * val R i v y g) (R.fdW i) (R.νW i) := by
  obtain ⟨h, -, rfl⟩ := KernLaws.exists_finite_lift _ x
  rw [KernLaws.kern_fin R i t hL.thP.ioP]
  exact integrable_kernA hP R F hL i t v y h w

theorem inner_rho (R : RealDat D A Ks) (F : Face D A) (hL : Laws R F) (i : Fin D.R.m) (h : GA D (Vc D i))
    (x z : (R.cV i).W) : ⟪x, (R.cV i).ρ h z⟫_ℂ = ⟪(R.cV i).ρ h⁻¹ x, z⟫_ℂ := by
  rw [← (hL.models.cV i).2.1 h⁻¹ x ((R.cV i).ρ h z), ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply]

theorem upVec_eq (hP : GlobalTheory.Published.CuspRapidDecay) (R : RealDat D A Ks) (F : Face D A) (hL : Laws R F)
    (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W) (y : (R.HW i (sg0 D A)).H) (h : GA D (Vc D i)) :
    upVec R i t v b y h = (R.cV i).ρ h⁻¹ (coVec R i v y b (kern R i t (Formalism.IndefR.FWT.fin (Vc D i) h))) := by
  have hinv : ∀ x : (R.cV i).W, (R.cV i).ρ h⁻¹ ((R.cV i).ρ h x) = x := fun x => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hin := inner_coVec R i v y b (kernA R i t h) (integrable_kernA hP R F hL i t v y h)
  apply ext_inner_left ℂ
  intro w
  rw [inner_rho R F hL, inv_inv, KernLaws.kern_fin R i t hL.thP.ioP, hin]
  have e2 : upVec R i t v b y h = ∑ k, phi R i v y (kernA R i t h) ((R.cV i).ρ h (b k)) • b k := by
    unfold upVec
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    unfold upLift phi
    refine integral_congr_ae (.of_forall fun g => ?_)
    dsimp only
    rw [KernLaws.kernA_apply, hinv]
    rfl
  rw [e2]
  refine inner_sum_eq b (fun w => phi R i v y (kernA R i t h) ((R.cV i).ρ h w)) (fun w w' => ?_) (fun c w => ?_) w
  · simp only [map_add (f := _), ← hin, inner_add_left]
  · simp only [map_smul, ← hin, inner_smul_left, Complex.star_def]


set_option maxHeartbeats 1000000 in
theorem coVec_level (R : RealDat D A Ks) (F : Face D A) (hL : Laws R F) (i : Fin D.R.m) (t : T)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W)
    (y : (R.HW i (sg0 D A)).H) (hT : DatumType R i t) (z : Formalism.IndefR.Bridge.Gf (Vc D i))
    (k : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J) :
    coVec R i v y b (kern R i t (z * k)) =
      (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ k : ℂˣ) : ℂ) • coVec R i v y b (kern R i t z) := by
  have hlev := (kern_laws R i t hL.models.inf hL.models.cV hL.thP.ωP hL.thP.pt_theta hL.thP.ioP hT).2.2.1
  unfold coVec
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul]
  congr 1
  unfold phi
  rw [← integral_const_mul]
  refine integral_congr_ae (.of_forall fun g => ?_)
  rw [hlev]
  simp only [Pi.smul_apply, smul_eq_mul, star_mul']
  rw [star_inv_of_finOrder _ (GlobalTheory.LevelCharOrder.levEnv_chi_isOfFinOrder (Vc D i) (R.βV i) (R.datVt i t) k), mul_assoc]

theorem coVec_rat (hP : GlobalTheory.Published.CuspRapidDecay) (R : RealDat D A Ks) (F : Face D A) (hL : Laws R F)
    (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W)
    (y : (R.HW i (sg0 D A)).H) (hT : DatumType R i t) (γ : GQ (Vc D i)) (x : Formalism.IndefR.Bridge.Gf (Vc D i)) :
    coVec R i v y b (kern R i t (Formalism.IndefR.Bridge.ratF (Vc D i) γ * x)) =
      (R.cV i).ρ (γ : GA D (Vc D i)) (coVec R i v y b (kern R i t x)) := by
  have hrat := (kern_laws R i t hL.models.inf hL.models.cV hL.thP.ωP hL.thP.pt_theta hL.thP.ioP hT).2.1
  apply ext_inner_left ℂ
  intro w
  rw [inner_coVec R i v y b _ (integrable_kern hP R F hL i t v y _), inner_rho R F hL,
    inner_coVec R i v y b _ (integrable_kern hP R F hL i t v y x)]
  unfold phi
  have e := hrat γ x ((R.cV i).ρ (γ : GA D (Vc D i))⁻¹ w)
  have e' : (R.cV i).coef.ρ γ ((R.cV i).ρ (γ : GA D (Vc D i))⁻¹ w) = w := by
    show (R.cV i).ρ (γ : GA D (Vc D i)) ((R.cV i).ρ (γ : GA D (Vc D i))⁻¹ w) = w
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [e'] at e
  rw [e]

theorem coefExt_apply {V : HSp D} (c : CoefA V) (f : Formalism.IndefR.Bridge.Gf V → c.W) (h : GA D V) :
    c.ext f h = c.ρ h⁻¹ (f (Formalism.IndefR.FWT.fin V h)) := rfl


set_option maxHeartbeats 2000000 in
theorem upVec_mem_range : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W) (y : (R.HW i (sg0 D A)).H), ∃ u : (R.HV i t).H, R.extV i t u = upVec R i t v b y := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R F hL _ i t v n b y
  have hT : DatumType R i t := fun g0 κ κ' h1 h2 =>
    GlobalTheory.VecInv.omega_lifts_vP R hL.lev hL.models.inf hL.thP.ωP hL.thP.vP i t g0 κ κ' h1 h2
  obtain ⟨f, hfd⟩ : ∃ f : Formalism.IndefR.Bridge.Gf (Vc D i) → (R.cV i).W, ∀ x, f x = coVec R i v y b (kern R i t x) :=
    ⟨_, fun _ => rfl⟩
  have hext : (R.cV i).ext f = upVec R i t v b y := by
    funext h
    rw [coefExt_apply, upVec_eq hP R F hL i t v b y h, hfd]
  have hmem : ∀ (γ : GQ (Vc D i)) (x : Formalism.IndefR.Bridge.Gf (Vc D i)) (k : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J),
      f (Formalism.IndefR.Bridge.ratF (Vc D i) γ * x * k) =
        (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ k : ℂˣ) : ℂ) • (R.cV i).ρ (γ : GA D (Vc D i)) (f x) := by
    intro γ x k
    rw [hfd, hfd]
    exact (coVec_level R F hL i t v b y hT (Formalism.IndefR.Bridge.ratF (Vc D i) γ * x) k).trans
      (congrArg _ (coVec_rat hP R F hL i t v b y hT γ x))
  obtain ⟨u, hu⟩ : f ∈ LinearMap.range (R.HV i t).e := by
    rw [(hL.models.HV i t).2.1]
    exact hmem
  refine ⟨u, ?_⟩
  show (R.cV i).ext ((R.HV i t).e u) = _
  rw [hu, hext]

end GlobalTheory.AdjRange
end
end

