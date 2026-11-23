module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0360
public import GroundTheory.AutomorphicForms.HarishChandraCentre.VermaCoordEqZeroOfMemNPlusU
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0368
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0418
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0413
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0402
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0405
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0423
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0395
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0606
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0409
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralEqSumSmallerLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralProductGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalAlgebraHolds

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LoweringWordsSpan
section
set_option maxSynthPendingDepth 1

noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount
open GroundTheory.Automorphic.HarishChandra

namespace GlobalTheory.CompanionTheory.PresRho

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

theorem exists_exp {μ : Fin n → ℤ} {x : U n} (h : x ∈ lowSpanW μ ⊔ vermaIdeal (rhoVec n))
    (hx : x ∉ vermaIdeal (rhoVec n)) : ∃ m : Fin n × Fin n →₀ ℕ, LowExp m ∧ wt m = μ := by
  by_contra hne
  have hbot : lowSpanW μ = ⊥ := by
    refine Submodule.span_eq_bot.2 ?_
    rintro _ ⟨m, hm, hw, rfl⟩
    exact absurd ⟨m, hm, hw⟩ hne
  rw [hbot, bot_sup_eq] at h
  exact hx h

theorem lowExp_wt_zero {m : Fin n × Fin n →₀ ℕ} (hm : LowExp m) (h : wt m = 0) : m = 0 := by
  refine GlobalTheory.T.eq_zero_of_low_exponent_casimir m hm (fun i j hij => ⟨1, by simp [h]⟩) ?_
  simp [h]

theorem mem_of_adW_zero {x : U n} (h : x ∈ lowSpanW (0 : Fin n → ℤ) ⊔ vermaIdeal (rhoVec n)) :
    ∃ c : ℂ, x - c • 1 ∈ vermaIdeal (rhoVec n) := by
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 h
  clear h
  have : ∃ c : ℂ, y = c • 1 := by
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, hm, hw0, rfl⟩ := hx
      exact ⟨1, by rw [lowExp_wt_zero hm hw0]; simp⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, rfl⟩ := hx
      obtain ⟨d, rfl⟩ := hy
      exact ⟨c + d, by rw [add_smul]⟩
    | smul r x _ hx =>
      obtain ⟨c, rfl⟩ := hx
      exact ⟨r * c, by rw [mul_smul]⟩
  obtain ⟨c, rfl⟩ := this
  exact ⟨c, by simpa using hw⟩

theorem mem_Jp_of_adW {A : Type} [AddCommGroup A] [Module ℂ A]
    (φ : U n →ₐ[ℂ] Module.End ℂ A) (t : A) (ht0 : t ≠ 0)
    (hd : ∀ k, φ (e (k, k)) t = rhoVec n k • t)
    (hu : ∀ a : Fin n × Fin n, IsUpper a → φ (e a) t = 0) :
    ∀ (N : ℕ) (μ : Fin n → ℤ) (x : U n), -ht μ < N → IsAdW μ x → φ x t = 0 → x ∈ Jp n := by
  intro N
  induction N with
  | zero =>
    intro μ x hN hx h0
    by_contra hJ
    obtain ⟨m, hm, rfl⟩ := exists_exp (GlobalTheory.T.weight_vector_mem_low_span_sup_verma μ x hx) fun h => hJ (vermaIdeal_le_Jp h)
    have := ht_wt_nonpos hm
    push_cast at hN
    omega
  | succ N ih =>
    intro μ x hN hx h0
    by_contra hJ
    obtain ⟨m, hm, rfl⟩ := exists_exp (GlobalTheory.T.weight_vector_mem_low_span_sup_verma μ x hx) fun h => hJ (vermaIdeal_le_Jp h)
    have hup : ∀ a : Fin n × Fin n, IsUpper a → e a * x ∈ Jp n := by
      intro a ha
      refine ih _ _ ?_ (hx.e_mul a) (by simp [h0])
      rw [ht_add_rootAt, ht_rootAt]
      have h1 : (a.1 : ℕ) < a.2 := ha
      push_cast at hN
      omega
    have hm0 : m = 0 := GlobalTheory.T.eq_zero_of_low_exponent_casimir m hm
      (fun i j hij => GlobalTheory.T.nat_of_simple_lowering_nilpotent (wt m) x i j hx hup hJ hij (GlobalTheory.T.simple_lowering_pow_mem_ideal i j x hij))
      (GlobalTheory.T.casimir_eq_of_singular_weight_vector (wt m) x hx hup hJ)
    subst hm0
    have hw0 : wt (0 : Fin n × Fin n →₀ ℕ) = 0 := by ext k; simp [wt]
    rw [hw0] at hx
    obtain ⟨c, hc⟩ := mem_of_adW_zero (GlobalTheory.T.weight_vector_mem_low_span_sup_verma 0 x hx)
    have h1 := act_eq_zero_of_mem φ t hd hu hc
    rw [map_sub, LinearMap.sub_apply, h0, zero_sub, map_smul, map_one] at h1
    have hc0 : c = 0 := by
      by_contra hne
      simp [hne, ht0] at h1
    rw [hc0, zero_smul, sub_zero] at hc
    exact hJ (vermaIdeal_le_Jp hc)

theorem word_mem_lowSpan {l : List (Fin n × Fin n)} (hl : ∀ p ∈ l, p.2 < p.1) :
    word l ∈ lowSpan n := by
  refine (Submodule.span_le.2 ?_) (word_mem_canonSpan closed_lower l hl)
  rintro _ ⟨m, hm, -, -, rfl⟩
  exact Submodule.subset_span ⟨m, hm, rfl⟩

theorem rho_cast (a : Fin n) : ((rhoV n a : ℝ) : ℂ) = rhoVec n a := by
  simp [rhoV, rhoVec]

theorem act_eq_zero_of_sqSpan {Z : Type} [AddCommGroup Z] [Module ℂ Z]
    {F : Fin n → Fin n → Module.End ℂ Z} (φ : U n →ₐ[ℂ] Module.End ℂ Z)
    (hφ : ∀ i j, φ (e (i, j)) = F i j) (z : Z)
    (hz : ∀ i j : Fin n, (j : ℕ) = i + 1 → ((F j i) ^ 2) z = 0) {x : U n}
    (hx : x ∈ sqSpan n) : φ x z = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, i, j, hij, rfl⟩ := hx
    simp only [map_mul, map_pow, hφ, Module.End.mul_apply]
    rw [hz i j hij, map_zero]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul r x _ hx => simp [hx]

theorem pres_rho : ∀ {n : ℕ} {A Z : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup Z] [Module ℂ Z]
    (G : Fin n → Fin n → Module.End ℂ A) (F : Fin n → Fin n → Module.End ℂ Z),
    Formalism.REAL.GlRel G → Formalism.REAL.GlRel F → ∀ t : A, t ≠ 0 →
    (∀ a, G a a t = ((rhoV n a : ℝ) : ℂ) • t) → (∀ a b, a < b → G a b t = 0) →
    ∀ z : Z, (∀ i j : Fin n, (j : ℕ) = i + 1 → ((F j i) ^ 2) z = 0) →
    ∀ (s : Finset (List (Fin n × Fin n))) (coef : List (Fin n × Fin n) → ℂ), (∀ l ∈ s, ∀ p ∈ l, p.2 < p.1) →
    ∑ l ∈ s, coef l • (l.map fun p => G p.1 p.2).prod t = 0 →
    ∑ l ∈ s, coef l • (l.map fun p => F p.1 p.2).prod z = 0 := by
  intro n A Z _ _ _ _ G F hG hF t ht0 hd hu z hz s coef hs hsum
  obtain ⟨φ, hφ⟩ := exists_act G hG
  obtain ⟨ψ, hψ⟩ := exists_act F hF
  have hd' : ∀ k, φ (e (k, k)) t = rhoVec n k • t := fun k => by
    rw [hφ, hd, rho_cast]
  have hu' : ∀ a : Fin n × Fin n, IsUpper a → φ (e a) t = 0 := fun a ha => by
    rw [show e a = e (a.1, a.2) from rfl, hφ]; exact hu _ _ ha
  set Y : U n := ∑ l ∈ s, coef l • word l with hY
  have hYlow : Y ∈ lowSpan n :=
    Submodule.sum_mem _ fun l hl => Submodule.smul_mem _ _ (word_mem_lowSpan (hs l hl))
  have hYt : φ Y t = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hY, map_sum, LinearMap.sum_apply, ← hsum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, LinearMap.smul_apply, act_word φ hφ]
  have hYJ : Y ∈ Jp n := by
    refine (Submodule.span_le.2 ?_) (GlobalTheory.T.annihilator_spanned_by_weight_vectors φ t hd' Y hYt)
    rintro y ⟨μ, hy, h0⟩
    exact mem_Jp_of_adW φ t ht0 hd' hu' (-ht μ + 1).toNat μ y (by omega) hy h0
  have hYs := _root_.GlobalTheory.CompanionTheory.PresRho.LowMeet.mem_sqSpan_of_mem_lowSpan_of_mem_Jp Y hYlow hYJ
  have h := act_eq_zero_of_sqSpan ψ hψ z hz hYs
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hY, map_sum, LinearMap.sum_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, LinearMap.smul_apply, act_word ψ hψ]

end GlobalTheory.CompanionTheory.PresRho
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeetOfSteps
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host
open PositivityTheory.jumpWindows

namespace GlobalTheory.CompanionTheory.ClosedInvariantMeet

theorem exists_space (hG2a : G2a) (hG2b : G2b) (hG2c : G2c) {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    {a : ℕ} (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ)
    (S : Finset (Pl E)) (B : Pl E → Multiset ℂˣ) (hB : ∀ w, w ∉ S → (B w).card = a)
    (H : Submodule ℂ (L2 (latticeGL E a) μ)) (hH : IsSubrep (R (latticeGL E a) μ) H) :
    ∃ Y : Submodule ℂ (XB E a), YOK ψ S Y ∧ ∀ φ : XB E a, φ ∈ Y ↔
      (Good ψ (a - 1) φ ∧ ∀ γ g, φ (ratGL E a γ * g) = φ g) ∧
        (∃ h : MemL2Quotient (latticeGL E a) μ φ, h.toL2 ∈ H) ∧ ∀ w, w ∉ S → SatFn w (B w) φ := by
  obtain ⟨Y0, c0, s0, m0⟩ := hG2a E a ψ hψ
  obtain ⟨YH, cH, sH, mH⟩ := hG2b E a μ H hH
  have hw := fun w (hw : w ∉ S) => hG2c E a w (B w) (hB w hw)
  choose! Yw cw sw mw using hw
  have mem : ∀ φ : XB E a, φ ∈ Y0 ⊓ YH ⊓ ⨅ w, ⨅ (_ : w ∉ S), Yw w ↔
      (φ ∈ Y0 ∧ φ ∈ YH) ∧ ∀ w, w ∉ S → φ ∈ Yw w := fun φ => by
    simp only [Submodule.mem_inf, Submodule.mem_iInf]
  refine ⟨Y0 ⊓ YH ⊓ ⨅ w, ⨅ (_ : w ∉ S), Yw w, ⟨?_, ?_, ?_⟩, fun φ => ?_⟩
  · have e : ((Y0 ⊓ YH ⊓ ⨅ w, ⨅ (_ : w ∉ S), Yw w : Submodule ℂ (XB E a)) : Set (XB E a)) =
        ((Y0 : Set (XB E a)) ∩ YH) ∩ ⋂ w, ⋂ (_ : w ∉ S), (Yw w : Set (XB E a)) := by
      ext φ
      simp only [SetLike.mem_coe, mem, Set.mem_inter_iff, Set.mem_iInter]
    rw [e]
    exact (c0.inter cH).inter (isClosed_iInter fun w => isClosed_iInter fun h => cw w h)
  · intro g hg φ hφ
    obtain ⟨⟨h0, h1⟩, h2⟩ := (mem φ).1 hφ
    exact (mem _).2 ⟨⟨s0 g φ h0, sH g φ h1⟩, fun w h => sw w h g (hg w h) φ (h2 w h)⟩
  · intro φ hφ
    exact ((m0 φ).1 ((mem φ).1 hφ).1.1).1
  · rw [mem, m0, mH]
    constructor
    · rintro ⟨⟨h0, h1⟩, h2⟩
      exact ⟨h0, h1, fun w h => (mw w h φ).1 (h2 w h)⟩
    · rintro ⟨h0, h1, h2⟩
      exact ⟨⟨h0, h1⟩, fun w h => (mw w h φ).2 (h2 w h)⟩

theorem eq_of_wh (hG5 : G5) (hG13 : WhittakerVanishingImpliesZero) {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (S : Finset (Pl E)) (hc : ∀ w, w ∉ S → Cond ψ w) (B : Pl E → Multiset ℂˣ)
    (hYs : ∀ w, w ∉ S → ∃ Z : Submodule ℂ (XB E a), ∀ φ, φ ∈ Z ↔ SatFn w (B w) φ)
    (hY0 : ∃ Z : Submodule ℂ (XB E a), ∀ φ : XB E a, φ ∈ Z ↔ Good ψ (a - 1) φ ∧ ∀ γ g, φ (ratGL E a γ * g) = φ g)
    {φ φ' : XB E a} (h : (Good ψ (a - 1) φ ∧ ∀ γ g, φ (ratGL E a γ * g) = φ g) ∧ ∀ w, w ∉ S → SatFn w (B w) φ)
    (h' : (Good ψ (a - 1) φ' ∧ ∀ γ g, φ' (ratGL E a γ * g) = φ' g) ∧ ∀ w, w ∉ S → SatFn w (B w) φ')
    (hW : ∀ g, MirS S g → InS S g → Wh ψ φ g = Wh ψ φ' g) : φ = φ' := by
  obtain ⟨Z, hZ⟩ := hY0
  have d0 : φ - φ' ∈ Z := Z.sub_mem ((hZ φ).2 h.1) ((hZ φ').2 h'.1)
  have hd := (hZ _).1 d0
  have e := hG13 E a ψ hψ S hc (φ - φ') hd.1 hd.2
    (fun w hw => ⟨B w, by
      obtain ⟨Z', hZ'⟩ := hYs w hw
      exact (hZ' _).1 (Z'.sub_mem ((hZ' φ).2 (h.2 w hw)) ((hZ' φ').2 (h'.2 w hw)))⟩)
    (fun g h1 h2 => by
      obtain ⟨Λ, hΛ⟩ := (hG5 E a ψ hψ).1 g
      rw [← hΛ _ hd.1, map_sub, hΛ _ h.1.1, hΛ _ h'.1.1, hW g h1 h2, sub_self])
  exact sub_eq_zero.1 e

theorem meet_of_steps : S2 → MirabolicColumnBlock → G0 → G1 → AlmostEverywhereSpherical → G2a → G2b → G2c → G5 → G5b → FourierInductionSteps → G8 → StandardCharacterExists → WhittakerVanishingImpliesZero → Meet := by
  intro _ hS10 hG0 hG1 hG1b hG2a hG2b hG2c hG5 _ hG7i hG8 hG10 hG13 E _ _ _ a μ _ _ π π' H H' hn hn' hH hH' hm hm' hss
  obtain ⟨ψ, hψ, hcond⟩ := hG10 E
  obtain ⟨φ0, hφ0, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  obtain ⟨φ0', hφ0', h0'⟩ := (Submodule.ne_bot_iff _).1 π'.ne_bot
  obtain ⟨x, hx, hxs, hxl⟩ := hG1 E a π hn φ0 hφ0
  obtain ⟨x', hx', hxs', hxl'⟩ := hG1 E a π' hn' φ0' hφ0'
  have hev := hcond.and (hss.and ((hG1b E a π hn φ0 hφ0 x hx).and (hG1b E a π' hn' φ0' hφ0' x' hx')))
  obtain ⟨S, hS⟩ : ∃ S : Finset (Pl E), ∀ w, w ∉ S → Cond ψ w ∧
      (∃ B, (CG.mk π).HasSat w B ∧ (CG.mk π').HasSat w B) ∧
      (∀ B, (CG.mk π).HasSat w B → SatFn w B x) ∧ (∀ B, (CG.mk π').HasSat w B → SatFn w B x') :=
    ⟨(Filter.eventually_cofinite.1 hev).toFinset, fun w hw => by
      by_contra h
      exact hw ((Set.Finite.mem_toFinset _).2 h)⟩
  have hBex := fun w (hw : w ∉ S) => (hS w hw).2.1
  choose! B hB using hBex
  have hcard : ∀ w, w ∉ S → (B w).card = a := fun w hw => CG.HasSat.card (hB w hw).1
  have hc : ∀ w, w ∉ S → Cond ψ w := fun w hw => (hS w hw).1
  obtain ⟨Y, hYok, hY⟩ := exists_space hG2a hG2b hG2c μ hψ S B hcard H hH
  obtain ⟨Y', hYok', hY'⟩ := exists_space hG2a hG2b hG2c μ hψ S B hcard H' hH'

  have hxY : x ∈ Y := by
    refine (hY x).2 ⟨⟨?_, ?_⟩, ?_, fun w hw => (hS w hw).2.2.1 _ (hB w hw).1⟩
    · rw [hx]; exact _root_.GlobalTheory.CuspGeneric.good_of_isCuspForm E a ψ φ0 (π.cusp _ hφ0)
    · rw [hx]; exact (π.cusp _ hφ0).1.left
    · rw [hx]; exact hm φ0 hφ0
  have hxY' : x' ∈ Y' := by
    refine (hY' x').2 ⟨⟨?_, ?_⟩, ?_, fun w hw => (hS w hw).2.2.2 _ (hB w hw).2⟩
    · rw [hx']; exact _root_.GlobalTheory.CuspGeneric.good_of_isCuspForm E a ψ φ0' (π'.cusp _ hφ0')
    · rw [hx']; exact (π'.cusp _ hφ0').1.left
    · rw [hx']; exact hm' φ0' hφ0'
  have hx0 : x ≠ 0 := fun e => h0 (Subtype.ext (by rw [← hx, e]; rfl))
  have hx0' : x' ≠ 0 := fun e => h0' (Subtype.ext (by rw [← hx', e]; rfl))
  obtain ⟨φ₁, hφ₁, hs₁, hl₁, hw₁⟩ := hG8 E a ψ hψ S hc Y hYok x hxY hx0 hxs (hxl S)
    fun w hw => ⟨B w, ((hY x).1 hxY).2.2 w hw⟩
  obtain ⟨φ₂, hφ₂, hs₂, hl₂, hw₂⟩ := hG8 E a ψ hψ S hc Y' hYok' x' hxY' hx0' hxs' (hxl' S)
    fun w hw => ⟨B w, ((hY' x').1 hxY').2.2 w hw⟩
  have hst : St ψ S Y Y' 0 (fun _ => 0) := by
    refine ⟨φ₁, hφ₁, φ₂, hφ₂, hs₁, hs₂, hl₁, hl₂, by rw [hw₁]; exact one_ne_zero, fun g hg => ?_⟩
    have e : g = 1 := by
      obtain ⟨-, -, -, -, -, hext, -⟩ := hG0 E a
      refine hext g 1 ?_ fun w => ?_
      · rw [map_one]; exact (hS10 _ a 0).2.1 _ hg.1
      · rw [map_one]; exact (hS10 _ a 0).2.1 _ (hg.2 w)
    rw [e, hw₁, hw₂]
  obtain ⟨φ, hφ, φ', hφ', -, -, -, -, hw, hag⟩ := hG7i E a ψ hψ S Y Y' hYok hYok' hst
  have hφm := (hY φ).1 hφ
  have hφm' := (hY' φ').1 hφ'
  obtain ⟨Z, -, -, hZ⟩ := hG2a E a ψ hψ
  have heq : φ = φ' := by
    refine eq_of_wh hG5 hG13 hψ S hc B (fun w hw => ?_) ⟨Z, hZ⟩ ⟨hφm.1, hφm.2.2⟩
      ⟨hφm'.1, hφm'.2.2⟩ fun g hg hi => hag g ⟨hg.1, fun w => ?_⟩
    · obtain ⟨Z', -, -, hZ'⟩ := hG2c E a w (B w) (hcard w hw)
      exact ⟨Z', hZ'⟩
    · by_cases hw : w ∈ S
      · simpa only [if_pos hw] using hg.2 w hw
      · simp only [if_neg hw]
        rw [hi w hw]
        exact (hS10 _ a 0).2.2.1
  subst heq
  obtain ⟨h, hhH⟩ := hφm.2.1
  obtain ⟨h', hhH'⟩ := hφm'.2.1
  have hφ0 : φ ≠ 0 := by
    rintro rfl
    obtain ⟨Λ, hΛ⟩ := (hG5 E a ψ hψ).1 1
    exact hw (by rw [← hΛ _ hφm.1.1, map_zero])
  have hne : h.toL2 ≠ 0 := toL2_ne_zero h φ.continuous fun e => hφ0 (DFunLike.coe_injective e)
  intro hbot
  have hmem : h.toL2 ∈ H ⊓ H' := ⟨hhH, hhH'⟩
  rw [hbot] at hmem
  exact hne ((Submodule.mem_bot _).1 hmem)

end GlobalTheory.CompanionTheory.ClosedInvariantMeet

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemSubmoduleOfBumps
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

theorem mem_of_bumps {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    (H : Subgroup G) (ρ : Representation ℂ H W) (K : Subgroup G) (hKo : IsOpen (K : Set G))
    (hKc : IsCompact (K : Set G)) (y : cIndSpace H ρ) (hy : ∀ g, ∀ x ∈ K, y.1.1.1 (g * x) = y.1.1.1 g)
    (S : Submodule ℂ (cIndSpace H ρ)) (hS : ∀ c B, IsBump H ρ K c (y.1.1.1 c) B → B ∈ S) : y ∈ S := by
  classical
  obtain ⟨C, hC, hsupp⟩ := y.2
  have hyeq : ∀ (a : H) (g : G), y.1.1.1 ((a : G) * g) = ρ a (y.1.1.1 g) := y.1.1.2
  obtain ⟨t, -, ht⟩ := hC.elim_nhds_subcover (fun c => (fun x => c * x) '' (K : Set G)) (fun c _ => by
    have : (fun y => c⁻¹ * y) ⁻¹' (K : Set G) ∈ 𝓝 c :=
      (hKo.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp [one_mem])
    filter_upwards [this] with y hy
    exact ⟨c⁻¹ * y, hy, by group⟩)
  let T : Finset (DoubleCoset.Quotient (H : Set G) (K : Set G)) := t.image (DoubleCoset.mk H K)
  have hres := fun d : DoubleCoset.Quotient (H : Set G) (K : Set G) =>
    GlobalTheory.CompanionTheory.LeibPhi.exists_indicator H ρ (GlobalTheory.CompanionTheory.LeibPhi.isHK_doubleCoset H K hKo (Quotient.out d)) y
  choose f hf1 hf0 using hres
  have hbump : ∀ d, IsBump H ρ K (Quotient.out d) (y.1.1.1 (Quotient.out d)) (f d) := by
    intro d
    refine ⟨fun a x hx => ?_, fun g hg => hf0 d g ?_⟩
    · rw [hf1 d _ ⟨a, a.2, x, hx, rfl⟩, hy _ x hx, hyeq]
    · rintro ⟨a, ha, x, hx, e⟩
      exact hg ⟨⟨a, ha⟩, x, hx, e⟩
  have hoff : ∀ (d : DoubleCoset.Quotient (H : Set G) (K : Set G)) (g : G), DoubleCoset.mk H K g ≠ d →
      (f d).1.1.1 g = 0 := by
    intro d g hne
    apply hf0
    rintro ⟨a, ha, x, hx, e⟩
    apply hne
    rw [← DoubleCoset.out_eq' d]
    exact ((@DoubleCoset.eq _ _ H K _ _).2 ⟨a, ha, x, hx, e⟩).symm
  have hmem : ∑ d ∈ T, f d ∈ S := S.sum_mem fun d _ => hS _ _ (hbump d)
  have hval : ∀ g, y.1.1.1 g = (∑ d ∈ T, f d).1.1.1 g := by
    intro g
    let ev : cIndSpace H ρ →ₗ[ℂ] W :=
      (LinearMap.proj g) ∘ₗ (indSpace H ρ).subtype ∘ₗ (smoothPart (ind H ρ)).subtype ∘ₗ (cIndSpace H ρ).subtype
    have hsum : (∑ d ∈ T, f d).1.1.1 g = ∑ d ∈ T, (f d).1.1.1 g := map_sum ev _ _
    rw [hsum]
    by_cases hg : DoubleCoset.mk H K g ∈ T
    · rw [Finset.sum_eq_single_of_mem _ hg (fun d _ hd => hoff d g (Ne.symm hd))]
      obtain ⟨a, ha, x, hx, e⟩ := (@DoubleCoset.eq _ _ H K _ _).1 (DoubleCoset.out_eq' (DoubleCoset.mk H K g))
      exact (hf1 _ g ⟨a, ha, x, hx, e⟩).symm
    · rw [Finset.sum_eq_zero (fun d hd => hoff d g (fun h => hg (h ▸ hd)))]
      by_contra hne
      obtain ⟨a, ha, c', hc', e⟩ := hsupp g hne
      obtain ⟨c, hc, hcc⟩ := Set.mem_iUnion₂.1 (ht hc')
      obtain ⟨x, hx, rfl⟩ := hcc
      apply hg
      have : DoubleCoset.mk H K c = DoubleCoset.mk H K g :=
        (@DoubleCoset.eq _ _ H K _ _).2 ⟨a, ha, x, hx, by rw [e]; group⟩
      rw [← this]
      exact Finset.mem_image_of_mem _ hc
  have e : y = ∑ d ∈ T, f d := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact hval g
  rw [e]
  exact hmem

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalParabolicMemPartialFlag
section
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.RapidDecay

theorem mul_firstCols_eq {R : Type} [CommRing R] {n r : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (Z : Matrix (Fin n) (Fin r) R) (B : Matrix (Fin r) (Fin r) R) (hB : B.BlockTriangular id)
    (e : M * Z = Z * B) (s : Fin r) :
    M * Z.submatrix id (Fin.castLE s.2) =
      Z.submatrix id (Fin.castLE s.2) * B.submatrix (Fin.castLE s.2) (Fin.castLE s.2) := by
  ext i j
  have h := congrFun (congrFun e i) (Fin.castLE s.2 j)
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id_eq] at h ⊢
  rw [h]
  refine (Fintype.sum_of_injective (Fin.castLE s.2) (Fin.castLE_injective s.2) _ _ ?_ ?_).symm
  · intro l hl
    have hlt : Fin.castLE s.2 j < l := by
      by_contra hc
      apply hl
      have hj := j.isLt
      have hc' : l.val ≤ j.val := not_lt.mp hc
      exact ⟨⟨l.val, by omega⟩, Fin.ext rfl⟩
    have h0 : B l (Fin.castLE s.2 j) = 0 := hB hlt
    rw [h0, mul_zero]
  · intro l
    rfl

theorem mem_parFlag_first_of_minParOne : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X : Matrix (Fin n) (Fin r) E), ∀ p ∈ minParOne σ J X, ∀ s : Fin r, p ∈ GlobalTheory.UAut.parFlag σ J (pre X s) fun _ => 0 := by
  intro F E _ _ _ _ _ σ n J r X p hp s
  obtain ⟨B, hB, e, hu⟩ := hp
  choose u hu1 _ using hu
  have e1 := mul_firstCols_eq _ _ B hB e s
  have hBs : (B.submatrix (Fin.castLE s.2) (Fin.castLE s.2)).BlockTriangular id := by
    intro i j hij
    exact hB hij
  have hdet : IsUnit (B.submatrix (Fin.castLE s.2) (Fin.castLE s.2)).det := by
    rw [Matrix.det_of_isUpperTriangular hBs]
    refine ⟨∏ i, u (Fin.castLE s.2 i), ?_⟩
    rw [Units.coe_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Matrix.submatrix_apply, hu1]
  have hZ : GlobalTheory.SiegelSet.adMat F (pre X s) =
      (GlobalTheory.SiegelSet.adMat F X).submatrix id (Fin.castLE s.2) := rfl
  refine ⟨⟨B.submatrix (Fin.castLE s.2) (Fin.castLE s.2), ?_, ?_⟩,
    ⟨(B.submatrix (Fin.castLE s.2) (Fin.castLE s.2))⁻¹, ?_, ?_⟩⟩
  · intro i j h
    exact absurd h (lt_irrefl 0)
  · rw [hZ]
    exact e1
  · intro i j h
    exact absurd h (lt_irrefl 0)
  · rw [hZ, map_inv]
    set g := GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ J p
    set Z := (GlobalTheory.SiegelSet.adMat F X).submatrix id (Fin.castLE s.2)
    set Bs := B.submatrix (Fin.castLE s.2) (Fin.castLE s.2)
    have h1 : Bs * Bs⁻¹ = 1 := Matrix.mul_nonsing_inv Bs hdet
    have h2 : (g⁻¹).val * g.val = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc (g⁻¹).val * Z
        = (g⁻¹).val * Z * (Bs * Bs⁻¹) := by rw [h1, Matrix.mul_one]
      _ = (g⁻¹).val * (g.val * Z) * Bs⁻¹ := by
          rw [e1]
          simp only [Matrix.mul_assoc]
      _ = Z * Bs⁻¹ := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]

end GlobalTheory.CompanionTheory.RapidDecay

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexNeZeroOfIsOpen
section
open GlobalTheory.BCT
open scoped Classical Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitConvHecke

theorem relIndex_ne_zero_of_isOpen {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (K L : Subgroup H) (hL : IsOpen (L : Set H)) (hK : IsCompact (K : Set H)) :
    L.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hop : IsOpen ((L.subgroupOf K : Subgroup K) : Set K) :=
    hL.preimage continuous_subtype_val
  haveI : Finite (K ⧸ L.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hop
  exact Subgroup.index_ne_zero_of_finite

end GlobalTheory.CompanionTheory.SplitConvHecke
end
end

