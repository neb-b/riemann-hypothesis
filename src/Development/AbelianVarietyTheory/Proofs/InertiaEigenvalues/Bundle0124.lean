module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSelfDualOfDualSubgroups
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0085

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdPrimePowDvd
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.Per


open PowerSeries in
theorem exists_div_X_sub_C {O : Type} [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (x : O) (hx : ¬ IsUnit x) (a : PowerSeries O) :
    ∃ (b : PowerSeries O) (c : O), a = (PowerSeries.X - PowerSeries.C x) * b + PowerSeries.C c := by
  have hres : (PowerSeries.X - PowerSeries.C x : PowerSeries O).map (IsLocalRing.residue O) =
      PowerSeries.X := by
    have hx0 : IsLocalRing.residue O x = 0 :=
      (IsLocalRing.residue_eq_zero_iff x).2 ((IsLocalRing.mem_maximalIdeal x).2 hx)
    rw [map_sub, PowerSeries.map_X, PowerSeries.map_C, hx0, map_zero, sub_zero]
  have hne : (PowerSeries.X - PowerSeries.C x : PowerSeries O).map (IsLocalRing.residue O) ≠ 0 := by
    rw [hres]; exact PowerSeries.X_ne_zero
  obtain ⟨q, r, hdeg, heq⟩ := a.exists_isWeierstrassDivision hne
  change r.degree < ((PowerSeries.X - PowerSeries.C x : PowerSeries O).map
      (IsLocalRing.residue O)).order.toNat at hdeg
  rw [hres, PowerSeries.order_X] at hdeg
  have hr : r = Polynomial.C (r.coeff 0) := by
    have h1 : r.degree < 0 + 1 := by simpa using hdeg
    exact Polynomial.eq_C_of_degree_le_zero (Order.le_of_lt_succ h1)
  refine ⟨q, r.coeff 0, ?_⟩
  rw [heq, hr, Polynomial.coe_C, Polynomial.coeff_C_zero]

section
variable {O : Type} [CommRing O] [IsLocalRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {L : Type} [Field L] [Algebra O L]

theorem ev_C (ev : PowerSeries O →ₐ[O] PowerSeries L) (c : O) :
    ev (PowerSeries.C c) = PowerSeries.C (algebraMap O L c) := by
  simpa [PowerSeries.algebraMap_apply] using ev.commutes c

theorem X_dvd_ev_iff (hinj : Function.Injective (algebraMap O L)) {x : O} (hx : ¬ IsUnit x)
    (ev : PowerSeries O →ₐ[O] PowerSeries L) {w : PowerSeries L}
    (hev : ev PowerSeries.X = PowerSeries.C (algebraMap O L x) + PowerSeries.X * w)
    (a : PowerSeries O) :
    PowerSeries.X ∣ ev a ↔ (PowerSeries.X - PowerSeries.C x) ∣ a := by
  have hXev : ev (PowerSeries.X - PowerSeries.C x) = PowerSeries.X * w := by
    rw [map_sub, hev, ev_C]; ring
  constructor
  · intro h
    obtain ⟨b, c, rfl⟩ := exists_div_X_sub_C x hx a
    rw [map_add (f := _), map_mul, hXev, ev_C] at h
    have h2 : PowerSeries.X ∣ PowerSeries.C (algebraMap O L c) :=
      (dvd_add_right (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)).1 h
    rw [PowerSeries.X_dvd_iff, PowerSeries.constantCoeff_C] at h2
    have hc : c = 0 := hinj (by rw [h2, map_zero])
    subst hc
    rw [map_zero, add_zero]
    exact dvd_mul_right _ _
  · rintro ⟨b, rfl⟩
    rw [map_mul, hXev, mul_assoc]
    exact dvd_mul_right _ _

theorem X_pow_dvd_ev_iff (hinj : Function.Injective (algebraMap O L)) {x : O} (hx : ¬ IsUnit x)
    (ev : PowerSeries O →ₐ[O] PowerSeries L) {w : PowerSeries L} (hw : IsUnit w)
    (hev : ev PowerSeries.X = PowerSeries.C (algebraMap O L x) + PowerSeries.X * w)
    (m : ℕ) (a : PowerSeries O) :
    PowerSeries.X ^ m ∣ ev a ↔ (PowerSeries.X - PowerSeries.C x) ^ m ∣ a := by
  have hXev : ev (PowerSeries.X - PowerSeries.C x) = PowerSeries.X * w := by
    rw [map_sub, hev, ev_C]; ring
  induction m generalizing a with
  | zero => simp
  | succ m ih =>
    constructor
    · intro h
      have h1 : PowerSeries.X ∣ ev a := (dvd_pow_self _ (Nat.succ_ne_zero m)).trans h
      obtain ⟨b, rfl⟩ := (X_dvd_ev_iff hinj hx ev hev a).1 h1
      rw [map_mul, hXev, pow_succ', mul_assoc] at h
      have h2 : PowerSeries.X ^ m ∣ w * ev b := (mul_dvd_mul_iff_left PowerSeries.X_ne_zero).1 h
      have h3 : PowerSeries.X ^ m ∣ ev b := (IsUnit.dvd_mul_left hw).1 h2
      rw [pow_succ']
      exact mul_dvd_mul_left _ ((ih b).1 h3)
    · rintro ⟨b, rfl⟩
      rw [pow_succ' (PowerSeries.X - PowerSeries.C x), mul_assoc, map_mul, hXev,
        pow_succ' (PowerSeries.X : PowerSeries L), mul_assoc]
      exact mul_dvd_mul_left _ (dvd_mul_of_dvd_right ((ih _).2 (dvd_mul_right _ _)) _)

theorem prime_X_sub_C (hinj : Function.Injective (algebraMap O L)) {x : O} (hx : ¬ IsUnit x)
    (ev : PowerSeries O →ₐ[O] PowerSeries L) {w : PowerSeries L}
    (hev : ev PowerSeries.X = PowerSeries.C (algebraMap O L x) + PowerSeries.X * w) :
    Prime (PowerSeries.X - PowerSeries.C x : PowerSeries O) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h1 := congrArg (PowerSeries.coeff 1) h
    simp at h1
  · rw [PowerSeries.isUnit_iff_constantCoeff]
    simpa using hx
  · intro a b h
    rw [← X_dvd_ev_iff hinj hx ev hev, map_mul] at h
    rw [← X_dvd_ev_iff hinj hx ev hev a, ← X_dvd_ev_iff hinj hx ev hev b]
    exact PowerSeries.X_prime.2.2 _ _ h

end

theorem prod_prime_pow_dvd {R ι : Type} [CommRing R] [IsDomain R] (p : ι → R) (m : ι → ℕ)
    (hp : ∀ k, Prime (p k)) (hne : ∀ j k, p j ∣ p k → j = k) (a : R)
    (h : ∀ k, p k ^ m k ∣ a) (s : Finset ι) : (∏ k ∈ s, p k ^ m k) ∣ a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    obtain ⟨t, ht⟩ := ih
    have hnd : ¬ p i ∣ ∏ k ∈ s, p k ^ m k := by
      intro hd
      obtain ⟨k, hk, hdk⟩ := ((hp i).dvd_finsetProd_iff _).1 hd
      have hik := hne i k ((hp i).dvd_of_dvd_pow hdk)
      subst hik
      exact hi hk
    have hdt : p i ^ m i ∣ t :=
      (hp i).pow_dvd_of_dvd_mul_left _ hnd (by rw [← ht]; exact h i)
    rw [ht, mul_comm _ t]
    exact mul_dvd_mul_right hdt _

theorem weierstrass_test : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O], ∀ (LL : Type) [Field LL] [Algebra O LL] [IsFractionRing O LL] (ι : Type) [Fintype ι] (x : ι → O) (m : ι → ℕ), Function.Injective x → (∀ k, ¬ IsUnit (x k)) → ∀ (ev : ι → (PowerSeries O →ₐ[O] PowerSeries LL)), (∀ k, ∃ w : PowerSeries LL, IsUnit w ∧ ev k PowerSeries.X = PowerSeries.C (algebraMap O LL (x k)) + PowerSeries.X * w) → ∀ a : PowerSeries O, (∀ k, PowerSeries.X ^ m k ∣ ev k a) ↔ (∏ k, (PowerSeries.X - PowerSeries.C (x k)) ^ m k) ∣ a := by
  intro O _ _ _ _ LL _ _ _ ι _ x m hxinj hxu ev hev a
  have hinj : Function.Injective (algebraMap O LL) := IsFractionRing.injective O LL
  have key : ∀ k, PowerSeries.X ^ m k ∣ ev k a ↔
      (PowerSeries.X - PowerSeries.C (x k)) ^ m k ∣ a := by
    intro k
    obtain ⟨w, hw, hwk⟩ := hev k
    exact X_pow_dvd_ev_iff hinj (hxu k) (ev k) hw hwk (m k) a
  simp_rw [key]
  constructor
  · intro h
    refine prod_prime_pow_dvd (fun k => PowerSeries.X - PowerSeries.C (x k)) m ?_ ?_ a h
      Finset.univ
    · intro k
      obtain ⟨w, -, hwk⟩ := hev k
      exact prime_X_sub_C hinj (hxu k) (ev k) hwk
    · intro j k hjk
      obtain ⟨w, -, hwj⟩ := hev j
      have h1 := (X_dvd_ev_iff hinj (hxu j) (ev j) hwj _).2 hjk
      rw [map_sub, hwj, ev_C, PowerSeries.X_dvd_iff] at h1
      have h2 : algebraMap O LL (x j) = algebraMap O LL (x k) := by
        simpa [sub_eq_zero] using h1
      exact hxinj (hinj h2)
  · intro h k
    exact (Finset.dvd_prod_of_mem _ (Finset.mem_univ k)).trans h

end GlobalTheory.Per
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualMeasureExistsUniqueFourierInversion
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.SelfDualUniq

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]

theorem fourB_nnsmul (μ : Measure V) (c : NNReal) (B : V → V → ℂ) (f : V → ℂ) (y : V) :
    fourB (c • μ) B f y = ((c : ℝ) : ℂ) * fourB μ B f y := by
  simp only [fourB, integral_smul_nnreal_measure]
  rw [NNReal.smul_def, Complex.real_smul]

theorem fourB_const_mul (μ : Measure V) (a : ℂ) (B : V → V → ℂ) (g : V → ℂ) (y : V) :
    fourB μ B (fun z => a * g z) y = a * fourB μ B g y := by
  simp only [fourB, mul_assoc]
  exact integral_const_mul a _

theorem selfDual_unique [IsTopologicalAddGroup V] [T2Space V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [BorelSpace V] {B : V → V → ℂ} {μ ν : Measure V}
    (hμ : SelfDual μ B) (hν : SelfDual ν B) (f : V → ℂ) (hf : IsTest f) (h0 : f 0 ≠ 0) : ν = μ := by
  obtain ⟨hμH, hμI⟩ := hμ
  obtain ⟨hνH, hνI⟩ := hν
  have hc := Measure.isAddLeftInvariant_eq_smul ν μ
  set c := Measure.addHaarScalarFactor ν μ
  have key := hνI f hf 0
  rw [hc] at key
  have e : fourB (c • μ) B f = fun y => ((c : ℝ) : ℂ) * fourB μ B f y := funext (fourB_nnsmul μ c B f)
  rw [e, fourB_nnsmul, fourB_const_mul, hμI f hf 0, neg_zero] at key
  have hsq : (((c : ℝ) : ℂ) * ((c : ℝ) : ℂ) - 1) * f 0 = 0 := by linear_combination key
  have h1 : ((c : ℝ) : ℂ) * ((c : ℝ) : ℂ) = 1 := by
    have := (mul_eq_zero.1 hsq).resolve_right h0
    linear_combination this
  have h2 : (c : ℝ) * (c : ℝ) = 1 := by exact_mod_cast h1
  have h3 : (c : ℝ) = 1 := by nlinarith [c.coe_nonneg]
  have h4 : c = 1 := by exact_mod_cast h3
  rw [hc, h4, one_smul]

end GlobalTheory.JR.SelfDualUniq

namespace GlobalTheory.JR.SelfDualUniq

theorem isTest_fourB {F : Type} [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F]
    (ψ : AddChar F ℂ) (hψ : IsStdChar ψ)
    (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V]
    [MeasurableSpace V] [BorelSpace V] (β : LinearMap.BilinForm F V) (hs : β.IsSymm) (hn : β.Nondegenerate)
    (μ : Measure V) [μ.IsAddHaarMeasure] (f : V → ℂ) (hf : IsTest f) :
    IsTest (fourB μ (fun x y => ψ (β x y)) f) := by
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F V
  obtain ⟨-, hl⟩ := GlobalTheory.JR.exists_small_dual_lattices F ψ hψ V β hs hn
  obtain ⟨U, hU, hUinv⟩ := AbsInv.exists_nhds_invariant hf
  obtain ⟨M, N, hMU, -, -, -, hNc, hN, -⟩ := hl U hU
  have hβ : Continuous (fun p : V × V => β p.1 p.2) :=
    IsModuleTopology.continuous_bilinear_of_finite_left β
  have hev : ∀ᶠ w in 𝓝 (0 : V), ∀ x ∈ tsupport f, ψ (β x w) = 1 := by
    refine hf.2.isCompact.eventually_forall_of_forall_eventually fun x _ => ?_
    have hc : Continuous (fun z : V × V => β z.2 z.1) := hβ.comp continuous_swap
    have ho : IsOpen {z : V × V | ‖β z.2 z.1‖ < 1} := isOpen_lt (continuous_norm.comp hc) continuous_const
    have hmem : ((0 : V), x) ∈ {z : V × V | ‖β z.2 z.1‖ < 1} := by simp
    filter_upwards [ho.mem_nhds hmem] with z hz
    exact hψ.1 _ hz.le
  constructor
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro y
    have hev' : ∀ᶠ y' in 𝓝 y, ∀ x ∈ tsupport f, ψ (β x (y' - y)) = 1 := by
      have ht : Tendsto (fun y' : V => y' - y) (𝓝 y) (𝓝 0) := by
        have h := (continuous_sub_right y).tendsto y
        rwa [sub_self] at h
      exact ht.eventually hev
    filter_upwards [hev'] with y' hy'
    simp only [fourB]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ tsupport f
    · have : β x y' = β x y + β x (y' - y) := by simp
      simp only [this, AddChar.map_add_eq_mul, hy' x hx, mul_one]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  · refine HasCompactSupport.intro hNc fun y hy => ?_
    have : ¬ ∀ x ∈ M, ψ (β x y) = 1 := fun h => hy ((hN y).2 h)
    push_neg at this
    obtain ⟨m, hm, hne⟩ := this
    refine AbsInv.integral_eq_zero_of_translate μ _ m _ hne fun x => ?_
    simp only [map_add (f := _), LinearMap.add_apply, AddChar.map_add_eq_mul, hUinv M hMU x m hm]
    ring

theorem selfDual_exists_unique_isTest : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] (β : LinearMap.BilinForm F V), β.IsSymm → β.Nondegenerate → (∃! μ : Measure V, SelfDual μ (fun x y => ψ (β x y))) ∧ ∀ μ : Measure V, μ.IsAddHaarMeasure → ∀ f, IsTest f → IsTest (fourB μ (fun x y => ψ (β x y)) f) := by
  intro F E _ _ _ _ hU ψ hψ V _ _ _ _ _ _ _ β hs hn
  haveI := hU.ultraF
  haveI := hU.lcF
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F V
  obtain ⟨-, hl⟩ := GlobalTheory.JR.exists_small_dual_lattices F ψ hψ V β hs hn
  obtain ⟨M, N, -, hMo, hMc, -, -, -, -⟩ := hl Set.univ Filter.univ_mem
  have hM1 : IsClopen (M : Set V) := ⟨AddSubgroup.isClosed_of_isOpen M hMo, hMo⟩
  set f : V → ℂ := ⇑(LocallyConstant.charFn ℂ hM1) with hfdef
  have hf : IsTest f := ⟨(LocallyConstant.charFn ℂ hM1).isLocallyConstant,
    HasCompactSupport.intro hMc fun x hx => by simp [f, LocallyConstant.coe_charFn, hx]⟩
  have hf0 : f 0 ≠ 0 := by simp [f, LocallyConstant.coe_charFn, M.zero_mem]
  refine ⟨?_, fun μ hμ g hg => isTest_fourB ψ hψ V β hs hn μ g hg⟩
  obtain ⟨μ, hμ⟩ := EtMeas.exists_selfDual F ψ hψ V β hs hn
  exact ⟨μ, hμ, fun ν hν => selfDual_unique hμ hν f hf hf0⟩

end GlobalTheory.JR.SelfDualUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeparatedRootsAdditivePoly
section
open Polynomial
open Classical

namespace GlobalTheory

theorem separated_roots_additive_poly : ∀ (l : ℕ) [Fact l.Prime] (E M h : ℕ) (a : ℕ → ℂ_[l]) (ρ : ℝ), M + h ≤ E → (∀ k, k ≤ E → ‖a k‖ ≤ 1) → ‖a (M + h)‖ = 1 → 0 < ρ → ρ < 1 → ‖a M‖ * ρ ^ l ^ M = ‖(l : ℂ_[l])‖ → (∀ k, M < k → k ≤ E → ‖a k‖ * ρ ^ l ^ k < ‖(l : ℂ_[l])‖) → ∃ Z : Finset ℂ_[l], l ^ h ≤ Z.card ∧ (∀ W ∈ Z, ‖W‖ ≤ 1 ∧ ∑ k ∈ Finset.range (E + 1), a k * W ^ l ^ k = 0) ∧ ∀ W ∈ Z, ∀ W' ∈ Z, W ≠ W' → ρ < ‖W - W'‖ := by
  intro l _ E M h a ρ hMh ha1 haMh hρ0 hρ1 haM hak
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hinj : Function.Injective (fun k : ℕ => l ^ k) := Nat.pow_right_injective hl
  set G : ℂ_[l][X] := ∑ k ∈ Finset.range (E + 1), Polynomial.monomial (l ^ k) (a k) with hG
  have hcoeff : ∀ j, G.coeff j = ∑ k ∈ Finset.range (E + 1), if l ^ k = j then a k else 0 := by
    intro j
    simp only [hG, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial_apply]
  have hcd : G.coeff (l ^ (M + h)) = a (M + h) := by
    rw [hcoeff, Finset.sum_eq_single (M + h)]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro hh; exact hb (hinj hh)
    · intro hn; exact absurd (Finset.mem_range.2 (by omega)) hn
  have hcd0 : G.coeff (l ^ (M + h)) ≠ 0 := by
    rw [hcd]; intro h0; rw [h0, norm_zero] at haMh; exact zero_ne_one haMh
  have hcle : ∀ j, ‖G.coeff j‖ ≤ 1 := by
    intro j
    rw [hcoeff]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k hk => ?_
    split_ifs
    · exact ha1 k (by have := Finset.mem_range.1 hk; omega)
    · simp
  have hrc := (_root_.GlobalTheory.card_roots_le_radius_bounds ℂ_[l] G 1 (l ^ (M + h)) one_pos hcd0).1 (by
    intro j; simp only [one_pow, mul_one]; rw [hcd, haMh]; exact hcle j)
  set s := G.roots.filter fun z => ‖z‖ ≤ 1 with hs
  have hG0 : G ≠ 0 := by
    intro h0; apply hcd0; rw [h0]; simp
  obtain ⟨Z, hZc, hZs, hZsep⟩ := _root_.GlobalTheory.multiset_many_separated_points ℂ_[l] s ρ (l ^ h) (l ^ M) hρ0.le
    (pow_pos (by omega) _) (by rw [mul_comm, ← pow_add]; exact hrc) (by
      intro W hW
      have hW1 : ‖W‖ ≤ 1 := (Multiset.mem_filter.1 hW).2
      refine le_trans (Multiset.card_le_card ?_) (_root_.GlobalTheory.few_roots_small_disc l E M a ρ W (by omega) ha1 hρ0 hρ1 haM hak hW1)
      exact Multiset.monotone_filter_left _ (Multiset.filter_le _ _))
  refine ⟨Z, hZc, fun W hW => ?_, hZsep⟩
  have hWs := Multiset.mem_filter.1 (hZs W hW)
  refine ⟨hWs.2, ?_⟩
  have hr := (Polynomial.mem_roots hG0).1 hWs.1
  have := hr.eq_zero
  rw [hG, Polynomial.eval_finsetSum] at this
  simpa [Polynomial.eval_monomial] using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SingleMemOfSupportSubset
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.Per

theorem single_mem_of_support_subset {LL D : Type} [Field LL] [AddCommGroup D] [Module LL D]
    (u : LL) (Λ : Submodule LL (ℤ → D)) (hu : u ≠ 0) (hr : ∀ k : ℤ, k ≠ 0 → u ^ k ≠ 1)
    (hγ : ∀ x ∈ Λ, (fun k => u ^ k • x k) ∈ Λ) (S : Finset ℤ) :
    ∀ x ∈ Λ, (∀ k, k ∉ S → x k = 0) → ∀ k, Pi.single k (x k) ∈ Λ := by
  induction S using Finset.induction_on with
  | empty =>
    intro x _ hx k
    rw [hx k (by simp), Pi.single_zero]
    exact Λ.zero_mem
  | insert a S' ha ih =>
    intro x hxΛ hx

    have hne : ∀ k, k ≠ a → u ^ k - u ^ a ≠ 0 := by
      intro k hk h
      apply hr (k - a) (sub_ne_zero.mpr hk)
      rw [zpow_sub₀ hu, sub_eq_zero.mp h, div_self (zpow_ne_zero a hu)]
    have hyΛ : (fun k => u ^ k • x k) - u ^ a • x ∈ Λ := Λ.sub_mem (hγ x hxΛ) (Λ.smul_mem _ hxΛ)
    have hyv : ∀ k, ((fun k => u ^ k • x k) - u ^ a • x) k = (u ^ k - u ^ a) • x k := by
      intro k
      simp [sub_smul]
    have hy : ∀ k, k ∉ S' → ((fun k => u ^ k • x k) - u ^ a • x) k = 0 := by
      intro k hk
      rw [hyv]
      by_cases hka : k = a
      · rw [hka, sub_self, zero_smul]
      · rw [hx k (by simp [hka, hk]), smul_zero]
    have hoff : ∀ k, k ≠ a → Pi.single k (x k) ∈ Λ := by
      intro k hk
      have h1 := ih _ hyΛ hy k
      rw [hyv] at h1
      have e : Pi.single k (x k) =
          (u ^ k - u ^ a)⁻¹ • (Pi.single k ((u ^ k - u ^ a) • x k) : ℤ → D) := by
        rw [Pi.single_smul, smul_smul, inv_mul_cancel₀ (hne k hk), one_smul]
      rw [e]
      exact Λ.smul_mem _ h1
    intro k
    by_cases hka : k = a
    · rw [hka]
      have hsum : (∑ j ∈ S', Pi.single j (x j)) ∈ Λ :=
        Λ.sum_mem (fun j hj => hoff j (by rintro rfl; exact ha hj))
      have e : Pi.single a (x a) = x - ∑ j ∈ S', Pi.single j (x j) := by
        funext j
        rw [Pi.sub_apply, Finset.sum_apply, Finset.sum_pi_single]
        by_cases hjS : j ∈ S'
        · have hja : j ≠ a := by rintro rfl; exact ha hjS
          simp [hjS, hja]
        · by_cases hja : j = a
          · rw [hja]
            simp [ha]
          · simp [hjS, hja, hx j (by simp [hja, hjS])]
      rw [e]
      exact Λ.sub_mem hxΛ hsum
    · exact hoff k hka

end GlobalTheory.Per
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableQuadraticGaussIntegralMulNorm
section
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
open scoped Pointwise ENNReal NNReal

namespace GlobalTheory.JR.WeilQuad.GaussTrans

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ (t s : A.Kˣ), (∃ ℓ : A.L, A.NL ℓ = s) → ∀ G : ℂ, IsStableGauss A ψ x μ t G → IsStableGauss A ψ x μ ((t * s : A.Kˣ) : A.K) (G * ((A.absK s : ℂ))⁻¹) := by
  intro F E _ _ _ _ U A ψ x μ ω hH t s ⟨ℓ, hℓ⟩ G ⟨Λ₀, ho₀, hc₀, hG⟩
  have := U.charZero; have := U.ultraF; have := U.lcF
  have : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  have := EtMeas.finite_L A
  obtain ⟨⟨b⟩, hinj, hN, -, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.K
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.L
  have : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  have : ContinuousStar A.L := ⟨IsModuleTopology.continuous_of_linearMap (EtMeas.starF A)⟩
  have hμ : μ.IsAddHaarMeasure := hH.2.2.2.1.1
  have hs' : algebraMap A.K A.L (s : A.K) = ℓ * star ℓ := by rw [← hℓ, hN]
  have hu : IsUnit ℓ := isUnit_of_mul_isUnit_left (hs' ▸ (s.isUnit.map (algebraMap A.K A.L)))
  set u : A.Lˣ := hu.unit with hu_def
  have hul : (u : A.L) = ℓ := hu.unit_spec
  have hmod : distribHaarChar A.L u = distribHaarChar A.K s :=
    GlobalTheory.JR.ModuleNorm.distribHaarChar_eq_norm A.K A.L b.equivFun.symm
      (IsModuleTopology.continuous_of_linearMap (b.equivFun.symm.toLinearMap.restrictScalars F))
      (IsModuleTopology.continuous_of_linearMap (b.equivFun.toLinearMap.restrictScalars F)) u s
      (by rw [hul]; exact hs')
  have hmap : μ.map (fun y => u • y) = (distribHaarChar A.L u⁻¹ : ℝ≥0∞) • μ := by
    ext S hS
    rw [Measure.map_apply (measurable_const_smul u) hS, Set.preimage_smul, Measure.smul_apply, smul_eq_mul,
      distribHaarChar_mul]
  have hemb : MeasurableEmbedding (fun y : A.L => u • y) :=
    (Homeomorph.smul u).measurableEmbedding
  have key : ∀ Λ : AddSubgroup A.L, gaussInt A ψ x μ ((t * s : A.Kˣ) : A.K) Λ =
      ((A.absK s : ℂ))⁻¹ * gaussInt A ψ x μ t (u • Λ : AddSubgroup A.L) := by
    intro Λ
    have h1 : gaussInt A ψ x μ ((t * s : A.Kˣ) : A.K) Λ =
        ∫ y in (Λ : Set A.L), A.psiK ψ ((t : A.K) * x * A.NL (u • y)) ∂μ := by
      unfold gaussInt
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      have hNm : A.NL (u • y) = s * A.NL y := by
        rw [Units.smul_def, hul, smul_eq_mul]
        unfold Et.NL
        rw [map_mul]
        exact congrArg (· * _) hℓ
      simp only
      rw [hNm]
      push_cast; ring_nf
    have h2 := hemb.setIntegral_map (μ := μ) (fun z => A.psiK ψ ((t : A.K) * x * A.NL z)) ((u • Λ : AddSubgroup A.L) : Set A.L)
    have hpre : (fun y => u • y) ⁻¹' ((u • Λ : AddSubgroup A.L) : Set A.L) = Λ := by
      ext y
      simp only [Set.mem_preimage, SetLike.mem_coe]
      exact ⟨fun h => by simpa using (AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem.1 h),
        fun h => AddSubgroup.smul_mem_pointwise_smul _ _ _ h⟩
    rw [hpre, hmap, Measure.restrict_smul, integral_smul_measure] at h2
    rw [h1, ← h2]
    unfold gaussInt
    rw [Complex.real_smul, EtMeas.absK_unit, ENNReal.coe_toReal, map_inv, hmod]
    congr 1
    push_cast
    rfl
  have hcoe : ∀ (v : A.Lˣ) (M : AddSubgroup A.L), ((v • M : AddSubgroup A.L) : Set A.L) = v • (M : Set A.L) :=
    fun v M => AddSubgroup.coe_pointwise_smul v M
  refine ⟨u⁻¹ • Λ₀, ?_, ?_, fun Λ hoΛ hcΛ hle => ?_⟩
  · rw [hcoe]; exact ho₀.smul _
  · rw [hcoe]; exact hc₀.smul _
  · rw [key, hG (u • Λ) (by rw [hcoe]; exact hoΛ.smul _) (by rw [hcoe]; exact hcΛ.smul _) ?_, mul_comm]
    intro z hz
    have : u⁻¹ • z ∈ Λ := hle (AddSubgroup.smul_mem_pointwise_smul _ _ _ hz)
    exact AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem.2 this

end GlobalTheory.JR.WeilQuad.GaussTrans
end

