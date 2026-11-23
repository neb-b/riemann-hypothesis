module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1160
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1134
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalization

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactUnipotentInCompactSubgroup
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix GlobalTheory.InertSupp

namespace GlobalTheory.UnipCptSub

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

theorem mem_grp_of_le {c : n → ℤ} {g : GL n k} (hg : g ∈ unipOf k c) {m M : ℕ} (hmM : m ≤ M)
    (h : g ∈ GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c m)) :
    g ∈ GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c M) := by
  have key : ∀ x : GL n k, x ∈ unipOf k c → (∀ i j, GlobalTheory.IwahoriInj.Deep ((m : ℤ) * (c i - c j)) (x.val i j)) →
      ∀ i j, GlobalTheory.IwahoriInj.Deep ((M : ℤ) * (c i - c j)) (x.val i j) := by
    intro x hx hd i j
    by_cases hij : c i < c j
    · refine (hd i j).mono ?_
      have : (m : ℤ) ≤ M := by exact_mod_cast hmM
      nlinarith
    · rw [mem_unipOf.1 hx i j hij]
      by_cases e : i = j
      · subst e
        simp [GlobalTheory.IwahoriInj.deep_zero_iff]
      · simp [one_apply_ne e, GlobalTheory.IwahoriInj.deep_zero]
  exact ⟨key g hg h.1, key g⁻¹ (inv_mem hg) h.2⟩

theorem isOpen_grp (c : n → ℤ) (m : ℕ) :
    IsOpen (GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c m) : Set (GL n k)) := by
  have e : (GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c m) : Set (GL n k)) =
      (⋂ i, ⋂ j, {g : GL n k | GlobalTheory.IwahoriInj.Deep ((m : ℤ) * (c i - c j)) (g.val i j)}) ∩
      ⋂ i, ⋂ j, {g : GL n k | GlobalTheory.IwahoriInj.Deep ((m : ℤ) * (c i - c j)) ((g⁻¹).val i j)} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    rfl
  rw [e]
  refine IsOpen.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
  · exact (GlobalTheory.SBUniform.isOpen_deep _).preimage (Units.continuous_val.matrix_elem i j)
  · exact (GlobalTheory.SBUniform.isOpen_deep _).preimage (Units.continuous_coe_inv.matrix_elem i j)

theorem unipB_eq_unipOf (N : ℕ) :
    unipB k (Fin N) = unipOf k (fun i : Fin N => ((i : ℕ) : ℤ)) := by
  ext g
  rw [mem_unipB, mem_unipOf]
  constructor
  · rintro ⟨h1, h2⟩ i j hij
    have hji : j ≤ i := by
      rw [not_lt] at hij
      exact Fin.le_def.2 (by exact_mod_cast hij)
    rcases hji.lt_or_eq with h | h
    · rw [h1 i j h, one_apply_ne (ne_of_gt h)]
    · subst h; rw [h2 j, one_apply_eq]
  · intro h
    refine ⟨fun i j hji => ?_, fun i => ?_⟩
    · have : ¬ ((i : ℕ) : ℤ) < ((j : ℕ) : ℤ) := by
        have := Fin.lt_def.1 hji
        omega
      rw [h i j this, one_apply_ne (ne_of_gt hji)]
    · rw [h i i (lt_irrefl _), one_apply_eq]

theorem exists_compact_subgroup_of_isCompact :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}
      (Q : Set (GL (Fin N) k)), IsCompact Q → Q ⊆ (unipB k (Fin N) : Set (GL (Fin N) k)) →
      ∃ U₀ : Subgroup (GL (Fin N) k), IsCompact (U₀ : Set (GL (Fin N) k)) ∧ Q ⊆ (U₀ : Set (GL (Fin N) k)) := by
  intro k _ _ _ _ N Q hQ hQU
  set c : Fin N → ℤ := fun i => ((i : ℕ) : ℤ)
  rw [unipB_eq_unipOf] at hQU
  let V : ℕ → Set (GL (Fin N) k) := fun m =>
    (GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c m) : Set (GL (Fin N) k)) ∪ (unipOf k c : Set _)ᶜ
  have hVo : ∀ m, IsOpen (V m) := fun m =>
    (isOpen_grp c m).union (GlobalTheory.UnipCompact.isClosed_unipOf c).isOpen_compl
  have hVmono : Monotone V := by
    intro m M hmM g hg
    rcases hg with hg | hg
    · by_cases hu : g ∈ unipOf k c
      · exact Or.inl (mem_grp_of_le hu hmM hg)
      · exact Or.inr hu
    · exact Or.inr hg
  have hcov : Q ⊆ ⋃ m, V m := fun g hg =>
    Set.mem_iUnion.2 (((GlobalTheory.UnipCompact.eventually_mem_grp (hQU hg)).exists).imp fun _ h => Or.inl h)
  obtain ⟨M, hM⟩ := hQ.elim_directed_cover V hVo hcov hVmono.directed_le
  refine ⟨GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c M) ⊓ unipOf k c, ?_, fun g hg => ?_⟩
  · rw [Subgroup.coe_inf]
    exact (GlobalTheory.IwahoriInj.isCompact_grp _).inter_right (GlobalTheory.UnipCompact.isClosed_unipOf c)
  · rcases hM hg with h | h
    · exact ⟨h, hQU hg⟩
    · exact absurd (hQU hg) h

end GlobalTheory.UnipCptSub
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousSectionPolynomialGrowth
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts

namespace GlobalTheory.SectionGrowth

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {B : LB Y}

theorem local_factor (hB : B.IsLB) {s : B.ι → CxPts p σ → ℂ} (hs : s ∈ fibSec p σ B)
    (hc : ∀ j, ContinuousOn (s j) (ptsIn p σ (B.U j))) {i : B.ι} {V Q : Y.Opens} (hV : V ≤ B.U i)
    (u : Γ(Y, V)) (η : Γ(Y, Q)) (hη : Y.basicOpen η = Q ⊓ V)
    (hu : resG Y (inf_le_right : Q ⊓ V ≤ V) u * resG Y (inf_le_left : Q ⊓ V ≤ Q) η = 1)
    {y₀ : CxPts p σ} (hy₀ : y₀ ∈ ptsIn p σ Q) :
    ∃ (F : CxPts p σ → ℂ) (N : ℕ), ContinuousAt F y₀ ∧
      ∀ᶠ y in 𝓝 y₀, y ∈ ptsIn p σ V → s i y = F y * ev p σ V u y ^ N := by

  obtain ⟨j, hy₀j⟩ : ∃ j, y₀ ∈ ptsIn p σ (B.U j) := ⟨_, mem_pick hB y₀⟩
  obtain ⟨W, hWa, hzW, hWle⟩ := (Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens)
    (Opens.mem_inf.2 ⟨mem_ptsIn.1 hy₀, mem_ptsIn.1 hy₀j⟩ :
      y₀.1 (IsLocalRing.closedPoint ℂ) ∈ Q ⊓ B.U j)
  have hWQ : W ≤ Q := hWle.trans inf_le_left
  have hWj : W ≤ B.U j := hWle.trans inf_le_right
  have hy₀W : y₀ ∈ ptsIn p σ W := mem_ptsIn.2 hzW

  set η' : Γ(Y, W) := resG Y hWQ η with hη'
  have hD : Y.basicOpen η' = W ⊓ (Q ⊓ V) := by
    rw [← hη]
    exact Y.basicOpen_res η (homOfLE hWQ).op
  have hDij : Y.basicOpen η' ≤ B.U i ⊓ B.U j := by
    rw [hD]
    exact le_inf (inf_le_right.trans (inf_le_right.trans hV)) (inf_le_left.trans hWj)

  have := hWa.isLocalization_basicOpen η'
  obtain ⟨⟨a, _, n, rfl⟩, han⟩ :=
    IsLocalization.surj (Submonoid.powers η') (resG Y hDij (B.g i j).val)
  rw [map_pow] at han
  refine ⟨fun y => ev p σ W a y * s j y, n, ?_, ?_⟩
  · exact ((continuousOn_ev a).continuousAt ((isOpen_ptsIn W).mem_nhds hy₀W)).mul
      ((hc j).continuousAt ((isOpen_ptsIn _).mem_nhds hy₀j))
  · filter_upwards [(isOpen_ptsIn W).mem_nhds hy₀W] with y hyW hyV
    have hyQ : y ∈ ptsIn p σ Q := ptsIn_mono hWQ hyW
    have hyj : y ∈ ptsIn p σ (B.U j) := ptsIn_mono hWj hyW
    have hyi : y ∈ ptsIn p σ (B.U i) := ptsIn_mono hV hyV
    have hyQV : y ∈ ptsIn p σ (Q ⊓ V) := mem_ptsIn_inf.2 ⟨hyQ, hyV⟩
    have huv : ev p σ V u y * ev p σ Q η y = 1 := by
      have h1 := congrArg (fun f => ev p σ (Q ⊓ V) f y) hu
      rwa [ev_mul, ev_res _ hyQV, ev_res _ hyQV, ev_one hyQV] at h1
    have hηne : ev p σ Q η y ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at huv
      exact zero_ne_one huv
    have hηW : ev p σ W η' y = ev p σ Q η y := ev_res hWQ hyW η
    have hyD : y ∈ ptsIn p σ (Y.basicOpen η') :=
      (mem_ptsIn_basicOpen hyW η').2 (hηW ▸ hηne)
    have hal : ∀ b : Γ(Y, W),
        ev p σ (Y.basicOpen η') (algebraMap Γ(Y, W) Γ(Y, Y.basicOpen η') b) y = ev p σ W b y :=
      fun b => ev_res (Y.basicOpen_le η') hyD b
    have e1 := congrArg (evHom hyD) han
    rw [map_mul, map_pow, ← ev_eq hyD, ← ev_eq hyD, ← ev_eq hyD, hal, hal, ev_res hDij hyD,
      hηW] at e1
    have hg : gv p σ B i j y = ev p σ (B.U i ⊓ B.U j) (B.g i j).val y := rfl
    have hun : (ev p σ V u y * ev p σ Q η y) ^ n = 1 := by rw [huv, one_pow]
    show s i y = ev p σ W a y * s j y * ev p σ V u y ^ n
    rw [hs.1 i j y hyi hyj, hg]
    linear_combination (s j y * ev p σ V u y ^ n) * e1 -
      (ev p σ (B.U i ⊓ B.U j) (B.g i j).val y * s j y) * hun

theorem global_bound {X : Type*} [TopologicalSpace X] [CompactSpace X] (S : Set X) (f T : X → ℝ)
    (hT : ∀ x, 1 ≤ T x)
    (h : ∀ x₀, ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧ ∀ᶠ x in 𝓝 x₀, x ∈ S → f x ≤ C * T x ^ m) :
    ∃ (C : ℝ) (m : ℕ), ∀ x ∈ S, f x ≤ C * T x ^ m := by
  choose C m hC hev using h
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover
    (fun x₀ => {x | x ∈ S → f x ≤ C x₀ * T x ^ m x₀}) (fun x₀ _ => hev x₀)
  refine ⟨∑ x₀ ∈ t, C x₀, t.sup m, fun x hx => ?_⟩
  obtain ⟨x₀, hx₀t, hx₀⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  have h1 : f x ≤ C x₀ * T x ^ m x₀ := hx₀ hx
  have h2 : T x ^ m x₀ ≤ T x ^ t.sup m := pow_le_pow_right₀ (hT x) (Finset.le_sup hx₀t)
  have h3 : C x₀ ≤ ∑ x₀ ∈ t, C x₀ := Finset.single_le_sum (fun i _ => hC i) hx₀t
  have h4 : 0 ≤ T x ^ t.sup m := pow_nonneg (zero_le_one.trans (hT x)) _
  calc f x ≤ C x₀ * T x ^ m x₀ := h1
    _ ≤ C x₀ * T x ^ t.sup m := mul_le_mul_of_nonneg_left h2 (hC x₀)
    _ ≤ (∑ x₀ ∈ t, C x₀) * T x ^ t.sup m := mul_le_mul_of_nonneg_right h3 h4

end GlobalTheory.SectionGrowth

namespace GlobalTheory

theorem continuous_section_polynomial_growth : ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ), IsProjOver p → ∀ (B : LB Y), B.IsLB → ∀ s ∈ fibSec p (RingHom.id ℂ) B, (∀ j, ContinuousOn (s j) (ptsIn p (RingHom.id ℂ) (B.U j))) → ∀ (i : B.ι) (V : Y.Opens) (n : ℕ) (u : Fin n → Γ(Y, V)), V ≤ B.U i → (∀ z : Y, ∃ (Q : Y.Opens) (η : Γ(Y, Q)) (l : Fin n), z ∈ Q ∧ Y.basicOpen η = Q ⊓ V ∧ resG Y (inf_le_right : Q ⊓ V ≤ V) (u l) * resG Y (inf_le_left : Q ⊓ V ≤ Q) η = 1) → ∃ (C : ℝ) (m : ℕ), ∀ y ∈ ptsIn p (RingHom.id ℂ) V, ‖s i y‖ ≤ C * (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ m := by
  intro Y p hp B hB s hs hc i V n u hV hloc
  have := CxPts.compactSpace (RingHom.id ℂ) hp
  obtain ⟨C, m, hCm⟩ := SectionGrowth.global_bound (ptsIn p (RingHom.id ℂ) V) (fun y => ‖s i y‖)
    (fun y => 1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖)
    (fun y => le_add_of_nonneg_right (Finset.sum_nonneg fun l _ => norm_nonneg _)) (by
      intro y₀
      obtain ⟨Q, η, l, hzQ, hη, hu⟩ := hloc (y₀.1 (IsLocalRing.closedPoint ℂ))
      obtain ⟨F, N, hF, hev⟩ :=
        SectionGrowth.local_factor hB hs hc hV (u l) η hη hu (mem_ptsIn.2 hzQ)
      have hFb : ∀ᶠ y in 𝓝 y₀, ‖F y‖ < ‖F y₀‖ + 1 :=
        hF.norm.eventually (gt_mem_nhds (lt_add_one _))
      refine ⟨‖F y₀‖ + 1, N, by positivity, ?_⟩
      filter_upwards [hev, hFb] with y hy1 hy2 hyV
      have hle : ‖ev p (RingHom.id ℂ) V (u l) y‖ ≤
          1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖ := by
        have := Finset.single_le_sum (f := fun l => ‖ev p (RingHom.id ℂ) V (u l) y‖)
          (fun l _ => norm_nonneg _) (Finset.mem_univ l)
        linarith
      show ‖s i y‖ ≤ (‖F y₀‖ + 1) * (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ N
      rw [hy1 hyV, norm_mul, norm_pow]
      exact mul_le_mul hy2.le (pow_le_pow_left₀ (norm_nonneg _) hle N) (by positivity)
        (by positivity))
  exact ⟨C, m, hCm⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetWirtingerAntiholomorphicDerivEqSum
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem det_dbar_eq_sum_dbar : ∀ {n : ℕ} (f : Fin n → V n → ℂ) (j : Fin n) (v : V n), (∀ i, ContDiffAt ℝ 2 (f i) v) → (Matrix.of fun i b => dbar (f i) v (coordVec b)).det = ∑ w : Equiv.Perm (Fin n), ((Equiv.Perm.sign w : ℤ) : ℂ) * dbar (fun x => f j x * ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) v (coordVec (w j)) := by
  intro n f j v hf
  have hP := GlobalTheory.T.piola_identity_wirtingerAntiholomorphic f j v (fun i _ => hf i)
  have hd : ∀ w : Equiv.Perm (Fin n), DifferentiableAt ℝ
      (fun x => ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) v := fun w =>
    (HasFDerivAt.finsetProd (u := Finset.univ.erase j) (g := fun i x => dbar (f i) x (coordVec (w i)))
      (fun i _ => (differentiableAt_dbar_apply (hf i) _).hasFDerivAt)).differentiableAt
  have hj : DifferentiableAt ℝ (f j) v := (hf j).differentiableAt (by norm_num)
  have key : ∀ w : Equiv.Perm (Fin n), ((Equiv.Perm.sign w : ℤ) : ℂ) *
      dbar (fun x => f j x * ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) v (coordVec (w j)) =
      ((Equiv.Perm.sign w : ℤ) : ℂ) * ∏ i, dbar (f i) v (coordVec (w i)) +
      f j v * (((Equiv.Perm.sign w : ℤ) : ℂ) *
        dbar (fun x => ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) v (coordVec (w j))) := by
    intro w
    rw [dbar_mul hj (hd w), ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    ring
  rw [Finset.sum_congr rfl (fun w _ => key w), Finset.sum_add_distrib, ← Finset.mul_sum, hP, mul_zero, add_zero,
    ← Matrix.det_transpose, Matrix.det_apply']
  rfl

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrPlaceCentreOnBaseOfEtaleTowerOverNormalLocal
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.FieldPair

theorem Place.ord_eq_zero_iff_isUnit {L : Type} [Field L] {cL : ℂ →+* L} (P : Place cL) {u : P.ring}
    (hu : u ≠ 0) : P.ord (u : L) = 0 ↔ IsUnit u := by
  refine ⟨fun h => ?_, P.ord_eq_zero⟩
  have hu' : (u : L) ≠ 0 := fun e => hu (Subtype.ext e)
  have hi : (u : L)⁻¹ ∈ P.ring := by
    rw [← P.ord_nonneg_iff (inv_ne_zero hu'), P.ord_inv, h, neg_zero]
  exact IsUnit.of_mul_eq_one ⟨_, hi⟩ (Subtype.ext (mul_inv_cancel₀ hu'))

theorem Place.exists_centre_of_isPrimeOf : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (T : Subring L) (P : Place cL), P.IsPrimeOf T →
    ∃ q : Ideal T, q.IsPrime ∧ q.height = 1 ∧ ∀ t : T, t ≠ 0 → (P.ord (t : L) = 0 ↔ t ∉ q) := by
  intro L _ cL T P hP
  have hC : ∀ t : T, (t : L) ∈ P.ring := fun t => hP.1 _ t.2
  let f : T →+* P.ring := T.subtype.codRestrict P.ring hC
  let q : Ideal T := (IsLocalRing.maximalIdeal P.ring).comap f
  haveI hq : q.IsPrime := Ideal.comap_isPrime _ _
  have hmem : ∀ t : T, t ∉ q ↔ IsUnit (f t) := fun t => by
    simp only [q, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  have hf : ∀ t : T, ((f t : P.ring) : L) = t := fun t => rfl
  have hord : ∀ t : T, t ≠ 0 → (P.ord (t : L) = 0 ↔ t ∉ q) := fun t ht => by
    rw [hmem t]
    have h0 : f t ≠ 0 := by
      intro e
      apply ht
      apply Subtype.ext
      rw [← hf t, e]
      simp
    have h1 := P.ord_eq_zero_iff_isUnit h0
    rw [hf t] at h1
    exact h1
  letI : Algebra T P.ring := f.toAlgebra
  haveI : IsLocalization.AtPrime P.ring q :=
    { map_units := fun y => (hmem y).1 y.2
      surj := fun z => by
        obtain ⟨a, ha, b, hb, hb0, hbo, e⟩ := hP.2 z z.2
        have hb' : (⟨b, hb⟩ : T) ∉ q :=
          (hord ⟨b, hb⟩ (fun e' => hb0 (congrArg Subtype.val e'))).1 hbo
        exact ⟨(⟨a, ha⟩, ⟨⟨b, hb⟩, hb'⟩), Subtype.ext e⟩
      exists_of_eq := fun {x y} e => ⟨1, by
        have h' : ((algebraMap T P.ring x : P.ring) : L) = ((algebraMap T P.ring y : P.ring) : L) :=
          congrArg Subtype.val e
        have : x = y := Subtype.ext h'
        rw [this]⟩ }
  have hd := IsLocalization.AtPrime.ringKrullDim_eq_height q P.ring
  rw [IsDiscreteValuationRing.ringKrullDim_eq_one] at hd
  refine ⟨q, hq, ?_, hord⟩
  exact_mod_cast hd.symm

end GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

theorem IsEtTower.flat {K L : Type} [Field K] [Field L] {cK : ℂ →+* K} {cL : ℂ →+* L} {r : ℕ}
    {R : Subring K} {T : Subring L} {ι : R →+* T} {ψ : T →+* R} {τ : Fin r → T}
    (h : IsEtTower cK R cL T ι ψ τ) : IsNoetherianRing R ∧ ι.Flat := by
  letI := (cK.codRestrict R h.base.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ R := h.base.essFiniteType
  haveI hR : IsNoetherianRing R := Algebra.EssFiniteType.isNoetherianRing ℂ R
  refine ⟨hR, ?_⟩
  let B := MvPolynomial (Fin r) R
  let e : B →+* T := MvPolynomial.eval₂Hom ι τ
  letI : Algebra B T := e.toAlgebra
  letI : Algebra R T := ι.toAlgebra
  haveI : IsScalarTower R B T := IsScalarTower.of_algebraMap_eq fun a => by
    show ι a = e (MvPolynomial.C a)
    exact (MvPolynomial.eval₂_C _ _ _).symm
  haveI : Algebra.FormallyEtale B T := h.etale
  have hc : (cL.codRestrict T h.top.const_mem) = e.comp ((algebraMap R B).comp (cK.codRestrict R h.base.const_mem)) := by
    refine RingHom.ext fun a => Subtype.ext ?_
    have h2 : e (MvPolynomial.C (cK.codRestrict R h.base.const_mem a)) = ι ⟨cK a, h.base.const_mem a⟩ :=
      MvPolynomial.eval₂_C _ _ _
    show cL a = ((e ((algebraMap R B) (cK.codRestrict R h.base.const_mem a)) : T) : L)
    rw [MvPolynomial.algebraMap_eq, h2, h.const]
  haveI : Algebra.EssFiniteType B T := by
    have h1 := h.top.essFiniteType
    rw [hc] at h1
    exact RingHom.EssFiniteType.of_comp _ h1
  haveI : Module.Flat B T := GlobalTheory.SmoothDescent.flat_of_formallySmooth_of_essFiniteType B T
  haveI : Module.Flat R T := Module.Flat.trans R B T
  exact RingHom.flat_algebraMap_iff.2 inferInstance

end GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

theorem centre_of_isEtTower : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (P : Place cL),
  IsEtTower cK R cL T ι ψ τ → P.IsPrimeOf T →
  (∀ g : R, g ≠ 0 → P.ord (ι g : L) = 0) ∨
  ∃ P0 : Place cK, P0.IsPrimeOf R ∧ ∀ g : R, g ≠ 0 → (P0.ord (g : K) = 0 ↔ P.ord (ι g : L) = 0) := by
  intro K L _ _ cK cL r R T ι ψ τ P h hP
  obtain ⟨-, hF⟩ := h.flat
  obtain ⟨q, hq, hq1, hqo⟩ := Place.exists_centre_of_isPrimeOf cL T P hP
  letI : Algebra R T := ι.toAlgebra
  haveI : Module.Flat R T := hF
  haveI : Algebra.HasGoingDown R T := Algebra.HasGoingDown.of_flat
  let p : Ideal R := q.comap ι
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  haveI : q.LiesOver p := ⟨rfl⟩
  have hinj : Function.Injective ι := fun a b e => by simpa [h.retr] using congrArg ψ e
  have hι : ∀ g : R, g ≠ 0 → (P.ord (ι g : L) = 0 ↔ g ∉ p) := fun g hg =>
    hqo (ι g) ((map_ne_zero_iff ι hinj).2 hg)
  by_cases hp0 : p = ⊥
  · left
    intro g hg
    exact (hι g hg).2 (by rw [hp0]; simpa using hg)
  · right
    have hp1 : p.height = 1 := by
      apply le_antisymm
      · rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl, Ideal.height_le_iff]
        intro p' hp' hlt
        haveI := hp'
        rw [Nat.cast_one, ENat.lt_one_iff_eq_zero, Ideal.height_eq_zero_iff_eq_bot]
        by_contra hne
        obtain ⟨Q, hQq, hQ, hQo⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (S := T) q hlt
        haveI := hQ
        have hQ0 : Q ≠ ⊥ := by
          rintro rfl
          apply hne
          rw [hQo.over]
          ext x
          simp only [Ideal.under, Ideal.mem_comap, Ideal.mem_bot]
          exact ⟨fun e => hinj (e.trans (map_zero ι).symm), fun e => by simp [e]⟩
        have h1 : 1 ≤ Q.height := ENat.one_le_iff_ne_zero.2 (mt Ideal.height_eq_zero_iff_eq_bot.1 hQ0)
        have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hQq
        rw [hq1] at h2
        have h3 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (by gcongr) h2
        exact absurd h3 (by decide)
      · exact ENat.one_le_iff_ne_zero.2 (mt Ideal.height_eq_zero_iff_eq_bot.1 hp0)
    obtain ⟨P0, h0, h0o⟩ := GlobalTheory.T.exists_place_isPrimeOf_of_height_one_normal_localModel cK R h.base h.normal p inferInstance hp1
    exact ⟨P0, h0, fun g hg => (h0o g hg).trans (hι g hg).symm⟩

end GlobalTheory.FieldPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfEvEqOfSmoothOfRelativeDimension
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CxPts

namespace GlobalTheory

theorem eq_of_ev_eq_of_smoothOfRelativeDimension :
    ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ) (D : ℕ), SmoothOfRelativeDimension D p → ∀ (W : Y.Opens) (a b : Γ(Y, W)), (∀ y ∈ ptsIn p (RingHom.id ℂ) W, ev p (RingHom.id ℂ) W a y = ev p (RingHom.id ℂ) W b y) → a = b := by
  intro Y p D hp W a b hab
  have hsm : Smooth p := SmoothOfRelativeDimension.smooth D p
  have hred : IsReduced Y :=
    (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field ℂ Y p hsm).1
  refine TopCat.Presheaf.IsSheaf.section_ext Y.IsSheaf fun x hx => ?_
  obtain ⟨U, hU, hxU, hUW⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens (show x ∈ W from hx)
  replace hU : IsAffineOpen U := hU
  refine ⟨U, hUW, hxU, ?_⟩
  have hc : (algX p U).FiniteType := by
    have h1 : (p.appLE ⊤ U (fun _ _ => trivial)).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
    exact h1.comp (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2)
  let : Algebra ℂ Γ(Y, U) := (algX p U).toAlgebra
  have : Algebra.FiniteType ℂ Γ(Y, U) := hc
  change resG Y hUW a = resG Y hUW b
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_algHom_complex _ fun e => ?_
  have hm := ofHom_mem (p := p) (σ := RingHom.id ℂ) hU e.toRingHom (fun c => e.commutes c)
  have h := hab _ (ptsIn_mono hUW hm)
  rw [← ev_res hUW hm, ← ev_res hUW hm, ev_ofHom, ev_ofHom] at h
  rw [map_sub, sub_eq_zero]
  exact h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssFiniteTypeOfLocalRingOfVarietyPoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory

theorem essFiniteType_of_isLocModel : ∀ {K : Type} [Field K] [Algebra ℂ K] (R : Subring K),
    IsLocModel (algebraMap ℂ K) R → Algebra.EssFiniteType ℂ K := by
  intro K _ _ R h
  letI : Algebra ℂ R := ((algebraMap ℂ K).codRestrict R h.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ R := h.essFiniteType
  haveI : IsScalarTower ℂ R K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsFractionRing R K := IsFractionRing.of_field R K fun z => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := h.frac z
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, by
      show z = a / b
      rw [eq_div_iff hb0, e]⟩
  haveI : Algebra.EssFiniteType R K :=
    Algebra.EssFiniteType.of_isLocalization K (nonZeroDivisors R)
  exact Algebra.EssFiniteType.comp ℂ R K

end GlobalTheory
end

