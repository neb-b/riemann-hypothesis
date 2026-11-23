module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairOperatorStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)

namespace GlobalTheory.JacquetExact

section Abstract

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem exists_finset_of_mem_twKer {τ : Representation ℂ G W} {N : Subgroup G} {w : W}
    (hw : w ∈ twKer τ N 1) :
    ∃ S : Finset G, (∀ u ∈ S, u ∈ N) ∧ ∀ H : Subgroup G, (∀ u ∈ S, u ∈ H) → w ∈ twKer τ H 1 := by
  classical
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, v, rfl⟩ := hx
    refine ⟨{(u : G)}, by simp, fun H hH => ?_⟩
    simpa using GlobalTheory.IwahoriInj.sub_mem_twKer (π := τ) (hH u (by simp)) v
  | zero => exact ⟨∅, by simp, fun _ _ => zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨S, hS, hx⟩ := hx
    obtain ⟨T, hT, hy⟩ := hy
    refine ⟨S ∪ T, fun u hu => (Finset.mem_union.1 hu).elim (hS u) (hT u), fun H hH => add_mem
      (hx H fun u hu => hH u (Finset.mem_union_left _ hu))
      (hy H fun u hu => hH u (Finset.mem_union_right _ hu))⟩
  | smul c x _ hx =>
    obtain ⟨S, hS, hx⟩ := hx
    exact ⟨S, hS, fun H hH => Submodule.smul_mem _ c (hx H hH)⟩

theorem map_mem_twKer {σ : Representation ℂ G V} {τ : Representation ℂ G W} (f : σ.IntertwiningMap τ)
    {H : Subgroup G} {v : V} (hv : v ∈ twKer σ H 1) : f v ∈ twKer τ H 1 := by
  have h : twKer σ H 1 ≤ (twKer τ H 1).comap f.toLinearMap := Submodule.span_le.2 (by
    rintro _ ⟨n, v, rfl⟩
    refine Submodule.subset_span ⟨n, f v, ?_⟩
    simp [f.isIntertwining])
  exact h hv

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem mem_twKer_of_compact {σ : Representation ℂ G V} {τ : Representation ℂ G W} (hτ : IsSmooth τ)
    (f : σ.IntertwiningMap τ) (hf : Function.Injective f) {H : Subgroup G} (hH : IsCompact (H : Set G))
    {v : V} (hv : f v ∈ twKer τ H 1) : v ∈ twKer σ H 1 := by
  have hσ : IsSmooth σ := (IsSubquotient.of_injective f hf).isSmooth hτ
  obtain ⟨v', hv', he⟩ := IwahoriOnto.exists_fixed_map_eq hσ hH (twKer σ H 1).mkQ v fun h hh =>
    (Submodule.Quotient.eq _).2 (GlobalTheory.IwahoriInj.sub_mem_twKer hh v)
  have h1 : v' - v ∈ twKer σ H 1 := (Submodule.Quotient.eq _).1 he
  have h2 : f v' ∈ twKer τ H 1 := by
    have := add_mem (map_mem_twKer f h1) hv
    rwa [map_sub, sub_add_cancel] at this
  have h3 : f v' ∈ fixed τ H := GlobalTheory.IwahoriInj.mem_fixed.2 fun h hh => by
    rw [← f.isIntertwining, GlobalTheory.IwahoriInj.mem_fixed.1 hv' h hh]
  have h4 : v' = 0 := hf ((GlobalTheory.IwahoriInj.eq_zero_of_fixed hτ hH h3 h2).trans (map_zero f).symm)
  rw [h4, zero_sub] at h1
  exact neg_mem_iff.1 h1

end Abstract

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {V W : Type} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] {s : ℕ} {d : Fin s → ℕ}

theorem jacMap_injective (e : (Σ a, Fin (d a)) ≃ n) {σ : Representation ℂ (GL n k) V}
    {τ : Representation ℂ (GL n k) W} (hτ : IsSmooth τ) (f : σ.IntertwiningMap τ)
    (hf : Function.Injective f) : Function.Injective (jacMap e f) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h1 : f v ∈ twKer τ (unipRad k e) 1 := (Submodule.Quotient.mk_eq_zero _).1 hx
  let c : n → ℤ := fun i => (blk e i).val
  have hN : unipRad k e = unipOf k c := unipRad_eq_unipOf k fun i j => by simp [c]
  obtain ⟨S, hS, h2⟩ := exists_finset_of_mem_twKer h1
  have hcompact : ∃ H : Subgroup (GL n k), H ≤ unipOf k c ∧
      IsCompact (H : Set (GL n k)) ∧ ∀ u ∈ S, u ∈ H := by
    let K (m : ℕ) := GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c m)
    have hentries {u : GL n k} (hu : u ∈ unipOf k c) :
        ∀ᶠ m : ℕ in Filter.atTop, ∀ i j, Deep ((m : ℤ) * (c i - c j)) (u.val i j) := by
      simp only [Filter.eventually_all]
      intro i j
      by_cases hij : c i < c j
      · filter_upwards [GlobalTheory.IwahoriInj.eventually_deep (u.val i j)] with m hm
        exact hm.mono (by nlinarith [Int.natCast_nonneg m])
      · rw [mem_unipOf.1 hu i j hij]
        refine Filter.Eventually.of_forall fun m => ?_
        by_cases heq : i = j
        · subst j
          simp [GlobalTheory.IwahoriInj.deep_zero_iff]
        · simp [one_apply_ne heq, GlobalTheory.IwahoriInj.deep_zero]
    have hmem : ∀ᶠ m in Filter.atTop, ∀ u ∈ S, u ∈ K m :=
      (Filter.eventually_all_finset S).2 fun u hu => by
        have hu' := hN ▸ hS u hu
        exact (hentries hu').and (hentries (inv_mem hu'))
    obtain ⟨m, hm⟩ := hmem.exists
    refine ⟨K m ⊓ unipOf k c, inf_le_right, ?_, fun u hu => ⟨hm u hu, hN ▸ hS u hu⟩⟩
    obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
    have hclosed : IsClosed (unipOf k c : Set (GL n k)) := by
      have heq : (unipOf k c : Set (GL n k)) =
          ⋂ i, ⋂ j, ⋂ (_ : ¬ c i < c j), {g : GL n k | g.val i j = (1 : Matrix n n k) i j} := by
        ext g
        simp only [SetLike.mem_coe, mem_unipOf, Set.mem_iInter, Set.mem_ofPred_eq]
      rw [heq]
      exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
        isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const
    rw [Subgroup.coe_inf]
    exact (GlobalTheory.IwahoriInj.isCompact_grp _).inter_right hclosed
  obtain ⟨H, hle, hH, hSH⟩ := hcompact
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  exact GlobalTheory.IwahoriInj.twKer_mono (hle.trans hN.ge) (mem_twKer_of_compact hτ f hf hH (h2 H hSH))

theorem jacMap_surjective (e : (Σ a, Fin (d a)) ≃ n) {σ : Representation ℂ (GL n k) V}
    {τ : Representation ℂ (GL n k) W} (f : σ.IntertwiningMap τ)
    (hf : Function.Surjective f) : Function.Surjective (jacMap e f) := fun y => by
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨v, rfl⟩ := hf w
  exact ⟨Submodule.Quotient.mk v, rfl⟩

theorem isSubquotient_jac (e : (Σ a, Fin (d a)) ≃ n) {π : Representation ℂ (GL n k) V}
    {τ : Representation ℂ (GL n k) W} (hτ : IsSmooth τ) (h : IsSubquotient π τ) :
    IsSubquotient (jac e π) (jac e τ) := by
  obtain ⟨S, f, hf⟩ := h
  let ι : S.toRepresentation.IntertwiningMap τ := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  exact (IsSubquotient.of_surjective _ (jacMap_surjective e f hf)).trans
    (.of_injective _ (jacMap_injective e hτ ι Subtype.val_injective))

end Local

theorem inSupport_of_isSubquotient (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (V : Type) [AddCommGroup V]
    [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL n k) V)
    (τ : Representation ℂ (GL n k) W) (χ : kˣ →* ℂˣ) (hτ : IsSmooth τ) (h : IsSubquotient π τ)
    (hχ : InSupport π χ) : InSupport τ χ := by
  obtain ⟨s, d, e, a, ha, Y, i1, i2, σ, hσ, hsub, hact⟩ := hχ
  exact ⟨s, d, e, a, ha, Y, i1, i2, σ, hσ, hsub.trans (isSubquotient_jac e hτ h), hact⟩

end GlobalTheory.JacquetExact
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IndicatorIdentity
section
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity GlobalTheory.PairOp

noncomputable section
namespace GlobalTheory.KernelComm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type}

section Indicator
open scoped Classical

variable [Fintype n'] (q : Unif k) {P₁ : Pair k n'} {e₁ : n' → k} (he : P₁.HasVal e₁ 1) (Q : Pair k n)
  (x : Matrix n n' k)
include he


open Classical in
theorem sum_target :
    ∑ Q₁ ∈ withKer Q.lat with cross q Q₁ Q = 1, phiOne P₁ Q₁ x = midInd q P₁.ker e₁ Q x := by
  have hm : ∀ Q₁ : Pair k n, Maps P₁ Q₁ x ↔ (∀ y ∈ P₁.ker, x *ᵥ y ∈ Q₁.ker) ∧ Q₁.HasVal (x *ᵥ e₁) 1 := fun Q₁ => by
    rw [maps_iff_glue he Q₁.hasVal_vec, Pair.hasVal_one_iff Q₁.hasVal_vec]
  rw [midInd, mulVec_smul]
  split_ifs with h
  · have hg : IsGlue Q.lat (x *ᵥ e₁) := (isGlue_iff q).2 ⟨Q.isLat, fun h0 =>
      one_ne_zero (h.2.unique (Pair.mem_ker.1 (Pair.smul_mem_ker q.mem_max h0))), h.2.mem⟩
    rw [Finset.sum_eq_single_of_mem (glue hg)]
    · exact if_pos ((hm _).2 ⟨by rw [glue_ker]; exact h.1, glue_hasVal hg⟩)
    · exact Finset.mem_filter.2 ⟨mem_withKer.2 (glue_ker hg),
        (cross_hasVal q (glue_ker hg).symm (glue_hasVal hg)).unique h.2⟩
    · exact fun Q₁ h1 h2 => if_neg fun h3 =>
        h2 ((eq_glue_iff hg).2 ⟨mem_withKer.1 (Finset.mem_filter.1 h1).1, ((hm _).1 h3).2⟩)
  · refine Finset.sum_eq_zero fun Q₁ h1 => if_neg fun h3 => h ?_
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 h1
    rw [mem_withKer] at h1
    exact ⟨h1 ▸ ((hm _).1 h3).1, h2 ▸ cross_hasVal q h1.symm ((hm _).1 h3).2⟩


open Classical in
theorem sum_source :
    midInd q P₁.ker e₁ Q x = ∑ P ∈ withLat P₁.ker with cross q P₁ P = 1, phiOne P Q x := by
  rw [midInd]
  have hq : q.1 • e₁ ∈ P₁.ker := Pair.smul_mem_ker q.mem_max he.mem
  split_ifs with h
  · let f : P₁.ker →ₗ[𝒪[k]] 𝓀[k] := Q.fn ∘ₗ ((Matrix.mulVecLin x).restrictScalars 𝒪[k]).restrict h.1
    have hf : ∀ y : P₁.ker, Q.HasVal (x *ᵥ y) (f y) := fun y => ⟨h.1 y y.2, rfl⟩
    have h1 : f ⟨_, hq⟩ = 1 := (hf ⟨_, hq⟩).unique h.2
    let R : Pair k n' := ⟨P₁.ker, P₁.ker_isLat, f, fun h0 => by simp [h0] at h1⟩
    have hR : Maps R Q x := ⟨h.1, fun _ => rfl⟩
    rw [Finset.sum_eq_single_of_mem R]
    · exact (if_pos hR).symm
    · exact Finset.mem_filter.2 ⟨mem_withLat.2 rfl, (cross_hasVal q (P := R) rfl he).unique ⟨hq, h1⟩⟩
    · refine fun P hP h2 => if_neg fun h3 => h2 (Pair.ext fun y a => ?_)
      have hl : P.lat = R.lat := mem_withLat.1 (Finset.mem_filter.1 hP).1
      rw [maps_iff_hasVal] at hR h3
      constructor
      · intro hy
        have h4 := R.hasVal_fn ⟨y, hl ▸ hy.mem⟩
        exact (hR _ _ h4).unique (h3 _ _ hy) ▸ h4
      · intro hy
        have h4 := P.hasVal_fn ⟨y, hl ▸ hy.mem⟩
        exact (h3 _ _ h4).unique (hR _ _ hy) ▸ h4
  · refine (Finset.sum_eq_zero fun P h1 => if_neg fun h3 => h ?_).symm
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 h1
    rw [mem_withLat] at h1
    exact ⟨h1 ▸ h3.1, maps_iff_hasVal.1 h3 _ _ (h2 ▸ cross_hasVal q h1 he)⟩

end Indicator

theorem card_withKer (q : Unif k) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] :
    (withKer L).card = (withLat L).card := by
  classical
  by_cases hfull : L.IsFullLattice k
  · letI : L.IsFullLattice k := hfull
    letI := Fintype.ofFinite (Red L)
    letI := Fintype.ofFinite (Module.Dual 𝓀[k] (Red L))
    have hc : Fintype.card (Red L) = Fintype.card (Module.Dual 𝓀[k] (Red L)) := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := 𝓀[k]),
        Module.natCard_eq_pow_finrank (K := 𝓀[k]) (V := Module.Dual 𝓀[k] (Red L)), Subspace.dual_finrank_eq]
    rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones, sum_withKer L q, sum_withLat L]
    simp [hc]
  · have hk : withKer L = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro P hP
      apply hfull
      rw [← mem_withKer.mp hP]
      exact P.ker_isLat)
    have hl : withLat L = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro P hP
      apply hfull
      rw [← mem_withLat.mp hP]
      exact P.isLat)
    simp [hk, hl]

variable [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem exists_det (q : Unif k) (P : Pair k n) :
    ∃ d : GL n k, d • P.ker = P.lat ∧ Matrix.GeneralLinearGroup.det d = q.unit⁻¹ := by
  obtain ⟨i⟩ : Nonempty n := by
    by_contra h
    haveI := not_nonempty_iff.1 h
    exact P.fn_ne (LinearMap.ext fun y => by rw [Subsingleton.elim y 0]; simp)
  obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq (GL n k) (stdPair k i) P
  have hdet : (Matrix.diagonal (Function.update (1 : n → k) i (q.1 : k))).det = (q.1 : k) := by
    simp [Matrix.det_diagonal, Finset.prod_update_of_mem]
  let d : GL n k := Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hdet ▸ q.ne_zero)
  have hd : ∀ (y : n → k) j, (d • y) j = Function.update (1 : n → k) i (q.1 : k) j * y j := fun y j =>
    Matrix.mulVec_diagonal _ _ _
  have h1 : d⁻¹ • (stdPair k i).ker = (stdPair k i).lat := by
    ext y
    rw [mem_smul_iff, inv_inv, Pair.mem_ker, stdPair_hasVal]
    change _ ↔ y ∈ stdLat k n
    rw [mem_stdLat]
    constructor
    · rintro ⟨h, h0⟩ j
      by_cases hj : j = i
      · subst hj
        obtain ⟨s, hs⟩ := q.mem_max_iff.1 ((residue_eq_zero_iff _).1 h0)
        have h2 : (q.1 : k) * y j = q.1 * s := by simpa [hd] using congrArg Subtype.val hs
        rw [mul_left_cancel₀ q.ne_zero h2]
        exact s.2
      · simpa [hd, hj] using h j
    · intro h
      refine ⟨fun j => ?_, (residue_eq_zero_iff _).2 (q.mem_max_iff.2 ⟨⟨y i, h i⟩, Subtype.ext (by simp [hd])⟩)⟩
      by_cases hj : j = i
      · subst hj
        simpa [hd] using mul_mem q.1.2 (h j)
      · simpa [hd, hj] using h j
  refine ⟨a * d⁻¹ * a⁻¹, by rw [Pair.smul_ker, Pair.smul_lat, mul_smul, mul_smul, inv_smul_smul, h1], ?_⟩
  rw [map_mul, map_mul, map_inv, map_inv, mul_inv_cancel_comm, _root_.inv_inj]
  exact Units.ext hdet

theorem valuation_det (q : Unif k) (P : Pair k n) {g : GL n k} (hg : g • P.ker = P.lat) :
    valuation k ((Matrix.GeneralLinearGroup.det g * q.unit : kˣ) : k) = 1 := by
  obtain ⟨d, hd, hdet⟩ := exists_det q P
  have := valuation_det_of_fix P.ker (h := d⁻¹ * g) (by rw [mul_smul, hg, ← hd, inv_smul_smul])
  rwa [map_mul, map_inv, hdet, inv_inv, mul_comm] at this

variable {V' V : Type} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V] [Module ℂ V]
  {μ : kˣ →* ℂˣ} {π' : Representation ℂ (GL n' k) V'} {π : Representation ℂ (GL n k) V}
  {θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V}
  (hμ : IsUnram μ) (hθ : IsEquivTheta μ π' π θ) (P₀ : Pair k n') (Q₀ : Pair k n)

theorem eq_of_base {φ φ' : Form k n V} (h : φ ∈ EqForm π) (h' : φ' ∈ EqForm π) (e : φ Q₀ = φ' Q₀) : φ = φ' := by
  ext Q
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GL n k) Q₀ Q
  rw [h g, h' g, e]

end GlobalTheory.KernelComm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableZetaIntegrand
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)

namespace GlobalTheory.ZetaConvergence

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_nabs_le {K : Set k} (hK : IsCompact K) : ∃ B : ℝ, ∀ x : kˣ, (x : k) ∈ K → nabs k x ≤ B := by
  obtain ⟨y, hy⟩ := hK.elim_directed_cover (fun y : kˣ => GlobalTheory.SplitWeil.cball y)
    (fun y => GlobalTheory.SplitWeil.isOpen_cball y)
    (fun x _ => by
      by_cases hx : x = 0
      · exact Set.mem_iUnion.2 ⟨1, by simp [hx, GlobalTheory.SplitWeil.cball]⟩
      · exact Set.mem_iUnion.2 ⟨Units.mk0 x hx, by simp [GlobalTheory.SplitWeil.cball]⟩)
    (fun a b => by
      rcases le_total (valuation k (a : k)) (valuation k (b : k)) with h | h
      · exact ⟨b, fun z hz => le_trans (show valuation k z ≤ _ from hz) h, subset_rfl⟩
      · exact ⟨a, subset_rfl, fun z hz => le_trans (show valuation k z ≤ _ from hz) h⟩)
  exact ⟨nabs k y, fun x hx => nabs_le_of_valuation_le (hy hx)⟩

theorem integrable_zetaIntegrand : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] (c : GL n k → ℂ) (α : ℝ), Continuous c → (∀ N : ℕ, ∃ C : ℝ, ∀ g : GL n k, (∀ i j, Deep (-(N : ℤ)) (g.val i j)) → ‖c g‖ ≤ C * nabs k (GeneralLinearGroup.det g) ^ (-α)) → ∀ Φ ∈ SB (Matrix n n k), ∃ b : ℝ, ∀ s : ℂ, b < s.re → Integrable (zetaIntegrand Φ c s) (volGL ν n) := by
  intro k _ _ _ _ _ _ ν _ n _ _ c α hc hb Φ hΦ
  obtain ⟨N, -, hN, -⟩ := GlobalTheory.SBUniform.exists_bound_period k n Φ hΦ
  obtain ⟨C, hC⟩ := hb N
  obtain ⟨hl, hK⟩ : IsLocallyConstant Φ ∧ HasCompactSupport Φ := hΦ
  obtain ⟨B, hB⟩ := exists_nabs_le (IsCompact.image hK (f := fun x : Matrix n n k => x.det)
    continuous_id.matrix_det)
  have := GlobalTheory.SplitWeil.secondCountable k
  have := GlobalTheory.SplitWeil.t2Space k
  have : BorelSpace (Matrix n n k) := inferInstanceAs (BorelSpace (n → n → k))
  have : (volM ν n n).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : BorelSpace (GL n k) := SplitFlip.borel_GL
  have : SecondCountableTopology (GL n k) := SplitFlip.secondCountable_GL
  have hE := GlobalTheory.SplitWeil.Model.measurableEmbedding_val (k := k) n
  have hd := continuous_density_volGL (k := k) (n := n)
  have hn : IsLocallyConstant fun g : GL n k => nabs k (GeneralLinearGroup.det g) :=
    (isLocallyConstant_nabs k).comp_continuous GeneralLinearGroup.continuous_det
  have hI : Integrable (fun g : GL n k => Φ g.val) ((volM ν n n).comap fun g : GL n k => g.val) := by
    have h1 : Integrable Φ (volM ν n n) := hl.continuous.integrable_of_hasCompactSupport hK
    refine hE.integrable_map_iff.1 ?_
    rw [hE.map_comap]
    exact h1.restrict
  refine ⟨α + Fintype.card n - ((Fintype.card n : ℝ) - 1) / 2, fun s hs => ?_⟩
  set t : ℂ := s + ((Fintype.card n : ℂ) - 1) / 2 with ht
  have htr : t.re = s.re + ((Fintype.card n : ℝ) - 1) / 2 := by
    have : ((Fintype.card n : ℂ) - 1) / 2 = ((((Fintype.card n : ℝ) - 1) / 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [ht, this, Complex.add_re, Complex.ofReal_re]
  have he : 0 ≤ -(Fintype.card n : ℝ) + -α + t.re := by linarith
  have hz : Continuous (zetaIntegrand Φ c s) :=
    ((hl.continuous.comp Units.continuous_val).mul hc).mul (hn.comp fun r : ℝ => (r : ℂ) ^ t).continuous
  unfold volGL
  rw [integrable_withDensity_iff_integrable_smul' hd.measurable
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine (hI.norm.mul_const (|C| * B ^ (-(Fintype.card n : ℝ) + -α + t.re))).mono'
    (hd.measurable.ennreal_toReal.aestronglyMeasurable.smul hz.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun g => ?_)
  have hp := nabs_pos' k (GeneralLinearGroup.det g)
  by_cases h0 : Φ g.val = 0
  · simp [zetaIntegrand, h0]
  have h1 : nabs k (GeneralLinearGroup.det g) ≤ B := hB _ ⟨g.val, subset_tsupport _ h0, rfl⟩
  have h2 := (hC g (hN _ h0)).trans
    (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hp.le _))
  rw [norm_smul, ENNReal.toReal_ofReal (Real.rpow_nonneg hp.le _), zetaIntegrand, norm_mul, norm_mul,
    val_absPow, Complex.norm_cpow_eq_rpow_re_of_pos hp, ← ht, Real.norm_of_nonneg (Real.rpow_nonneg hp.le _)]
  set a := nabs k (GeneralLinearGroup.det g)
  calc _ ≤ a ^ (-(Fintype.card n : ℝ)) * (‖Φ g.val‖ * (|C| * a ^ (-α)) * a ^ t.re) := by gcongr
    _ = ‖Φ g.val‖ * (|C| * a ^ (-(Fintype.card n : ℝ) + -α + t.re)) := by
      rw [Real.rpow_add hp, Real.rpow_add hp]; ring
    _ ≤ _ := by gcongr

end GlobalTheory.ZetaConvergence
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralBiInvariantHasSumDoubleCoset
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

open scoped Pointwise

namespace GlobalTheory

theorem integral_biInvariant_hasSum_doubleCoset :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  (m : Measure G) [m.IsHaarMeasure] (J : Subgroup G), IsOpen (J : Set G) → IsCompact (J : Set G) →
  ∀ (ι : Type) [Countable ι] (x : ι → G),
    Pairwise (Function.onFun Disjoint fun i => DoubleCoset.doubleCoset (x i) (J : Set G) (J : Set G)) →
  ∀ F : G → ℂ, (∀ g, ∀ j ∈ J, ∀ j' ∈ J, F (j * g * j') = F g) →
    (∀ g, F g ≠ 0 → ∃ i, g ∈ DoubleCoset.doubleCoset (x i) (J : Set G) (J : Set G)) →
    Summable (fun i => m.real (DoubleCoset.doubleCoset (x i) (J : Set G) (J : Set G)) * ‖F (x i)‖) →
    Integrable F m ∧
    HasSum (fun i => (m.real (DoubleCoset.doubleCoset (x i) (J : Set G) (J : Set G)) : ℂ) * F (x i)) (∫ g, F g ∂m) ∧
    HasSum (fun c : DoubleCoset.Quotient (J : Set G) (J : Set G) =>
      (m.real (DoubleCoset.doubleCoset c.out (J : Set G) (J : Set G)) : ℂ) * F c.out) (∫ g, F g ∂m) := by
  first
  | exact @_root_.GlobalTheory.TwistedOperatorMainTheorem.main_thm
  | exact _root_.GlobalTheory.TwistedOperatorMainTheorem.main_thm
  | (apply _root_.GlobalTheory.TwistedOperatorMainTheorem.main_thm <;> assumption)
  | (intros; apply _root_.GlobalTheory.TwistedOperatorMainTheorem.main_thm <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TwistedOperatorMainTheorem.main_thm <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TwistedOperatorMainTheorem.main_thm ..)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenIsCompactTwoBlockParahoricSubgroup
section
noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection
  GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

namespace GlobalTheory.ParahoricOpenCompact

theorem KOne_le_parahoric (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] :
    KOne k (A ⊕ D) ≤ parahoric k A D := by
  intro g hg
  refine mem_parahoric.2 ⟨StepData.KOne_le_KO hg, fun i j => ?_⟩
  have h := StepData.mem_KOne.1 hg
  have h' : valuation k ((g.val - 1) (.inr i) (.inl j)) < 1 := h _ _
  simpa using h'

theorem isOpen_isCompact_parahoric : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D],
    IsOpen (parahoric k A D : Set (GL (A ⊕ D) k)) ∧ IsCompact (parahoric k A D : Set (GL (A ⊕ D) k)) := by
  intro k _ _ _ _ A D _ _ _ _
  have ho : IsOpen (parahoric k A D : Set (GL (A ⊕ D) k)) :=
    Subgroup.isOpen_mono (KOne_le_parahoric k A D) StepData.isOpen_KOne
  exact ⟨ho, SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho)
    fun _ hg => (mem_parahoric.1 hg).1⟩

end GlobalTheory.ParahoricOpenCompact
end
end

