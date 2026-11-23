module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.CrystallineAtPlaces
public import Mathlib
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.LocalRingCardinality.Bundle0002
public import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0044
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataParams
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.WeaklyAdmissibleFiltrations.Statement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0041
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemTwistedDualJumpsWithoutBlockIff
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem half_int_eq (R : Ranks) : ((((R.t : ℤ) - 1) / 2 : ℤ) : ℚ) = ((R.t : ℚ) - 1) / 2 := by
  obtain ⟨k, hk⟩ := R.t_odd
  rw [hk]
  push_cast
  have : ((2 * (k : ℤ) + 1 - 1) / 2) = k := by omega
  rw [this]; push_cast; ring

theorem mem_cloud_iff {R : Ranks} (P : HCParam R) (j : Fin R.m) (X : ℤ) :
    X ∈ cloud P j ↔ ∃ a, (X : ℚ) = P.e j + P.v a + ((R.t : ℚ) - 1) / 2 := by
  obtain ⟨ze, hze⟩ := P.e_int j
  unfold cloud
  simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨zv, hzv⟩ := P.v_int a
    refine ⟨a, ?_⟩
    rw [← ha, hze, hzv, Int.floor_intCast, Int.floor_intCast]
    push_cast
    rw [half_int_eq]
  · rintro ⟨a, ha⟩
    obtain ⟨zv, hzv⟩ := P.v_int a
    refine ⟨a, ?_⟩
    rw [hze, hzv, Int.floor_intCast, Int.floor_intCast]
    rw [hze, hzv, ← half_int_eq] at ha
    exact_mod_cast ha.symm

theorem mem_lows_iff {R : Ranks} (P : HCParam R) (j : Fin R.m) (X : ℤ) :
    X ∈ lows P j ↔ ∃ a, (X : ℚ) = P.e j - P.b a + ((R.t : ℚ) - 1) / 2 := by
  obtain ⟨ze, hze⟩ := P.e_int j
  unfold lows
  simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨zv, hzv⟩ := P.b_int a
    refine ⟨a, ?_⟩
    rw [← ha, hze, hzv, Int.floor_intCast, Int.floor_intCast]
    push_cast
    rw [half_int_eq]
  · rintro ⟨a, ha⟩
    obtain ⟨zv, hzv⟩ := P.b_int a
    refine ⟨a, ?_⟩
    rw [hze, hzv, Int.floor_intCast, Int.floor_intCast]
    rw [hze, hzv, ← half_int_eq] at ha
    exact_mod_cast ha.symm

theorem mem_twistedDualJumpsWithoutBlock_iff {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool) (u : ℤ) :
    u ∈ jT2 P j s ↔ (if s then -u - 1 else (R.t : ℤ) - 1 - (-u - 1)) ∈ cloud P j + lows P j := by
  unfold jT2 jW
  cases s
  · simp only [Bool.false_eq_true, if_false, Multiset.map_map, Function.comp_def, Multiset.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      convert hx using 1; ring
    · intro h
      exact ⟨_, h, by ring⟩
  · simp only [if_true, Multiset.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      convert hx using 1; ring
    · intro h
      exact ⟨_, h, by ring⟩

theorem jumps_rat {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool) (u : ℤ) :
    (u ∈ jT2 P j s ↔ ((∃ a, (if s then (-(u : ℚ) - 1) else (R.t : ℚ) - 1 - (-(u : ℚ) - 1)) = P.e j + P.v a + ((R.t : ℚ) - 1) / 2) ∨ ∃ a, (if s then (-(u : ℚ) - 1) else (R.t : ℚ) - 1 - (-(u : ℚ) - 1)) = P.e j - P.b a + ((R.t : ℚ) - 1) / 2)) ∧ (u ∈ jT1 P j s ↔ u ∈ jT2 P j s ∨ ∃ c : ℕ, c < R.t ∧ -u - 1 = c) := by
  have hcast : (if s then (-(u : ℚ) - 1) else (R.t : ℚ) - 1 - (-(u : ℚ) - 1)) =
      (((if s then -u - 1 else (R.t : ℤ) - 1 - (-u - 1)) : ℤ) : ℚ) := by
    split_ifs <;> push_cast <;> ring
  refine ⟨?_, ?_⟩
  · rw [mem_twistedDualJumpsWithoutBlock_iff, Multiset.mem_add, hcast, mem_cloud_iff, mem_lows_iff]
  · unfold jT1 jR
    rw [Multiset.map_add (f := _), Multiset.mem_add]
    show u ∈ jT2 P j s ∨ _ ↔ _
    apply or_congr Iff.rfl
    unfold block
    simp only [Multiset.map_map, Function.comp_def, Multiset.mem_map, Multiset.mem_range]
    constructor
    · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, by ring⟩
    · rintro ⟨c, hc, h⟩; exact ⟨c, hc, by omega⟩

end GlobalTheory.HTW.Rec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemberFormsStableOfReferenceTuple
section
open Formalism.BasicNotions Classical

namespace GlobalTheory.KFiMu0

theorem fi_eq_range' {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL] {embLL : LL →+* ℂ} {Pl : Rows.Places LL}
    {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R} {C : ColumnChain R Tau hc} {A : ColumnsAtT R C} {P : PeriodMap R C}
    (M : MemberForms LL embLL Pl Tau hc C A P) (j : ℕ) : M.Fi j = Submodule.span ℂ (Set.range (M.emb j)) := by
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · rw [← (M.emb_basis j).2]
    exact Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨_, rfl⟩)
  · rintro _ ⟨x, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← (M.emb_basis j).2, ← (M.lat j).b.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem carries_one {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL] {embLL : LL →+* ℂ} {Pl : Rows.Places LL}
    {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R} {C C' : ColumnChain R Tau hc} (h : C' = C)
    {A : ColumnsAtT R C} {P : PeriodMap R C} {A' : ColumnsAtT R C'} {P' : PeriodMap R C'}
    (M : MemberForms LL embLL Pl Tau hc C A P) (M' : MemberForms LL embLL Pl Tau hc C' A' P')
    (e : ∀ j, j ≤ R.m → ((M.lat j).V ≃ₗ[LL] (M'.lat j).V)) (he : ∀ j hj x, HEq (M'.emb j (e j hj x)) (M.emb j x))
    (i : ℕ) (hi : i < R.m) (H : ∀ φ ∈ M'.Fi i, C'.K i φ ∈ M'.Fi (i + 1)) :
    ∀ φ ∈ M.Fi i, C.K i φ ∈ M.Fi (i + 1) := by
  subst h
  have k : ∀ j, j ≤ R.m → M.Fi j = M'.Fi j := fun j hj => by
    rw [fi_eq_range', fi_eq_range']
    congr 1
    ext φ
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨e j hj x, eq_of_heq (he j hj x)⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := (e j hj).surjective y
      exact ⟨x, (eq_of_heq (he j hj x)).symm⟩
  intro φ hφ
  rw [k _ hi.le] at hφ
  rw [k _ hi]
  exact H φ hφ

theorem memberForms_stable_of_reference_tuple : ∀ (D : D7) (T : TwForms D) (u : D.what₂.Word), ∀ i < D.R.m,
    (∀ φ ∈ (T.fm u D.what₂.mu0).Fi i, (D.chTw u D.what₂.mu0).K i φ ∈ (T.fm u D.what₂.mu0).Fi (i + 1)) →
    ∀ φ ∈ (D.fm u).Fi i, (D.mem u).C.K i φ ∈ (D.fm u).Fi (i + 1) :=
  fun D T u i hi H => carries_one (D.memberColumns_twistedChain_base u) (D.fm u) (T.fm u D.what₂.mu0) (T.eMu0 u) (T.eMu0_emb u) i hi H

end GlobalTheory.KFiMu0
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NonemptyEquivOfMem
section
open NumberField IsDedekindDomain
open _root_.Formalism.BasicNotions _root_.Formalism.L2.Host _root_.Formalism.FrobeniusOrbits
open _root_.Formalism.L2.DIV

namespace GlobalTheory.Formalism.L2.Col

namespace HostOk

variable {R : Ranks} {H : _root_.Formalism.BasicNotions.Host R} (T : Frame H)

theorem sigma_conj (σ : H.E ≃ₐ[ℚ] H.E) (x : H.E) : σ (H.conj x) = H.conj (σ x) := by
  apply H.φ₀.injective
  have h1 := H.conjE_apply (H.φ₀.comp (σ : H.E →+* H.E)) x
  have h2 := H.conjE_apply H.φ₀ (σ x)
  exact h1.trans h2.symm

theorem galE_sigmaOf (g : R.GG) : H.galE (H.sigmaOf g) = g :=
  (H.gal).apply_symm_apply g

theorem sigmaOf_b (g : R.Psi) : H.sigmaOf g H.sqrtMinusD = H.sqrtMinusD :=
  (H.galE_mem_Psi_iff _).1 (by rw [galE_sigmaOf]; exact g.2)

theorem d_pos (H : _root_.Formalism.BasicNotions.Host R) : 0 < H.d := H.hyp.2.1.pos

theorem b_sq (H : _root_.Formalism.BasicNotions.Host R) : H.sqrtMinusD ^ 2 = -(H.d : H.E) := by
  exact H.sqd_sq

theorem conj_b (H : _root_.Formalism.BasicNotions.Host R) : H.conj H.sqrtMinusD = -H.sqrtMinusD := by
  apply H.φ₀.injective
  have h2 := H.conjE_apply H.φ₀ H.sqrtMinusD
  refine h2.trans ?_
  have h3 : H.φ₀ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem
  rw [map_neg, h3]
  simp

theorem b_ne (H : _root_.Formalism.BasicNotions.Host R) : H.sqrtMinusD ≠ -H.sqrtMinusD := by
  intro h
  have h0 : H.sqrtMinusD = 0 := by
    have : (2 : H.E) * H.sqrtMinusD = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).resolve_left two_ne_zero
  have h1 := b_sq H
  rw [h0] at h1
  have h2 : (H.d : H.E) = 0 := by linear_combination h1
  have h3 : H.d = 0 := by exact_mod_cast h2
  exact (d_pos H).ne' h3

variable (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : H.EQ ≤ LL)

end HostOk

end GlobalTheory.Formalism.L2.Col
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PageLargeScaleBoundsOfLargeScale
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem roomy_of_large : ∀ eps C A : ℝ, 0 < eps → 100 ≤ C → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L), L.sc.eps = eps → P.CLw ≤ A → x0 ≤ L.sc.x → Roomy L C := by
  intro eps C A he hC
  have hC0 : (0 : ℝ) ≤ C := by linarith
  obtain ⟨x1, h1⟩ := _root_.GlobalTheory.HTW.thinSize_dominates eps he
  obtain ⟨x2, h2⟩ := _root_.GlobalTheory.scale_log_mul_b'_le_b eps C (max A 0) he hC0 (le_max_right _ _)
  refine ⟨max (max x1 x2) 4, fun D L P hL hA hx => ?_⟩
  have hx1 : x1 ≤ L.sc.x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : x2 ≤ L.sc.x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx4 : (4 : ℝ) ≤ L.sc.x := le_trans (le_max_right _ _) hx
  obtain ⟨a1, a2, a3⟩ := h1 D L P hL hx1
  refine ⟨hC, a1, a2, a3, _root_.GlobalTheory.Ggeo.bT_add_div_le_three_halves D L P hx4, ?_⟩
  have hb : (0 : ℝ) ≤ L.sc.b' := by linarith
  have hlog : 0 ≤ Real.log L.sc.x := Real.log_nonneg (by linarith)
  have hw : (D.host.Lw : ℝ) ≤ max A 0 * Real.log L.sc.x :=
    P.Lw_le.trans (mul_le_mul_of_nonneg_right (hA.trans (le_max_left _ _)) hlog)
  refine le_trans ?_ (h2 L.sc hL hx2)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hC0) hb

end GlobalTheory.HTW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RoundedSizesSumLeParametersPageHeightStatement
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_roundedSizes_le_height : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ), Roomy L C → (bHat L : ℝ) + (etaHat L : ℝ) + (sHat L : ℝ) ≤ hPage L := by
  first | exact @GlobalTheory.HTW.bHat_add_etaHat_add_sHat_le_hPage | exact GlobalTheory.HTW.bHat_add_etaHat_add_sHat_le_hPage | (intros; apply GlobalTheory.HTW.bHat_add_etaHat_add_sHat_le_hPage <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SecondTwistSmallIffExactlyAtAndFinClause
section
noncomputable section

namespace GlobalTheory.Cmp.SmallJumps

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.FrobeniusOrbits GlobalTheory.HTW Module
open GlobalTheory.IndefiniteRowSideFullHecke

theorem finite_of_jumps {L M : Type} [Field L] [AddCommGroup M] [Module L M] (F : ℤ → Submodule L M)
    (U : Submodule L M) (anti : ∀ a, F (a + 1) ≤ F a) (exh : ∀ x ∈ U, ∃ a, x ∈ F a)
    (J : Multiset ℤ) (hJ : J ≠ 0)
    (h : ∀ a, (finrank L (F a) : ℤ) - finrank L (F (a + 1)) = (J.count a : ℤ)) :
    FiniteDimensional L U := by
  have hA : Antitone F := antitone_int_of_succ_le anti
  have hd : Antitone fun a => finrank L (F a) := antitone_int_of_succ_le fun a => by
    have := h a
    omega
  obtain ⟨a₀, ha₀⟩ := Multiset.exists_mem_of_ne_zero hJ
  have hpos : 0 < finrank L (F a₀) := by
    have := h a₀
    have := Multiset.count_pos.2 ha₀
    omega
  have hfin : ∀ a ≤ a₀, FiniteDimensional L (F a) := fun a ha =>
    Module.finite_of_finrank_pos (lt_of_lt_of_le hpos (hd ha))
  obtain ⟨b, hb⟩ := J.toFinset.bddBelow
  have hb' : ∀ a ∈ J, b ≤ a := fun a ha => hb (by simpa using ha)
  have hb0 : b ≤ a₀ := hb' a₀ ha₀
  have hst : ∀ a ≤ b, F a = F b := by
    intro a ha
    induction a, ha using Int.leInductionDown with
    | base => rfl
    | pred a ha ih =>
      haveI := hfin (a - 1) (by omega)
      have h1 := h (a - 1)
      have h2 : J.count (a - 1) = 0 := Multiset.count_eq_zero.2 fun hm => by
        have := hb' _ hm
        omega
      rw [sub_add_cancel, h2] at h1
      rw [← ih]
      exact (Submodule.eq_of_le_of_finrank_eq (hA (by omega)) (by omega)).symm
  haveI := hfin b hb0
  refine Submodule.finiteDimensional_of_le (S₂ := F b) fun x hx => ?_
  obtain ⟨a, ha⟩ := exh x hx
  rcases le_total a b with hab | hab
  · rwa [← hst a hab]
  · exact hA hab ha

section Periods

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem filV_anti : Antitone fun a => FilV PD (LL := LL) (V := V) a := by
  refine antitone_int_of_succ_le fun a => ?_
  rintro _ ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => exact ⟨v ⊗ₜ ⟨b.1, PD.Fil_anti a b.2⟩, rfl⟩
  | add x y hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy

theorem filV_exh (x : TensorProduct Qp V BdR) : ∃ a, x ∈ FilV PD (LL := LL) (V := V) a := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | tmul v b =>
    obtain ⟨a, ha⟩ := PD.Fil_exh b
    exact ⟨a, v ⊗ₜ ⟨b, ha⟩, rfl⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨min a b, Submodule.add_mem _ (filV_anti PD (min_le_left a b) ha)
      (filV_anti PD (min_le_right a b) hb)⟩

theorem finite_ddRE_of_multV (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (J : Multiset ℤ) (hJ : J ≠ 0)
    (h : ∀ a, multV PD ρ τ a = (J.count a : ℤ)) : FiniteDimensional LL (DdRE PD ρ τ) :=
  finite_of_jumps (FildR PD ρ τ) _
    (fun a => inf_le_inf_left _ (filV_anti PD (by omega : a ≤ a + 1)))
    (fun x hx => (filV_exh PD (LL := LL) x).imp fun _ ha => ⟨hx, ha⟩) J hJ h

end Periods

theorem linearIndepOn_of_invariant {K F W G ι : Type} [Field K] [Field F] [Algebra K F] [AddCommGroup W]
    [Module F W] [Module K W] [IsScalarTower K F W] (a : G → F → F) (σ : G → W →+ W)
    (hσ : ∀ g b w, σ g (b • w) = a g b • σ g w)
    (hinv : ∀ b, (∀ g, a g b = b) → ∃ c, algebraMap K F c = b) (v : ι → W) (hv : ∀ g i, σ g (v i) = v i)
    (s : Finset ι) (h : LinearIndepOn K v s) : LinearIndepOn F v s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    have hx' : x ∉ (s : Set ι) := hx
    rw [Finset.coe_insert, linearIndepOn_insert hx'] at h ⊢
    refine ⟨ih h.1, fun hm => h.2 ?_⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_image_finset_iff_exists_fun' F).1 hm
    have key : ∀ i ∈ s, ∀ g, a g (c i) = c i := by
      intro i hi g
      have h1 : ∑ i ∈ s, a g (c i) • v i = v x := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← hv g x, ← hc, map_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [hσ, hv]
      have h2 := linearIndepOn_finset_iff.1 (ih h.1) (fun j => a g (c j) - c j) (by
        simp only [sub_smul, Finset.sum_sub_distrib, h1, hc, sub_self]) i hi
      exact sub_eq_zero.1 h2
    rw [← hc]
    refine Submodule.sum_mem _ fun i hi => ?_
    obtain ⟨k, hk⟩ := hinv _ (key i hi)
    rw [← hk, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)

theorem finite_of_invariant {K F W G : Type} [Field K] [Field F] [Algebra K F] [AddCommGroup W]
    [Module F W] [Module K W] [IsScalarTower K F W] [Module.Finite F W] (a : G → F → F) (σ : G → W →+ W)
    (hσ : ∀ g b w, σ g (b • w) = a g b • σ g w)
    (hinv : ∀ b, (∀ g, a g b = b) → ∃ c, algebraMap K F c = b) (U : Submodule K W)
    (hU : ∀ x ∈ U, ∀ g, σ g x = x) : Module.Finite K U := by
  rw [← Module.rank_lt_aleph0_iff]
  refine lt_of_le_of_lt (rank_le (n := finrank F W) fun s hs => ?_) (Cardinal.natCast_lt_aleph0)
  have h1 : LinearIndepOn K (fun x : U => (x : W)) s := hs.map' U.subtype U.ker_subtype
  have h2 := linearIndepOn_of_invariant a σ hσ hinv (fun x : U => (x : W))
    (fun g x => hU x x.2 g) s h1
  simpa using LinearIndependent.fintype_card_le_finrank h2

section FieldPeriods

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem finite_ddR_of_isField (hF : IsField BdR) [Module.Finite Qp V] (ρ : Representation LL G V) :
    Module.Finite LL (DdR PD ρ) := by
  letI : Field BdR := hF.toField
  haveI := PD.finK
  let σ : G → TensorProduct Qp BdR V →ₗ[Qp] TensorProduct Qp BdR V := fun g =>
    TensorProduct.map (((PD.actdR g).toAlgHom.toLinearMap).restrictScalars Qp) ((ρ g).restrictScalars Qp)
  have hσ : ∀ g (b : BdR) w, σ g (b • w) = PD.actdR g b • σ g w := by
    intro g b w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c v => simp [σ, TensorProduct.smul_tmul']
    | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]
  let U : Submodule K (TensorProduct Qp BdR V) :=
    { carrier := {x | ∀ g, σ g x = x}
      zero_mem' := fun g => map_zero _
      add_mem' := fun hx hy g => by rw [map_add (f := _), hx g, hy g]
      smul_mem' := fun c x hx g => by
        rw [← algebraMap_smul BdR c x, hσ, hx g, AlgEquiv.commutes] }
  haveI : Module.Finite K U := finite_of_invariant (F := BdR) (fun g b => PD.actdR g b)
    (fun g => (σ g).toAddMonoidHom) hσ PD.invdR U fun _ hx => hx
  haveI : Module.Finite Qp U := Module.Finite.trans K U
  have hc : ∀ g x, σ g (TensorProduct.comm Qp V BdR x) =
      TensorProduct.comm Qp V BdR (actVdR PD ρ g x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c v => simp [σ, actVdR]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  let f : DdR PD ρ →ₗ[Qp] U :=
    { toFun := fun x => ⟨TensorProduct.comm Qp V BdR x, fun g => by
        have := x.2
        simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
          LinearMap.id_apply, sub_eq_zero] at this
        rw [hc, this g]⟩
      map_add' := fun x y => Subtype.ext (map_add _ _ _)
      map_smul' := fun c x => Subtype.ext (map_smul (TensorProduct.comm Qp V BdR) c _) }
  haveI : Module.Finite Qp (DdR PD ρ) := Module.Finite.of_injective f fun x y h =>
    Subtype.ext ((TensorProduct.comm Qp V BdR).injective (congrArg Subtype.val h))
  exact Module.Finite.of_restrictScalars_finite Qp LL _

end FieldPeriods

variable (D : D7)

section Place

variable (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

variable {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))

end Place

variable {D}

end GlobalTheory.Cmp.SmallJumps
end
end

