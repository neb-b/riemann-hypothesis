module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0205
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0031
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0170

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTateMaximalIdealKillsFirstCohomology
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc.AveragingRankOne

theorem exists_reps {G : Type*} [Group G] (H U V : Subgroup G) [U.FiniteIndex]
    (hV : ∀ g ∈ H, g ∈ V ↔ g ∈ U) :
    ∃ S : Finset G, (∀ s ∈ S, s ∈ H) ∧ ∀ h ∈ H, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ V := by
  classical
  letI : Fintype (H ⧸ U.subgroupOf H) := Fintype.ofFinite _
  refine ⟨Finset.univ.image (fun q : H ⧸ U.subgroupOf H => (q.out : G)), ?_, ?_⟩
  · intro s hs
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hs
    exact q.out.2
  · intro h hh
    have key : ∀ q : H ⧸ U.subgroupOf H, (q.out : G)⁻¹ * h ∈ V ↔ q = ((⟨h, hh⟩ : H) : H ⧸ U.subgroupOf H) := by
      intro q
      rw [hV _ (H.mul_mem (H.inv_mem q.out.2) hh)]
      conv_rhs => rw [← q.out_eq']
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      rfl
    refine ⟨(((⟨h, hh⟩ : H) : H ⧸ U.subgroupOf H).out : G),
      ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, (key _).2 rfl⟩, ?_⟩
    rintro s ⟨hs, hs'⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hs
    rw [(key q).1 hs']

variable {l : ℕ} [Fact l.Prime]

theorem exists_field (F : IntermediateField ℚ_[l] (Om l)) (W : Set (GQ l)) (hW : W ∈ nhds (1 : GQ l)) :
    ∃ (L : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l)), F ≤ L ∧
      (∀ h ∈ F.fixingSubgroup, ∀ x ∈ L, h x ∈ L) ∧ (∀ s ∈ S, s ∈ F.fixingSubgroup) ∧
      (∀ h ∈ F.fixingSubgroup, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ L.fixingSubgroup) ∧
      ∀ g ∈ L.fixingSubgroup, g ∈ W := by
  obtain ⟨E, hfd, hN, hE⟩ := (krullTopology_mem_nhds_one_iff_of_normal ℚ_[l] (Om l) W).1 hW
  haveI : E.fixingSubgroup.FiniteIndex := by
    haveI := Subgroup.quotient_finite_of_isOpen E.fixingSubgroup E.fixingSubgroup_isOpen
    exact Subgroup.finiteIndex_of_finite_quotient
  have hsup : (F ⊔ E).fixingSubgroup = F.fixingSubgroup ⊓ E.fixingSubgroup :=
    IntermediateField.fixingSubgroup_sup
  obtain ⟨S, hS, hS'⟩ := exists_reps F.fixingSubgroup E.fixingSubgroup (F ⊔ E).fixingSubgroup
    (fun g hg => by rw [hsup, Subgroup.mem_inf]; exact ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩)
  refine ⟨F ⊔ E, S, le_sup_left, ?_, hS, hS', fun g hg => hE ?_⟩
  · intro h hh
    have : F ⊔ E ≤ (F ⊔ E).comap (h : Om l →ₐ[ℚ_[l]] Om l) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · have h1 : h x = x := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hh x hx
        change h x ∈ F ⊔ E
        rw [h1]; exact (le_sup_left : F ≤ F ⊔ E) hx
      · change h x ∈ F ⊔ E
        have h1 := AlgEquiv.restrictNormal_commutes h E ⟨x, hx⟩
        have h2 : h x ∈ E := by
          have : h x = (h.restrictNormal E ⟨x, hx⟩ : E) := h1.symm
          rw [this]; exact Subtype.property _
        exact (le_sup_right : E ≤ F ⊔ E) h2
    exact fun x hx => this hx
  · rw [hsup] at hg; exact hg.2

theorem average {G C : Type*} [Group G] [NormedField C] [IsUltrametricDist C]
    (act : G →* (C ≃+* C)) (hn : ∀ g y, ‖act g y‖ = ‖y‖) (H V : Subgroup G) (S : Finset G)
    (hS : ∀ s ∈ S, s ∈ H) (hS' : ∀ h ∈ H, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ V)
    (a b : C) (hb : ‖b‖ ≤ 1) (hbV : ∀ g ∈ V, act g b = b) (hab : ∑ s ∈ S, act s b = a)
    (c : G → C) (hc : ∀ g ∈ H, ∀ h ∈ H, c (g * h) = c g + act g (c h))
    (t ε : ℝ) (ht0 : 0 ≤ t) (hε : 0 ≤ ε) (ht : ∀ g ∈ H, ‖c g‖ ≤ t)
    (hV : ∀ g ∈ H, g ∈ V → ‖c g‖ ≤ ε) :
    ∃ x : C, ‖x‖ ≤ t ∧ ∀ h ∈ H, ‖a * c h - (act h x - x)‖ ≤ ε := by
  first
  | exact @_root_.GlobalTheory.PermutationExistence.main
  | exact _root_.GlobalTheory.PermutationExistence.main
  | (apply _root_.GlobalTheory.PermutationExistence.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PermutationExistence.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PermutationExistence.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PermutationExistence.main ..)

theorem step (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (hact : IsActC act) (K : FinExt l)
    (a : PadicComplex l) (ha : a ∈ inC (Kinf K)) (ha1 : ‖a‖ < 1) (c : GQ l → PadicComplex l)
    (hcont : ContinuousOn c (Hinf K))
    (hc : ∀ g ∈ Hinf K, ∀ h ∈ Hinf K, c (g * h) = c g + act g (c h))
    (t ε : ℝ) (ht0 : 0 ≤ t) (hε : 0 < ε) (ht : ∀ g ∈ Hinf K, ‖c g‖ ≤ t) :
    ∃ x : PadicComplex l, ‖x‖ ≤ t ∧ ∀ h ∈ Hinf K, ‖a * c h - (act h x - x)‖ ≤ ε := by
  obtain ⟨a₀, ha₀, rfl⟩ := ha
  have hc1 : c 1 = 0 := by
    have := hc 1 (one_mem _) 1 (one_mem _)
    simpa using this
  have hev : ∀ᶠ g in nhdsWithin (1 : GQ l) (Hinf K), ‖c g‖ < ε := by
    have := (hcont 1 (one_mem _)).norm
    refine this.eventually (p := fun r => r < ε) (gt_mem_nhds ?_)
    simpa [hc1] using hε
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨L, S, hL, hst, hS, hS', hW⟩ := exists_field (Kinf K) _ hev
  obtain ⟨b, hbL, hb1, hb⟩ := GlobalTheory.T.cyclotomicTower_trace_almost_surjective l K L S hL hst hS hS' a₀ ha₀ (by simpa using ha1)
  refine average act hact.2 (Hinf K) L.fixingSubgroup S hS hS' _ (b : PadicComplex l)
    (by simpa using hb1) (fun g hg => ?_) ?_ c hc t ε ht0 hε.le ht (fun g hg hg' => (hW g hg' hg).le)
  · rw [hact.1, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg b hbL]
  · simp only [hact.1, ← hb]
    exact (map_sum (algebraMap (Om l) (PadicComplex l)) _ _).symm

theorem rank_one (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (hact : IsActC act)
    (K : FinExt l) (a : PadicComplex l) (ha : a ∈ inC (Kinf K)) (ha1 : ‖a‖ < 1)
    (c : GQ l → PadicComplex l) (hcont : ContinuousOn c (Hinf K))
    (hc : ∀ g ∈ Hinf K, ∀ h ∈ Hinf K, c (g * h) = c g + act g (c h))
    (ht : ∀ g ∈ Hinf K, ‖c g‖ ≤ 1) :
    ∃ x : PadicComplex l, ‖x‖ ≤ 1 ∧ ∀ h ∈ Hinf K, a * c h = act h x - x := by
  rcases eq_or_ne a 0 with rfl | ha0
  · exact ⟨0, by simp, by simp⟩
  have hapos : 0 < ‖a‖ := norm_pos_iff.2 ha0
  have hfix : ∀ g ∈ Hinf K, act g a = a := by
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    intro g hg
    rw [hact.1, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg a₀ ha₀]
  let Q : ℕ → PadicComplex l → Prop := fun n y =>
    ‖y‖ ≤ 1 ∧ ∀ h ∈ Hinf K, ‖a * c h - (act h y - y)‖ ≤ ‖a‖ * (1 / 2) ^ n
  have hstep : ∀ n y, Q n y → ∃ y', Q (n + 1) y' ∧ dist y y' ≤ 1 * (1 / 2 : ℝ) ^ n := by
    rintro n y ⟨hy1, hy⟩
    obtain ⟨x, hx, hx'⟩ := step act hact K a ha ha1 (fun g => c g - a⁻¹ * (act g y - y))
      (hcont.sub (continuousOn_const.mul
        ((GlobalTheory.T.continuous_orbit_padicComplex l act hact y).continuousOn.sub continuousOn_const)))
      (fun g hg h hh => by
        simp only [hc g hg h hh, map_mul, map_sub, map_inv₀, hfix g hg, RingAut.mul_apply]
        ring)
      ((1 / 2) ^ n) (‖a‖ * (1 / 2) ^ (n + 1)) (by positivity) (by positivity)
      (fun g hg => by
        have e : c g - a⁻¹ * (act g y - y) = a⁻¹ * (a * c g - (act g y - y)) := by
          field_simp
        rw [e, norm_mul, norm_inv, inv_mul_le_iff₀ hapos]
        exact hy g hg)
    refine ⟨y + x, ⟨?_, fun h hh => ?_⟩, ?_⟩
    · refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hy1 (hx.trans ?_))
      exact pow_le_one₀ (by norm_num) (by norm_num)
    · have e : a * c h - (act h (y + x) - (y + x)) =
          a * (c h - a⁻¹ * (act h y - y)) - (act h x - x) := by
        rw [map_add (f := _)]; field_simp; ring
      rw [e]; exact hx' h hh
    · simpa [dist_eq_norm] using hx
  choose! f hfQ hfd using hstep
  let y : ℕ → PadicComplex l := fun n => Nat.rec 0 f n
  have hQ : ∀ n, Q n (y n) := by
    intro n
    induction n with
    | zero =>
      refine ⟨by simp [y], fun h hh => ?_⟩
      simpa [y] using mul_le_mul_of_nonneg_left (ht h hh) hapos.le
    | succ n ih => exact hfQ n _ ih
  have hcau : CauchySeq y :=
    cauchySeq_of_le_geometric (1 / 2) 1 (by norm_num) fun n => hfd n _ (hQ n)
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcau
  refine ⟨x, le_of_tendsto' hx.norm fun n => (hQ n).1, fun h hh => ?_⟩
  have hiso : Continuous (act h) :=
    (AddMonoidHomClass.isometry_of_norm (act h) (hact.2 h)).continuous
  have h1 : Filter.Tendsto (fun n => ‖a * c h - (act h (y n) - y n)‖) Filter.atTop
      (nhds ‖a * c h - (act h x - x)‖) :=
    (tendsto_const_nhds.sub (((hiso.tendsto x).comp hx).sub hx)).norm
  have h2 : Filter.Tendsto (fun n : ℕ => ‖a‖ * (1 / 2 : ℝ) ^ n) Filter.atTop (nhds (‖a‖ * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul _
  have := le_of_tendsto_of_tendsto' h1 h2 fun n => (hQ n).2 h hh
  rw [mul_zero, norm_le_zero_iff, sub_eq_zero] at this
  exact this

theorem cyclotomic_maximalIdeal_smul_cocycle_isCoboundary : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)), IsActC act → ∀ (K : FinExt l) (r : ℕ) (a : PadicComplex l), a ∈ inC (Kinf K) → ‖a‖ < 1 → ∀ c : GQ l → Fin r → PadicComplex l, CocOn (Hinf K) (fun g y k => act g (y k)) (ball l r) c → CobOn (Hinf K) (fun g y k => act g (y k)) (ball l r) (fun g => a • c g) := by
  intro l _ act hact K r a ha ha1 c ⟨h1, h2, h3⟩
  choose x hx hx' using fun k : Fin r => rank_one act hact K a ha ha1 (fun g => c g k)
    ((continuous_apply k).comp_continuousOn h1)
    (fun g hg h hh => congrFun (h3 g hg h hh) k) (fun g hg => h2 g hg k)
  exact ⟨x, hx, fun g hg => funext fun k => hx' k g hg⟩

end GlobalTheory.Cyc.AveragingRankOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerFixedIffMemCompletedIntegers
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.CycInvariants

theorem exists_reps {G : Type} [Group G] (H N : Subgroup G) [(N.subgroupOf H).FiniteIndex] :
    ∃ S : Finset G, (∀ s ∈ S, s ∈ H) ∧ ∀ h ∈ H, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ N := by
  classical
  have : Fintype (H ⧸ N.subgroupOf H) := Fintype.ofFinite _
  refine ⟨Finset.univ.image (fun q : H ⧸ N.subgroupOf H => ((q.out : H) : G)), ?_, ?_⟩
  · intro s hs
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hs
    exact q.out.2
  · intro h hh
    refine ⟨((QuotientGroup.mk (⟨h, hh⟩ : H) : H ⧸ N.subgroupOf H).out : H),
      ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩, ?_⟩
    · have h1 := QuotientGroup.out_eq' (QuotientGroup.mk (⟨h, hh⟩ : H) : H ⧸ N.subgroupOf H)
      have h2 := QuotientGroup.eq.1 h1
      simpa [Subgroup.mem_subgroupOf] using h2
    · rintro s ⟨hs, hsN⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hs
      have : (QuotientGroup.mk q.out : H ⧸ N.subgroupOf H) = QuotientGroup.mk (⟨h, hh⟩ : H) :=
        QuotientGroup.eq.2 (by simpa [Subgroup.mem_subgroupOf] using hsN)
      rw [QuotientGroup.out_eq'] at this
      rw [this]

theorem sum_reps_invariant {G M : Type} [Group G] [AddCommMonoid M] (H N : Subgroup G)
    (S : Finset G) (hS : ∀ s ∈ S, s ∈ H) (hu : ∀ h ∈ H, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ N)
    (f : G → M) (hf : ∀ g, ∀ n ∈ N, f (g * n) = f g) (h : G) (hh : h ∈ H) :
    ∑ s ∈ S, f (h * s) = ∑ s ∈ S, f s := by
  first
  | exact @_root_.GlobalTheory.LeftTransversalSum.sum_mul_left_transversal
  | exact _root_.GlobalTheory.LeftTransversalSum.sum_mul_left_transversal
  | (apply _root_.GlobalTheory.LeftTransversalSum.sum_mul_left_transversal <;> assumption)
  | (intros; apply _root_.GlobalTheory.LeftTransversalSum.sum_mul_left_transversal <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LeftTransversalSum.sum_mul_left_transversal <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LeftTransversalSum.sum_mul_left_transversal ..)

variable {l : ℕ} [Fact l.Prime]

theorem stabilizer_finiteIndex (x : Om l) : (MulAction.stabilizer (GQ l) x).FiniteIndex := by
  refine ⟨?_⟩
  rw [MulAction.index_stabilizer]
  have hint : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have hfin : (MulAction.orbit (GQ l) x).Finite := by
    refine ((minpoly ℚ_[l] x).rootSet_finite (Om l)).subset ?_
    rintro _ ⟨g, rfl⟩
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    change Polynomial.aeval (g x) _ = 0
    rw [Polynomial.aeval_algEquiv]
    simp
  exact ((Set.ncard_pos hfin).2 ⟨x, MulAction.mem_orbit_self x⟩).ne'

theorem exists_field (F : IntermediateField ℚ_[l] (Om l)) (x : Om l) :
    ∃ (L : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l)), x ∈ L ∧ F ≤ L ∧
      (∀ h ∈ F.fixingSubgroup, ∀ x ∈ L, h x ∈ L) ∧ (∀ s ∈ S, s ∈ F.fixingSubgroup) ∧
      (∀ h ∈ F.fixingSubgroup, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ L.fixingSubgroup) := by
  have := stabilizer_finiteIndex x
  set N := (MulAction.stabilizer (GQ l) x).normalCore with hN
  set L := IntermediateField.fixedField (F.fixingSubgroup ⊓ N) with hL
  have hle : F.fixingSubgroup ⊓ N ≤ L.fixingSubgroup :=
    (IntermediateField.le_iff_le _ _).1 le_rfl
  have hfi : (L.fixingSubgroup.subgroupOf F.fixingSubgroup).FiniteIndex := by
    refine Subgroup.finiteIndex_of_le (H := N.subgroupOf F.fixingSubgroup) ?_
    intro g hg
    exact hle ⟨g.2, hg⟩
  obtain ⟨S, hS, hu⟩ := exists_reps F.fixingSubgroup L.fixingSubgroup
  refine ⟨L, S, ?_, ?_, ?_, hS, hu⟩
  · rw [hL, IntermediateField.mem_fixedField_iff]
    intro g hg
    exact Subgroup.normalCore_le _ hg.2
  · exact (IntermediateField.le_iff_le _ _).2 inf_le_left
  · intro h hh y hy
    rw [hL, IntermediateField.mem_fixedField_iff] at hy ⊢
    intro g hg
    have h1 : h⁻¹ * g * h ∈ F.fixingSubgroup ⊓ N :=
      ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hh) hg.1) hh,
        by simpa using (Subgroup.normalCore_normal _).conj_mem g hg.2 h⁻¹⟩
    have h2 := congrArg h (hy _ h1)
    simpa using h2

theorem fixed_iff_mem_Ohat : ∀ (l : ℕ) [Fact l.Prime]
    (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)), IsActC act →
    ∀ (K : FinExt l) (y : PadicComplex l), ‖y‖ ≤ 1 →
      ((∀ h ∈ Hinf K, act h y = y) ↔ y ∈ Ohat K) := by
  intro l _ act hact K y hy
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  constructor
  · intro hfix
    rw [Ohat, Metric.mem_closure_iff]
    intro ε hε
    set δ : ℝ := min (ε / 2) 1 with hδ
    have hδ0 : 0 < δ := lt_min (by linarith) one_pos
    obtain ⟨x, hx⟩ := (UniformSpace.Completion.denseRange_coe (α := Om l)).exists_dist_lt y
      (div_pos hδ0 hl0)
    rw [dist_eq_norm] at hx
    obtain ⟨L, S, hxL, hKL, hst, hS, hu⟩ := exists_field (Kinf K) x
    have hnl : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
      rw [← map_natCast (algebraMap ℚ_[l] (Om l))]
      exact (PadicAlgCl.norm_extends l _).trans Padic.norm_p
    have hlne : (l : Om l) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
    obtain ⟨b, hbL, hb1, hb⟩ := GlobalTheory.T.cyclotomicTower_trace_almost_surjective l K L S hKL hst hS hu (l : Om l)
      (natCast_mem _ _) (by rw [hnl]; exact inv_lt_one_of_one_lt₀ hl1)
    set w : Om l := ∑ s ∈ S, s (b * x) with hw
    have hwK : w ∈ Kinf K := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup (Kinf K), IntermediateField.mem_fixedField_iff]
      intro h hh
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hw, map_sum]
      refine sum_reps_invariant _ _ S hS hu (fun g => g (b * x)) ?_ h hh
      intro g n hn
      have := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hn _ (L.mul_mem hbL hxL)
      simp only [AlgEquiv.mul_apply, this]
    set ι := algebraMap (Om l) (PadicComplex l) with hι
    have hιn : ∀ u, ‖ι u‖ = ‖u‖ := fun u => PadicComplex.norm_extends l u
    have hιa : ∀ g u, act g (ι u) = ι (g u) := hact.1
    have hdiff : ι l * y - ι w = ∑ s ∈ S, act s (ι b * (y - ι x)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hb, hw, map_sum, map_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [map_mul (act s), map_sub, hfix s (hS s hs), hιa, hιa, map_mul, map_mul, mul_sub]
    have hle : ‖ι l * y - ι w‖ ≤ δ / l := by
      rw [hdiff]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (div_pos hδ0 hl0).le ?_
      intro s _
      rw [hact.2, norm_mul, hιn]
      calc ‖b‖ * ‖y - ι x‖ ≤ 1 * (δ / l) := mul_le_mul hb1 hx.le (norm_nonneg _) one_pos.le
        _ = δ / l := one_mul _
    have hle' : ‖y - ι (w / l)‖ ≤ δ := by
      have h1 : ι l * y - ι w = ι l * (y - ι (w / l)) := by
        rw [mul_sub, ← map_mul, mul_div_cancel₀ _ hlne]
      rw [h1, norm_mul, hιn, hnl, div_eq_inv_mul δ] at hle
      exact le_of_mul_le_mul_left hle (inv_pos.2 hl0)
    refine ⟨ι (w / l), ⟨⟨w / l, div_mem hwK (natCast_mem _ _), rfl⟩, ?_⟩, ?_⟩
    · have h1 : ι (w / l) = y + -(y - ι (w / l)) := by ring
      rw [h1]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hy ?_)
      rw [norm_neg]
      exact hle'.trans (min_le_right _ _)
    · rw [dist_eq_norm]
      exact lt_of_le_of_lt (hle'.trans (min_le_left _ _)) (by linarith)
  · intro hyO h hh
    have hc : Continuous (act h) :=
      (AddMonoidHomClass.isometry_of_norm (act h) (hact.2 h)).continuous
    refine closure_minimal (t := {z | act h z = z}) ?_ (isClosed_eq hc continuous_id) hyO
    rintro _ ⟨⟨u, hu, rfl⟩, -⟩
    change act h (u : PadicComplex l) = (u : PadicComplex l)
    rw [hact.1, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hh u hu]

end GlobalTheory.CycInvariants
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemTameDescentClassEqOfPowMem
section
noncomputable section

namespace GlobalTheory.LcImage

open PowerSeries GlobalTheory.BK GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction

theorem norm_intCast_eq_one {K : Type} [NormedField K] (l : ℕ) [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] {u : ℤ} (hu : ¬ (l : ℤ) ∣ u) : ‖(u : K)‖ = 1 := by
  rw [← map_intCast (algebraMap ℚ_[l] K), norm_algebraMap']
  exact le_antisymm (Padic.norm_int_le_one u)
    (not_lt.1 fun h => hu (Padic.norm_intCast_lt_one_iff.1 h))

theorem exists_mul_intCast_eq {O K : Type} [CommRing O] [NormedField K] [Algebra O K]
    [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] {r : ℤ} (hr : r ≠ 0)
    {m : ℕ} (hm : padicValInt l r ≤ m) : ∃ t : O, algebraMap O K t * (r : K) = (l : K) ^ m := by
  obtain ⟨v, hvdef⟩ : ∃ v, padicValInt l r = v := ⟨_, rfl⟩
  have hdv := padicValInt_dvd (p := l) r
  rw [hvdef] at hdv hm
  obtain ⟨u, hu⟩ := hdv
  have hpr : (l : ℕ).Prime := Fact.out
  have hu' : ¬ (l : ℤ) ∣ u := by
    rintro ⟨k, rfl⟩
    have h := (padicValInt_dvd_iff (p := l) (v + 1) r).1
      ⟨k, by rw [hu, pow_succ]; ring⟩
    omega
  have hl0 : (l : K) ≠ 0 := natCast_ne_zero' l hpr.ne_zero
  have hu0 : (u : K) ≠ 0 := by
    intro h
    have := norm_intCast_eq_one (K := K) l hu'
    rw [h, norm_zero] at this
    exact zero_ne_one this
  set t : K := (l : K) ^ (m - v) * (u : K)⁻¹ with ht
  obtain ⟨t', ht'⟩ := (IsUnitBall.mem_range_iff (O := O) t).2 (by
    rw [ht, norm_mul, norm_pow, norm_inv, norm_intCast_eq_one l hu', inv_one, mul_one, norm_l l]
    exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by exact_mod_cast hpr.one_le)))
  refine ⟨t', ?_⟩
  rw [ht', ht, hu]
  push_cast
  rw [mul_comm ((l : K) ^ v), ← mul_assoc, mul_assoc _ _ (u : K), inv_mul_cancel₀ hu0,
    mul_one, ← pow_add, Nat.sub_add_cancel hm]

theorem exists_mem_Y'_Lc_cls_eq : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H) (U : Finset ℤ) (N : ℕ), D.jumps ⊆ U → U ⊆ Finset.Icc (-(η : ℤ)) H → U.card ≤ N + 1 → η < H → H + η < l → 10 * H + 2 ≤ l → ∀ c : ℕ, ∀ w ∈ D.Zl, (l : K) ^ c • D.Lc w ∈ D.Z → ∃ y ∈ D.Y', D.Lc (D.cls y) = (l : K) ^ (c + η + (N + 1) * η) • D.Lc w := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D U N hJ hU hN hηH hl h10 c w hw hc
  obtain ⟨-, hVal, hInt⟩ := _root_.GlobalTheory.LcImage.image_valuation_integralImage O K l e a ι η H D U N hJ hU hN hηH
  obtain ⟨-, hR0, hv, hcard, hcard'⟩ := hVal hl

  obtain ⟨z, hz, hRz⟩ := hInt h10 (c : ℤ) (D.LcZ ⟨w, hw⟩) ⟨_, rfl⟩ (by
    rw [zpow_natCast, D.coe_LcZ]; exact hc)
  rw [zpow_natCast] at hz
  have hRz' : (((polyR l e U η).eval 0 : ℤ) : K) • D.Lc w = D.Lc z := by
    simpa using congrArg Subtype.val hRz

  obtain ⟨t, ht⟩ := exists_mul_intCast_eq (O := O) (K := K) l hR0 (m := (N + 1) * η)
    (by omega)
  have hx1 : t • ((l : K) ^ c • (z : D.Pol)) ∈ D.Z := D.Z.smul_mem t hz
  have hLx1 : D.Lc (t • ((l : K) ^ c • (z : D.Pol))) = (l : K) ^ (c + (N + 1) * η) • D.Lc w := by
    rw [← algebraMap_smul K t, map_smul, map_smul, ← hRz', smul_smul, smul_smul, pow_add]
    congr 1
    rw [← ht]; ring

  obtain ⟨z'', hz'', hv''⟩ := (_root_.GlobalTheory.divisible_of_BKDat O K l e a ι η H D).1 _ hx1

  have hz3 : z'' ∈ (D.desc.Y η).map (D.cls.restrictScalars O) := by
    rw [Descent.map_Y]; exact hz''
  obtain ⟨y'', hy'', rfl⟩ := hz3
  refine ⟨(X : K⟦X⟧) ^ e • y'', (Descent.mem_Y' _).2 ⟨y'', hy'', rfl⟩, ?_⟩
  have h1 : D.cls ((X : K⟦X⟧) ^ e • y'') = (l : K) ^ η • (t • ((l : K) ^ c • (z : D.Pol))) := by
    rw [hv'']; rfl
  rw [h1, map_smul, hLx1, smul_smul, ← pow_add]
  congr 2
  ring

end GlobalTheory.LcImage
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMixedSpaceNormSignCharacterStatement
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mixedSpace_norm_sign_character : ∀ (K : Type) [Field K] [NumberField K] (ε : ℂ), ε * ε = 1 → ∃ φ : mixedSpace K → ℂ, (∀ x y, φ (x * y) = φ x * φ y) ∧ (∀ (t : ℝ) x, 0 < t → φ (t • x) = φ x) ∧ ContDiffOn ℝ ∞ φ {x | mixedEmbedding.norm x ≠ 0} ∧ (∀ x, mixedEmbedding.norm x ≠ 0 → ‖φ x‖ = 1) ∧ ∀ β : 𝓞 K, β ≠ 0 → φ (mixedEmbedding K β) = if 0 < Algebra.norm ℤ β then 1 else ε := by
  first | exact @GlobalTheory.NormSign.exists_normSign | exact GlobalTheory.NormSign.exists_normSign | (intros; apply GlobalTheory.NormSign.exists_normSign <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinIsoDualLatticeOfLocalTateDualityStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finIso_dualLattice_of_localTateDuality : Formalism.GaloisCohomology.LocalTateDualityK → ReciprocityTheory.ChartRestriction.T2.FinIso := by
  first | exact @GlobalTheory.FinIsoDualLattice.finIso_of_localTateDuality | exact GlobalTheory.FinIsoDualLattice.finIso_of_localTateDuality | (intros; apply GlobalTheory.FinIsoDualLattice.finIso_of_localTateDuality <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Main
section
namespace GlobalTheory.ScalarStatement

open Formalism.L2.FormalSeriesBounds

theorem main : (let d1 : {C : Type} → [inst : Field C] → Formalism.L2.FormalSeriesBounds.VF C → (ℕ → C) → Prop := @(fun {C : Type} [Field C] (V : Formalism.L2.FormalSeriesBounds.VF C) (s : ℕ → C) ↦ ∃ (K : ℝ), ∀ (n : ℕ), Formalism.L2.FormalSeriesBounds.VF.Ge V K (s n)); ∀ {C : Type} [inst : Field C] {V : Formalism.L2.FormalSeriesBounds.VF C} {ι : Type} (S : Finset ι) {s : ι → ℕ → C}, (∀ i ∈ S, d1 V (s i)) → d1 V fun (n : ℕ) ↦ ∑ i ∈ S, s i n) := by
  intro d1 C _ V ι S s h
  classical
  have h' : ∀ i, ∃ K : ℝ, i ∈ S → ∀ n, Formalism.L2.FormalSeriesBounds.VF.Ge V K (s i n) := by
    intro i
    by_cases hi : i ∈ S
    · obtain ⟨K, hK⟩ := h i hi
      exact ⟨K, fun _ => hK⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose K hK using h'
  refine ⟨-(∑ i ∈ S, |K i|), fun n => ?_⟩
  refine Formalism.L2.FormalSeriesBounds.VF.Ge.sum fun i hi => (hK i hi n).mono ?_
  have h1 : |K i| ≤ ∑ j ∈ S, |K j| :=
    Finset.single_le_sum (f := fun j => |K j|) (fun j _ => abs_nonneg _) hi
  have h2 : -|K i| ≤ K i := neg_abs_le _
  linarith

end GlobalTheory.ScalarStatement
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCardH2CompEquivStatement
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natCard_H2_comp_equiv : ∀ {R : Type} [CommRing R] {G Γ : Type} [Group G] [TopologicalSpace G] [Group Γ] [TopologicalSpace Γ] {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (i : G ≃ₜ* Γ) (rho : Representation R Γ M), Nat.card (H2 (rho.comp i.toMulEquiv.toMonoidHom)) = Nat.card (H2 rho) := by
  first | exact @GlobalTheory.TransportH2.natCard_H2_comp | exact GlobalTheory.TransportH2.natCard_H2_comp | (intros; apply GlobalTheory.TransportH2.natCard_H2_comp <;> assumption)
end

