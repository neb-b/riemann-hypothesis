module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1085
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0923
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0919
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1073
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1075

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactClosureZpowersLeftMulGLIffIntegral
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TwOrbLat

section Top

variable {E : Type} [Field E] [NumberField E] {w : Pl E} {a : ℕ}

theorem isCompact_boundedGL (R : ℝ) :
    IsCompact {g : GLw a w | ∀ i j, ‖g.val i j‖ ≤ R ∧ ‖(g⁻¹).val i j‖ ≤ R} := by
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion E w
  have hK : IsCompact {A : Matrix (Fin a) (Fin a) (w.adicCompletion E) | ∀ i j, ‖A i j‖ ≤ R} := by
    have h : IsCompact (Set.pi Set.univ fun _ : Fin a => Set.pi Set.univ fun _ : Fin a =>
        Metric.closedBall (0 : w.adicCompletion E) R) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
    have e : {A : Matrix (Fin a) (Fin a) (w.adicCompletion E) | ∀ i j, ‖A i j‖ ≤ R} =
        (Set.pi Set.univ fun _ : Fin a => Set.pi Set.univ fun _ : Fin a =>
          Metric.closedBall (0 : w.adicCompletion E) R) :=
      Set.ext fun A => ⟨fun hA i _ j _ => by simpa using hA i j, fun hA i j => by simpa using hA i trivial j trivial⟩
    rw [e]
    exact h
  have h := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin a) (Fin a) (w.adicCompletion E))).isCompact_preimage
    (hK.prod (hK.image MulOpposite.continuous_op))
  convert h using 1
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod,
    (MulOpposite.op_injective).mem_set_image]
  exact ⟨fun hg => ⟨fun i j => (hg i j).1, fun i j => (hg i j).2⟩, fun hg i j => ⟨hg.1 i j, hg.2 i j⟩⟩

theorem isCompact_closure_zpowers_iff (g : GLw a w) :
    IsCompact (closure (Subgroup.zpowers g : Set (GLw a w))) ↔
      ∃ R : ℝ, ∀ n : ℤ, ∀ i j, ‖(g ^ n).val i j‖ ≤ R := by
  constructor
  · intro hc
    have hb : ∀ i j : Fin a, ∃ C : ℝ, ∀ h ∈ closure (Subgroup.zpowers g : Set (GLw a w)), ‖h.val i j‖ ≤ C :=
      fun i j => hc.exists_bound_of_continuousOn (f := fun h : GLw a w => h.val i j)
        ((Units.continuous_val (M := Matrix (Fin a) (Fin a) (w.adicCompletion E))).matrix_elem i j).continuousOn
    choose C hC using hb
    refine ⟨∑ i, ∑ j, max (C i j) 0, fun n i j => ?_⟩
    have h1 := hC i j (g ^ n) (subset_closure (Subgroup.zpow_mem_zpowers g n))
    calc _ ≤ max (C i j) 0 := h1.trans (le_max_left _ _)
      _ ≤ ∑ j', max (C i j') 0 :=
        Finset.single_le_sum (f := fun j' => max (C i j') 0) (fun _ _ => le_max_right _ _) (Finset.mem_univ j)
      _ ≤ _ := Finset.single_le_sum (f := fun i' => ∑ j', max (C i' j') 0)
        (fun _ _ => Finset.sum_nonneg fun _ _ => le_max_right _ _) (Finset.mem_univ i)
  · rintro ⟨R, hR⟩
    refine (isCompact_boundedGL R).closure_of_subset ?_
    intro h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    refine fun i j => ⟨hR n i j, ?_⟩
    rw [← _root_.zpow_neg]
    exact hR (-n) i j

end Top

section Alg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {a : ℕ} {B : GlobalTheory.UnitLemma.InvAlg K} (b : Module.Basis (Fin a) K.E B.A)

omit [IsCMField E] in
theorem norm_le_one_iff_mem (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (x : K.E) :
    ‖e x‖ ≤ 1 ↔ x ∈ (algebraMap K.O K.E).range := by
  rw [he]
  exact Valued.toNormedField.norm_le_one_iff


omit [IsCMField E] in
theorem exists_norm_ge (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (R : ℝ) :
    ∃ c : K.E, c ≠ 0 ∧ R ≤ ‖e c‖ := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  have hπ0 : algebraMap K.O K.E π ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective K.O K.E)]
    exact hπ.ne_zero
  have hn : ¬ (algebraMap K.O K.E π)⁻¹ ∈ (algebraMap K.O K.E).range := by
    rintro ⟨o, ho⟩
    apply hπ.not_isUnit
    have h : π * o = 1 := IsFractionRing.injective K.O K.E (by rw [map_mul, ho, mul_inv_cancel₀ hπ0, map_one])
    exact isUnit_iff_exists_inv.2 ⟨o, h⟩
  have h1 : 1 < ‖e (algebraMap K.O K.E π)⁻¹‖ := by
    rw [← not_le, norm_le_one_iff_mem e he]
    exact hn
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt R h1
  refine ⟨((algebraMap K.O K.E π)⁻¹) ^ n, pow_ne_zero _ (inv_ne_zero hπ0), ?_⟩
  rw [map_pow, norm_pow]
  exact hn.le


omit [IsCMField E] in
theorem exists_fg_of_crd_le (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (R : ℝ) :
    ∃ M : Submodule K.O B.A, M.FG ∧ ∀ y, (∀ i, ‖crd e b y i‖ ≤ R) → y ∈ M := by
  obtain ⟨c, hc0, hc⟩ := exists_norm_ge e he R
  refine ⟨Submodule.span K.O (Set.range fun j => c • b j), Submodule.fg_span (Set.finite_range _), fun y hy => ?_⟩
  have hec : e c ≠ 0 := by rwa [Ne, map_eq_zero_iff _ e.injective]
  rw [← b.sum_repr y]
  refine Submodule.sum_mem _ fun j _ => ?_
  have hm : b.repr y j / c ∈ (algebraMap K.O K.E).range := by
    rw [← norm_le_one_iff_mem e he, map_div₀, norm_div, div_le_one (norm_pos_iff.2 hec)]
    exact (hy j).trans hc
  obtain ⟨o, ho⟩ := hm
  have : b.repr y j • b j = o • (c • b j) := by
    rw [← algebraMap_smul K.E o, smul_smul, ho, div_mul_cancel₀ _ hc0]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem isIntegral_of_bounded (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (u : B.A)
    (R : ℝ) (hR : ∀ n : ℕ, ∀ i j, ‖mulHom e b (u ^ n) i j‖ ≤ R) : IsIntegral K.O u := by
  obtain ⟨M, hMfg, hM⟩ := exists_fg_of_crd_le e b he (∑ j, R * ‖crd e b 1 j‖)
  have hle : Subalgebra.toSubmodule (Algebra.adjoin K.O {u}) ≤ M := by
    rw [Algebra.adjoin_eq_span, Submodule.span_le, ← Submonoid.powers_eq_closure]
    rintro _ ⟨n, rfl⟩
    refine hM _ fun i => ?_
    have h1 : crd e b (u ^ n) = mulHom e b (u ^ n) *ᵥ crd e b 1 := by rw [← crd_mul, mul_one]
    rw [h1]
    simp only [Matrix.mulVec, dotProduct]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hR n i j) (norm_nonneg _)
  haveI : IsNoetherian K.O M := isNoetherian_of_fg_of_noetherian M hMfg
  haveI : IsNoetherian K.O (Subalgebra.toSubmodule (Algebra.adjoin K.O {u})) := isNoetherian_of_le hle
  exact isIntegral_of_submodule_noetherian _ this u (Algebra.self_mem_adjoin_singleton K.O u)

theorem bounded_of_fg (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (M : Submodule K.O B.A)
    (hM : M.FG) : ∃ R : ℝ, ∀ y ∈ M, ∀ i j, ‖mulHom e b y i j‖ ≤ R := by
  obtain ⟨S, rfl⟩ := hM
  refine ⟨∑ y ∈ S, ∑ i, ∑ j, ‖mulHom e b y i j‖, fun x hx i j => ?_⟩
  obtain ⟨f, -, rfl⟩ := Submodule.mem_span_finset.1 hx
  have hsum : mulHom e b (∑ y ∈ S, f y • y) i j = ∑ y ∈ S, e (algebraMap K.O K.E (f y)) * mulHom e b y i j := by
    rw [mulHom_apply]
    simp only [mulHom_apply, Finset.sum_mul, smul_mul_assoc]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← algebraMap_smul K.E (f _), map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.smul_apply, smul_eq_mul, map_mul]
  rw [hsum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  rw [norm_mul]
  have h1 : ‖e (algebraMap K.O K.E (f y))‖ ≤ 1 := (norm_le_one_iff_mem e he _).2 ⟨f y, rfl⟩
  calc _ ≤ 1 * ‖mulHom e b y i j‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = ‖mulHom e b y i j‖ := one_mul _
    _ ≤ ∑ j', ‖mulHom e b y i j'‖ :=
      Finset.single_le_sum (f := fun j' => ‖mulHom e b y i j'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖mulHom e b y i' j'‖ :=
      Finset.single_le_sum (f := fun i' => ∑ j', ‖mulHom e b y i' j'‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)

end Alg

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {a : ℕ} {B : GlobalTheory.UnitLemma.InvAlg K} (b : Module.Basis (Fin a) K.E B.A)

theorem mulGL_zpow_val (t : B.Aˣ) (n : ℤ) : ((mulGL e b t) ^ n).val = mulHom e b ((t ^ n : B.Aˣ) : B.A) := by
  rw [← map_zpow]
  rfl

theorem isCompact_closure_zpowers_mulGL_iff' (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1)
    (t : B.Aˣ) : IsCompact (closure (Subgroup.zpowers (mulGL e b t) : Set (GLw a w))) ↔
      t ∈ GlobalTheory.UnitLemma.intUnits K.O B.A := by
  rw [isCompact_closure_zpowers_iff]
  simp only [mulGL_zpow_val]
  constructor
  · rintro ⟨R, hR⟩
    refine ⟨isIntegral_of_bounded e b he _ R fun n i j => ?_, isIntegral_of_bounded e b he _ R fun n i j => ?_⟩
    · have := hR n i j
      rwa [zpow_natCast, Units.val_pow_eq_pow_val] at this
    · have := hR (-(n : ℤ)) i j
      rwa [_root_.zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val] at this
  · rintro ⟨h1, h2⟩
    obtain ⟨R, hR⟩ := bounded_of_fg e b he _
      (fg_adjoin_of_finite (s := {(t : B.A), ((t⁻¹ : B.Aˣ) : B.A)}) (Set.toFinite _)
        (by rintro x (rfl | rfl); exacts [h1, h2]))
    refine ⟨R, fun n i j => hR _ ((Subalgebra.mem_toSubmodule _).2 ?_) i j⟩
    obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · rw [zpow_natCast, Units.val_pow_eq_pow_val]
      exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_insert _ _)) k
    · rw [_root_.zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
      exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_insert_of_mem _ (Set.mem_singleton _))) k

end Main

theorem isCompact_closure_zpowers_mulGL_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (a : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K) (b : Module.Basis (Fin a) K.E B.A) (t : B.Aˣ), IsCompact (closure (Subgroup.zpowers (GlobalTheory.TwOrbLat.mulGL e b t) : Set (GLw a w))) ↔ t ∈ GlobalTheory.UnitLemma.intUnits K.O B.A :=
  fun _ _ _ _ _ _ e he _ _ b t => isCompact_closure_zpowers_mulGL_iff' e b he t

end GlobalTheory.TwOrbLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLevelBlockLevelsSplitPlace
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.CtLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem continuous_dgM_inl {a b n : ℕ} (h : a + b = n) (w : Pl E) :
    Continuous ((dgM h w).comp (MonoidHom.inl (GLw a w) (GLw b w))) := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun x : GLw a w => dgMat h x.val (1 : GLw b w).val
    exact (Continuous.matrix_fromBlocks Units.continuous_val continuous_const continuous_const
      continuous_const).matrix_reindex _ _
  · have : (fun x : GLw a w => (((dgM h w).comp (MonoidHom.inl (GLw a w) (GLw b w))) x)⁻¹.val) =
        fun x => dgMat h (x⁻¹).val ((1 : GLw b w)⁻¹).val := by
      funext x
      rw [← map_inv]
      rfl
    rw [this]
    exact (Continuous.matrix_fromBlocks Units.continuous_coe_inv continuous_const continuous_const
      continuous_const).matrix_reindex _ _

theorem continuous_dgM_inr {a b n : ℕ} (h : a + b = n) (w : Pl E) :
    Continuous ((dgM h w).comp (MonoidHom.inr (GLw a w) (GLw b w))) := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun x : GLw b w => dgMat h (1 : GLw a w).val x.val
    exact (Continuous.matrix_fromBlocks continuous_const continuous_const continuous_const
      Units.continuous_val).matrix_reindex _ _
  · have : (fun x : GLw b w => (((dgM h w).comp (MonoidHom.inr (GLw a w) (GLw b w))) x)⁻¹.val) =
        fun x => dgMat h ((1 : GLw a w)⁻¹).val (x⁻¹).val := by
      funext x
      rw [← map_inv]
      rfl
    rw [this]
    exact (Continuous.matrix_fromBlocks continuous_const continuous_const continuous_const
      Units.continuous_coe_inv).matrix_reindex _ _

theorem continuous_det_GLw (m : ℕ) (w : Pl E) :
    Continuous (GeneralLinearGroup.det : GLw m w → (w.adicCompletion E)ˣ) := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun x : GLw m w => (x.val).det
    exact Units.continuous_val.matrix_det
  · have : (fun x : GLw m w => ((GeneralLinearGroup.det x)⁻¹ : (w.adicCompletion E)ˣ).val) =
        fun x => ((x⁻¹).val).det := by
      funext x
      rw [← map_inv]
      rfl
    rw [this]
    exact Units.continuous_coe_inv.matrix_det

theorem isOpen_detKer (m : ℕ) (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (hμ : IsOpen {x | μ x = 1}) :
    IsOpen ((μ.ker.comap GeneralLinearGroup.det : Subgroup (GLw m w)) : Set (GLw m w)) :=
  hμ.preimage (continuous_det_GLw m w)

theorem thL_split (m : ℕ) (w : Pl E) (hw : IsSplitAt w) : thL m w = MonoidHom.id _ := by
  rw [thL, if_pos hw]

end GlobalTheory.BCT.CtLevel

theorem GlobalTheory.BCT.CtLevel.isLevel_lev_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E)
    (N : Subgroup (GLw n w)) (μ : (w.adicCompletion E)ˣ →* ℂˣ), IsSplitAt w → IsOpen (N : Set (GLw n w)) →
    IsOpen {x | μ x = 1} →
    IsLevel (thL a w) (GlobalTheory.LFun.KGL w (n := a)) (lev₁ h w N μ) ∧ IsLevel (thL b w) (GlobalTheory.LFun.KGL w (n := b)) (lev₂ h w N μ) := by
  intro E _ _ _ a b n h w N μ hw hN hμ
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · exact (((GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1.inter
      (hN.preimage (continuous_dgM_inl h w))).inter (isOpen_detKer a w μ hμ))
  · exact inf_le_left.trans inf_le_left
  · intro k hk
    rw [thL_split a w hw]
    exact hk
  · exact (((GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1.inter
      (hN.preimage (continuous_dgM_inr h w))).inter (isOpen_detKer b w μ hμ))
  · exact inf_le_left.trans inf_le_left
  · intro k hk
    rw [thL_split b w hw]
    exact hk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzPairTermEqPointSumAnyTrivialisation
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.Pair

theorem term_eq_termAt : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) → ∀ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (δ z : Gr G r), IsNrm G r P.atP δ z → P.term Kf f r K φ = P.termAt Kf f r K φ x t hx δ z := by
  intro p _ G P Kf f r K φ hr hf hφ x t hx δ z hn
  have hex : ∃ dz : Gr G r × Gr G r, IsNrm G r P.atP dz.1 dz.2 := ⟨(δ, z), hn⟩
  unfold term
  rw [dite_eq_left hex]
  set x₀ := P.trivAf.choose
  set t₀ := P.trivAf.choose_spec.choose
  have h₀ : Triv G (AfP p) P.β x₀ t₀ := P.trivAf.choose_spec.choose_spec
  set δ₀ := hex.choose.1
  set z₀ := hex.choose.2
  have hn₀ : IsNrm G r P.atP δ₀ z₀ := hex.choose_spec
  obtain ⟨_, hreg, hcent⟩ := GlobalTheory.T.similitudePair_regular_image_at_p p G P
  obtain ⟨g, hgx⟩ := GlobalTheory.T.hermitianTripleTrivializations_differ_by_group_point p G (AfP p) (P.β : G.C) x x₀ t t₀ hx h₀
  obtain ⟨g₂, hδ, hcz⟩ := GlobalTheory.T.twistedConj_of_twistedNormConj_hermitianTriple_regular p G r P.atP δ z δ₀ z₀ hr hreg hn hn₀
  have htw := GlobalTheory.T.map_centralizer_regular_twistedCentraliser p G r P.atP δ z hr hreg hn
  have hAf : P.toAf x₀ t₀ h₀ = (MulAut.conj g⁻¹⁻¹).toMonoidHom.comp (P.toAf x t hx) := by
    ext y : 1
    apply Subtype.ext
    apply Prod.ext
    · have e : x₀ = (g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 * x := by rw [hgx, inv_mul_cancel_right]
      simp only [toAf, MonoidHom.comp_apply, MonoidHom.codRestrict_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Subgroup.coe_mul, Subgroup.coe_inv, Prod.fst_mul, Prod.fst_inv, MonoidHom.prodMap, MonoidHom.prod_apply, Subgroup.coe_subtype]
      rw [e]; group
    · simp only [toAf, MonoidHom.comp_apply, MonoidHom.codRestrict_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Subgroup.coe_mul, Subgroup.coe_inv, Prod.snd_mul, Prod.snd_inv, MonoidHom.prodMap, MonoidHom.prod_apply, Subgroup.coe_subtype]
      rw [mul_comm, inv_mul_cancel_left]
  have hQr : P.toQr r z₀ = (MulAut.conj g₂⁻¹).toMonoidHom.comp (P.toQr r z) := by
    ext y : 1
    have := hcz (locC G y.1) (hcent y)
    simp only [toQr, MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [this]
  have hself : P.toAf x₀ t₀ h₀ P.self = g⁻¹⁻¹ * P.toAf x t hx P.self * g⁻¹ := by
    rw [hAf]; simp [MulAut.conj_apply]
  unfold termAt
  rw [hself, hAf, hQr, hδ]
  refine GlobalTheory.T.kottwitzIsogenyClassPointSum_conj_data _ _ _ _ _ _ _ _ _ _ _ hf hφ ?_ ?_
  · intro y
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Prod.ext
    · exact y.2.1
    · exact mul_comm _ _
  · intro y
    have hm : P.toQr r z y ∈ GlobalTheory.BCT.twCent (sigG G r) δ := by
      rw [← htw]; exact ⟨locC G y.1, hcent y, rfl⟩
    exact hm

end GlobalTheory.LKMid.Pair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSpannedByGLColumnsEqIff
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TwOrbLat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {a : ℕ} {B : GlobalTheory.UnitLemma.InvAlg K} (b : Module.Basis (Fin a) K.E B.A)

theorem crd_smulO (c : K.O) (y : B.A) : crd e b (c • y) = e (algebraMap K.O K.E c) • crd e b y := by
  rw [← crd_smul, algebraMap_smul]

theorem crd_zero : crd e b (0 : B.A) = 0 := by
  funext i; simp [crd]

theorem mem_lat_iff (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (q : GLw a w) (y : B.A) :
    y ∈ GlobalTheory.TwLat.lat e b q ↔ ∀ i, Valued.v (((q⁻¹ : GLw a w).val *ᵥ crd e b y) i) ≤ 1 := by
  rw [latOf_eq]
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      intro i
      rw [crd_ofCrd, ← col_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    | zero => intro i; simp [crd_zero]
    | add x z _ _ hx hz =>
      intro i
      rw [crd_add, Matrix.mulVec_add, Pi.add_apply]
      exact (Valued.v.map_add _ _).trans (max_le (hx i) (hz i))
    | smul c x _ hx =>
      intro i
      rw [crd_smulO, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul]
      exact mul_le_one' ((he _).1 ⟨c, rfl⟩) (hx i)
  · intro h
    choose c hc using fun j => (he (e.symm (((q⁻¹ : GLw a w).val *ᵥ crd e b y) j))).2 (by
      rw [RingEquiv.apply_symm_apply]; exact h j)
    have hy : y = ∑ j, c j • ofCrd e b (fun i => q.val i j) := by
      apply crd_injective e b
      rw [crd_sum]
      have h1 : crd e b y = q.val *ᵥ ((q⁻¹ : GLw a w).val *ᵥ crd e b y) := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      conv_lhs => rw [h1]
      funext i
      simp only [crd_smulO, hc, RingEquiv.apply_symm_apply, crd_ofCrd, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [hy]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem lat_le_iff (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (q q' : GLw a w) :
    GlobalTheory.TwLat.lat e b q ≤ GlobalTheory.TwLat.lat e b q' ↔ ∀ i j, Valued.v ((q'⁻¹ * q : GLw a w).val i j) ≤ 1 := by
  constructor
  · intro hle i j
    have hm : ofCrd e b (fun i => q.val i j) ∈ GlobalTheory.TwLat.lat e b q := by
      rw [latOf_eq]; exact Submodule.subset_span ⟨j, rfl⟩
    have := (mem_lat_iff e b he q' _).1 (hle hm) i
    rw [crd_ofCrd, ← col_mul, ← Units.val_mul] at this
    exact this
  · intro h
    conv_lhs => rw [latOf_eq]
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, mem_lat_iff e b he, crd_ofCrd, ← col_mul, ← Units.val_mul]
    exact fun i => h i j

theorem lat_eq_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ)
    (e : K.E ≃+* w.adicCompletion E), (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) →
    ∀ (a : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K) (b : Module.Basis (Fin a) K.E B.A) (q q' : GLw a w),
    GlobalTheory.TwLat.lat e b q = GlobalTheory.TwLat.lat e b q' ↔ q⁻¹ * q' ∈ GlobalTheory.LFun.KGL w (n := a) := by
  intro E _ _ _ w K e he a B b q q'
  rw [le_antisymm_iff, lat_le_iff e b he, lat_le_iff e b he, GlobalTheory.LFun.KGL, GlobalTheory.AdelicU.mem_GLint_iff,
    _root_.mul_inv_rev, inv_inv]
  exact and_comm

end GlobalTheory.TwOrbLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSpannedByGLColumnsEqIffGLintCosetStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeSpannedByGLColumns_eq_iff_GLint_coset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), (∀ g g' : GLw m w, GlobalTheory.TwLat.lat e b g = GlobalTheory.TwLat.lat e b g' ↔ g⁻¹ * g' ∈ GlobalTheory.LFun.KGL w (n := m)) ∧ ∀ g : GLw m w, GlobalTheory.UnitLemma.IsLat K.O K.E (GlobalTheory.TwLat.lat e b g) := by
  first | exact @GlobalTheory.TwLatCoset.lat_coset | exact GlobalTheory.TwLatCoset.lat_coset | (intros; apply GlobalTheory.TwLatCoset.lat_coset <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalComponentDefiniteUnitaryFinitePartEqLocalPoStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localComponent_definiteUnitaryFinitePart_eq_localPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ (γ : UE E n) (w : Pl E), toSub (UL n w) (cLoc w ((finPt γ : finU (E := E) (n := n)) : UA E n)) = locPt w γ := by
  first | exact @GlobalTheory.BCT.locPt_finPt | exact GlobalTheory.BCT.locPt_finPt | (intros; apply GlobalTheory.BCT.locPt_finPt <;> assumption)
end

