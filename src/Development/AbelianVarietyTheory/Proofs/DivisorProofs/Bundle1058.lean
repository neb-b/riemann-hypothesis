module

public import Mathlib
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactSetTwistedCentralizerElliptic
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct Pointwise

namespace GlobalTheory.CentCpt

section Closed
variable {L : Type} [NormedField L] [IsAlgClosed L] {n : ℕ}

theorem exists_eigenbasis (y : Matrix (Fin n) (Fin n) L) (hs : y.charpoly.Separable) :
    ∃ (ι : Type) (_ : Fintype ι) (v : ι → Fin n → L) (l : ι → L), LinearIndependent L v ∧
      Fintype.card ι = n ∧ ∀ i, Module.End.HasEigenvector (Matrix.toLin' y) (l i) (v i) := by
  classical
  have hnd : y.charpoly.roots.Nodup := nodup_roots hs
  have hcard : y.charpoly.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hnd, splits_iff_card_roots.1 (IsAlgClosed.splits _),
      charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hev : ∀ r : y.charpoly.roots.toFinset, ∃ v : Fin n → L,
      Module.End.HasEigenvector (Matrix.toLin' y) r.1 v := fun r =>
    ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).2 (by
      rw [Matrix.charpoly_toLin']
      exact isRoot_of_mem_roots (Multiset.mem_toFinset.1 r.2))).exists_hasEigenvector
  choose v hv using hev
  exact ⟨_, inferInstance, v, fun r => r.1,
    Module.End.eigenvectors_linearIndependent' _ _ Subtype.val_injective v hv,
    by rw [Fintype.card_coe, hcard], hv⟩

theorem aeval_mulVec_eigen (y : Matrix (Fin n) (Fin n) L) {μ : L} {x : Fin n → L}
    (h : Module.End.HasEigenvector (Matrix.toLin' y) μ x) (q : L[X]) :
    aeval y q *ᵥ x = q.eval μ • x := by
  rw [← Module.End.aeval_apply_of_hasEigenvector h]
  have h1 := aeval_algHom_apply (toLinAlgEquiv' (R := L) (n := Fin n)).toAlgHom y q
  exact (LinearMap.congr_fun h1 x).symm

theorem exists_bound (y : Matrix (Fin n) (Fin n) L) (hs : y.charpoly.Separable) :
    ∃ M : ℝ, ∀ t : Matrix (Fin n) (Fin n) L, t * y = y * t →
      (∃ B : ℝ, ∀ k : ℕ, ∀ i j, ‖(t ^ k) i j‖ ≤ B) → ∀ i j, ‖t i j‖ ≤ M := by
  classical
  obtain ⟨ι, _, v, l, hli, hcard, hv⟩ := exists_eigenbasis y hs
  let b : Module.Basis ι L (Fin n → L) :=
    basisOfLinearIndependentOfCardEqFinrank' v hli (by rw [hcard, Module.finrank_fin_fun])
  have hb : ⇑b = v := coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _
  let c : Fin n → ι → L := fun j i => b.repr (Pi.single j 1) i
  refine ⟨∑ a, ∑ j, ∑ i, ‖c j i‖ * ‖v i a‖, fun t ht ⟨B, hB⟩ a j => ?_⟩
  obtain ⟨p, hp⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm y t hs ht.symm
  have hpow : ∀ k : ℕ, ∀ i, (t ^ k) *ᵥ v i = (p.eval (l i)) ^ k • v i := by
    intro k i
    rw [hp, ← map_pow, aeval_mulVec_eigen y (hv i), eval_pow]
  have hd : ∀ i, ‖p.eval (l i)‖ ≤ 1 := by
    intro i
    obtain ⟨a0, ha0⟩ : ∃ a0, v i a0 ≠ 0 := by
      by_contra h
      push_neg at h
      exact (hv i).2 (funext h)
    have hk : ∀ k : ℕ, ‖p.eval (l i)‖ ^ k ≤ (B * ∑ j, ‖v i j‖) / ‖v i a0‖ := by
      intro k
      rw [le_div_iff₀ (norm_pos_iff.2 ha0), ← norm_pow, ← norm_mul]
      have e := congrFun (hpow k i) a0
      rw [Pi.smul_apply, smul_eq_mul] at e
      rw [← e, Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hB k a0 j) (norm_nonneg _)
    by_contra h1
    push_neg at h1
    obtain ⟨k, hk'⟩ := ((tendsto_pow_atTop_atTop_of_one_lt h1).eventually_gt_atTop
      ((B * ∑ j, ‖v i j‖) / ‖v i a0‖)).exists
    exact absurd (hk k) (not_le.2 hk')
  have hcol : t a j = (t *ᵥ Pi.single j 1) a := by
    rw [Matrix.mulVec_single_one]; rfl
  have hexp : (Pi.single j 1 : Fin n → L) = ∑ i, c j i • v i := by
    rw [← hb]; exact (b.sum_repr _).symm
  have hval : t a j = ∑ i, c j i * (p.eval (l i) * v i a) := by
    rw [hcol, hexp, Matrix.mulVec_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hpow 1 i
    rw [pow_one, pow_one] at this
    rw [Matrix.mulVec_smul, this, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  rw [hval]
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∑ i, ‖c j i * (p.eval (l i) * v i a)‖ ≤ ∑ i, ‖c j i‖ * ‖v i a‖ := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (by
      simpa using mul_le_mul_of_nonneg_right (hd i) (norm_nonneg (v i a))) (norm_nonneg _)
  refine h1.trans ?_
  have hnn : ∀ a' j', 0 ≤ ∑ i, ‖c j' i‖ * ‖v i a'‖ := fun _ _ =>
    Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  calc ∑ i, ‖c j i‖ * ‖v i a‖ ≤ ∑ j', ∑ i, ‖c j' i‖ * ‖v i a‖ :=
        Finset.single_le_sum (f := fun j' => ∑ i, ‖c j' i‖ * ‖v i a‖) (fun j' _ => hnn a j') (Finset.mem_univ j)
    _ ≤ ∑ a', ∑ j', ∑ i, ‖c j' i‖ * ‖v i a'‖ :=
        Finset.single_le_sum (f := fun a' => ∑ j', ∑ i, ‖c j' i‖ * ‖v i a'‖)
          (fun a' _ => Finset.sum_nonneg fun j' _ => hnn a' j') (Finset.mem_univ a)

end Closed
end GlobalTheory.CentCpt

namespace GlobalTheory.CentCpt

section Local
variable {F : Type} [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] {n : ℕ}

theorem exists_bound_local (y : Matrix (Fin n) (Fin n) F) (hs : y.charpoly.Separable) :
    ∃ M : ℝ, ∀ t : Matrix (Fin n) (Fin n) F, t * y = y * t →
      (∃ B : ℝ, ∀ k : ℕ, ∀ i j, ‖(t ^ k) i j‖ ≤ B) → ∀ i j, ‖t i j‖ ≤ M := by
  letI : NormedField (AlgebraicClosure F) := spectralNorm.normedField F (AlgebraicClosure F)
  let f : F →+* AlgebraicClosure F := algebraMap F _
  have hf : ∀ x : F, ‖f x‖ = ‖x‖ := fun x => spectralNorm_extends (L := AlgebraicClosure F) x
  obtain ⟨M, hM⟩ := exists_bound (y.map f) (by rw [Matrix.charpoly_map]; exact hs.map)
  refine ⟨M, fun t ht ⟨B, hB⟩ i j => ?_⟩
  have := hM (t.map f) (by rw [← Matrix.map_mul, ht, Matrix.map_mul]) ⟨B, fun k a b => by
      rw [← Matrix.map_pow, Matrix.map_apply, hf]; exact hB k a b⟩ i j
  rwa [Matrix.map_apply, hf] at this

theorem isCompact_bdd [ProperSpace F] (M : ℝ) :
    IsCompact {g : GL (Fin n) F | (∀ i j, ‖(g : Matrix (Fin n) (Fin n) F) i j‖ ≤ M) ∧
      ∀ i j, ‖((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j‖ ≤ M} := by
  first
  | exact @_root_.GlobalTheory.BoundedUnitsCompact.isCompact_bounded_units
  | exact _root_.GlobalTheory.BoundedUnitsCompact.isCompact_bounded_units
  | (apply _root_.GlobalTheory.BoundedUnitsCompact.isCompact_bounded_units <;> assumption)
  | (intros; apply _root_.GlobalTheory.BoundedUnitsCompact.isCompact_bounded_units <;> assumption)
  | (intros; apply @_root_.GlobalTheory.BoundedUnitsCompact.isCompact_bounded_units <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.BoundedUnitsCompact.isCompact_bounded_units ..)

end Local

theorem norm_le_sum {F : Type} [NormedField F] {n : ℕ} (A : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    ‖A i j‖ ≤ ∑ a, ∑ b, ‖A a b‖ :=
  (Finset.single_le_sum (f := fun b => ‖A i b‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun a => ∑ b, ‖A a b‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (Finset.mem_univ i))

end GlobalTheory.CentCpt

namespace GlobalTheory.CentCpt

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : UL n w),
    y.1.val.charpoly.Separable → ∃ Ω : Set (UL n w), IsCompact Ω ∧ ∀ t ∈ twCent (MonoidHom.id (UL n w)) y,
      IsCompact (closure (Subgroup.zpowers t : Set (UL n w))) → t ∈ Ω := by
  intro E _ _ _ _ n w y hs
  letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _
  haveI : IsUltrametricDist (w.adicCompletion E) :=
    inferInstanceAs (@IsUltrametricDist (w.adicCompletion E)
      (Valued.toNormedField (w.adicCompletion E) (WithZero (Multiplicative ℤ))).toDist)
  haveI : CompleteSpace (w.adicCompletion E) := inferInstance
  haveI : ProperSpace (w.adicCompletion E) :=
    ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace (w.adicCompletion E)
  obtain ⟨M, hM⟩ := exists_bound_local (y.1.val) hs
  refine ⟨Subtype.val ⁻¹' {g : GLw n w | (∀ i j, ‖(g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j‖ ≤ M) ∧
      ∀ i j, ‖((g⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j‖ ≤ M},
    (GlobalTheory.LocFinU.isClosed_UL n w).isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_bdd (n := n) M), ?_⟩
  have hbd : ∀ s ∈ twCent (MonoidHom.id (UL n w)) y, IsCompact (closure (Subgroup.zpowers s : Set (UL n w))) →
      ∀ i j, ‖(s.1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j‖ ≤ M := by
    intro s hs' hcs
    have hcont : Continuous fun g : UL n w =>
        ∑ a, ∑ b, ‖(g.1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) a b‖ :=
      continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
        ((Units.continuous_val.comp continuous_subtype_val).matrix_elem a b).norm
    obtain ⟨B, hB⟩ := (hcs.image hcont).bddAbove
    refine hM _ ?_ ⟨B, fun k a b => ?_⟩
    · have h1 : s * y = y * s := hs'
      have h2 := congrArg (fun g : UL n w => (g.1 : Matrix (Fin n) (Fin n) (w.adicCompletion E))) h1
      simpa using h2
    · have hk : s ^ k ∈ closure (Subgroup.zpowers s : Set (UL n w)) :=
        subset_closure (Subgroup.npow_mem_zpowers s k)
      have e : ((s ^ k).1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
          (s.1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) ^ k := by
        simp [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
      rw [← e]
      exact (norm_le_sum _ a b).trans (hB ⟨_, hk, rfl⟩)
  intro t ht hc
  refine ⟨hbd t ht hc, ?_⟩
  have := hbd t⁻¹ (inv_mem ht) (by rwa [Subgroup.zpowers_inv])
  simpa using this

end GlobalTheory.CentCpt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveCartierDivisorAddEffective
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

set_option autoImplicit false
noncomputable section
open GlobalTheory.Cartier.CartierDiv
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.Cartier.EffDiff

variable {X : Scheme.{0}} [IsIntegral X]

theorem exists_pow_regAt {V : X.Opens} (hV : IsAffineOpen V) (τ : Γ(X, V))
    (hη : genericPoint X ∈ X.basicOpen τ) {f : X.functionField}
    (hf : ∀ x ∈ X.basicOpen τ, RegAt x f) :
    ∃ m : ℕ, ∀ x ∈ V, RegAt x (f * fnOf V (X.basicOpen_le τ hη) τ ^ m) := by
  obtain ⟨b, hb⟩ := exists_fnOf_eq hη hf
  haveI := hV.isLocalization_basicOpen τ
  obtain ⟨m, a, e⟩ := IsLocalization.Away.surj τ b
  refine ⟨m, fun x hx => ?_⟩
  have e' := congrArg (fnOf _ hη) e
  rw [map_mul, map_pow, hb] at e'
  have h1 : ∀ c : Γ(X, V), fnOf _ hη (algebraMap Γ(X, V) Γ(X, X.basicOpen τ) c) =
      fnOf V (X.basicOpen_le τ hη) c := fun c => fnOf_resG (X.basicOpen_le τ) hη c
  rw [h1, h1] at e'
  rw [e']
  exact regAt_fnOf hx _ a

theorem eventually_eff_add_nsmul [CompactSpace X] {L : LB X} (hL : L.IsLB) (t : L.Sec)
    (ht : genericPoint X ∈ nonzeroLocus t) (D : CartierDiv X)
    (hD : ∀ x ∈ nonzeroLocus t, D.RegularAt x 1) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → (D + N • divOfSec hL t ht).Eff := by
  have key : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ ∃ m : ℕ, ∀ N, m ≤ N → ∀ y ∈ V,
      (D + N • divOfSec hL t ht).RegularAt y 1 := by
    intro x
    obtain ⟨W, hxW, h, hh⟩ := D.exists_isEqn_nhds x
    obtain ⟨i, hi⟩ := exists_chart hL x
    obtain ⟨V, hVa, hxV, hVle⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (show x ∈ W ⊓ L.U i from ⟨hxW, hi⟩)
    have hVW : V ≤ W := hVle.trans inf_le_left
    have hVi : V ≤ L.U i := hVle.trans inf_le_right
    set τ : Γ(X, V) := resG X hVi (t.f i)
    have hbo : ∀ y, y ∈ X.basicOpen τ ↔ y ∈ V ∧ y ∈ nonzeroLocus t := fun y => by
      have hb : X.basicOpen τ = V ⊓ X.basicOpen (t.f i) := X.basicOpen_res _ _
      rw [hb]
      exact ⟨fun hy => ⟨hy.1, (mem_nonzeroLocus_iff t i (hVi hy.1)).2 hy.2⟩,
        fun hy => ⟨hy.1, (mem_nonzeroLocus_iff t i (hVi hy.1)).1 hy.2⟩⟩
    have hη : genericPoint X ∈ X.basicOpen τ := (hbo _).2 ⟨gen_mem hxV, ht⟩
    obtain ⟨m, hm⟩ := exists_pow_regAt hVa τ hη (f := h) fun y hy => by
      obtain ⟨hyV, hyt⟩ := (hbo y).1 hy
      have := (hh y (hVW hyV)).regularAt_iff.1 (hD y hyt)
      rwa [one_mul] at this
    refine ⟨V, hxV, m, fun N hN y hyV => ?_⟩
    have hT := (presents_divOfRatSec hL (isRatSec_ratOfSec t ht)).isEqn i y (hVi hyV)
    refine ⟨_, (hh y (hVW hyV)).add (hT.nsmul N), ?_⟩
    have e : (ratOfSec t ht i : X.functionField) = fnOf V (X.basicOpen_le τ hη) τ := by
      rw [val_ratOfSec (gen_mem (hVi hyV)), fnOf_resG]
    rw [one_mul, Units.val_mul, Units.val_pow_eq_pow_val, e, ← Nat.add_sub_cancel' hN, pow_add,
      ← mul_assoc]
    have hp := regAt_fnOf hyV (X.basicOpen_le τ hη) (τ ^ (N - m))
    rw [map_pow] at hp
    exact (hm y hyV).mul hp
  choose V hxV m hm using key
  obtain ⟨S, hS⟩ := exists_finset_iSup_eq_top V hxV
  refine ⟨S.sup m, fun N hN y => ?_⟩
  obtain ⟨x, hy⟩ := Opens.mem_iSup.1 (hS.ge (Set.mem_univ y))
  exact hm x N ((Finset.le_sup x.2).trans hN) y hy

end GlobalTheory.Cartier.EffDiff

theorem GlobalTheory.Cartier.EffDiff.exists_eff_and_add_eff : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (H : LB X),
    IsAmpleLB H → ∀ D : CartierDiv X, ∃ E : CartierDiv X, E.Eff ∧ (D + E).Eff := by
  intro X _ _ H hH D
  haveI := hH.compactSpace
  obtain ⟨W, hηW, g, hg⟩ := D.exists_isEqn_nhds (genericPoint X)
  obtain ⟨n, -, t, hηt, htW, hU⟩ := hH.exists_affine_le hηW
  have hL := isLB_lbPow hH.isLB n
  haveI : Nonempty (nonzeroLocus t) := ⟨⟨_, hηt⟩⟩
  haveI := functionField_isFractionRing_of_isAffineOpen X _ hU
  obtain ⟨a, c, hc, e⟩ := IsFractionRing.div_surjective (A := Γ(X, nonzeroLocus t))
    (g : X.functionField)
  have hfn : ∀ b : Γ(X, nonzeroLocus t),
      algebraMap Γ(X, nonzeroLocus t) X.functionField b = fnOf _ hηt b := fun _ => rfl
  have hc0 : fnOf _ hηt c ≠ 0 := by
    rw [← hfn]; exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hc
  obtain ⟨N₁, h₁⟩ := eventually_eff_add_nsmul hL t hηt (principal (Units.mk0 _ hc0))
    fun x hx => ⟨_, isEqn_principal _ x, by rw [one_mul, Units.val_mk0]; exact regAt_fnOf hx hηt c⟩
  obtain ⟨N₂, h₂⟩ := eventually_eff_add_nsmul hL t hηt (D + principal (Units.mk0 _ hc0))
    fun x hx => ⟨_, (hg x (htW hx)).add (isEqn_principal _ x), by
      rw [one_mul, Units.val_mul, Units.val_mk0, ← e, hfn, hfn, div_mul_cancel₀ _ hc0]
      exact regAt_fnOf hx hηt a⟩
  refine ⟨principal (Units.mk0 _ hc0) + max N₁ N₂ • divOfSec hL t hηt, h₁ _ (le_max_left _ _), ?_⟩
  rw [← add_assoc]
  exact h₂ _ (le_max_right _ _)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryPointCutToFibreUnion
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.FibreCut

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def idemF (P : Set (Pl E)) : Af E :=
  ⟨fun v => if v ∈ P then 1 else 0,
    Filter.Eventually.of_forall fun v => by
      dsimp only
      split_ifs
      · exact one_mem _
      · exact zero_mem _⟩

def idem (P : Set (Pl E)) : Ad E := sFin E (idemF P)

theorem idem_mul_idem (P : Set (Pl E)) : idem P * idem P = idem P := by
  refine Prod.ext (mul_zero _) (FiniteAdeleRing.ext E fun v => ?_)
  change (idemF P).1 v * (idemF P).1 v = (idemF P).1 v
  simp only [idemF]
  split_ifs <;> simp

def sIdem (P : Set (Pl E)) : Ad E →ₙ+* Ad E where
  toFun x := idem P * x
  map_mul' x y := by
    calc idem P * (x * y) = (idem P * idem P) * (x * y) := by rw [idem_mul_idem]
      _ = idem P * x * (idem P * y) := by ring
  map_zero' := mul_zero _
  map_add' x y := mul_add _ _ _

theorem pInf_sIdem (P : Set (Pl E)) (x : Ad E) : pInf E (sIdem P x) = 0 := by
  change pInf E (sFin E (idemF P) * x) = 0
  rw [map_mul]
  have : pInf E (sFin E (idemF P)) = 0 := map_zero (infEq E).symm
  rw [this, zero_mul]

theorem pLoc_sIdem_of_mem (P : Set (Pl E)) {v : Pl E} (hv : v ∈ P) (x : Ad E) :
    ((pLoc E v).comp (pFin E)) (sIdem P x) = ((pLoc E v).comp (pFin E)) x := by
  change ((pLoc E v).comp (pFin E)) (idem P) * _ = _
  have : ((pLoc E v).comp (pFin E)) (idem P) = 1 := by
    change (idemF P).1 v = 1
    simp only [idemF, if_pos hv]
  rw [this, one_mul]
  rfl

theorem pLoc_sIdem_of_not_mem (P : Set (Pl E)) {v : Pl E} (hv : v ∉ P) (x : Ad E) :
    ((pLoc E v).comp (pFin E)) (sIdem P x) = 0 := by
  change ((pLoc E v).comp (pFin E)) (idem P) * _ = _
  have : ((pLoc E v).comp (pFin E)) (idem P) = 0 := by
    change (idemF P).1 v = 0
    simp only [idemF, if_neg hv]
  rw [this, zero_mul]

theorem conjAd_idem (P : Set (Pl E))
    (hP : ∀ u v : Pl E, u.under (𝓞 (maximalRealSubfield E)) = v.under (𝓞 (maximalRealSubfield E)) → u ∈ P → v ∈ P) :
    conjAd E (idem P) = idem P := by
  refine Prod.ext ?_ (FiniteAdeleRing.ext E fun v => ?_)
  · change (infEq E) ((starRingEnd (Cinf E)) ((infEq E).symm 0)) = 0
    simp
  change pLoc E v (conjFin (IsCMField.complexConj E).toRingEquiv (idemF P)) = (idemF P).1 v
  rw [pLoc_conjFin]
  change conjLoc _ v ((idemF P).1 _) = (idemF P).1 v
  have hc := GlobalTheory.DefU.LocRet.under_conjSrc (E := E) v
  simp only [idemF]
  split_ifs with h1 h2 h2
  · simp
  · exact absurd (hP _ _ hc h1) h2
  · exact absurd (hP _ _ hc.symm h2) h1
  · simp

variable {n : ℕ}

theorem cT_corner (P : Set (Pl E))
    (hP : ∀ u v : Pl E, u.under (𝓞 (maximalRealSubfield E)) = v.under (𝓞 (maximalRealSubfield E)) → u ∈ P → v ∈ P)
    (M : Matrix (Fin n) (Fin n) (Ad E)) :
    cT (conjAd E) (corner (matN n (sIdem P)) M) = corner (matN n (sIdem P)) (cT (conjAd E) M) := by
  ext i j
  change conjAd E ((1 : Matrix (Fin n) (Fin n) (Ad E)) j i - idem P * (1 : Matrix (Fin n) (Fin n) (Ad E)) j i +
      idem P * M j i) = (1 : Matrix (Fin n) (Fin n) (Ad E)) i j - idem P * (1 : Matrix (Fin n) (Fin n) (Ad E)) i j +
      idem P * conjAd E (M j i)
  rw [map_add (f := _), map_sub, map_mul, map_mul, conjAd_idem P hP, Matrix.one_apply, Matrix.one_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h, Ne.symm h]

theorem corner_mem (P : Set (Pl E))
    (hP : ∀ u v : Pl E, u.under (𝓞 (maximalRealSubfield E)) = v.under (𝓞 (maximalRealSubfield E)) → u ∈ P → v ∈ P)
    (g : UA E n) : cornerGL n (sIdem P) g.1 ∈ UA E n := by
  have hg : cT (conjAd E) (g.1 : Matrix (Fin n) (Fin n) (Ad E)) * 1 * g.1 = 1 := g.2
  change cT (conjAd E) (corner (matN n (sIdem P)) g.1.1) * 1 * corner (matN n (sIdem P)) g.1.1 = 1
  rw [cT_corner P hP, Matrix.mul_one, ← map_mul, ← Matrix.mul_one (cT (conjAd E) _), hg, map_one]

theorem exists_cut : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : Set (Pl E)),
    (∀ u v : Pl E, u.under (𝓞 (maximalRealSubfield E)) = v.under (𝓞 (maximalRealSubfield E)) → u ∈ P → v ∈ P) →
    ∀ g ∈ finU (E := E) (n := n), ∃ x ∈ finU (E := E) (n := n), ∀ v : Pl E, cLoc v x = if v ∈ P then cLoc v g else 1 := by
  intro E _ _ _ n P hP g _
  refine ⟨⟨cornerGL n (sIdem P) g.1, corner_mem P hP g⟩, ?_, fun v => ?_⟩
  · exact MonoidHom.mem_ker.2 (map_cornerGL_of_zero _ _ (pInf_sIdem P) _)
  · split_ifs with hv
    · exact map_cornerGL_of_hom _ _ _ (pLoc_sIdem_of_mem P hv) _
    · exact map_cornerGL_of_zero _ _ (pLoc_sIdem_of_not_mem P hv) _

end GlobalTheory.FibreCut

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralClopenCoverOfSmoothQuasiCompactFie
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory

theorem exists_integral_clopen_cover_of_smooth_field :
    ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k) [Smooth f] [QuasiCompact f], ∃ (κ : Type) (U : κ → X.Opens), ⨆ c, U c = ⊤ ∧ (Pairwise fun a b => Disjoint (U a) (U b)) ∧ ∀ c, IsIntegral (U c).toScheme ∧ IsClosedImmersion (U c).ι := by
  intro k _ X f _ _
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hopen : ∀ c : _root_.ConnectedComponents X, IsOpen ((_root_.ConnectedComponents.mk : X → _) ⁻¹' {c}) := by
    intro c
    obtain ⟨x, rfl⟩ := _root_.ConnectedComponents.surjective_coe c
    rw [connectedComponents_preimage_singleton]
    exact GlobalTheory.isOpen_connectedComponent_of_isLocallyNoetherian X inferInstance x
  let U : _root_.ConnectedComponents X → X.Opens := fun c => ⟨_, hopen c⟩
  refine ⟨_root_.ConnectedComponents X, U, ?_, ?_, fun c => ?_⟩
  · rw [eq_top_iff]
    intro x _
    exact Opens.mem_iSup.2 ⟨_root_.ConnectedComponents.mk x, rfl⟩
  · intro a b hab
    rw [disjoint_iff, ← SetLike.coe_set_eq]
    ext x
    simp only [U, Opens.coe_inf, Opens.coe_mk, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, Opens.coe_bot, Set.mem_empty_iff_false, iff_false, not_and]
    rintro rfl rfl
    exact hab rfl
  · obtain ⟨x, rfl⟩ := _root_.ConnectedComponents.surjective_coe c
    have hU : ((U (_root_.ConnectedComponents.mk x) : X.Opens) : Set X) = connectedComponent x :=
      connectedComponents_preimage_singleton
    constructor
    · haveI : ConnectedSpace (U (_root_.ConnectedComponents.mk x)).toScheme := by
        show ConnectedSpace ((U (_root_.ConnectedComponents.mk x) : Set X))
        rw [← isConnected_iff_connectedSpace, hU]
        exact isConnected_connectedComponent
      exact isIntegral_of_smooth_field_of_connectedSpace ((U (_root_.ConnectedComponents.mk x)).ι ≫ f)
    · refine IsClosedImmersion.of_isPreimmersion _ ?_
      rw [Scheme.Opens.range_ι, hU]
      exact isClosed_connectedComponent

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRenormalizationRigidificationMultipleStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
open GlobalTheory.Poinc.Tors
theorem _root_.GlobalTheory.T.exists_renormalization_rigidification_multiple : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (w₀ : W0 U), w₀.IsGen → ∀ ρ : LB.Gen (A.L.pull (eSec A.A)), ρ.IsGen → ∃ (ρ' : LB.Gen (A.L.pull (eSec A.A))) (c : FractionRing R), c ≠ 0 ∧ NormW U w₀ ρ' ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ) (x : TFK (R := R) F ⟶ A.A) (fr fr' : FrAt x), IsTorsFrame A ρ N x fr → fr'.IsGen → (∀ z J, Good A.L z J → (val fr' (𝟙 _) z J).val = @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z (algebraMap (FractionRing R) F c)) * (val fr (𝟙 _) z J).val) → IsTorsFrame A ρ' N x fr' := by
  first | exact @GlobalTheory.Poinc.Renorm.exists_renorm | exact GlobalTheory.Poinc.Renorm.exists_renorm | (intros; apply GlobalTheory.Poinc.Renorm.exists_renorm <;> assumption)
end

