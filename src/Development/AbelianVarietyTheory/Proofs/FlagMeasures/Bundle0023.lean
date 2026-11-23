module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTupleGramDetNeZero
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.NondegTuple

theorem conj_conj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

theorem exists_tuple_gram_det_ne_zero :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ a : ℕ, a ≤ n → ∃ X0 : Fin a → Fin n → E, (gramE σ J X0).det ≠ 0 ∧
        ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j := by
  intro F E _ _ _ _ _ σ hσ n J hJ a ha
  have hc : ∀ t, (σ : E →+* E) ((σ : E →+* E) t) = t := conj_conj hσ
  obtain ⟨P, d, -, hd, hfix, hne⟩ := GlobalTheory.HermDiag.exists_congr_diagonal (c := (σ : E →+* E))
    (G := J) two_ne_zero hc (fun i j => hJ.1 j i)
  have hg : gramE σ J (fun i k => σ (P k (Fin.castLE ha i))) =
      Matrix.diagonal fun i => d (Fin.castLE ha i) := by
    ext i j
    have h1 := congrFun (congrFun hd (Fin.castLE ha i)) (Fin.castLE ha j)
    rw [GlobalTheory.HermDiag.transpose_mul_mul_map_apply,
      GlobalTheory.HermDiag.dotProduct_mulVec_comp_eq_sum] at h1
    have h2 : Matrix.diagonal d (Fin.castLE ha i) (Fin.castLE ha j) =
        Matrix.diagonal (fun i => d (Fin.castLE ha i)) i j := by
      simp only [Matrix.diagonal_apply, (Fin.castLE_injective ha).eq_iff]
    rw [← h2, ← h1]
    simp only [gramE, hE, Formalism.UG.hform, RingHom.coe_coe, conj_conj hσ]
  refine ⟨fun i k => σ (P k (Fin.castLE ha i)), ?_, ?_⟩
  · rw [hg, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hne hJ.2 _
  · intro i j
    rw [hg]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
      exact hfix _
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ (Ne.symm hij), map_zero]

end GlobalTheory.NondegTuple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralValIntegerIff
section
open ValuativeRel MeasureTheory ComplexConjugate Formalism.MainNotions.S.Loc
open scoped ComplexOrder

namespace GlobalTheory.SgLoc

noncomputable def idemPairHom {F E : Type} [Field F] [CommRing E] [Algebra F E] (p q : E)
    (h1 : p + q = 1) (h0 : p * q = 0) : F × F →ₐ[F] E :=
  AlgHom.ofLinearMap
    ((LinearMap.toSpanSingleton F E p).coprod (LinearMap.toSpanSingleton F E q))
    (by simpa using h1)
    (by
      rintro ⟨a, b⟩ ⟨c, d⟩
      simp only [Prod.mk_mul_mk, LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply,
        Algebra.smul_def, map_mul]
      linear_combination
        (-(algebraMap F E a * algebraMap F E c * p) - algebraMap F E b * algebraMap F E d * q) * h1
        + (algebraMap F E a * algebraMap F E c + algebraMap F E b * algebraMap F E d
          - algebraMap F E a * algebraMap F E d - algebraMap F E b * algebraMap F E c) * h0)

end GlobalTheory.SgLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormGaussSumHermitianFormLinearLeStatement
section
open GlobalTheory.GramCount
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_gauss_sum_hermitian_form_linear_le : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (q : ℕ), 2 ≤ q → Fintype.card B = q ^ 2 → ∀ (χ : AddChar B ℂ), χ.IsPrimitive → (∀ u, χ (c u) = χ u) → ∀ (n : ℕ) (a : B), IsUnit (a + c a) → ∀ (v : Fin n → B), ‖∑ y : Fin n → B, χ (a * ip c y y + ip c y v)‖ ≤ (q : ℝ) ^ n := by
  first | exact @GlobalTheory.GramCount.norm_gauss_sum_ip_le | exact GlobalTheory.GramCount.norm_gauss_sum_ip_le | (intros; apply GlobalTheory.GramCount.norm_gauss_sum_ip_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveTuplesWithGramMatrixHenselCount
section
open GlobalTheory.GramCount
open scoped Classical

namespace GlobalTheory.GramCount

variable {A : Type} [CommRing A]

def henselHerm (c : A →+* A) (m : ℕ) (q : A) : AddSubgroup (Matrix (Fin m) (Fin m) A) where
  carrier := {H | (∀ a b, c (H b a) = H a b) ∧ ∀ a b, q ∣ H a b}
  zero_mem' := ⟨fun a b => by simp, fun a b => by simp⟩
  add_mem' := fun {H K} hH hK =>
    ⟨fun a b => by simp [Matrix.add_apply, hH.1, hK.1],
      fun a b => by simpa [Matrix.add_apply] using dvd_add (hH.2 a b) (hK.2 a b)⟩
  neg_mem' := fun {H} hH =>
    ⟨fun a b => by simp [Matrix.neg_apply, hH.1],
      fun a b => by simpa [Matrix.neg_apply] using hH.2 a b⟩

def henselGram (c : A →+* A) {m n : ℕ} (x : Fin m → Fin n → A) : Matrix (Fin m) (Fin m) A :=
  Matrix.of fun a b => ip c (x b) (x a)

def henselDiff (c : A →+* A) {m n : ℕ} (q : A) (x : Fin m → Fin n → A) :
    (Fin m → Fin n → A) →+ Matrix (Fin m) (Fin m) A where
  toFun w := Matrix.of fun a b => q * (ip c (w b) (x a) + ip c (x b) (w a))
  map_zero' := by
    ext a b
    simp [ip_zero_left, ip_zero_right]
  map_add' w w' := by
    ext a b
    simp only [Matrix.of_apply, Matrix.add_apply, Pi.add_apply, ip_add_left, ip_add_right]
    ring

theorem hensel_step [Finite A] (c : A →+* A) (hc : ∀ u, c (c u) = u) {ω : A}
    (hω : IsUnit (ω - c ω)) {p : A} (hp : c p = p) (hn : IsNilpotent p) (m n : ℕ)
    (G : Matrix (Fin m) (Fin m) A) (i : ℕ) :
    Set.ncard {x : Fin m → Fin n → A | x ∈ {x | Prim c x} ∧
        henselGram c x - G ∈ henselHerm c m (p ^ (i + 1))} *
      Nat.card (henselHerm c m (p ^ (i + 2))) =
    Set.ncard {x : Fin m → Fin n → A | x ∈ {x | Prim c x} ∧
        henselGram c x - G ∈ henselHerm c m (p ^ (i + 2))} *
      Nat.card (henselHerm c m (p ^ (i + 1))) := by
  obtain ⟨θ, -, hθ, -, -⟩ := exists_trace_one c hc hω
  have hq : c (p ^ (i + 1)) = p ^ (i + 1) := by rw [map_pow, hp]
  refine GlobalTheory.henselStep_count (DistribSMul.toAddMonoidHom (Fin m → Fin n → A) (p ^ (i + 1)))
    (henselGram c) _ _ _ G ?_ ?_ ?_
  · intro H hH
    exact ⟨hH.1, fun a b => (pow_dvd_pow p (by omega)).trans (hH.2 a b)⟩
  · rintro x ⟨y, hy⟩ w
    refine prim_of_sub_mem c hc (Ideal.span {p}) ?_ _ y fun a b => ?_
    · intro u hu
      obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton.1 hu
      exact IsNilpotent.isUnit_one_add ((Commute.all _ _).isNilpotent_mul_right hn)
    · rw [Ideal.mem_span_singleton]
      refine ⟨p ^ i * ip c (w a) (y b), ?_⟩
      simp only [Pi.add_apply, DistribSMul.toAddMonoidHom_apply, Pi.smul_apply, ip_add_left,
        ip_smul_left, hy]
      ring
  · rintro x ⟨y, hy⟩
    refine ⟨henselDiff c (p ^ (i + 1)) x, fun w => ⟨fun a b => ?_, fun a b => ?_⟩, ?_, fun w => ⟨fun a b => ?_, fun a b => ?_⟩⟩
    · simp only [henselDiff, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.of_apply, map_mul,
        map_add, hq, cj_ip c hc]
      ring
    · exact Dvd.intro _ rfl
    · intro H hH
      choose u hu using hH.2
      have hy' : ∀ a b, ip c (y b) (x a) = if a = b then 1 else 0 := by
        intro a b
        rw [← cj_ip c hc, hy]
        split_ifs <;> simp
      refine ⟨fun b => ∑ e, (θ * u e b) • y e, ?_⟩
      have : henselDiff c (p ^ (i + 1)) x (fun b => ∑ e, (θ * u e b) • y e) = H := by
        ext a b
        have h1 : p ^ (i + 1) * c (u b a) = H a b := by
          rw [← hH.1 a b, hu b a, map_mul, hq]
        simp only [henselDiff, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.of_apply,
          ip_sum_left, ip_sum_right, ip_smul_left, ip_smul_right, hy, hy', mul_ite, mul_one,
          mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_mul]
        linear_combination (c θ) * h1 - θ * hu a b + H a b * hθ
      rw [this, sub_self]
      exact zero_mem _
    · simp only [henselDiff, henselGram, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.of_apply,
        Matrix.sub_apply, map_mul, map_sub, map_add, hq, cj_ip c hc]
      ring
    · refine ⟨p ^ i * ip c (w b) (w a), ?_⟩
      simp only [henselDiff, henselGram, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.of_apply,
        Matrix.sub_apply, Pi.add_apply, DistribSMul.toAddMonoidHom_apply, Pi.smul_apply,
        ip_add_left, ip_add_right, ip_smul_left, ip_smul_right, hq]
      ring

theorem hensel_iter [Finite A] (c : A →+* A) (hc : ∀ u, c (c u) = u) {ω : A}
    (hω : IsUnit (ω - c ω)) {p : A} (hp : c p = p) (hn : IsNilpotent p) (m n : ℕ)
    (G : Matrix (Fin m) (Fin m) A) (k : ℕ) :
    Set.ncard {x : Fin m → Fin n → A | x ∈ {x | Prim c x} ∧
        henselGram c x - G ∈ henselHerm c m (p ^ (0 + 1))} *
      Nat.card (henselHerm c m (p ^ (k + 1))) =
    Set.ncard {x : Fin m → Fin n → A | x ∈ {x | Prim c x} ∧
        henselGram c x - G ∈ henselHerm c m (p ^ (k + 1))} *
      Nat.card (henselHerm c m (p ^ (0 + 1))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h := hensel_step c hc hω hp hn m n G k
    have hpos : 0 < Nat.card (henselHerm c m (p ^ (k + 1))) := Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [show k + 1 + 1 = k + 2 from rfl]
    rw [mul_right_comm, ih, mul_right_comm, h, mul_right_comm]

theorem hensel_count : ∀ {A : Type} [CommRing A] [Finite A] (c : A →+* A), (∀ u, c (c u) = u) → ∀ (ω : A), IsUnit (ω - c ω) → ∀ (p : A), c p = p → IsNilpotent p → ∀ (m n : ℕ) (G : Matrix (Fin m) (Fin m) A), (∀ a b, c (G b a) = G a b) → Set.ncard (sols c n G) * Nat.card {H : Matrix (Fin m) (Fin m) A // (∀ a b, c (H b a) = H a b) ∧ ∀ a b, p ∣ H a b} = Set.ncard {x : Fin m → Fin n → A | Prim c x ∧ ∀ a b, p ∣ ip c (x b) (x a) - G a b} := by
  intro A _ _ c hc ω hω p hp hn m n G hG
  obtain ⟨k, hk⟩ := id hn
  have h := hensel_iter c hc hω hp hn m n G k
  have hk' : p ^ (k + 1) = 0 := by rw [pow_succ, hk, zero_mul]
  have hbot : henselHerm c m (p ^ (k + 1)) = ⊥ := by
    rw [hk', eq_bot_iff]
    intro H hH
    rw [AddSubgroup.mem_bot]
    ext a b
    simpa using hH.2 a b
  rw [hbot, zero_add, pow_one, AddSubgroup.card_bot, mul_one] at h
  have e1 : {x : Fin m → Fin n → A | x ∈ {x | Prim c x} ∧
        henselGram c x - G ∈ henselHerm c m p} =
      {x : Fin m → Fin n → A | Prim c x ∧ ∀ a b, p ∣ ip c (x b) (x a) - G a b} := by
    ext x
    refine and_congr_right fun _ => ⟨fun h => h.2, fun h => ⟨fun a b => ?_, h⟩⟩
    simp only [henselGram, Matrix.sub_apply, Matrix.of_apply, map_sub, cj_ip c hc, hG]
  have e2 : {x : Fin m → Fin n → A | x ∈ {x | Prim c x} ∧
        henselGram c x - G ∈ (⊥ : AddSubgroup (Matrix (Fin m) (Fin m) A))} = sols c n G := by
    ext x
    refine and_congr_right fun _ => ?_
    rw [AddSubgroup.mem_bot, sub_eq_zero, ← Matrix.ext_iff]
    rfl
  rw [e1, e2] at h
  exact h.symm

end GlobalTheory.GramCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SameBlockAppend
section
open ValuativeRel MeasureTheory ComplexConjugate Formalism.MainNotions.S.Loc
open scoped ComplexOrder

namespace GlobalTheory.SgLoc.PtAlg

variable {E : Type} [CommRing E]

theorem ptEntryL_append (bs : List (Eˣ × ℕ+)) (t : Eˣ) (s : ℕ+) :
    ∀ (m : ℕ), (bs.map (fun b => (b.2 : ℕ))).sum = m → ∀ a b : ℕ,
      ptEntryL (bs ++ [(t, s)]) a b =
        if a < m ∧ b < m then ptEntryL bs a b
        else if m ≤ a ∧ m ≤ b ∧ a + b + 1 = 2 * m + s then (t : E) else 0 := by
  induction bs with
  | nil =>
    intro m hm a b
    simp only [List.map_nil, List.sum_nil] at hm
    subst hm
    simp only [List.nil_append, ptEntryL]
    split_ifs <;> first | rfl | omega
  | cons hd bs ih =>
    obtain ⟨t', s'⟩ := hd
    intro m hm a b
    simp only [List.map_cons, List.sum_cons] at hm
    simp only [List.cons_append, ptEntryL]
    rw [ih _ rfl]
    split_ifs <;> first | rfl | omega

theorem mat_snoc {m : ℕ} (h : Pt E m) (t : Eˣ) (s : ℕ+) (a b : Fin (m + s)) :
    (h.snoc t s).mat a b =
      if hab : (a : ℕ) < m ∧ (b : ℕ) < m then h.mat ⟨a, hab.1⟩ ⟨b, hab.2⟩
      else if m ≤ (a : ℕ) ∧ m ≤ (b : ℕ) ∧ (a : ℕ) + b + 1 = 2 * m + s then (t : E) else 0 := by
  show ptEntryL (h.blocks ++ [(t, s)]) a b = _
  rw [ptEntryL_append h.blocks t s m h.size]
  split_ifs <;> rfl

theorem det_snoc_eq {m : ℕ} (h : Pt E m) (t : Eˣ) (s : ℕ+) :
    (h.snoc t s).mat.det =
      h.mat.det * (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s)) : ℤˣ) : ℤ) *
        (t : E) ^ (s : ℕ)) := by
  have key : Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm (h.snoc t s).mat =
      Matrix.fromBlocks h.mat 0 0
        ((t : E) • (Fin.revPerm : Equiv.Perm (Fin s)).permMatrix E) := by
    ext (i | i) (j | j) <;>
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, mat_snoc,
        finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.val_castAdd, Fin.val_natAdd,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] <;>
      have hi := i.isLt <;> have hj := j.isLt
    · rw [dite_eq_left ⟨hi, hj⟩]
    · rw [dite_eq_right (by omega), ite_eq_right (by omega)]
    · rw [dite_eq_right (by omega), ite_eq_right (by omega)]
    · rw [dite_eq_right (by omega)]
      simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
        Option.mem_def, Option.some.injEq, Fin.revPerm_apply]
      by_cases hij : Fin.rev i = j
      · rw [ite_eq_left (by rw [← hij, Fin.val_rev]; omega), ite_eq_left hij, mul_one]
      · rw [ite_eq_right (fun hc => hij (Fin.ext (by rw [Fin.val_rev]; omega))),
          ite_eq_right hij, mul_zero]
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul,
    Matrix.det_permutation, Fintype.card_fin] at hdet
  rw [hdet]
  ring

theorem det_snoc {m : ℕ} (h : Pt E m) (t : Eˣ) (s : ℕ+) :
    (h.snoc t s).mat.det = h.mat.det * (t : E) ^ (s : ℕ) ∨
      (h.snoc t s).mat.det = -(h.mat.det * (t : E) ^ (s : ℕ)) := by
  rw [det_snoc_eq]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s))) with h1 | h1
  · left
    rw [h1]
    simp
  · right
    rw [h1]
    simp

private theorem isUnit_det_of_mem_UH_Hpk (bs : List (Eˣ × ℕ+)) :
    ∀ (n : ℕ) (hn : (bs.map (fun b => (b.2 : ℕ))).sum = n),
      IsUnit (Pt.mat (⟨bs, hn⟩ : Pt E n)).det := by
  induction bs using List.reverseRecOn with
  | nil =>
    intro n hn
    have hn' : n = 0 := by rw [← hn]; simp
    subst hn'
    simp
  | append_singleton bs x ih =>
    obtain ⟨t, s⟩ := x
    intro n hn
    have hn' : n = (bs.map (fun b => (b.2 : ℕ))).sum + s := by rw [← hn]; simp
    subst hn'
    have hu := ih _ rfl
    change IsUnit (Pt.snoc (⟨bs, rfl⟩ : Pt E _) t s).mat.det
    rcases det_snoc (⟨bs, rfl⟩ : Pt E _) t s with h1 | h1
    · rw [h1]
      exact hu.mul ((Units.isUnit t).pow _)
    · rw [h1]
      exact (hu.mul ((Units.isUnit t).pow _)).neg

theorem isUnit_det {m : ℕ} (h : Pt E m) : IsUnit h.mat.det := by
  exact isUnit_det_of_mem_UH_Hpk h.blocks m h.size

end GlobalTheory.SgLoc.PtAlg

namespace GlobalTheory.SgLoc

end GlobalTheory.SgLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilIntegrationFormulaOrbit
section
open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.WeilOrbit

theorem measurableEmbedding_of_sigmaCompact {Y X : Type} [TopologicalSpace Y] [T2Space Y]
    [SigmaCompactSpace Y] [MeasurableSpace Y] [BorelSpace Y] [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] {φ : Y → X} (hc : Continuous φ)
    (hi : Function.Injective φ) : MeasurableEmbedding φ := by
  refine ⟨hi, hc.measurable, fun s hs => ?_⟩
  have h : φ '' s = ⋃ n, (fun y : compactCovering Y n => φ y) '' (Subtype.val ⁻¹' s) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨n, hn⟩ := exists_mem_compactCovering y
      exact ⟨n, ⟨y, hn⟩, hy, rfl⟩
    · rintro ⟨n, y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
  rw [h]
  refine MeasurableSet.iUnion fun n => ?_
  haveI : CompactSpace (compactCovering Y n) :=
    isCompact_iff_compactSpace.mp (isCompact_compactCovering Y n)
  have hce : Topology.IsClosedEmbedding (fun y : compactCovering Y n => φ y) :=
    (hc.comp continuous_subtype_val).isClosedEmbedding (hi.comp Subtype.val_injective)
  exact hce.measurableEmbedding.measurableSet_image.mpr (measurable_subtype_coe hs)

theorem exists_compact_cover {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] (H : Subgroup G) {C : Set (G ⧸ H)} (hC : IsCompact C) :
    ∃ K : Set G, IsCompact K ∧ C ⊆ (QuotientGroup.mk : G → G ⧸ H) '' K := by
  refine hC.induction_on (p := fun C => ∃ K : Set G, IsCompact K ∧
    C ⊆ (QuotientGroup.mk : G → G ⧸ H) '' K) ⟨∅, isCompact_empty, by simp⟩ ?_ ?_ ?_
  · rintro s t hst ⟨K, hK, h⟩
    exact ⟨K, hK, hst.trans h⟩
  · rintro s t ⟨K, hK, h⟩ ⟨L, hL, h'⟩
    exact ⟨K ∪ L, hK.union hL, by rw [Set.image_union]; exact Set.union_subset_union h h'⟩
  · intro q _
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨K, hK, hg⟩ := exists_compact_mem_nhds g
      exact ⟨_, mem_nhdsWithin_of_mem_nhds (QuotientGroup.isOpenMap_coe.image_mem_nhds hg),
        K, hK, subset_rfl⟩

def orbitMap (G : Type) {X : Type} [Group G] [MulAction G X] (x0 : X) :
    G ⧸ MulAction.stabilizer G x0 → X :=
  MulAction.ofQuotientStabilizer G x0

theorem orbitMap_mk {G X : Type} [Group G] [MulAction G X] (x0 : X) (g : G) :
    orbitMap G x0 (g : G ⧸ MulAction.stabilizer G x0) = g • x0 := rfl

theorem orbitMap_injective {G X : Type} [Group G] [MulAction G X] (x0 : X) :
    Function.Injective (orbitMap G x0) :=
  MulAction.injective_ofQuotientStabilizer G x0

theorem weil_formula : ∀ (G X : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [MulAction G X] [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (x0 : X), Continuous (fun p : G × X => p.1 • p.2) → ∀ (μ : Measure G), μ.IsHaarMeasure → ∀ (ν : Measure X), ν {y | ¬ ∃ g : G, g • x0 = y} = 0 → (∀ (g : G) (s : Set X), MeasurableSet s → ν ((fun y => g • y) ⁻¹' s) = ν s) → (∀ K : Set G, IsCompact K → ν ((fun g => g • x0) '' K) < ⊤) → ν ≠ 0 → ∃ μ' : Measure (MulAction.stabilizer G x0), μ'.IsHaarMeasure ∧ ∀ f : G → ℝ≥0∞, Measurable f → ∀ s : X → G, (∀ y, (∃ g : G, g • x0 = y) → s y • x0 = y) → ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ h', f (s y * (h' : G)) ∂μ' ∂ν := by
  intro G X _ _ _ _ _ _ _ _ _ _ _ _ _ _ x0 hcont μ hμ ν hν0 hinv hfin hne
  set H := MulAction.stabilizer G x0 with hHdef
  have hc0 : Continuous (fun g : G => g • x0) :=
    hcont.comp (continuous_id.prodMk continuous_const)
  have hH : IsClosed (H : Set G) := isClosed_eq hc0 continuous_const
  haveI := hH
  letI : MeasurableSpace (G ⧸ H) := borel _
  haveI : BorelSpace (G ⧸ H) := ⟨rfl⟩
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SigmaCompactSpace (G ⧸ H) := inferInstance
  let φ : G ⧸ H → X := orbitMap G x0
  have hφc : Continuous φ := (QuotientGroup.isQuotientMap_mk H).continuous_iff.mpr hc0
  have hφ : MeasurableEmbedding φ :=
    measurableEmbedding_of_sigmaCompact hφc (orbitMap_injective x0)
  have hrange : Set.range φ = {y | ∃ g : G, g • x0 = y} := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      induction q using QuotientGroup.induction_on with
      | H g => exact ⟨g, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨(g : G ⧸ H), rfl⟩
  have hae : ∀ᵐ y ∂ν, y ∈ Set.range φ := by
    rw [hrange]
    exact hν0
  have hmap : (ν.comap φ).map φ = ν := by
    rw [hφ.map_comap, Measure.restrict_eq_self_of_ae_mem hae]
  have hrad : GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.IsInvariantRadon H (ν.comap φ) := by
    refine ⟨fun h0 => hne ?_, ⟨fun C hC => ?_⟩, ⟨fun g s hs => ?_⟩⟩
    · rw [← hmap, h0, Measure.map_zero]
    · obtain ⟨K, hK, hCK⟩ := exists_compact_cover H hC
      rw [hφ.comap_apply]
      refine (measure_mono ?_).trans_lt (hfin K hK)
      rintro _ ⟨q, hq, rfl⟩
      obtain ⟨g, hg, rfl⟩ := hCK hq
      exact ⟨g, hg, rfl⟩
    · rw [hφ.comap_apply, hφ.comap_apply, ← hinv g (φ '' s) (hφ.measurableSet_image.mpr hs)]
      congr 1
      have heq : ∀ (a : G) (q : G ⧸ H), φ (a • q) = a • φ q := by
        intro a q
        induction q using QuotientGroup.induction_on with
        | H b => exact mul_smul a b x0
      ext y
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact ⟨g • q, hq, heq g q⟩
      · rintro ⟨q, hq, h⟩
        refine ⟨g⁻¹ • q, by simpa using hq, ?_⟩
        rw [heq, h, inv_smul_smul]
  let ν0 : Measure H := Measure.haar
  obtain ⟨dg, ⟨hdg, hq⟩, -⟩ :=
    GlobalTheory.QuotientHaar.existsUnique_haar_of_invariantRadon G H hH ν0 _ hrad
  let c := Measure.haarScalarFactor μ dg
  have hc : μ = c • dg := Measure.isMulLeftInvariant_eq_smul μ dg
  have hcpos : c ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure μ dg).ne'
  refine ⟨c • ν0, Measure.IsHaarMeasure.nnreal_smul ν0 hcpos, fun f hf s hs => ?_⟩
  have h1 : ∫⁻ y, ∫⁻ h' : H, f (s y * (h' : G)) ∂ν0 ∂ν = ∫⁻ g, f g ∂dg := by
    rw [(hq f hf).2]
    conv_lhs => rw [← hmap]
    rw [hφ.lintegral_map]
    refine lintegral_congr fun q => ?_
    rw [← GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.fibreIntegral_mk H ν0 f]
    congr 1
    apply orbitMap_injective x0
    rw [orbitMap_mk]
    exact hs _ (by
      have : φ q ∈ Set.range φ := ⟨q, rfl⟩
      rwa [hrange] at this)
  rw [hc]
  simp only [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, h1]

end GlobalTheory.WeilOrbit
end

