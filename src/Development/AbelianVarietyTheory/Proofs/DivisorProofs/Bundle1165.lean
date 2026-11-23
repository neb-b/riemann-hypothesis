module

public import Mathlib
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0097
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0204
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjIntegralIffLatticeUnimodular
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1078

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShiftedCapelliDeterminantSubleadingCoeffTrace
section
namespace GlobalTheory.CapelliNext

open Finset

variable {A : Type} [Ring A] [Algebra ℂ A]

def shiftCoeff (d : ℕ) (p q : A) (c : ℕ → A) : ℕ → A :=
  fun i => (Nat.casesOn i 0 (fun j => p * c j) : A) + (if i < d + 1 then q * c i else 0)

theorem affine_mul_eq (d : ℕ) (p q : A) (c : ℕ → A) (u : ℂ) :
    (u • p + q) * (∑ i ∈ range (d + 1), u ^ i • c i)
      = ∑ i ∈ range (d + 1 + 1), u ^ i • shiftCoeff d p q c i := by
  unfold shiftCoeff
  simp only [smul_add, sum_add_distrib, add_mul]
  congr 1
  · rw [sum_range_succ' _ (d + 1), mul_sum]
    simp only [Nat.rec_zero, smul_zero, add_zero]
    refine sum_congr rfl fun i _ => ?_
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, pow_succ]
  · rw [sum_range_succ _ (d + 1), mul_sum]
    simp only [lt_irrefl, if_false, smul_zero, add_zero]
    refine sum_congr rfl fun i hi => ?_
    rw [if_pos (mem_range.mp hi), mul_smul_comm]

theorem prod_affine_two_top (t : ℕ) (p : Fin (t + 1) → ℂ) (q : Fin (t + 1) → A) :
    ∃ c : ℕ → A, c (t + 1) = (∏ k, p k) • (1 : A) ∧
      c t = ∑ k, (∏ j, (if j = k then (1 : ℂ) else p j)) • q k ∧
      ∀ u : ℂ, (List.ofFn fun k => (u * p k) • (1 : A) + q k).prod
        = ∑ i ∈ range (t + 1 + 1), u ^ i • c i := by
  induction t with
  | zero =>
    let c : ℕ → A := fun i => if i = 0 then q 0 else if i = 1 then (p 0) • (1 : A) else 0
    refine ⟨c, ?_, ?_, fun u => ?_⟩
    · simp [c]
    · simp [c]
    · simp [c, sum_range_succ, add_comm]
      rw [mul_smul]
  | succ t ih =>
    obtain ⟨c, hc1, hc0, hc⟩ := ih (fun k => p k.succ) (fun k => q k.succ)
    refine ⟨shiftCoeff (t + 1) (p 0 • (1 : A)) (q 0) c, ?_, ?_, fun u => ?_⟩
    · simp only [shiftCoeff, lt_irrefl, if_false, add_zero]
      rw [hc1, smul_one_mul, smul_smul, ← Fin.prod_univ_succ]
    · simp only [shiftCoeff, lt_add_iff_pos_right, Nat.lt_add_one, if_true]
      rw [hc0, hc1, smul_one_mul, mul_smul_comm, mul_one, smul_sum, add_comm]
      conv_rhs => rw [Fin.sum_univ_succ]
      congr 1
      · simp [Fin.prod_univ_succ, smul_mul_assoc]
      · refine sum_congr rfl fun k _ => ?_
        simp [Fin.prod_univ_succ, Fin.succ_ne_zero, smul_smul, (Fin.succ_ne_zero _).symm]
    · rw [List.ofFn_succ, List.prod_cons, hc u]
      have : (u * p 0) • (1 : A) + q 0 = u • (p 0 • (1 : A)) + q 0 := by rw [smul_smul]
      rw [this, affine_mul_eq]

end GlobalTheory.CapelliNext

namespace GlobalTheory.CapelliNext
open Finset

theorem qdet_shift_next_coeff : ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A) (s : ℂ), ∃ (c : ℕ → A) (t : ℂ),
    c (m + 1) = 1 ∧ c m = ∑ i, E i i + t • (1 : A) ∧
      ∀ u : ℂ, Formalism.REAL.qdet E (u - s) = ∑ k ∈ Finset.range (m + 1 + 1), u ^ k • c k := by
  intro A _ _ m E s
  have h : ∀ σ : Equiv.Perm (Fin (m + 1)), ∃ c : ℕ → A,
      c (m + 1) = (∏ k, (if σ k = k then (1 : ℂ) else 0)) • (1 : A) ∧
      c m = ∑ k, (∏ j, (if j = k then (1 : ℂ) else (if σ j = j then (1 : ℂ) else 0))) •
        ((if σ k = k then algebraMap ℂ A (-s - ((k : ℕ) : ℂ)) else 0) + E (σ k) k) ∧
      ∀ u : ℂ, (List.ofFn fun k : Fin (m + 1) => Formalism.REAL.Tm E (u - s - ((k : ℕ) : ℂ)) (id (σ k)) (id k)).prod
        = ∑ i ∈ range (m + 1 + 1), u ^ i • c i := by
    intro σ
    obtain ⟨c, hc1, hc0, hc⟩ := prod_affine_two_top m (fun k => if σ k = k then (1 : ℂ) else 0)
      (fun k => (if σ k = k then algebraMap ℂ A (-s - ((k : ℕ) : ℂ)) else 0) + E (σ k) k)
    refine ⟨c, hc1, hc0, fun u => ?_⟩
    rw [← hc u]
    congr 2
    funext k
    unfold Formalism.REAL.Tm
    simp only [id]
    split_ifs with hk
    · rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ← add_assoc, ← add_smul]
      congr 2
      ring
    · simp
  choose c hc1 hc0 hc using h
  refine ⟨fun i => ∑ σ : Equiv.Perm (Fin (m + 1)), ((Equiv.Perm.sign σ : ℤ) : A) * c σ i,
    ∑ k : Fin (m + 1), (-s - ((k : ℕ) : ℂ)), ?_, ?_, fun u => ?_⟩
  · simp only
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin (m + 1)))]
    · rw [hc1 1]
      simp
    · intro σ _ hσ
      obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
        by_contra hne
        push_neg at hne
        exact hσ (Equiv.ext hne)
      rw [hc1 σ, Finset.prod_eq_zero (mem_univ k) (if_neg hk), zero_smul, mul_zero]
    · intro h1
      exact absurd (mem_univ _) h1
  · simp only
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin (m + 1)))]
    · rw [hc0 1]
      simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul, Equiv.Perm.coe_one,
        id_eq, if_true, ite_self, prod_const_one, one_smul]
      rw [sum_add_distrib, add_comm]
      congr 1
      simp only [Algebra.algebraMap_eq_smul_one, ← sum_smul]
    · intro σ _ hσ
      obtain ⟨k₀, hk₀⟩ : ∃ k, σ k ≠ k := by
        by_contra hne
        push_neg at hne
        exact hσ (Equiv.ext hne)
      rw [hc0 σ]
      have hz : ∀ k, (∏ j, (if j = k then (1 : ℂ) else (if σ j = j then (1 : ℂ) else 0))) = 0 := by
        intro k
        by_cases hk : σ k = k
        · refine Finset.prod_eq_zero (mem_univ k₀) ?_
          have : k₀ ≠ k := fun e => hk₀ (e ▸ hk)
          simp [this, hk₀]
        · refine Finset.prod_eq_zero (mem_univ (σ k)) ?_
          have h2 : σ (σ k) ≠ σ k := fun e => hk (σ.injective e)
          simp [hk, h2]
      simp [hz]
    · intro h1
      exact absurd (mem_univ _) h1
  · unfold Formalism.REAL.qdet Formalism.REAL.qminor
    rw [Finset.sum_congr rfl fun σ _ => by rw [hc σ u]]
    simp_rw [mul_sum, mul_smul_comm]
    rw [Finset.sum_comm]
    simp_rw [← smul_sum]

end GlobalTheory.CapelliNext
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelDimGeomConnectedDescendFieldExtension
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

namespace GlobalTheory.FieldDescentSm

theorem smoothOfRelativeDimension_and_geometricallyConnected_descend : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → ∀ D : ℕ, Nonempty X → SmoothOfRelativeDimension D q → GeometricallyConnected q → SmoothOfRelativeDimension D p ∧ GeometricallyConnected p := by
  intro k E _ _ _ Y X p q π H D hX hD hq
  have hf := GlobalTheory.FieldDescentAb.fpqc_spMap (algebraMap k E)
  have hsq : Smooth q := SmoothOfRelativeDimension.smooth D q
  have hsm : Smooth p :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) H.flip hf hsq
  have hp : GeometricallyConnected p :=
    GlobalTheory.FieldDescentAb.geometricallyConnected_of_isPullback (algebraMap k E) H
  refine ⟨?_, hp⟩
  have hc : ConnectedSpace Y :=
    hp.geometrically_connectedSpace (𝟙 _) (𝟙 Y) p (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨x⟩ := hX
  obtain ⟨D', hD'⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_dim_of_preconnected p (π x)
  have h' : SmoothOfRelativeDimension D' q :=
    (smoothOfRelativeDimension_isStableUnderBaseChange D').of_isPullback H hD'
  rw [ReciprocityTheory.ChartRestriction.G.H1.dim_unique q hD h' x]
  exact hD'

end GlobalTheory.FieldDescentSm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializesOfPointLocalRingLeSeparated
section
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem specializes_of_locRing_le (X : Scheme.{0}) [IsIntegral X] [X.IsSeparated] (x z : X)
    (h : locRing x ≤ locRing z) : z ⤳ x := by
  have hgz : genericPoint X ⤳ z := (genericPoint_spec X).specializes trivial
  have hgx : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  have hinjz : Function.Injective (algebraMap (X.presheaf.stalk z) X.functionField) :=
    IsFractionRing.injective _ _
  let ez : X.presheaf.stalk z ≃+* locRing z := RingEquiv.ofBijective
    (algebraMap (X.presheaf.stalk z) X.functionField).rangeRestrict
    ⟨fun _ _ e => hinjz (congrArg Subtype.val e), RingHom.rangeRestrict_surjective _⟩
  let φ : X.presheaf.stalk x →+* X.presheaf.stalk z :=
    ez.symm.toRingHom.comp
      ((Subring.inclusion h).comp (algebraMap (X.presheaf.stalk x) X.functionField).rangeRestrict)
  have hφ (a : X.presheaf.stalk x) :
      algebraMap (X.presheaf.stalk z) X.functionField (φ a) =
        algebraMap (X.presheaf.stalk x) X.functionField a := by
    have e1 : ez (φ a) = Subring.inclusion h
        ((algebraMap (X.presheaf.stalk x) X.functionField).rangeRestrict a) := by
      exact ez.apply_symm_apply _
    exact congrArg Subtype.val e1
  have key : X.presheaf.stalkSpecializes hgx =
      CommRingCat.ofHom φ ≫ X.presheaf.stalkSpecializes hgz := by
    ext a
    exact (hφ a).symm
  let ι := Spec.map (X.presheaf.stalkSpecializes hgz)
  have hdom : IsDominant ι := by
    rw [isDominant_iff]
    show DenseRange (PrimeSpectrum.comap (X.presheaf.stalkSpecializes hgz).hom)
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot (X.presheaf.stalkSpecializes hgz).hom).1 hinjz]
    exact bot_le
  let g := Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk x
  have hfg : X.fromSpecStalk z = g := by
    refine ext_of_isDominant_of_isSeparated (Limits.terminal.from X)
      (Limits.terminal.hom_ext _ _) ι ?_
    rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgz]
    simp only [g, ι, ← Category.assoc, ← Spec.map_comp, ← key,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgx]
  have hz : z = g (IsLocalRing.closedPoint (X.presheaf.stalk z)) := by
    rw [← hfg, Scheme.fromSpecStalk_closedPoint]
  have hr : g (IsLocalRing.closedPoint (X.presheaf.stalk z)) ∈ Set.range (X.fromSpecStalk x) :=
    ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
  rw [Scheme.range_fromSpecStalk] at hr
  rw [hz]
  exact hr

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalVectorValueUnitaryRankOneGindikinKarpel
section
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

namespace GlobalTheory.GKUnitaryRankOne
variable {L : Type} [Field L]

def transv {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c : L) : GL (Fin n) L :=
  ⟨1 + Matrix.single i j c, 1 - Matrix.single i j c,
    by rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.single_mul_single_of_ne _ _ _ _ hij.symm]; simp,
    by rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, Matrix.single_mul_single_of_ne _ _ _ _ hij.symm]; simp⟩

theorem transv_val {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c : L) :
    ((transv i j hij c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 + Matrix.single i j c := rfl

theorem transv_inv_val {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c : L) :
    (((transv i j hij c)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 - Matrix.single i j c := rfl

theorem transv_mem_GU (σ : L →+* L) {n : ℕ} (i j : Fin n) (hij : i ≠ j) (hr : i.rev = j) (c : L)
    (hc : σ c = -c) : transv i j hij c ∈ GU σ n := by
  rw [GlobalTheory.LGrp.mem_GU_iff]
  intro p r
  have e1 : ∀ x : Fin n, i = x.rev ↔ x = j := fun x => by rw [← hr]; exact ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [h, Fin.rev_rev]⟩
  have e2 : ∀ x : Fin n, j = x.rev ↔ x = i := fun x => by
    rw [← hr]; exact ⟨fun h => Fin.rev_injective (by rw [← h]), fun h => by rw [h]⟩
  rw [transv_inv_val, transv_val]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Fin.rev_inj, e1, e2]
  by_cases h : i = p ∧ j = r
  · obtain ⟨rfl, rfl⟩ := h
    simp [hij, hij.symm, hc, sub_eq_add_neg]
  · have h' : ¬ (r = j ∧ p = i) := fun h' => h ⟨h'.2.symm, h'.1.symm⟩
    rw [if_neg h, if_neg h']
    by_cases hpr : p = r
    · subst hpr; simp
    · simp [hpr, Ne.symm hpr]
end GlobalTheory.GKUnitaryRankOne

namespace GlobalTheory.GKUnitaryRankOne
variable {L : Type} [Field L]

theorem monomial_mul_apply {n : ℕ} {t : Equiv.Perm (Fin n)} {Y : GL (Fin n) L} (hY : IsWeylRep t Y)
    (M : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    ((Y : Matrix (Fin n) (Fin n) L) * M) i j = (Y : Matrix (Fin n) (Fin n) L) i (t⁻¹ i) * M (t⁻¹ i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (t⁻¹ i)]
  · intro l _ hl
    rw [hY i l (fun h => hl (by rw [h]; simp)), zero_mul]
  · simp

variable [Valued L (WithZero (Multiplicative ℤ))]

theorem mem_intL {x : L} (hx : Valued.v x ≤ 1) : x ∈ intL L := hx

theorem transv_mem_GLint {n : ℕ} (i j : Fin n) (hij : i ≠ j) {c : L} (hc : Valued.v c ≤ 1) :
    transv i j hij c ∈ GLint (Fin n) (intL L) := by
  have hc' : c ∈ intL L := mem_intL hc
  refine P.cartan_mem_of_entries (intL L) _ (fun p r => ?_) (fun p r => ?_)
  · rw [transv_val, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    refine add_mem ?_ ?_ <;> split_ifs <;> first | exact one_mem _ | exact zero_mem _ | exact hc'
  · rw [transv_inv_val, Matrix.sub_apply, Matrix.one_apply, Matrix.single_apply]
    refine sub_mem ?_ ?_ <;> split_ifs <;> first | exact one_mem _ | exact zero_mem _ | exact hc'

theorem ordL_neg (x : L) : ordL (-x) = ordL x := by
  simp only [ordL, Valuation.map_neg]

theorem ordL_one' : ordL (1 : L) = 0 :=
  P.fIwasawa_ordL_unit 1 1 (by rw [map_one]) (by rw [map_one]) (mul_one 1)

theorem ordL_inv {x : L} (hx : x ≠ 0) : ordL x⁻¹ = -ordL x := by
  have h := P.fIwasawa_ordL_mul x x⁻¹ hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, ordL_one'] at h
  omega

theorem ordL_monomial_entry {n : ℕ} {t : Equiv.Perm (Fin n)} {Y : GL (Fin n) L} (hY : IsWeylRep t Y)
    (hYK : Y ∈ GLint (Fin n) (intL L)) (i : Fin n) :
    ordL ((Y : Matrix (Fin n) (Fin n) L) i (t⁻¹ i)) = 0 := by
  have h := congrFun (congrFun (Units.mul_inv Y) i) i
  rw [monomial_mul_apply hY, Matrix.one_apply_eq] at h
  exact P.fIwasawa_ordL_unit _ _ (P.cartan_entries_of_mem _ Y hYK _ _)
    (P.cartan_entries_of_mem _ _ (inv_mem hYK) _ _) (by rw [mul_comm]; exact h)

theorem isBorelU_one (σ : L →+* L) (n : ℕ) : IsBorelU (1 : GU σ n) := by
  intro i j h
  simp [Matrix.one_apply, ne_of_gt h]

theorem chiDeltaU_one (σ : L →+* L) (n m q : ℕ) (α : Fin m → ℂ) : chiDeltaU q α (1 : GU σ n) = 1 := by
  unfold chiDeltaU
  refine Finset.prod_eq_one fun i _ => ?_
  split_ifs
  · simp [ordL_one']
  · rfl

end GlobalTheory.GKUnitaryRankOne

namespace GlobalTheory.GKUnitaryRankOne
variable {L : Type} [Field L]

theorem monomial_entry_ne_zero {n : ℕ} {t : Equiv.Perm (Fin n)} {Y : GL (Fin n) L} (hY : IsWeylRep t Y)
    (i : Fin n) : (Y : Matrix (Fin n) (Fin n) L) i (t⁻¹ i) ≠ 0 := by
  intro h0
  have h := congrFun (congrFun (Units.mul_inv Y) i) i
  rw [monomial_mul_apply hY, Matrix.one_apply_eq, h0, zero_mul] at h
  exact zero_ne_one h
end GlobalTheory.GKUnitaryRankOne

namespace GlobalTheory.GKUnitaryRankOne

theorem value_rankOne : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    IsUnramInv ϖ σ q → ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → Even n →
    ∀ (α : Fin (n / 2) → ℂ) (φ : GU σ n → ℂ), IsSphericalU q α φ → φ 1 = 1 →
    ∀ (y : GU σ n), y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ (u : GU σ n), (∀ i j, ¬ (i = lo k ∧ j = (lo k).rev) →
      ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = (1 : Matrix (Fin n) (Fin n) L) i j) →
    φ (y⁻¹ * u) = if Valued.v (((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev) ≤ 1 then 1
      else α k ^ (-ordL (((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev)) *
        (q : ℂ) ^ (ordL (((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev)) := by
  intro L _ _ ϖ σ q _ n k hk hn α φ hφ hφ1 y hy hyw u hu
  have hn2 : n = 2 * k.val + 2 := by obtain ⟨r, hr⟩ := hn; omega
  set a : Fin n := lo k with ha
  set a' : Fin n := (lo k).rev with ha'
  have hav : a.val = k.val := rfl
  have ha'v : a'.val = k.val + 1 := by rw [ha', Fin.val_rev]; simp; omega
  have haa' : a ≠ a' := fun h => by have := congrArg Fin.val h; omega
  have hra : a'.rev = a := by rw [ha', Fin.rev_rev]
  set b := ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a' with hb
  have hU : (u : GL (Fin n) L) = transv a a' haa' b := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [transv_val]
    by_cases h : i = a ∧ j = a'
    · obtain ⟨rfl, rfl⟩ := h
      simp [Matrix.single_apply, haa', hb]
    · rw [hu i j h, Matrix.add_apply, Matrix.single_apply, if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩), add_zero]
  have hσb : σ b = -b := by
    have h := (GlobalTheory.LGrp.mem_GU_iff σ n (u : GL (Fin n) L)).1 u.2 a a'
    rw [hra, ← ha', ← hb, hU, transv_inv_val] at h
    simpa [Matrix.single_apply, haa'] using h.symm
  by_cases hv : Valued.v b ≤ 1
  · rw [if_pos hv]
    have huK : u ∈ KU σ n := by
      rw [← SetLike.mem_coe, GlobalTheory.LFun.IntPtsUnitary.coe_KU]
      show (u : GL (Fin n) L) ∈ GLint (Fin n) (intL L)
      rw [hU]; exact transv_mem_GLint a a' haa' hv
    have h := hφ 1 1 (y⁻¹ * u) (isBorelU_one σ n) (mul_mem (inv_mem hy) huK)
    rw [one_mul, one_mul] at h
    rw [h, chiDeltaU_one, hφ1, one_mul]
  · rw [if_neg hv]
    push_neg at hv
    have hb0 : b ≠ 0 := fun h => by rw [h, map_zero] at hv; exact not_lt_of_ge zero_le' hv
    set c := b⁻¹ with hc
    have hvc : Valued.v c ≤ 1 := ((Valuation.one_lt_val_iff _ hb0).1 hv).le
    have hσc : σ c = -c := by rw [hc, map_inv₀, hσb, inv_neg]
    have hbc : b * c = 1 := mul_inv_cancel₀ hb0
    let κ : GU σ n := ⟨transv a' a haa'.symm c, transv_mem_GU σ a' a haa'.symm hra c hσc⟩
    have hκ : κ ∈ KU σ n := by
      rw [← SetLike.mem_coe, GlobalTheory.LFun.IntPtsUnitary.coe_KU]
      exact transv_mem_GLint a' a haa'.symm hvc
    set Pb : GU σ n := y⁻¹ * u * κ⁻¹ with hPb
    have e : Pb * 1 * κ = y⁻¹ * u := by rw [hPb]; group
    have hyK : (y : GL (Fin n) L) ∈ GLint (Fin n) (intL L) := hy.2
    have hyiw := IsWeylRep.inv hyw
    have hs : simpleU k = Equiv.swap a a' := by unfold simpleU; rw [if_neg hk]
    set M : Matrix (Fin n) (Fin n) L := (1 + Matrix.single a a' b) * (1 - Matrix.single a' a c) with hMdef
    have hM : ∀ l j, M l j = (1 : Matrix (Fin n) (Fin n) L) l j + (if a = l ∧ a' = j then b else 0)
        - (if a' = l ∧ a = j then c else 0) - (if a = l ∧ a = j then 1 else 0) := by
      intro l j
      rw [hMdef, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.single_mul_single_same, hbc]
      simp [Matrix.single_apply]; ring
    have hP : ∀ i j, (((Pb : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
        (((y : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i (Equiv.swap a a' i) *
          M (Equiv.swap a a' i) j := by
      intro i j
      have : (((Pb : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
          (((y : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M := by
        rw [hPb, hMdef, ← transv_val a a' haa' b, ← transv_inv_val a' a haa'.symm, ← hU]
        simp [Matrix.mul_assoc, κ]
      rw [this, monomial_mul_apply hyiw, inv_inv, hs]
    have hunit : ∀ i, ordL ((((y : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i
        (Equiv.swap a a' i)) = 0 := fun i => by
      have := ordL_monomial_entry hyiw (inv_mem hyK) i
      rwa [inv_inv, hs] at this
    have hB : IsBorelU Pb := by
      intro i j hji
      have hj : j.val < i.val := hji
      rw [hP, hM]
      apply mul_eq_zero_of_right
      simp only [Matrix.one_apply, Equiv.swap_apply_def, Fin.ext_iff]
      split_ifs <;> first | omega | ring
    rw [← e, hφ Pb 1 κ hB hκ, hφ1, mul_one]
    have hdiag : ∀ i : Fin n, i ≠ a → i ≠ a' →
        ordL ((((Pb : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) = 0 := by
      intro i h1 h2
      rw [hP, Equiv.swap_apply_of_ne_of_ne h1 h2, hM]
      simp only [Matrix.one_apply_eq, if_neg (fun h : a = i ∧ a' = i => h1 h.1.symm),
        if_neg (fun h : a' = i ∧ a = i => h2 h.1.symm), if_neg (fun h : a = i ∧ a = i => h1 h.1.symm)]
      have := hunit i
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2] at this
      simpa using this
    have hdiag_a : ordL ((((Pb : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a) = -ordL b := by
      rw [hP, Equiv.swap_apply_left, hM]
      simp only [Matrix.one_apply, if_neg haa'.symm, if_neg (fun h : a = a' ∧ a' = a => haa' h.1),
        if_pos (⟨rfl, rfl⟩ : a' = a' ∧ a = a), if_neg (fun h : a = a' ∧ a = a => haa' h.1)]
      have hy0 : (((y : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a' ≠ 0 := by
        have := monomial_entry_ne_zero hyiw a
        rwa [inv_inv, hs, Equiv.swap_apply_left] at this
      have hc0 : c ≠ 0 := inv_ne_zero hb0
      have e2 : ((0 : L) + 0 - if True ∧ True then c else 0) - (if a = a' ∧ True then 1 else 0) = -c := by
        rw [if_pos ⟨trivial, trivial⟩, if_neg (fun h => haa' h.1)]; ring
      rw [e2, P.fIwasawa_ordL_mul _ _ hy0 (neg_ne_zero.2 hc0), ordL_neg, hc, ordL_inv hb0]
      have := hunit a
      rw [Equiv.swap_apply_left] at this
      rw [this, zero_add]
    unfold chiDeltaU
    rw [Finset.prod_eq_single k]
    · rw [dite_eq_left (by omega)]
      show α k ^ ordL ((((Pb : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a) *
          (q : ℂ) ^ (-(ordL ((((Pb : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a)) *
            ((n : ℤ) - 1 - 2 * (k.val : ℤ))) = _
      have e3 : (n : ℤ) - 1 - 2 * (k.val : ℤ) = 1 := by omega
      rw [hdiag_a, e3, neg_neg, mul_one]
    · intro i _ hik
      have hi : i.val < k.val := by
        have : i.val ≠ k.val := fun h => hik (Fin.ext h)
        omega
      rw [dite_eq_left (by omega), hdiag _ (fun h => by have := congrArg Fin.val h; simp at this; omega)
        (fun h => by have := congrArg Fin.val h; simp at this; omega)]
      simp
    · simp

end GlobalTheory.GKUnitaryRankOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjIntegralIffLatticeUnimodularStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedConj_integral_iff_lattice_unimodular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (a : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K) (β : B.Aˣ) (b : Module.Basis (Fin a) K.E B.A) (δ : GLw a w), (∀ i j, ((δ.val * GlobalTheory.Tw.Phi a (w.adicCompletion E))⁻¹)ᵀ i j = e (B.herm β (b i) (b j))) → ∀ q : GLw a w, (q⁻¹ * δ * thL a w q ∈ GlobalTheory.LFun.KGL w (n := a) ↔ ∀ z, z ∈ GlobalTheory.TwLat.lat e b q ↔ ∀ y ∈ GlobalTheory.TwLat.lat e b q, B.herm β y z ∈ (algebraMap K.O K.E).range) := by
  first | exact @GlobalTheory.TwOrbUnimod.twist_integral_iff_unimodular | exact GlobalTheory.TwOrbUnimod.twist_integral_iff_unimodular | (intros; apply GlobalTheory.TwOrbUnimod.twist_integral_iff_unimodular <;> assumption)
end

