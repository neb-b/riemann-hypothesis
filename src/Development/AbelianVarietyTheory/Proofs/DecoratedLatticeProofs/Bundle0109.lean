module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientHeightLowerBoundShortIsotropicVector
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0014

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMulRightInvariantMapWittFlagCoordinatesHaar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf.HaarCoord

theorem measurePreserving_skew_add {A B : Type*} [AddGroup A] [MeasurableSpace A] [MeasurableAdd₂ A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν] [μ.IsAddLeftInvariant] {f : B → A} (hf : Measurable f) :
    MeasurePreserving (fun p : A × B => (f p.2 + p.1, p.2)) (μ.prod ν) (μ.prod ν) := by
  have h : MeasurePreserving (fun p : B × A => (id p.1, f p.1 + p.2)) (ν.prod μ) (ν.prod μ) :=
    (MeasurePreserving.id ν).skew_product (g := fun b a => f b + a)
      ((hf.comp measurable_fst).add measurable_snd) (Filter.Eventually.of_forall fun b => map_add_left_eq_self μ (f b))
  exact Measure.measurePreserving_swap.comp (h.comp Measure.measurePreserving_swap)

theorem isMulRightInvariant_map {X G : Type*} [MeasurableSpace X] [MeasurableSpace G] [Mul G] (P : Measure X) (e : X ≃ᵐ G)
    (h : ∀ q, ∃ T : X → X, MeasurePreserving T P P ∧ ∀ p, e (T p) = e p * e q) : (P.map e).IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  obtain ⟨T, hT, hTe⟩ := h (e.symm g)
  have hg : (fun x : G => x * g) = e ∘ T ∘ e.symm := by
    funext x
    simp only [Function.comp, hTe, e.apply_symm_apply]
  rw [hg]
  have h1 : MeasurePreserving e P (P.map e) := ⟨e.measurable, rfl⟩
  exact (h1.comp (hT.comp (h1.symm e))).map_eq

theorem coord_mul {D : D7} {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (c c' : skewA D ρ) (b b' : Mx D ρ V₀.rank)
    (u u' : GL (Fin ρ) (AE D)) :
    d.nC ((skewConj u.1 c' + cComm V₀ b (u.1 ⬝ b')) + c) * (d.nB (u.1 ⬝ b' + b) * d.levi (u * u')) =
      d.nC c * (d.nB b * d.levi u) * (d.nC c' * (d.nB b' * d.levi u')) := by
  have h1 : d.levi u * (d.nC c' * (d.nB b' * d.levi u')) =
      d.nC (skewConj u.1 c') * (d.nB (u.1 ⬝ b') * d.levi (u * u')) := by
    rw [← mul_assoc, d.levi_mul_nC, mul_assoc, ← mul_assoc (d.levi u), d.levi_mul_nB, mul_assoc, map_mul]
  rw [mul_assoc, mul_assoc, h1, ← mul_assoc (d.nB b), ← d.nC_mul_nB, mul_assoc, ← mul_assoc (d.nB b), d.nB_mul_nB,
    ← d.nC_mul_nB, add_comm _ c, add_comm _ b, d.nC_add, d.nC_add]
  simp only [mul_assoc]

theorem measurableAdd₂_addSubgroup {A : Type*} [AddGroup A] [MeasurableSpace A] [MeasurableAdd₂ A] (H : AddSubgroup A) :
    MeasurableAdd₂ H :=
  ⟨Measurable.subtype_mk ((measurable_subtype_coe.comp measurable_fst).add (measurable_subtype_coe.comp measurable_snd))⟩

theorem measurePreserving_triple {A B U : Type*} [AddGroup A] [MeasurableSpace A] [MeasurableAdd₂ A] [AddGroup B]
    [MeasurableSpace B] [MeasurableAdd₂ B] [Mul U] [MeasurableSpace U] [MeasurableMul U]
    (l : Measure A) (μ : Measure B) (ν : Measure U) [SFinite l] [SFinite μ] [SFinite ν] [l.IsAddLeftInvariant]
    [μ.IsAddLeftInvariant] [ν.IsMulRightInvariant] {f : B × U → A} (hf : Measurable f) {g : U → B} (hg : Measurable g)
    (u' : U) :
    MeasurePreserving (fun p : A × (B × U) => (f p.2 + p.1, (g p.2.2 + p.2.1, p.2.2 * u')))
      (l.prod (μ.prod ν)) (l.prod (μ.prod ν)) := by
  have T1 := measurePreserving_skew_add l (μ.prod ν) hf
  have T2 := (MeasurePreserving.id l).prod (measurePreserving_skew_add μ ν hg)
  have T3 := (MeasurePreserving.id l).prod ((MeasurePreserving.id μ).prod (measurePreserving_mul_right ν u'))
  exact T3.comp (T2.comp T1)

theorem continuous_UX_val (D : D7) (ρ : ℕ) : Continuous fun u : UX D ρ => (u.1.1 : Mx D ρ ρ) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_UX_mul {D : D7} {ρ n : ℕ} (b' : Mx D ρ n) : Continuous fun u : UX D ρ => (u.1.1 ⬝ b' : Mx D ρ n) :=
  (continuous_UX_val D ρ).matrix_mul continuous_const

theorem continuous_skewConj {D : D7} {ρ : ℕ} (c' : skewA D ρ) : Continuous fun a : Mx D ρ ρ => skewConj a c' := by
  have h1 : Continuous fun a : Mx D ρ ρ => (a ⬝ c'.1 : Mx D ρ ρ) := continuous_id.matrix_mul continuous_const
  have h2 : Continuous fun a : Mx D ρ ρ => (a ⬝ c'.1 ⬝ adj a : Mx D ρ ρ) := h1.matrix_mul continuous_adj
  exact Continuous.subtype_mk h2 _

theorem continuous_cComm {D : D7} (V₀ : HSp D) (ρ : ℕ) :
    Continuous fun x : Mx D ρ V₀.rank × Mx D ρ V₀.rank => cComm V₀ x.1 x.2 := by
  have := (lattice_Mx D ρ ρ).1
  have : ContinuousSub (Mx D ρ ρ) := IsTopologicalAddGroup.to_continuousSub
  have hp : Continuous (plus V₀ : Mx D ρ V₀.rank → _) := continuous_const.matrix_mul continuous_adj
  have h1 : Continuous fun x : Mx D ρ V₀.rank × Mx D ρ V₀.rank => (x.2 ⬝ plus V₀ x.1 : Mx D ρ ρ) :=
    continuous_snd.matrix_mul (hp.comp continuous_fst)
  have h2 : Continuous fun x : Mx D ρ V₀.rank × Mx D ρ V₀.rank => (x.1 ⬝ plus V₀ x.2 : Mx D ρ ρ) :=
    continuous_fst.matrix_mul (hp.comp continuous_snd)
  have h3 : Continuous fun x : Mx D ρ V₀.rank × Mx D ρ V₀.rank =>
      (half D • (x.2 ⬝ plus V₀ x.1 - x.1 ⬝ plus V₀ x.2) : Mx D ρ ρ) := (h1.sub h2).const_smul (half D)
  exact Continuous.subtype_mk h3 _

set_option synthInstance.maxHeartbeats 200000 in
theorem continuous_shift {D : D7} (V₀ : HSp D) (ρ : ℕ) (c' : skewA D ρ) (b' : Mx D ρ V₀.rank) :
    Continuous fun y : Mx D ρ V₀.rank × UX D ρ => skewConj y.2.1.1 c' + cComm V₀ y.1 (y.2.1.1 ⬝ b') := by
  have := (lattice_Mx D ρ ρ).1
  have h1 : Continuous fun y : Mx D ρ V₀.rank × UX D ρ => skewConj y.2.1.1 c' :=
    (continuous_skewConj c').comp (f := fun y : Mx D ρ V₀.rank × UX D ρ => y.2.1.1)
      ((continuous_UX_val D ρ).comp continuous_snd)
  have h2 : Continuous fun y : Mx D ρ V₀.rank × UX D ρ => cComm V₀ y.1 (y.2.1.1 ⬝ b') :=
    (continuous_cComm V₀ ρ).comp (f := fun y : Mx D ρ V₀.rank × UX D ρ => (y.1, (y.2.1.1 ⬝ b' : Mx D ρ V₀.rank)))
      (continuous_fst.prodMk ((continuous_UX_mul b').comp continuous_snd))
  exact h1.add h2

set_option synthInstance.maxHeartbeats 200000 in
theorem measurable_shift {D : D7} (V₀ : HSp D) (ρ : ℕ) (c' : skewA D ρ) (b' : Mx D ρ V₀.rank) :
    Measurable fun y : Mx D ρ V₀.rank × UX D ρ => skewConj y.2.1.1 c' + cComm V₀ y.1 (y.2.1.1 ⬝ b') := by
  obtain ⟨b1, b2, b3, b4, -⟩ := lattice_Mx D ρ V₀.rank
  obtain ⟨u1, u2, u3⟩ := GlobalTheory.UnitU.topology D ρ
  have : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  have : BorelSpace (Mx D ρ V₀.rank) := ⟨rfl⟩
  have : BorelSpace (UX D ρ) := ⟨rfl⟩
  have : BorelSpace (skewA D ρ) := Subtype.borelSpace _
  exact (continuous_shift V₀ ρ c' b').measurable


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 400000 in
theorem isMulRightInvariant_map_coord : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (e : skewA D ρ × (Mx D ρ V₀.rank × UX D ρ) ≃ᵐ flagN d), (∀ p, (e p : GA D V) = d.nC p.1 * (d.nB p.2.1 * d.levi p.2.2.1)) → ∀ (lC : Measure (skewA D ρ)), lC.IsAddHaarMeasure → SFinite lC → ((lC.prod (vb.μ.prod vU.ν)).map e).IsMulRightInvariant := by
  intro D V V₀ ρ d vb vU e he lC hC hS
  obtain ⟨a1, a2, a3, a4, -⟩ := lattice_Mx D ρ ρ
  obtain ⟨b1, b2, b3, b4, -⟩ := lattice_Mx D ρ V₀.rank
  obtain ⟨u1, u2, u3⟩ := GlobalTheory.UnitU.topology D ρ
  have : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  have : BorelSpace (Mx D ρ V₀.rank) := ⟨rfl⟩
  have : BorelSpace (UX D ρ) := ⟨rfl⟩
  have := vb.covol.1
  have := vU.unit.1
  have : vU.ν.IsMulRightInvariant := (GlobalTheory.UnitU.isUnitU_exists_unique_rightInvariant D ρ).2.2 _ vU.unit
  have : SFinite vb.μ := inferInstance
  have : SFinite vU.ν := inferInstance
  have : MeasurableAdd₂ (Mx D ρ ρ) := inferInstance
  have : MeasurableAdd₂ (skewA D ρ) := measurableAdd₂_addSubgroup _
  have : MeasurableAdd₂ (Mx D ρ V₀.rank) := inferInstance
  have : MeasurableMul (UX D ρ) := inferInstance
  refine isMulRightInvariant_map _ e ?_
  rintro ⟨c', b', u'⟩
  refine ⟨_, measurePreserving_triple lC vb.μ vU.ν (measurable_shift V₀ ρ c' b') (continuous_UX_mul b').measurable u', ?_⟩
  rintro ⟨c, b, u⟩
  apply Subtype.ext
  rw [Subgroup.coe_mul, he, he, he]
  exact coord_mul d c c' b b' u.1 u'.1

end GlobalTheory.Unf.HaarCoord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceComapUnitarySupported
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
open scoped TensorProduct

namespace GlobalTheory.IwaPlace.SdComap

set_option synthInstance.maxHeartbeats 400000

variable {D : D7}

theorem exists_nat_mul_isIntegral' (e : D.host.E) : ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : D.host.E) * e) := by
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := D.host.E) {e}
  have h := hy e (Finset.mem_singleton_self e)
  have hpos : 0 < y.natAbs := Int.natAbs_pos.2 hy0
  refine ⟨y.natAbs * y.natAbs, Nat.mul_pos hpos hpos, ?_⟩
  have e1 : ((y.natAbs * y.natAbs : ℕ) : D.host.E) * e = (y : D.host.E) * ((y : D.host.E) * e) := by
    have h2 := Int.natAbs_mul_self' y
    rw [← mul_assoc, ← Int.cast_natCast, Nat.cast_mul, h2, Int.cast_mul]
  rw [e1]
  rw [zsmul_eq_mul] at h
  refine IsIntegral.mul ?_ h
  simpa using (isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := y))

theorem mul_mem_intAE' {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem natCast_mem_intAE (n : ℕ) : (n : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D := by
  rw [Algebra.TensorProduct.natCast_def]
  refine AddSubgroup.subset_closure ⟨(n : Af D.host.F), fun v => ?_, 1, ?_⟩
  · rw [map_natCast]; exact natCast_mem _ n
  · simp

theorem exists_natCast_mul_mem_intAE (z : Af D.host.F ⊗[D.host.F] D.host.E) :
    ∃ n : ℕ, 0 < n ∧ (n : Af D.host.F ⊗[D.host.F] D.host.E) * z ∈ intAE D := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, by rw [mul_zero]; exact zero_mem _⟩
  | tmul a e =>
    obtain ⟨n, hn, he⟩ := exists_nat_mul_isIntegral' (D := D) e
    obtain ⟨d, hd, ha⟩ := GlobalTheory.HolDict.ShortVec.exists_denom_adele (F := D.host.F) a
    refine ⟨d * n, Nat.mul_pos hd hn, ?_⟩
    have e1 : ((d * n : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * (a ⊗ₜ[D.host.F] e) =
        ((d : Af D.host.F) * a) ⊗ₜ[D.host.F] ((n : D.host.E) * e) := by
      rw [Nat.cast_mul, Algebra.TensorProduct.natCast_def, Algebra.TensorProduct.natCast_def',
        Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [e1]
    exact AddSubgroup.subset_closure ⟨_, fun v => Subring.mem_iInf.1 ha v, ⟨_, he⟩, rfl⟩
  | add x y hx hy =>
    obtain ⟨n₁, h₁, hx⟩ := hx
    obtain ⟨n₂, h₂, hy⟩ := hy
    refine ⟨n₁ * n₂, Nat.mul_pos h₁ h₂, ?_⟩
    have e1 : ((n₁ * n₂ : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * (x + y) =
        (n₂ : Af D.host.F ⊗[D.host.F] D.host.E) * ((n₁ : Af D.host.F ⊗[D.host.F] D.host.E) * x) +
          (n₁ : Af D.host.F ⊗[D.host.F] D.host.E) * ((n₂ : Af D.host.F ⊗[D.host.F] D.host.E) * y) := by
      push_cast; ring
    rw [e1]
    exact add_mem (mul_mem_intAE' (natCast_mem_intAE n₂) hx) (mul_mem_intAE' (natCast_mem_intAE n₁) hy)

theorem exists_natCast_mul_mem_intAt {P : Pl D → Prop} {a : AE D} (ha : a ∈ idAt D P) :
    ∃ n : ℕ, 0 < n ∧ (n : AE D) * a ∈ intAt D P := by
  obtain ⟨n, hn, h⟩ := exists_natCast_mul_mem_intAE (D := D) (finPart D a)
  refine ⟨n, hn, Ideal.mul_mem_left _ _ ha, ?_⟩
  rw [map_mul, map_natCast]; exact h

theorem intAt_add {P : Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) : a + b ∈ intAt D P :=
  ⟨add_mem ha.1 hb.1, by rw [map_add]; exact add_mem ha.2 hb.2⟩

theorem intAt_mul {P : Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) : a * b ∈ intAt D P :=
  ⟨Ideal.mul_mem_left _ _ hb.1, by rw [map_mul]; exact mul_mem_intAE' ha.2 hb.2⟩

theorem intAt_natCast_mul {P : Pl D → Prop} {a : AE D} (n : ℕ) (ha : a ∈ intAt D P) : (n : AE D) * a ∈ intAt D P :=
  ⟨Ideal.mul_mem_left _ _ ha.1, by rw [map_mul, map_natCast]; exact mul_mem_intAE' (natCast_mem_intAE n) ha.2⟩

theorem intAt_sum {P : Pl D → Prop} {ι : Type} (s : Finset ι) (f : ι → AE D) (h : ∀ i ∈ s, f i ∈ intAt D P) :
    ∑ i ∈ s, f i ∈ intAt D P := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩
  | insert a s has ih =>
    rw [Finset.sum_insert has]
    exact intAt_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem cA_mulVec {n : ℕ} (M : Mx D n n) (y : Fin n → AE D) :
    (fun i => cA D ((M *ᵥ y) i)) = Matrix.vecMul (fun i => cA D (y i)) (adj M) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, adj, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem hermAt_eq (S : HSp D) (x y : Fin S.rank → AE D) :
    hermAt S x y = Matrix.vecMul (fun i => cA D (y i)) (gA S) ⬝ᵥ x := by
  simp only [hermAt, Matrix.vecMul, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem hermAt_mt (S : HSp D) (g : GA D S) (x y : Fin S.rank → AE D) :
    hermAt S (mt S g *ᵥ x) (mt S g *ᵥ y) = hermAt S x y := by
  rw [hermAt_eq, hermAt_eq, cA_mulVec (mt S g) y, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul,
    mt_unitary]

theorem mulVec_eq_add {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (y : Fin n → R) (i : Fin n) :
    (M *ᵥ y) i = y i + ∑ j, (M i j - (1 : Matrix (Fin n) (Fin n) R) i j) * y j := by
  have h : M *ᵥ y = y + (M - 1) *ᵥ y := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  rw [h]; rfl

theorem eq_mulVec_sub {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (y : Fin n → R) (i : Fin n) :
    y i = (M *ᵥ y) i - ∑ j, (M i j - (1 : Matrix (Fin n) (Fin n) R) i j) * y j := by
  rw [mulVec_eq_add, add_sub_cancel_right]

theorem smul_mulVec_apply {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (y : Fin n → R) (c : R)
    (i : Fin n) : (c • (M *ᵥ y)) i = c * y i + ∑ j, (c * (M i j - (1 : Matrix (Fin n) (Fin n) R) i j)) * y j := by
  rw [Pi.smul_apply, smul_eq_mul, mulVec_eq_add, mul_add, Finset.mul_sum]
  simp only [mul_assoc]

theorem mulVec_natCast_smul {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (y : Fin n → R) (m K : ℕ) :
    M *ᵥ (((m * K : ℕ) : R) • y) = (m : R) • ((K : R) • (M *ᵥ y)) := by
  rw [Matrix.mulVec_smul, Nat.cast_mul, mul_smul]

theorem mulVec_mulVec_of_mul_eq_one {R : Type} [CommRing R] {n : ℕ} {M N : Matrix (Fin n) (Fin n) R} (h : M * N = 1)
    (x : Fin n → R) : M *ᵥ (N *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

theorem exists_common_natCast_mul_mem_intAt {P : Pl D → Prop} {ι : Type} [Fintype ι] (a : ι → AE D)
    (ha : ∀ i, a i ∈ idAt D P) : ∃ K : ℕ, 0 < K ∧ ∀ i, (K : AE D) * a i ∈ intAt D P := by
  classical
  choose n hn hx using fun i => exists_natCast_mul_mem_intAt (ha i)
  refine ⟨∏ p, n p, Finset.prod_pos fun p _ => hn p, fun i => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Nat.cast_mul, mul_assoc]
  exact intAt_natCast_mul _ (hx i)

theorem isSDAt_comap_of (S : HSp D) (v : Pl D) (M N : Mx D S.rank S.rank) (hMN : M * N = 1)
    (hM1 : ∀ i j, M i j - (1 : Mx D S.rank S.rank) i j ∈ idAt D (· = v))
    (hherm : ∀ x y, hermAt S (M *ᵥ x) (M *ᵥ y) = hermAt S x y)
    (Λ : AddSubgroup (Fin S.rank → AE D)) (hΛ : IsSDAt S v Λ) :
    IsSDAt S v (Λ.comap (Matrix.mulVecLin M).toAddMonoidHom) := by
  obtain ⟨hsupp, ⟨m, hm, hmint⟩, hsd⟩ := hΛ
  have hmem : ∀ y, y ∈ Λ.comap (Matrix.mulVecLin M).toAddMonoidHom ↔ M *ᵥ y ∈ Λ := fun y => Iff.rfl
  refine ⟨fun y hy i => ?_, ?_, ?_⟩
  · rw [eq_mulVec_sub M y i]
    exact sub_mem (hsupp _ ((hmem y).1 hy) i) (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hM1 i j))
  · obtain ⟨K, hK, hKint⟩ := exists_common_natCast_mul_mem_intAt
      (fun p : Fin S.rank × Fin S.rank => M p.1 p.2 - (1 : Mx D S.rank S.rank) p.1 p.2) fun p => hM1 p.1 p.2
    refine ⟨m * K, Nat.mul_pos hm hK, fun y hy => (hmem _).2 ?_⟩
    rw [mulVec_natCast_smul M y m K]
    refine hmint _ fun i => ?_
    rw [smul_mulVec_apply M y (K : AE D) i]
    exact intAt_add (intAt_natCast_mul K (hy i)) (intAt_sum _ _ fun j _ => intAt_mul (hKint (i, j)) (hy j))
  · intro y hy
    have key := hsd _ (mulVec_mem_idAt M hy)
    refine ⟨fun h x hx => ?_, fun h => (hmem y).2 (key.2 fun x hx => ?_)⟩
    · rw [← hherm y x]; exact key.1 ((hmem y).1 h) _ ((hmem x).1 hx)
    · have hx' : M *ᵥ (N *ᵥ x) = x := mulVec_mulVec_of_mul_eq_one hMN x
      have h3 := h (N *ᵥ x) ((hmem _).2 (by rw [hx']; exact hx))
      rwa [← hherm, hx'] at h3

theorem isSDAt_comap (D : D7) (S : HSp D) (v : Pl D) (g : GA D S) (hg : g ∈ grpAt S (· = v))
    (Λ : AddSubgroup (Fin S.rank → AE D)) (hΛ : IsSDAt S v Λ) :
    IsSDAt S v (Λ.comap (Matrix.mulVecLin (mt S g)).toAddMonoidHom) :=
  isSDAt_comap_of S v (mt S g) (mt S g⁻¹) (mt_mul_inv S g) ((mem_congGrp_iff S (idAt D (· = v)) g).1 hg)
    (hermAt_mt S g) Λ hΛ

end GlobalTheory.IwaPlace.SdComap

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LintegralUnfoldSumTransitiveOrbit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ENNReal Pointwise

namespace GlobalTheory
namespace Unf

theorem lintegral_integral_unfold_transitive : ∀ (H : Type) [Group H] [MeasurableSpace H] [MeasurableMul H] (ν : Measure H) [ν.IsMulLeftInvariant] (Γ : Subgroup H) [Countable Γ] (Y : Type) [Countable Y] [MulAction Γ Y] (y₀ : Y), (∀ y, ∃ γ : Γ, γ • y₀ = y) → ∀ (𝓕 𝓖 : Set H), IsFundamentalDomain Γ 𝓕 ν → IsFundamentalDomain ((MulAction.stabilizer Γ y₀).map Γ.subtype) 𝓖 ν → ∀ Φ : Y → H → ℂ, (∀ y, Measurable (Φ y)) → (∀ (γ : Γ) y h, Φ (γ • y) ((γ : H) * h) = Φ y h) → (∫⁻ h in 𝓖, ‖Φ y₀ h‖ₑ ∂ν = ∫⁻ h in 𝓕, ∑' y, ‖Φ y h‖ₑ ∂ν) ∧ (∫⁻ h in 𝓕, ∑' y, ‖Φ y h‖ₑ ∂ν ≠ ⊤ → ∫ h in 𝓖, Φ y₀ h ∂ν = ∫ h in 𝓕, ∑' y, Φ y h ∂ν) := by
  intro H _ _ _ ν _ Γ _ Y _ _ y₀ htr 𝓕 𝓖 hF hG Φ hΦ hinv
  set S : Subgroup H := (MulAction.stabilizer Γ y₀).map Γ.subtype with hSdef
  haveI : Countable S := by
    have hle : S ≤ Γ := Subgroup.map_subtype_le _
    exact Function.Injective.countable (Subgroup.inclusion_injective hle)
  choose σ hσ using htr
  have hO : ∀ γ : Γ, γ • y₀ ∈ (Set.univ : Set Y) := fun _ => Set.mem_univ _
  have hσ' : ∀ a : (Set.univ : Set Y), σ a • y₀ = a := fun a => hσ a
  let pull (g : H) : Set H := (fun h => g * h) ⁻¹' 𝓕
  have hnull (g : H) : NullMeasurableSet (pull g) ν :=
    hF.nullMeasurableSet.preimage (measurePreserving_mul_left ν g).quasiMeasurePreserving
  have hpull (c : Γ) : pull (c : H) = c⁻¹ • 𝓕 := by
    ext x
    simp [pull, Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def]
  have hG' : IsFundamentalDomain S (⋃ y : Y, pull (σ y : H)) ν := by
    refine ⟨.iUnion (fun y => hnull _), ?_, ?_⟩
    · filter_upwards [hF.ae_covers] with x ⟨γ, hγ⟩
      have hs : (σ (γ • y₀))⁻¹ * γ ∈ MulAction.stabilizer Γ y₀ := by
        rw [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff, hσ]
      refine ⟨⟨Γ.subtype ((σ (γ • y₀))⁻¹ * γ), Subgroup.mem_map_of_mem _ hs⟩,
        Set.mem_iUnion.2 ⟨γ • y₀, ?_⟩⟩
      simpa [pull, Subgroup.smul_def, mul_assoc] using hγ
    · rintro ⟨_, s, hs, rfl⟩ ⟨_, t, ht, rfl⟩ hst
      have hset : ∀ (u : Γ) (hu : u ∈ MulAction.stabilizer Γ y₀) (a : Y),
          (⟨Γ.subtype u, Subgroup.mem_map_of_mem _ hu⟩ : S) • pull (σ a : H) =
            (σ a * u⁻¹)⁻¹ • 𝓕 := by
        intro u hu a
        ext x
        simp [Set.mem_smul_set_iff_inv_smul_mem, pull, Subgroup.smul_def, mul_assoc]
      simp only [Function.onFun, Set.smul_set_iUnion, hset s hs, hset t ht]
      refine AEDisjoint.iUnion_left_iff.2 fun a => AEDisjoint.iUnion_right_iff.2 fun b => ?_
      refine hF.aedisjoint (inv_injective.ne fun h => hst ?_)
      have hab : a = b := by
        have h1 := congrArg (· • y₀) h
        simp only [mul_smul] at h1
        rwa [inv_smul_eq_iff.2 hs.symm, inv_smul_eq_iff.2 ht.symm, hσ, hσ] at h1
      subst hab
      have : s = t := inv_injective (mul_left_cancel h)
      subst this
      rfl
  have hinvS : ∀ (s : S) (h : H), Φ y₀ (s • h) = Φ y₀ h := by
    rintro ⟨s, hs⟩ h
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hs
    have := hinv t y₀ h
    rw [show t • y₀ = y₀ from ht] at this
    simpa [Subgroup.smul_def] using this
  have hfun : ∀ (y : Y) (h : H), Φ y ((σ y : H) * h) = Φ y₀ h := fun y h => by
    have := hinv (σ y) y₀ h
    rwa [hσ y] at this
  have hlint : ∀ y : Y, ∫⁻ h in pull (σ y : H), ‖Φ y₀ h‖ₑ ∂ν
      = ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν := fun y => by
    rw [← (measurePreserving_mul_left ν (σ y : H)).setLIntegral_comp_preimage_emb (measurableEmbedding_mulLeft (σ y : H)) (fun h => ‖Φ y h‖ₑ) 𝓕]
    simp only [hfun, pull]
  have hint : ∀ y : Y, ∫ h in pull (σ y : H), Φ y₀ h ∂ν
      = ∫ h in 𝓕, Φ y h ∂ν := fun y => by
    rw [← (measurePreserving_mul_left ν (σ y : H)).setIntegral_preimage_emb (measurableEmbedding_mulLeft (σ y : H)) (Φ y) 𝓕]
    simp only [hfun, pull]
  have hd : Pairwise (Function.onFun (AEDisjoint ν) fun y : Y =>
      pull (σ y : H)) := by
    intro a b hab
    dsimp only [Function.onFun]
    rw [hpull, hpull]
    refine hF.aedisjoint (inv_injective.ne fun h => hab ?_)
    rw [← hσ a, ← hσ b, h]
  have hL1 : ∫⁻ h in 𝓖, ‖Φ y₀ h‖ₑ ∂ν
      = ∫⁻ h in ⋃ y : Y, pull (σ y : H), ‖Φ y₀ h‖ₑ ∂ν :=
    hG.setLIntegral_eq hG' (fun h => ‖Φ y₀ h‖ₑ) (fun s h => by simp only [hinvS])
  have hL2 : ∫⁻ h in ⋃ y : Y, pull (σ y : H), ‖Φ y₀ h‖ₑ ∂ν
      = ∑' y, ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν := by
    rw [lintegral_iUnion₀ (fun y => hnull _) hd]
    simp only [hlint]
  have hL3 : ∫⁻ h in 𝓕, ∑' y, ‖Φ y h‖ₑ ∂ν = ∑' y, ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν :=
    lintegral_tsum fun y => (hΦ y).enorm.aemeasurable
  have hmain : ∫⁻ h in 𝓖, ‖Φ y₀ h‖ₑ ∂ν = ∫⁻ h in 𝓕, ∑' y, ‖Φ y h‖ₑ ∂ν := by
    rw [hL1, hL2, hL3]
  refine ⟨hmain, fun hfin => ?_⟩
  have hfin' : ∑' y, ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν ≠ ⊤ := by rwa [← hL3]
  have hI : IntegrableOn (Φ y₀) (⋃ y : Y, pull (σ y : H)) ν := by
    refine ⟨(hΦ y₀).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, hL2]
    exact lt_top_iff_ne_top.2 hfin'
  have hI1 : ∫ h in 𝓖, Φ y₀ h ∂ν
      = ∫ h in ⋃ y : Y, pull (σ y : H), Φ y₀ h ∂ν :=
    hG.setIntegral_eq hG' (fun s h => hinvS s h)
  rw [hI1, integral_iUnion_ae (fun y => hnull _) hd hI]
  simp only [hint]
  exact (integral_tsum (fun y => (hΦ y).aestronglyMeasurable) hfin').symm

end Unf
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuasiMeasurePreservingAdelicUnitriangularLeftMul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.LeftUniQmp

theorem qmp_left_uni : ∀ (D : D7) (ρ n : ℕ) (μ : Measure (Mx D ρ n)), μ.IsAddHaarMeasure → ∀ u : UX D ρ, Measure.QuasiMeasurePreserving (fun b : Mx D ρ n => u.1.1 ⬝ b) μ μ := by
  intro D ρ n μ hμ u
  obtain ⟨i1, i2, i3, i4, -⟩ := lattice_Mx D ρ n
  haveI : BorelSpace (Mx D ρ n) := ⟨rfl⟩
  have hc : Continuous (fun b : Mx D ρ n => u.1.1 ⬝ b) := continuous_const.matrix_mul continuous_id
  have hc' : Continuous (fun b : Mx D ρ n => (u.1⁻¹).1 ⬝ b) := continuous_const.matrix_mul continuous_id
  let T : Mx D ρ n ≃+ Mx D ρ n :=
    { toFun := fun b => u.1.1 ⬝ b
      invFun := fun b => (u.1⁻¹).1 ⬝ b
      left_inv := fun b => by
        show (u.1⁻¹).1 ⬝ (u.1.1 ⬝ b) = b
        rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      right_inv := fun b => by
        show u.1.1 ⬝ ((u.1⁻¹).1 ⬝ b) = b
        rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      map_add' := fun a b => Matrix.mul_add _ _ _ }
  haveI : (μ.map T).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μ T hc hc'
  refine ⟨hc.measurable.aemeasurable, ?_⟩
  have e := Measure.isAddLeftInvariant_eq_smul (μ.map T) μ
  show μ.map T ≪ μ
  rw [e]
  exact Measure.smul_absolutelyContinuous

end GlobalTheory.LeftUniQmp
end

