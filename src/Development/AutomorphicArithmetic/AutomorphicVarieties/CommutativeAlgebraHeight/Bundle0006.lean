module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0002
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDetOfRep
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.d_toDet_ofRep :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G], (∀ ρ : G →* Matrix (Fin n) (Fin n) A, (GDet.ofRep ρ).toDet = Det.ofRep (Fintype.card_fin n) (GDet.repAlg ρ A)) ∧ ∀ (D : GDet n A G) (H : Type) [Group H] (φ : H →* G), (D.comap φ).toDet = D.toDet.pull (MonoidAlgebra.mapDomainAlgHom A A φ) := by
  intro n A G _ _
  refine ⟨fun ρ => Det.ext' fun S _ _ x => ?_, fun D H _ φ => Det.ext' fun S _ _ x => ?_⟩
  · change (GDet.repAlg ρ S (ofT A G S x)).det = (Det.repS (GDet.repAlg ρ A) S x).det
    congr 1
    induction x with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul s y =>
      rw [ofT_tmul, Det.repS_tmul, map_smul]
      congr 1
      induction y using MonoidAlgebra.induction_linear with
      | zero => ext i j; simp
      | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _)]; ext i j; simp
      | single g r => ext i j; simp [GDet.repAlg]
  · change D.D S (MonoidAlgebra.mapDomainRingHom S φ (ofT A H S x)) =
      D.D S (ofT A G S (Algebra.TensorProduct.map (AlgHom.id S S) (MonoidAlgebra.mapDomainAlgHom A A φ) x))
    congr 1
    induction x with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul s y =>
      induction y using MonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [tmul_add, map_add (f := _), ha, hb]
      | single g r => simp [ofT_tmul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
section
noncomputable section

open IsLocalRing TensorProduct Polynomial UpperTheory.V.W UpperTheory.V.Alg

namespace UpperTheory.V.CA

def Z1 {G k : Type} [Group G] [TopologicalSpace G] [Field k] (χ ψ : G →* kˣ) : Submodule k (G → k) where
  carrier := {a | IsLocallyConstant a ∧ ∀ g h, a (g * h) = χ g * a h + a g * ψ h}
  add_mem' {a b} ha hb := ⟨ha.1.add hb.1, fun g h => by simp only [Pi.add_apply, ha.2, hb.2]; ring⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, fun g h => by simp⟩
  smul_mem' c a ha := ⟨ha.1.comp fun x => c * x, fun g h => by simp only [Pi.smul_apply, smul_eq_mul, ha.2]; ring⟩

structure MultFree {n : ℕ} {G k : Type} [Group G] [TopologicalSpace G] [Field k] (χ : Fin n → G →* kˣ) (h : ℕ) :
    Prop where
  isOpen : ∀ i, IsOpen ((χ i).ker : Set G)
  inj : Function.Injective χ
  fin : ∀ i j, i ≠ j → Module.Finite k (Z1 (χ i) (χ j)) ∧ Module.finrank k (Z1 (χ i) (χ j)) ≤ h

def finBound (n h : ℕ) : ℕ := n + ∑ p ∈ Finset.range n, (n ^ 2 * h) ^ p

structure IsGMA {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (e : Fin n → E) : Prop where
  ch : D.IsCH
  idem : CompleteOrthogonalIdempotents e
  rank : ∀ i, D.D A[X] (1 + X ⊗ₜ e i) = 1 + X

structure IsDef (O : Type) [CommRing O] [IsLocalRing O] {n : ℕ} {G : Type} [Group G] [TopologicalSpace G]
    (Dbar : GDet n (ResidueField O) G) {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (D : GDet n R G) : Prop where
  cont : D.IsCont (maximalIdeal R)
  red : D.map (res O R : R →+* ResidueField O) = Dbar

structure IsUnivDet (O : Type) [CommRing O] [IsLocalRing O] {n : ℕ} {G : Type} [Group G] [TopologicalSpace G]
    (Dbar : GDet n (ResidueField O) G) {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (D : GDet n R G) : Prop where
  isDef : IsDef O Dbar D
  univ : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (D' : GDet n R' G), IsDef O Dbar D' →
    ∃! f : R →ₐ[O] R', D.map (f : R →+* R') = D'

end UpperTheory.V.CA
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GDimcpl
section
open IsLocalRing

theorem UpperTheory.V.CA.g_dimcpl :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
      ringKrullDim (AdicCompletion (maximalIdeal R) R) = ringKrullDim R := by
  intro R _ _ _
  haveI := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion R (maximalIdeal R)
  have hm := AdicCompletion.maximalIdeal_eq_map (R := R)
  haveI : (maximalIdeal (AdicCompletion (maximalIdeal R) R)).LiesOver (maximalIdeal R) :=
    ⟨(IsLocalRing.maximalIdeal.isMaximal R).eq_of_le Ideal.IsPrime.ne_top'
      (Ideal.map_le_iff_le_comap.mp hm.ge)⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal R)
    (maximalIdeal (AdicCompletion (maximalIdeal R) R))
  rw [← hm, Ideal.map_quotient_self, Ideal.height_bot, add_zero] at h
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.InjDim
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

theorem UpperTheory.V.CA.inj_dim :
    ∀ (A B : Type) [CommRing A] [IsDomain A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B] (d : ℕ), ringKrullDim A = d → ringKrullDim B = d → Function.Injective (algebraMap A B) := by
  intro A B _ _ _ _ _ d hA hB
  by_contra hni
  obtain ⟨r, hr, hr0⟩ : ∃ r : A, algebraMap A B r = 0 ∧ r ≠ 0 := by
    rw [injective_iff_map_eq_zero] at hni
    push_neg at hni
    exact hni
  have hrz : r ∈ nonZeroDivisors A := mem_nonZeroDivisors_of_ne_zero hr0
  let g : (A ⧸ Ideal.span {r}) →+* B := Ideal.Quotient.lift (Ideal.span {r}) (algebraMap A B) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, hr, mul_zero])
  letI : Algebra (A ⧸ Ideal.span {r}) B := g.toAlgebra
  haveI : Algebra.IsIntegral (A ⧸ Ideal.span {r}) B := by
    refine ⟨fun b => ?_⟩
    obtain ⟨p, hp, hpb⟩ := Algebra.IsIntegral.isIntegral (R := A) b
    refine ⟨p.map (Ideal.Quotient.mk _), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map, RingHom.algebraMap_toAlgebra, Ideal.Quotient.lift_comp_mk]
    exact hpb
  have h1 : ringKrullDim B ≤ ringKrullDim (A ⧸ Ideal.span {r}) :=
    Order.krullDim_le_of_strictMono
      (fun P => (⟨Ideal.comap (algebraMap (A ⧸ Ideal.span {r}) B) P.asIdeal, inferInstance⟩ :
        PrimeSpectrum _))
      (fun P Q h => Ideal.IsIntegral.comap_lt_comap h)
  have h2 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hrz
  rw [hA] at h2
  rw [hB] at h1
  have h3 : ((d : WithBot ℕ∞) + 1) ≤ d := le_trans (add_le_add_left h1 1) h2
  norm_cast at h3
  omega
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.UnopMemCH
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

section SlopeTestRemainingChoices

variable {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E]

private theorem unopS_tmul (S : Type) [CommRing S] [Algebra A S] (s : S) (a : Eᵐᵒᵖ) :
    Det.unopS A E S (s ⊗ₜ a) = s ⊗ₜ a.unop := by
  simp [Det.unopS]

private theorem unopS_surj (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] E) :
    ∃ z, Det.unopS A E S z = y := by
  induction y with
  | tmul s a => exact ⟨s ⊗ₜ MulOpposite.op a, unopS_tmul S s _⟩
  | add a b ha hb =>
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    exact ⟨a' + b', map_add _ _ _⟩

private theorem op_D (D : Det n A E) (S : Type) [CommRing S] [Algebra A S] (x : S ⊗[A] Eᵐᵒᵖ) :
    D.op.D S x = D.D S (Det.unopS A E S x) := rfl

private theorem unopS_map (S T : Type) [CommRing S] [Algebra A S] [CommRing T] [Algebra A T] (φ : S →ₐ[A] T)
    (x : S ⊗[A] Eᵐᵒᵖ) :
    Det.unopS A E T (Algebra.TensorProduct.map φ (AlgHom.id A _) x) =
      Algebra.TensorProduct.map φ (AlgHom.id A E) (Det.unopS A E S x) := by
  induction x with
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul s a => simp [Det.unopS]

private theorem op_chiS (D : Det n A E) (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] Eᵐᵒᵖ) :
    D.op.chiS S y = D.chiS S (Det.unopS A E S y) := by
  unfold Det.chiS
  rw [op_D, map_sub, unopS_map, unopS_tmul, MulOpposite.unop_one]

private theorem unopS_pow (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] Eᵐᵒᵖ) (k : ℕ) :
    Det.unopS A E S (y ^ k) = Det.unopS A E S y ^ k := by
  induction k with
  | zero => simp [Det.unopS, Algebra.TensorProduct.one_def]
  | succ k ih => rw [pow_succ, Det.unopS_mul, ih, pow_succ']

private theorem unopS_aeval (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] Eᵐᵒᵖ) (p : Polynomial S) :
    Det.unopS A E S (Polynomial.aeval y p) = Polynomial.aeval (Det.unopS A E S y) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | monomial k s =>
    rw [aeval_monomial, aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def, map_smul, unopS_pow]

private theorem unopS_gen {k : ℕ} (x : Fin k → Eᵐᵒᵖ) :
    Det.unopS A E _ (Det.gen (A := A) x) = Det.gen (A := A) fun a => (x a).unop := by
  unfold Det.gen
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun a _ => unopS_tmul _ _ _

private theorem lid_unopS (S : Type) [CommRing S] [Algebra A S] (f : S →ₗ[A] A) (y : S ⊗[A] Eᵐᵒᵖ) :
    (TensorProduct.lid A Eᵐᵒᵖ (f.rTensor Eᵐᵒᵖ y)).unop =
      TensorProduct.lid A E (f.rTensor E (Det.unopS A E S y)) := by
  induction y with
  | add a b ha hb => simp only [map_add (f := _), MulOpposite.unop_add, ha, hb]
  | tmul s a => simp [unopS_tmul]

private theorem op_chElt (D : Det n A E) {k : ℕ} (x : Fin k → Eᵐᵒᵖ) (α : Fin k →₀ ℕ) :
    (D.op.chElt x α).unop = D.chElt (fun a => (x a).unop) α := by
  unfold Det.chElt
  rw [lid_unopS, unopS_aeval, op_chiS, unopS_gen]

private theorem unop_mem_CH (D : Det n A E) {x : Eᵐᵒᵖ} (h : x ∈ D.op.CH) : x.unop ∈ D.CH := by
  unfold Det.CH at h
  induction h using TwoSidedIdeal.span_induction with
  | mem x hx =>
    obtain ⟨k, y, α, rfl⟩ := hx
    exact TwoSidedIdeal.subset_span ⟨k, _, α, op_chElt D y α⟩
  | zero => exact D.CH.zero_mem
  | add x y _ _ hx hy => exact D.CH.add_mem hx hy
  | neg x _ hx => exact D.CH.neg_mem hx
  | left_absorb a x _ hx => exact D.CH.mul_mem_right _ _ hx
  | right_absorb b x _ hx => exact D.CH.mul_mem_left _ _ hx

private theorem op_mem_CH (D : Det n A E) {x : E} (h : x ∈ D.CH) : MulOpposite.op x ∈ D.op.CH := by
  unfold Det.CH at h
  induction h using TwoSidedIdeal.span_induction with
  | mem x hx =>
    obtain ⟨k, y, α, rfl⟩ := hx
    exact TwoSidedIdeal.subset_span ⟨k, fun a => MulOpposite.op (y a), α,
      (congrArg MulOpposite.op (op_chElt D (fun a => MulOpposite.op (y a)) α)).symm⟩
  | zero => exact D.op.CH.zero_mem
  | add x y _ _ hx hy => exact D.op.CH.add_mem hx hy
  | neg x _ hx => exact D.op.CH.neg_mem hx
  | left_absorb a x _ hx => exact D.op.CH.mul_mem_right _ _ hx
  | right_absorb b x _ hx => exact D.op.CH.mul_mem_left _ _ hx

end SlopeTestRemainingChoices

theorem UpperTheory.V.CA.d_op :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E), (∀ x, D.op.chi (MulOpposite.op x) = D.chi x) ∧ (∀ x, MulOpposite.op x ∈ D.op.ker ↔ x ∈ D.ker) ∧ ∀ x, MulOpposite.op x ∈ D.op.CH ↔ x ∈ D.CH := by
  intro n A E _ _ _ D
  refine ⟨fun x => ?_, fun x => ?_, fun x => ⟨fun h => unop_mem_CH D h, op_mem_CH D⟩⟩
  · unfold Det.chi
    rw [op_D, map_sub, unopS_tmul, unopS_tmul, MulOpposite.unop_one, MulOpposite.unop_op]
  · rw [Det.mem_ker, Det.mem_ker]
    constructor
    · intro h S _ _ y u v
      obtain ⟨y, rfl⟩ := unopS_surj S y
      obtain ⟨u, rfl⟩ := unopS_surj S u
      obtain ⟨v, rfl⟩ := unopS_surj S v
      have := h S y v u
      rw [op_D, op_D, map_add (f := _), Det.unopS_mul, Det.unopS_mul, unopS_tmul, MulOpposite.unop_op, ← mul_assoc] at this
      exact this
    · intro h S _ _ y u v
      rw [op_D, op_D, map_add (f := _), Det.unopS_mul, Det.unopS_mul, unopS_tmul, MulOpposite.unop_op, ← mul_assoc]
      exact h S _ _ _
end

