module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0229
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemStabilizerIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0238
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0199
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0219
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0248
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0250
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingEtaleOverIndEtaleDirectedUnion
section
open IsLocalRing

namespace GlobalTheory

theorem localDecomp_indEtale : ∀ (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧ ∀ i, (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i))) → ∀ (U : Subalgebra S T) (B : Type) [CommRing B] [Algebra S B] [Algebra.Etale S B] (Q : Ideal B) [Q.IsPrime], Nonempty (Localization.AtPrime Q ≃ₐ[S] U) → ∃ (μ : Type) (_ : Preorder μ) (_ : IsDirected μ (· ≤ ·)) (_ : Nonempty μ) (V : μ → Subalgebra R T), Monotone V ∧ (∀ m, V m ≤ U.restrictScalars R) ∧ (∀ x ∈ U, ∃ m, x ∈ V m) ∧ (∀ m, ∀ x ∈ V m, ∀ y ∈ U, x * y = 1 → ∃ z ∈ V m, x * z = 1) ∧ ∀ m, (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] V m)) := by
  intro R S T _ _ _ _ _ _ _ hS U B _ _ _ Q _ hf
  obtain ⟨f⟩ := hf
  letI : Algebra R B := ((algebraMap S B).comp (algebraMap R S)).toAlgebra
  haveI : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨ι, _, _, _, C, hCm, hCc, hCe⟩ := _root_.GlobalTheory.EtaleOverDirectedUnion.construct R S B hS
  have hCe' : ∀ i, (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Localization.AtPrime (Q.comap ((C i).val : C i →ₐ[R] B)))) :=
    fun i => hCe i _ inferInstance
  have hann := _root_.GlobalTheory.ann_of_directed_essEtale R B Q ι C hCm hCc hCe'
  obtain ⟨μ, _, _, _, W, hWm, hWc, hWu, hWe⟩ := _root_.GlobalTheory.localDecomp_core R B Q ι C hCm hCc hCe' hann
  let g : Localization.AtPrime Q →ₐ[R] T :=
    { toRingHom := U.val.toRingHom.comp f.toRingHom
      commutes' := fun r => by
        show ((f (algebraMap R _ r) : U) : T) = algebraMap R T r
        rw [IsScalarTower.algebraMap_apply R S (Localization.AtPrime Q), f.commutes,
          IsScalarTower.algebraMap_apply R S T]
        rfl }
  have hg : ∀ x, g x = ((f x : U) : T) := fun _ => rfl
  have hinj : Function.Injective g := fun x y h => f.injective (Subtype.ext (by simpa [hg] using h))
  refine ⟨μ, inferInstance, inferInstance, inferInstance, fun m => (W m).map g, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun m n h => Subalgebra.map_mono (hWm h)
  · rintro m x ⟨w, -, rfl⟩
    exact (f w).2
  · intro x hx
    obtain ⟨m, hm⟩ := hWc (f.symm ⟨x, hx⟩)
    exact ⟨m, f.symm ⟨x, hx⟩, hm, by simp [hg]⟩
  · rintro m x ⟨w, hw, rfl⟩ y hy hxy
    have h1 : f w * ⟨y, hy⟩ = 1 := Subtype.ext (by simpa [hg] using hxy)
    have hu : IsUnit w := by
      have h2 : w * f.symm ⟨y, hy⟩ = 1 := by apply f.injective; simpa using h1
      exact ⟨⟨w, _, h2, by rw [mul_comm]; exact h2⟩, rfl⟩
    obtain ⟨z, hz, hwz⟩ := hWu m w hw hu
    exact ⟨g z, ⟨z, hz, rfl⟩, by show g w * g z = 1; rw [← map_mul, hwz, map_one]⟩
  · intro m
    obtain ⟨A, _, _, _, q, _, ⟨e⟩⟩ := hWe m
    exact ⟨A, inferInstance, inferInstance, inferInstance, q, inferInstance,
      ⟨e.trans (Subalgebra.equivMapOfInjective (W m) g hinj)⟩⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MassFormulaConjugationAction
section
open scoped Classical

namespace GlobalTheory.MassConj

theorem exists_smul_eq_out' {T α : Type} [Group T] [MulAction T α] (p : α) :
    ∃ t : T, t • p = Quotient.out (Quotient.mk'' p : MulAction.orbitRel.Quotient T α) := by
  have h : (Quotient.mk'' (Quotient.out (Quotient.mk'' p : MulAction.orbitRel.Quotient T α)) :
      MulAction.orbitRel.Quotient T α) = Quotient.mk'' p := Quotient.out_eq' _
  exact MulAction.orbitRel_apply.1 (Quotient.eq''.1 h)

theorem finite_support_pairs : ∀ (H : Type) [Group H] (X : Type) [MulAction H X] (f : H → X → ℂ),
    (∀ δ γ : H, ∀ x : X, f (δ * γ * δ⁻¹) (δ • x) = f γ x) →
    Finite (MulAction.orbitRel.Quotient H X) →
    (∀ x : X, (Function.support fun γ : H => f γ x).Finite) →
    {O : MulAction.orbitRel.Quotient H (GlobalTheory.MassConj.ConjPair H X) |
      f (Quotient.out O).elt (Quotient.out O).pt ≠ 0}.Finite := by
  intro H _ X _ f hinv hfo hsupp
  refine (Set.finite_iUnion fun a : MulAction.orbitRel.Quotient H X =>
    (hsupp (Quotient.out a)).image fun γ => (Quotient.mk'' (ConjPair.mk γ (Quotient.out a)) :
      MulAction.orbitRel.Quotient H (ConjPair H X))).subset ?_
  intro O hO
  have hO' : f (Quotient.out O).elt (Quotient.out O).pt ≠ 0 := hO
  obtain ⟨δ, hδ⟩ := exists_smul_eq_out' (T := H) (Quotient.out O).pt
  refine Set.mem_iUnion.2 ⟨Quotient.mk'' (Quotient.out O).pt, δ * (Quotient.out O).elt * δ⁻¹, ?_, ?_⟩
  · show f _ _ ≠ 0
    rw [← hδ, hinv]; exact hO'
  · have e : ConjPair.mk (δ * (Quotient.out O).elt * δ⁻¹)
        (Quotient.out (Quotient.mk'' (Quotient.out O).pt : MulAction.orbitRel.Quotient H X)) =
        δ • Quotient.out O := by
      rw [← hδ]; rfl
    show (Quotient.mk'' (ConjPair.mk _ _) : MulAction.orbitRel.Quotient H (ConjPair H X)) = O
    rw [e]
    exact (Quotient.sound' (MulAction.mem_orbit _ δ)).trans (Quotient.out_eq' O)

theorem finite_support_weighted {H X : Type} [Group H] [MulAction H X] (f : H → X → ℂ)
    (hfin : {O : MulAction.orbitRel.Quotient H (ConjPair H X) |
      f (Quotient.out O).elt (Quotient.out O).pt ≠ 0}.Finite) :
    (Function.support fun O : MulAction.orbitRel.Quotient H (ConjPair H X) =>
      (1 / (Nat.card (MulAction.stabilizer H (Quotient.out O)) : ℂ)) *
        f (Quotient.out O).elt (Quotient.out O).pt).Finite := by
  refine hfin.subset fun O hO => ?_
  exact right_ne_zero_of_mul hO

theorem mass_pt_side : ∀ (H : Type) [Group H] (X : Type) [MulAction H X] (f : H → X → ℂ),
    (∀ δ γ : H, ∀ x : X, f (δ * γ * δ⁻¹) (δ • x) = f γ x) →
    Finite (MulAction.orbitRel.Quotient H X) → (∀ x : X, Finite (MulAction.stabilizer H x)) →
    (∀ x : X, (Function.support fun γ : H => f γ x).Finite) →
    {O : MulAction.orbitRel.Quotient H (GlobalTheory.MassConj.ConjPair H X) |
      f (Quotient.out O).elt (Quotient.out O).pt ≠ 0}.Finite →
    ∑ᶠ a : MulAction.orbitRel.Quotient H X,
        (1 / (Nat.card (MulAction.stabilizer H (Quotient.out a)) : ℂ)) * ∑ᶠ γ : H, f γ (Quotient.out a) =
      ∑ᶠ O : MulAction.orbitRel.Quotient H (GlobalTheory.MassConj.ConjPair H X),
        (1 / (Nat.card (MulAction.stabilizer H (Quotient.out O)) : ℂ)) *
          f (Quotient.out O).elt (Quotient.out O).pt := by
  intro H _ X _ f hinv hfo hstab hsupp hfin
  rw [GlobalTheory.finsum_fiberwise_of_finite_support
    (fun O : MulAction.orbitRel.Quotient H (ConjPair H X) =>
      (Quotient.mk'' (Quotient.out O).pt : MulAction.orbitRel.Quotient H X)) _
    (finite_support_weighted f hfin)]
  refine finsum_congr fun a => ?_
  have h := GlobalTheory.T.finsum_over_conj_pairs_eq_orbit_sum H X f hinv hstab hsupp (Quotient.out a)
  rw [Quotient.out_eq'] at h
  exact h.symm

theorem mass_class_side : ∀ (G : Type) [Group G] (X : Type) [MulAction G X] (Γ : Subgroup G) (Φ : Γ → X → ℂ),
    (∀ δ γ : Γ, ∀ x : X, Φ (δ * γ * δ⁻¹) ((δ : G) • x) = Φ γ x) →
    (∀ x : X, Finite (MulAction.stabilizer Γ x)) →
    {O : MulAction.orbitRel.Quotient Γ (GlobalTheory.MassConj.ConjPair Γ X) |
      Φ (Quotient.out O).elt (Quotient.out O).pt ≠ 0}.Finite →
    ∑ᶠ O : MulAction.orbitRel.Quotient Γ (GlobalTheory.MassConj.ConjPair Γ X),
        (1 / (Nat.card (MulAction.stabilizer Γ (Quotient.out O)) : ℂ)) *
          Φ (Quotient.out O).elt (Quotient.out O).pt =
      ∑ᶠ c : ConjClasses Γ, ∑ᶠ b : MulAction.orbitRel.Quotient
          (Γ ⊓ Subgroup.centralizer {((Quotient.out c : Γ) : G)} : Subgroup G) X,
        (1 / (Nat.card (MulAction.stabilizer (Γ ⊓ Subgroup.centralizer {((Quotient.out c : Γ) : G)} : Subgroup G)
          (Quotient.out b)) : ℂ)) * Φ (Quotient.out c) (Quotient.out b) := by
  intro G _ X _ Γ Φ hinv hstab hfin
  rw [GlobalTheory.finsum_fiberwise_of_finite_support
    (fun O : MulAction.orbitRel.Quotient Γ (ConjPair Γ X) => ConjClasses.mk (Quotient.out O).elt) _
    (finite_support_weighted Φ hfin)]
  refine finsum_congr fun c => ?_
  have h := GlobalTheory.T.finsum_stabilizer_weighted_pair_orbits_conjClass G X Γ Φ hinv (Quotient.out c)
  have e : ConjClasses.mk (Quotient.out c) = c := Quotient.out_eq c
  rw [e] at h
  exact h

theorem mass_formula_conj : ∀ (G : Type) [Group G] (X : Type) [MulAction G X] (Γ : Subgroup G) (Φ : Γ → X → ℂ),
    (∀ δ γ : Γ, ∀ x : X, Φ (δ * γ * δ⁻¹) ((δ : G) • x) = Φ γ x) →
    Finite (MulAction.orbitRel.Quotient Γ X) → (∀ x : X, Finite (MulAction.stabilizer Γ x)) →
    (∀ x : X, (Function.support fun γ : Γ => Φ γ x).Finite) →
    {c : ConjClasses Γ | ∃ x : X, Φ (Quotient.out c) x ≠ 0}.Finite ∧
    ∑ᶠ a : MulAction.orbitRel.Quotient Γ X,
        (1 / (Nat.card (MulAction.stabilizer Γ (Quotient.out a)) : ℂ)) * ∑ᶠ γ : Γ, Φ γ (Quotient.out a) =
      ∑ᶠ c : ConjClasses Γ, ∑ᶠ b : MulAction.orbitRel.Quotient
          (Γ ⊓ Subgroup.centralizer {((Quotient.out c : Γ) : G)} : Subgroup G) X,
        (1 / (Nat.card (MulAction.stabilizer (Γ ⊓ Subgroup.centralizer {((Quotient.out c : Γ) : G)} : Subgroup G)
          (Quotient.out b)) : ℂ)) * Φ (Quotient.out c) (Quotient.out b) := by
  intro G _ X _ Γ Φ hinv hfo hstab hsupp
  have hinv' : ∀ δ γ : Γ, ∀ x : X, Φ (δ * γ * δ⁻¹) (δ • x) = Φ γ x := fun δ γ x => hinv δ γ x
  have hfin := finite_support_pairs Γ X Φ hinv' hfo hsupp
  refine ⟨?_, mass_pt_side Γ X Φ hinv' hfo hstab hsupp hfin |>.trans (mass_class_side G X Γ Φ hinv hstab hfin)⟩
  refine (hfin.image (fun O => ConjClasses.mk (Quotient.out O).elt)).subset ?_
  rintro c ⟨x, hx⟩
  obtain ⟨δ, hδ⟩ := exists_smul_eq_out' (T := Γ) (ConjPair.mk (Quotient.out c) x)
  refine ⟨Quotient.mk'' (ConjPair.mk (Quotient.out c) x), ?_, ?_⟩
  · show Φ _ _ ≠ 0
    rw [← hδ, smul_elt, smul_pt, hinv']
    exact hx
  · show ConjClasses.mk _ = c
    rw [← hδ, smul_elt]
    calc ConjClasses.mk (δ * Quotient.out c * δ⁻¹) = ConjClasses.mk (Quotient.out c) :=
          ConjClasses.mk_eq_mk_iff_isConj.2 (isConj_iff.2 ⟨δ, rfl⟩).symm
      _ = c := Quotient.out_eq c

end GlobalTheory.MassConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMatLatSmulBlockLat
section
open Matrix MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel
open scoped Pointwise

noncomputable section
namespace GlobalTheory.SplitFlip.FourierDepth

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type*} [DecidableEq D]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem setCols_add (P : Finset D) (Y Z : Matrix A D k) (T : Matrix A P k) :
    setCols P (Y + Z) T = setCols P Y T + setCols P Z 0 := by
  ext i j
  by_cases h : j ∈ P <;> simp [setCols, h]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq D] in
theorem pairCols_add [Fintype A] (P : Finset D) (Y Z : Matrix A D k) (T : Matrix A P k) :
    pairCols P (Y + Z) T = pairCols P Y T + pairCols P Z T := by
  simp [pairCols, mul_add, Finset.sum_add_distrib]


omit [DecidableEq D] in
theorem mem_matLat_diagLat {c : D → kˣ} {X : Matrix A D k} :
    X ∈ matLat A (diagLat c) ↔ ∀ i j, valuation k (X i j) ≤ valuation k (c j : k) := Iff.rfl


omit [DecidableEq D] in
theorem mem_matLat_smul_stdLat {c : kˣ} {X : Matrix A D k} :
    X ∈ matLat A (c • stdLat k D) ↔ ∀ i j, valuation k (X i j) ≤ valuation k (c : k) := by
  rw [stdLat, smul_diagLat, mem_matLat_diagLat]
  simp

theorem mem_matLat_blockLat {ϖ : kˣ} {e : ℕ} {P : Finset D} {X : Matrix A D k} :
    X ∈ matLat A (blockLat ϖ e P) ↔
      (∀ i, ∀ j ∈ P, ((ϖ ^ e : kˣ) : k) * X i j ∈ 𝒪[k]) ∧ ∀ i, ∀ j ∉ P, X i j ∈ 𝒪[k] := by
  have h0 : 0 < valuation k ((ϖ ^ e : kˣ) : k) := zero_lt_iff.2 (by simp)
  have h1 : ∀ x : k, ((ϖ ^ e : kˣ) : k) * x ∈ 𝒪[k] ↔
      valuation k x ≤ valuation k (((ϖ ^ e)⁻¹ : kˣ) : k) := fun x => by
    rw [Valuation.mem_integer_iff, map_mul, Units.val_inv_eq_inv_val, map_inv₀, mul_comm, ← le_mul_inv_iff₀ h0, one_mul]
  rw [blockLat, mem_matLat_diagLat]
  simp only [h1]
  constructor
  · intro h
    exact ⟨fun i j hj => by simpa only [blockUnits, if_pos hj] using h i j,
      fun i j hj => by simpa [blockUnits, hj, Valuation.mem_integer_iff] using h i j⟩
  · rintro ⟨h, h'⟩ i j
    by_cases hj : j ∈ P
    · simpa only [blockUnits, if_pos hj] using h i j hj
    · simpa [blockUnits, hj, Valuation.mem_integer_iff] using h' i j hj

theorem mem_matLat_smul_blockLat {ϖ : kˣ} {e : ℕ} {P : Finset D} {X : Matrix A D k} :
    X ∈ matLat A (ϖ ^ e • blockLat ϖ e P) ↔
      (∀ i, ∀ j ∈ P, X i j ∈ 𝒪[k]) ∧ ∀ i, ∀ j ∉ P, valuation k (X i j) ≤ valuation k ((ϖ ^ e : kˣ) : k) := by
  rw [blockLat, smul_diagLat, mem_matLat_diagLat]
  constructor
  · intro h
    exact ⟨fun i j hj => by simpa [blockUnits, hj, Valuation.mem_integer_iff] using h i j,
      fun i j hj => by simpa only [blockUnits, if_neg hj, mul_one] using h i j⟩
  · rintro ⟨h, h'⟩ i j
    by_cases hj : j ∈ P
    · simpa [blockUnits, hj, Valuation.mem_integer_iff] using h i j hj
    · simpa only [blockUnits, if_neg hj, mul_one] using h' i j hj

variable [Fintype A] [DecidableEq A]

theorem hasDepth_fourierSum {ψ : AddChar k Circle} {ϖ : kˣ} (hϖ : IsUnif ϖ) (hψ : HasConductor ψ 1) (e : ℕ)
    (P : Finset D) {Φ : Matrix A D k → ℂ} (hΦ : IsNatDatum ϖ e Φ) :
    HasDepth ϖ e (blockLat ϖ e P) (fourierSum ψ ϖ e P Φ) := by
  classical
  have triv : ∀ y ∈ 𝒪[k], ψ y = 1 := fun y hy => (hψ 1).2 le_rfl y (by simpa using (show valuation k y ≤ 1 from hy))
  have hc : ((ϖ ^ e : kˣ) : k) ∈ 𝒪[k] := by
    rw [Units.val_pow_eq_pow_val]; exact pow_mem hϖ.mem e
  refine ⟨fun Y hY => ?_, fun Y Z hZ => ?_⟩
  · rw [fourierSum_apply]
    split_ifs with h
    · rw [Finset.sum_eq_zero, mul_zero]
      intro T _
      rw [hΦ.1, zero_mul]
      intro H
      refine hY (mem_matLat_blockLat.2 ⟨h, fun i j hj => ?_⟩)
      simpa [setCols, hj] using mem_matLat_stdLat.1 H i j
    · rfl
  · obtain ⟨h1, h2⟩ := mem_matLat_smul_blockLat.1 hZ
    rw [fourierSum_apply, fourierSum_apply]
    refine if_congr (forall_congr' fun i => forall₂_congr fun j hj => ?_) ?_ rfl
    · rw [Matrix.add_apply, mul_add, add_mem_cancel_right (mul_mem hc (h1 i j hj))]
    · congr 1
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [setCols_add, pairCols_add, hΦ.2, AddChar.map_add_eq_mul, triv (pairCols P Z _), mul_one]
      · exact Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => mul_mem (liftRes_mem T i j) (h1 i j j.2)
      · refine mem_matLat_smul_stdLat.2 fun i j => ?_
        by_cases hj : j ∈ P
        · simp [setCols, hj]
        · simpa only [setCols, of_apply, dif_neg hj] using h2 i j hj

theorem isNatDatum_invFourierSum {ψ : AddChar k Circle} {ϖ : kˣ} (hϖ : IsUnif ϖ) (hψ : HasConductor ψ 1) (e : ℕ)
    (P : Finset D) {Ψ : Matrix A D k → ℂ} (hΨ : HasDepth ϖ e (blockLat ϖ e P) Ψ) :
    IsNatDatum ϖ e (invFourierSum ψ ϖ e P Ψ) := by
  classical
  have triv : ∀ y ∈ 𝒪[k], ψ y = 1 := fun y hy => (hψ 1).2 le_rfl y (by simpa using (show valuation k y ≤ 1 from hy))
  have hc : ((ϖ ^ e : kˣ) : k) ∈ 𝒪[k] := by
    rw [Units.val_pow_eq_pow_val]; exact pow_mem hϖ.mem e
  have h0 : 0 < valuation k ((ϖ ^ e : kˣ) : k) := zero_lt_iff.2 (by simp)
  refine ⟨fun Y hY => ?_, fun Y Z hZ => ?_⟩
  · rw [invFourierSum_apply]
    split_ifs with h
    · refine Finset.sum_eq_zero fun S _ => ?_
      rw [hΨ.1, zero_mul]
      intro H
      refine hY (mem_matLat_stdLat.2 fun i j => ?_)
      by_cases hj : j ∈ P
      · exact h i j hj
      · simpa only [setCols, of_apply, dif_neg hj] using (mem_matLat_blockLat (ϖ := ϖ) (e := e) (P := P) |>.1 H).2 i j hj
    · rfl
  · have h1 := mem_matLat_smul_stdLat.1 hZ
    rw [invFourierSum_apply, invFourierSum_apply]
    refine if_congr (forall_congr' fun i => forall₂_congr fun j _ => ?_) ?_ rfl
    · rw [Matrix.add_apply, add_mem_cancel_right (show Z i j ∈ 𝒪[k] from (Valuation.mem_integer_iff _ _).2
        ((h1 i j).trans ((Valuation.mem_integer_iff _ _).1 hc)))]
    · refine Finset.sum_congr rfl fun S _ => ?_
      rw [setCols_add, pairCols_add, hΨ.2, neg_add, AddChar.map_add_eq_mul, triv (-pairCols P Z _), mul_one]
      · refine neg_mem (Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => ?_)
        have h2 : (((ϖ ^ e)⁻¹ : kˣ) : k) * Z i j ∈ 𝒪[k] := by
          rw [Valuation.mem_integer_iff, map_mul, Units.val_inv_eq_inv_val, map_inv₀, inv_mul_le_iff₀ h0, mul_one]
          exact h1 i j
        convert mul_mem (liftRes_mem S i j) h2 using 1
        simp only [Matrix.smul_apply, Units.smul_def, smul_eq_mul]
        ring
      · refine mem_matLat_smul_blockLat.2 ⟨fun i j hj => ?_, fun i j hj => ?_⟩
        · simp [setCols, hj]
        · simpa only [setCols, of_apply, dif_neg hj] using h1 i j

end GlobalTheory.SplitFlip.FourierDepth

theorem GlobalTheory.SplitFlip.FourierDepth.fourier_exchange (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ) (P : Finset D) (hϖ : IsUnif ϖ) (hψ : HasConductor ψ 1) :
    (∀ Φ : Matrix A D k → ℂ, IsNatDatum ϖ e Φ → HasDepth ϖ e (blockLat ϖ e P) (fourierSum ψ ϖ e P Φ)) ∧
      ∀ Ψ : Matrix A D k → ℂ, HasDepth ϖ e (blockLat ϖ e P) Ψ → IsNatDatum ϖ e (invFourierSum ψ ϖ e P Ψ) :=
  ⟨fun _ h => hasDepth_fourierSum hϖ hψ e P h, fun _ h => isNatDatum_invFourierSum hϖ hψ e P h⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModDepthGETwoQuotientPowFreeOverRegularLocalRing
section
open IsLocalRing

namespace GlobalTheory


open Pointwise in
theorem modDepthGE_two_quotient_pow_of_free_of_isRegularLocalRing :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R], 3 ≤ ringKrullDim R → ∀ f ∈ maximalIdeal R,
      f ≠ 0 → ∀ (B : Type) [CommRing B] [Algebra R B] [Module.Finite R B] [Module.Free R B]
      [Nontrivial B] (k : ℕ), 1 ≤ k →
      ReciprocityTheory.CA.ModDepthGE R (B ⧸ (Ideal.span {f}).map (algebraMap R B) ^ k) 2 := by
  intro R _ _ hd f hf hf0 B _ _ _ _ _ k hk
  haveI : IsDomain R := GlobalTheory.isDomain_of_isRegularLocalRing R
  have h3 : ReciprocityTheory.CA.ModDepthGE R B 3 :=
    GlobalTheory.modDepthGE_three_of_free_of_isRegularLocalRing R hd B
  have hfk0 : f ^ k ≠ 0 := pow_ne_zero k hf0
  have hfkm : f ^ k ∈ maximalIdeal R := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
    rw [pow_succ]
    exact Ideal.mul_mem_left _ _ hf
  have hreg : IsSMulRegular B (f ^ k) := smul_right_injective B hfk0
  have h2 : ReciprocityTheory.CA.ModDepthGE R (QuotSMulTop (f ^ k) B) 2 :=
    ReciprocityTheory.CA.ModDepthGE.quotSMulTop hfkm hreg h3
  have hpow : (Ideal.span {f}).map (algebraMap R B) ^ k =
      (Ideal.span {f ^ k}).map (algebraMap R B) := by
    rw [← Ideal.map_pow, Ideal.span_singleton_pow]
  have heq : ((f ^ k) • (⊤ : Submodule R B)) =
      ((Ideal.span {f}).map (algebraMap R B) ^ k).restrictScalars R := by
    rw [hpow]
    ext x
    simp [Submodule.mem_smul_pointwise_iff_exists, Ideal.map_span, Ideal.mem_span_singleton',
      Algebra.smul_def, mul_comm]
  let e : QuotSMulTop (f ^ k) B ≃ₗ[R] (B ⧸ (Ideal.span {f}).map (algebraMap R B) ^ k) :=
    (Submodule.quotEquivOfEq _ _ heq).trans
      (Submodule.Quotient.restrictScalarsEquiv R ((Ideal.span {f}).map (algebraMap R B) ^ k))
  exact (ReciprocityTheory.CA.modDepthGE_congr e 2).mp h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuleFreeOfRegularOfFreeQuotientLocal
section
open IsLocalRing

namespace GlobalTheory.AnnRegSeq

theorem free_of_free_quotient_map (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing A] [Algebra R A] [Module.Finite R A] (f : R) (hf : f ∈ maximalIdeal R)
    (reg : IsSMulRegular A f)
    (hfree : Module.Free (R ⧸ Ideal.span {f}) (A ⧸ (Ideal.span {f}).map (algebraMap R A))) :
    Module.Free R A := by
  set I : Ideal R := Ideal.span {f}
  have hsub : I • (⊤ : Submodule R A) = (I.map (algebraMap R A)).restrictScalars R :=
    Ideal.smul_top_eq_map I
  let e0 : (A ⧸ I • (⊤ : Submodule R A)) ≃ₗ[R] (A ⧸ I.map (algebraMap R A)) :=
    (Submodule.quotEquivOfEq _ _ hsub).trans
      (Submodule.Quotient.restrictScalarsEquiv R (I.map (algebraMap R A)))
  let e : (A ⧸ I • (⊤ : Submodule R A)) ≃ₗ[R ⧸ I] (A ⧸ I.map (algebraMap R A)) :=
    { e0.toAddEquiv with
      map_smul' := by
        intro c x
        obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        show e0 (Ideal.Quotient.mk I c • Submodule.Quotient.mk x) = Ideal.Quotient.mk I c • e0 (Submodule.Quotient.mk x)
        rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul, algebraMap_smul, map_smul] }
  haveI := hfree
  haveI : Module.Free (R ⧸ I) (A ⧸ I • (⊤ : Submodule R A)) := Module.Free.of_equiv e.symm
  exact free_of_free_quotient hf reg

end GlobalTheory.AnnRegSeq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLinearEquivOfPiFinPowFinite
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.PowCancel

def linMapPiEquiv (R : Type) [Ring R] (X M : Type) [AddCommGroup X] [Module R X]
    [AddCommGroup M] [Module R M] (l : ℕ) :
    (X →ₗ[R] (Fin l → M)) ≃ (Fin l → (X →ₗ[R] M)) where
  toFun f i := (LinearMap.proj i).comp f
  invFun g := LinearMap.pi g
  left_inv f := by ext x i; rfl
  right_inv g := by funext i; ext x; rfl

theorem card_linMap_pow (R : Type) [Ring R] (X M : Type) [AddCommGroup X] [Module R X]
    [AddCommGroup M] [Module R M] (l : ℕ) :
    Nat.card (X →ₗ[R] (Fin l → M)) = Nat.card (X →ₗ[R] M) ^ l := by
  rw [Nat.card_congr (linMapPiEquiv R X M l), Nat.card_fun, Nat.card_fin]

theorem cancel_pow : ∀ (R : Type) [Ring R] (M N : Type) [AddCommGroup M] [Module R M] [Finite M]
    [AddCommGroup N] [Module R N] [Finite N] (l : ℕ), 0 < l →
    Nonempty ((Fin l → M) ≃ₗ[R] (Fin l → N)) → Nonempty (M ≃ₗ[R] N) := by
  intro R _ M N _ _ _ _ _ _ l hl ⟨e⟩
  refine GlobalTheory.T.nonempty_linearEquiv_of_card_hom_eq R M N ?_
  intro X _ _ _
  have h1 : Nat.card (X →ₗ[R] (Fin l → M)) = Nat.card (X →ₗ[R] (Fin l → N)) :=
    Nat.card_congr
      { toFun := fun f => e.toLinearMap.comp f
        invFun := fun g => e.symm.toLinearMap.comp g
        left_inv := fun f => by ext x; simp
        right_inv := fun g => by ext x; simp }
  rw [card_linMap_pow, card_linMap_pow] at h1
  exact Nat.pow_left_injective hl.ne' h1

end GlobalTheory.PowCancel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCoefficientIdealFamilyEqTopOfDisjointStatement
section
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normCoefficientIdealFamily_eq_top_of_disjoint : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsFinite π] [IsIntegral Y]
    (hK : IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)))
    (hfd : letI := GlobalTheory.NormSheafDescent.fieldK π hK; letI := GlobalTheory.NormSheafDescent.algKL π
      FiniteDimensional (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) Y.functionField)
    (I : Y.IdealSheafData) (U : Z.affineOpens), (∀ y ∈ I.support, π y ∉ (U : Set Z)) →
    GlobalTheory.NormSheafDescent.famIdeal π hK hfd I U = ⊤ := by
  first | exact @GlobalTheory.NormSheafDescent.famIdeal_eq_top_of_disjoint | exact GlobalTheory.NormSheafDescent.famIdeal_eq_top_of_disjoint | (intros; apply GlobalTheory.NormSheafDescent.famIdeal_eq_top_of_disjoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthogonalSymplecticFixesSiegelPointIStatement
section
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonal_symplectic_fixes_siegel_point_i : ∀ (l : Type) [Fintype l] [DecidableEq l] (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ), (∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)) → (∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)) → s ∈ Matrix.symplecticGroup l ℝ → sᵀ * s = 1 → P.det ≠ 0 → GlobalTheory.Published.Metaplectic.holPart s = P ∧ ∀ x : l → ℝ, cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (-(Q * P⁻¹)) *ᵥ fun i => (x i : ℂ))) = cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.holPart_eq_and_gaussian_of_orthogonal_symplectic | exact GlobalTheory.holPart_eq_and_gaussian_of_orthogonal_symplectic | (intros; apply GlobalTheory.holPart_eq_and_gaussian_of_orthogonal_symplectic <;> assumption)
end

