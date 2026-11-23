module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbhyankarResidueFieldIsSeparable
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BicharacterFourierTransformTwiceEqPosSmulReflect
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0131
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import ReciprocityTheory.SemistableReduction.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0290

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbhyankarResidueFieldIsSeparableStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abhyankar_residueField_isSeparable_alt : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D],
    Nonempty (D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) → Irreducible π → IsUnit (e : S) →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → P.ramificationIdx S ∣ e) →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → ∀ [P.LiesOver (maximalIdeal S)],
      Algebra.IsSeparable (S ⧸ maximalIdeal S) (integralClosure S L ⧸ P)) →
    ∀ [IsDomain D] [IsDiscreteValuationRing D] (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsMaximal],
    ∀ [Q.LiesOver (maximalIdeal D)],
    Algebra.IsSeparable (D ⧸ maximalIdeal D) (integralClosure D (TensorProduct S D L) ⧸ Q) := by
  first | (exact @GlobalTheory.abhyankar_residueField_isSeparable) | (exact GlobalTheory.abhyankar_residueField_isSeparable) | (intros; apply GlobalTheory.abhyankar_residueField_isSeparable  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentedExactIff
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.AugExact

theorem augmented_exact_iff (C : Type 2) [Category.{1} C] [Abelian C] (K : SimplicialObject C) (B : C)
    (f : K ⟶ (SimplicialObject.const C).obj B) :
    QuasiIso ((AlgebraicTopology.alternatingFaceMapComplex C).map f) ↔
      (Epi (f.app (op (SimplexCategory.mk (0)))) ∧
        (∃ w : (K.δ (n := 0) 0 - K.δ (n := 0) 1) ≫ f.app (op (SimplexCategory.mk (0))) = 0,
          (ShortComplex.mk _ _ w).Exact) ∧
        ∀ n : ℕ, ((AlgebraicTopology.alternatingFaceMapComplex C).obj K).ExactAt (n + 1)) := by
  let e := (SimplicialObject.Augmented.ExtraDegeneracy.const B).homotopyEquiv
  let g : (AlgebraicTopology.alternatingFaceMapComplex C).obj ((SimplicialObject.const C).obj B) ⟶
      (ChainComplex.single₀ C).obj B := e.hom
  haveI : QuasiIso g := e.quasiIso_hom
  have hg : g.f 0 = 𝟙 B := AlgebraicTopology.AlternatingFaceMapComplex.ε_app_f_zero _
  rw [← quasiIso_iff_comp_right _ g, quasiIso_iff]
  set φ := (AlgebraicTopology.alternatingFaceMapComplex C).map f ≫ g with hφ
  have h0 : φ.f 0 = f.app (op (SimplexCategory.mk 0)) := by
    rw [hφ, HomologicalComplex.comp_f, hg]
    exact Category.comp_id _
  have hd : ((AlgebraicTopology.alternatingFaceMapComplex C).obj K).d 1 0 =
      K.δ (n := 0) 0 - K.δ (n := 0) 1 := by
    change (AlgebraicTopology.AlternatingFaceMapComplex.obj K).d (0 + 1) 0 = _
    rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq, Fin.sum_univ_two]
    simp [sub_eq_add_neg]
  have w : (K.δ (n := 0) 0 - K.δ (n := 0) 1) ≫ f.app (op (SimplexCategory.mk (0))) = 0 := by
    simp [Preadditive.sub_comp, SimplicialObject.δ_naturality, SimplicialObject.δ]
  have he : Epi (φ.f 0) ↔ Epi (f.app (op (SimplexCategory.mk (0)))) := h0 ▸ Iff.rfl
  have hz : QuasiIsoAt φ 0 ↔ (Epi (f.app (op (SimplexCategory.mk (0)))) ∧
      (∃ w : (K.δ (n := 0) 0 - K.δ (n := 0) 1) ≫ f.app (op (SimplexCategory.mk (0))) = 0,
        (ShortComplex.mk _ _ w).Exact)) := by
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros' _ rfl rfl rfl]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨he.1 h2, w, (ShortComplex.exact_iff_of_iso ?_).1 h1⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        ((Category.id_comp _).trans (hd.symm.trans (Category.comp_id _).symm))
        ((Category.id_comp _).trans (h0.symm.trans (Category.comp_id _).symm))
    · rintro ⟨h1, _, h2⟩
      refine ⟨(ShortComplex.exact_iff_of_iso ?_).1 h2, he.2 h1⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        ((Category.id_comp _).trans (hd.trans (Category.comp_id _).symm))
        ((Category.id_comp _).trans (h0.trans (Category.comp_id _).symm))
  have hs : ∀ n : ℕ, QuasiIsoAt φ (n + 1) ↔
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj K).ExactAt (n + 1) :=
    fun n => quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _)
  constructor
  · intro h
    exact ⟨(hz.1 (h 0)).1, (hz.1 (h 0)).2, fun n => (hs n).1 (h (n + 1))⟩
  · rintro ⟨h1, h2, h3⟩ i
    cases i with
    | zero => exact hz.2 ⟨h1, h2⟩
    | succ n => exact (hs n).2 (h3 n)

end GlobalTheory.EtC.AugExact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwOCommD
section
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

noncomputable section
namespace GlobalTheory.EZ.AWChain

theorem bop_comp {n m p q r s : ℕ} (α : SimplexCategory.mk p ⟶ SimplexCategory.mk n)
    (β : SimplexCategory.mk q ⟶ SimplexCategory.mk m) (α' : SimplexCategory.mk r ⟶ SimplexCategory.mk p)
    (β' : SimplexCategory.mk s ⟶ SimplexCategory.mk q) :
    bop α β ≫ bop α' β' = bop (α' ≫ α) (β' ≫ β) := by
  have := Free.single_comp_single (R := ℤ) (C := SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ)
    (X := (op (SimplexCategory.mk n), op (SimplexCategory.mk m)))
    (Y := (op (SimplexCategory.mk p), op (SimplexCategory.mk q)))
    (Z := (op (SimplexCategory.mk r), op (SimplexCategory.mk s))) (α.op, β.op) (α'.op, β'.op) 1 1
  simp only [mul_one] at this
  exact this

theorem comp_apply' {a b c : ℕ} (f : SimplexCategory.mk a ⟶ SimplexCategory.mk b)
    (g : SimplexCategory.mk b ⟶ SimplexCategory.mk c) (j : Fin (a+1)) :
    ((f ≫ g).toOrderHom j : ℕ) = (g.toOrderHom (f.toOrderHom j) : ℕ) := rfl

theorem hom_ext' {a b : ℕ} (f g : SimplexCategory.mk a ⟶ SimplexCategory.mk b)
    (h : ∀ j : Fin (a+1), (f.toOrderHom j : ℕ) = (g.toOrderHom j : ℕ)) : f = g := by
  apply SimplexCategory.Hom.ext
  ext j
  exact h j

theorem faceFun_lt {i j : ℕ} (h : j < i) : faceFun i j = j := if_pos h
theorem faceFun_ge {i j : ℕ} (h : i ≤ j) : faceFun i j = j + 1 := if_neg (by omega)

theorem backc_apply (n a b : ℕ) (j : Fin (b+1)) : ((backc n a b).toOrderHom j : ℕ) = min n (a + j) := rfl
theorem idc_apply (n m : ℕ) (j : Fin (m+1)) : ((idc n m).toOrderHom j : ℕ) = min n j := rfl
theorem fc_apply (n m i : ℕ) (j : Fin (m+1)) : ((fc n m i).toOrderHom j : ℕ) = min n (faceFun i j) := rfl

section
variable (a b : ℕ)

theorem front_face_low (i : ℕ) (hi : i ≤ a) :
    idc (a+b) a ≫ fc (a+b+1) (a+b) i = fc (a+1) a i ≫ idc (a+b+1) (a+1) := by
  apply hom_ext'; intro j; have hj := j.isLt
  simp only [comp_apply', fc_apply, idc_apply, backc_apply]
  rcases lt_or_ge (j:ℕ) i with h | h
  · rw [faceFun_lt (by omega), faceFun_lt h]; omega
  · rw [faceFun_ge (by omega), faceFun_ge h]; omega

theorem back_face_low (i : ℕ) (hi : i ≤ a) :
    backc (a+b) a b ≫ fc (a+b+1) (a+b) i = idc b b ≫ backc (a+b+1) (a+1) b := by
  apply hom_ext'; intro j; have hj := j.isLt
  simp only [comp_apply', fc_apply, idc_apply, backc_apply]
  rw [faceFun_ge (by omega)]; omega

theorem front_face_high (i : ℕ) (hi : a < i) :
    idc (a+b) a ≫ fc (a+b+1) (a+b) i = idc a a ≫ idc (a+b+1) a := by
  apply hom_ext'; intro j; have hj := j.isLt
  simp only [comp_apply', fc_apply, idc_apply, backc_apply]
  rw [faceFun_lt (by omega)]; omega

theorem back_face_high (j : ℕ) (hj : j ≤ b) :
    backc (a+b) a b ≫ fc (a+b+1) (a+b) (a+1+j) = fc (b+1) b (j+1) ≫ backc (a+b+1) a (b+1) := by
  apply hom_ext'; intro k; have hk := k.isLt
  simp only [comp_apply', fc_apply, idc_apply, backc_apply]
  rcases lt_or_ge (k:ℕ) (j+1) with h | h
  · rw [faceFun_lt (by omega), faceFun_lt h]; omega
  · rw [faceFun_ge (by omega), faceFun_ge h]; omega

theorem front_face_cancel : fc (a+1) a (a+1) ≫ idc (a+b+1) (a+1) = idc a a ≫ idc (a+b+1) a := by
  apply hom_ext'; intro j; have hj := j.isLt
  simp only [comp_apply', fc_apply, idc_apply, backc_apply]
  rw [faceFun_lt (by omega)]; omega

theorem back_face_cancel : idc b b ≫ backc (a+b+1) (a+1) b = fc (b+1) b 0 ≫ backc (a+b+1) a (b+1) := by
  apply hom_ext'; intro j; have hj := j.isLt
  simp only [comp_apply', fc_apply, idc_apply, backc_apply]
  rw [faceFun_ge (by omega)]; omega

end

theorem dT_h (a b : ℕ) : dT (a+1) b a b = ∑ i ∈ Finset.range (a+1+1), ((-1 : ℤ) ^ i) • bop (fc (a+1) a i) (idc b b) := by
  simp [dT, dH, dV]

theorem dT_v (a b : ℕ) : dT a (b+1) a b = ((-1 : ℤ) ^ a) • ∑ j ∈ Finset.range (b+1+1), ((-1 : ℤ) ^ j) • bop (idc a a) (fc (b+1) b j) := by
  simp [dT, dH, dV]

theorem dT_zero (x y a b : ℕ) (h1 : ¬ (x = a + 1 ∧ y = b)) (h2 : ¬ (x = a ∧ y = b + 1)) : dT x y a b = 0 := by
  simp [dT, dH, dV, h1, h2]

end GlobalTheory.EZ.AWChain

namespace GlobalTheory.EZ
open GlobalTheory.EZ.AWChain

theorem awO_comm_d : ∀ (n a b : ℕ), a + b = n → dD (n + 1) n ≫ awO n a b =
    ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), awO (n + 1) x.1 x.2 ≫ dT x.1 x.2 a b := by
  intro n a b hab
  subst hab
  rw [Finset.sum_eq_add (a + 1, b) (a, b + 1) (by simp)]
  rotate_left
  · rintro c hc ⟨h1, h2⟩
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hc
    rw [dT_zero, Limits.comp_zero]
    · rintro ⟨e1, e2⟩; exact h1 (Prod.ext e1 e2)
    · rintro ⟨e1, e2⟩; exact h2 (Prod.ext e1 e2)
  · intro h; exact absurd (by rw [Finset.HasAntidiagonal.mem_antidiagonal]; omega) h
  · intro h; exact absurd (by rw [Finset.HasAntidiagonal.mem_antidiagonal]; omega) h
  simp only [dT_h, dT_v]
  have e1 : awO (a + b + 1) (a + 1) b = bop (idc (a+b+1) (a+1)) (backc (a+b+1) (a+1) b) := if_pos (by omega)
  have e2 : awO (a + b + 1) a (b + 1) = bop (idc (a+b+1) a) (backc (a+b+1) a (b+1)) := if_pos (by omega)
  have e3 : awO (a + b) a b = bop (idc (a+b) a) (backc (a+b) a b) := if_pos rfl
  have e4 : dD (a + b + 1) (a + b) = ∑ i ∈ Finset.range (a+b+1+1),
      ((-1 : ℤ) ^ i) • bop (fc (a+b+1) (a+b) i) (fc (a+b+1) (a+b) i) := if_pos rfl
  rw [e1, e2, e3, e4]
  simp only [Preadditive.sum_comp, Preadditive.comp_sum, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    bop_comp]
  rw [show a + b + 1 + 1 = (a + 1) + (b + 1) by omega, Finset.sum_range_add]
  conv_rhs => rw [Finset.sum_range_succ _ (a + 1), Finset.sum_range_succ' _ (b + 1), smul_add]
  have hA : ∑ i ∈ Finset.range (a + 1), ((-1 : ℤ) ^ i) •
      bop (idc (a+b) a ≫ fc (a+b+1) (a+b) i) (backc (a+b) a b ≫ fc (a+b+1) (a+b) i) =
      ∑ i ∈ Finset.range (a + 1), ((-1 : ℤ) ^ i) •
      bop (fc (a+1) a i ≫ idc (a+b+1) (a+1)) (idc b b ≫ backc (a+b+1) (a+1) b) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [front_face_low a b i (by omega), back_face_low a b i (by omega)]
  have hB : ∑ j ∈ Finset.range (b + 1), ((-1 : ℤ) ^ (a + 1 + j)) •
      bop (idc (a+b) a ≫ fc (a+b+1) (a+b) (a + 1 + j)) (backc (a+b) a b ≫ fc (a+b+1) (a+b) (a + 1 + j)) =
      ((-1 : ℤ) ^ a) • ∑ j ∈ Finset.range (b + 1), ((-1 : ℤ) ^ (j + 1)) •
      bop (idc a a ≫ idc (a+b+1) a) (fc (b+1) b (j + 1) ≫ backc (a+b+1) a (b+1)) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [front_face_high a b (a + 1 + j) (by omega), back_face_high a b j (by omega), smul_smul, ← pow_add, show a + (j + 1) = a + 1 + j by omega]
  have hC : ((-1 : ℤ) ^ (a + 1)) • bop (fc (a+1) a (a + 1) ≫ idc (a+b+1) (a+1)) (idc b b ≫ backc (a+b+1) (a+1) b)
      + ((-1 : ℤ) ^ a) • (((-1 : ℤ) ^ 0) • bop (idc a a ≫ idc (a+b+1) a) (fc (b+1) b 0 ≫ backc (a+b+1) a (b+1))) = 0 := by
    rw [front_face_cancel, back_face_cancel, smul_smul, pow_zero, mul_one, pow_succ, mul_neg_one, neg_smul, neg_add_cancel]
  rw [hA, hB, add_add_add_comm, hC, add_zero]

end GlobalTheory.EZ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayMapCompAlgebraMap
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC

theorem chains_spMap_comp (R : Type) [CommRing R] {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : A →+* B)
    (h : B →+* C) : (chains R).map (spMap h) ≫ (chains R).map (spMap g) = (chains R).map (spMap (h.comp g)) := by
  rw [← Functor.map_comp]
  congr 1
  simp only [spMap, ← Functor.map_comp, ← Spec.map_comp]
  rfl

theorem awayMap_comp_algebraMap {A B : Type} [CommRing A] [CommRing B] (g : A →+* B) (f : A) :
    (Localization.awayMap g f).comp (algebraMap A (Localization.Away f)) = (algebraMap B (Localization.Away (g f))).comp g :=
  IsLocalization.map_comp _

theorem excision_square_comm (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A) :
    (chains R).map (spMap (algebraMap A' (Localization.Away (algebraMap A A' f)))) ≫ (chains R).map (spMap (algebraMap A A')) =
      (chains R).map (spMap (Localization.awayMap (algebraMap A A') f)) ≫
        (chains R).map (spMap (algebraMap A (Localization.Away f))) := by
  rw [chains_spMap_comp, chains_spMap_comp, awayMap_comp_algebraMap]

def excisionConeMap (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A) :
    mappingCone ((chains R).map (spMap (algebraMap A' (Localization.Away (algebraMap A A' f))))) ⟶
      mappingCone ((chains R).map (spMap (algebraMap A (Localization.Away f)))) :=
  mappingCone.map _ _ _ _ (excision_square_comm R A A' f)

end GlobalTheory.EtC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgHomFactorThroughSplitInjection
section
open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

namespace GlobalTheory

theorem bialgHom_factor_through_split :
    ∀ (O : Type) [CommRing O] (A B D : Type) [CommRing A] [CommRing B] [CommRing D] [Bialgebra O A] [Bialgebra O B] [Bialgebra O D] (j : B →ₐc[O] A) (ρ : A →ₗ[O] B) (f : D →ₐc[O] A), (∀ b, ρ (j b) = b) → (∀ d, f d ∈ Set.range j) → ∃ g : D →ₐc[O] B, ∀ d, j (g d) = f d := by
  intro O _ A B D _ _ _ _ _ _ j ρ f hρ hf
  have hjinj : Function.Injective j := fun x y h => by
    have := congrArg ρ h; rwa [hρ, hρ] at this
  have hjg : ∀ d, j (ρ (f d)) = f d := fun d => by
    obtain ⟨b, hb⟩ := hf d; rw [← hb, hρ]
  have hmapinj : Function.Injective (TensorProduct.map (j : B →ₗ[O] A) (j : B →ₗ[O] A)) := by
    have hid : (TensorProduct.map ρ ρ).comp (TensorProduct.map (j : B →ₗ[O] A) (j : B →ₗ[O] A)) = LinearMap.id := by
      apply TensorProduct.ext'
      intro x y
      simp [hρ]
    intro x y h
    have := congrArg (TensorProduct.map ρ ρ) h
    simpa [← LinearMap.comp_apply, hid] using this
  let gl : D →ₗ[O] B := ρ ∘ₗ (f : D →ₗ[O] A)
  have hgl : ∀ d, j (gl d) = f d := hjg
  have hcomp : (j : B →ₗ[O] A) ∘ₗ gl = (f : D →ₗ[O] A) := LinearMap.ext hgl
  refine ⟨{ gl with
    counit_comp := ?_
    map_comp_comul := ?_
    map_one' := ?_
    map_mul' := ?_ }, hgl⟩
  · ext d
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [← CoalgHomClass.counit_comp_apply j, hgl, CoalgHomClass.counit_comp_apply]
  · ext d
    apply hmapinj
    show TensorProduct.map (j : B →ₗ[O] A) (j : B →ₗ[O] A) (TensorProduct.map gl gl (comul d)) =
      TensorProduct.map (j : B →ₗ[O] A) (j : B →ₗ[O] A) (comul (gl d))
    rw [CoalgHomClass.map_comp_comul_apply j, hgl, ← LinearMap.comp_apply, ← TensorProduct.map_comp, hcomp,
      CoalgHomClass.map_comp_comul_apply f]
  · apply hjinj
    show j (gl 1) = j 1
    rw [hgl, map_one, map_one]
  · intro x y
    apply hjinj
    show j (gl (x * y)) = j (gl x * gl y)
    rw [hgl, map_mul, map_mul, hgl, hgl]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BicharacterFourierTransformTwiceEqPosSmulReflectStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bicharacterFourierTransform_twice_eq_pos_smul_reflect : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (_ : Good X) (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ), IsPair e → ∃ C : ℝ, 0 < C ∧ ∀ φ ∈ SB X, ∀ x, four μ e (four μ e φ) x = (C : ℂ) * φ (-x) := by
  first | exact @GlobalTheory.KSp.four_four | exact GlobalTheory.KSp.four_four | (intros; apply GlobalTheory.KSp.four_four <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveMultiplicativeGroupSectionsUnits
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.GmSec

def gammaIso : yoneda.obj (Spec (CommRingCat.of (MvPolynomial Unit (ULift ℤ)))) ≅ Scheme.Γ ⋙ forget CommRingCat :=
  NatIso.ofComponents (fun U => Equiv.toIso
    ((AffineSpace.toSpecMvPolyIntEquiv Unit (X := U.unop)).trans (Equiv.funUnique Unit _))) (by
      intro U V f
      ext g
      rfl)


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct in
theorem _root_.GlobalTheory.EtC.GmSec.isSheaf_gamma :
    Presieve.IsSheaf Scheme.etaleTopology.{0} (Scheme.Γ ⋙ forget CommRingCat) :=
  Presieve.isSheaf_iso _ _root_.GlobalTheory.EtC.GmSec.gammaIso
    (Presieve.isSheaf_of_le _ Scheme.etaleTopology_le_proetaleTopology
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _))

abbrev uval {V : Scheme.{0}} (t : ((Scheme.Γ ⋙ unitsF) ⋙ forget (ModuleCat.{1} (ULift.{1} ℤ))).obj (op V)) : Γ(V, ⊤)ˣ :=
  Additive.toMul (ULift.down (α := Additive Γ(V, ⊤)ˣ) t)

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct in
private lemma gmSec_uval_map_eq_units_map {U V : Scheme.{0}} (g : V ⟶ U)
    (t : ((Scheme.Γ ⋙ _root_.GlobalTheory.EtC.unitsF) ⋙
      forget (ModuleCat.{1} (ULift.{1} ℤ))).obj (op U)) :
    _root_.GlobalTheory.EtC.GmSec.uval (((Scheme.Γ ⋙ _root_.GlobalTheory.EtC.unitsF) ⋙
        forget (ModuleCat.{1} (ULift.{1} ℤ))).map g.op t) =
      Units.map (Scheme.Γ.map g.op).hom.toMonoidHom (_root_.GlobalTheory.EtC.GmSec.uval t) :=
  rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct in
private lemma gmSec_eq_of_uval_eq {U : Scheme.{0}}
    (s s' : ((Scheme.Γ ⋙ _root_.GlobalTheory.EtC.unitsF) ⋙
      forget (ModuleCat.{1} (ULift.{1} ℤ))).obj (op U))
    (h : _root_.GlobalTheory.EtC.GmSec.uval s = _root_.GlobalTheory.EtC.GmSec.uval s') : s = s' := by
  cases s; cases s'; congr 1

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct in
private theorem isSheaf_etaleTopology_units :
    Presieve.IsSheaf Scheme.etaleTopology.{0}
      ((Scheme.Γ ⋙ _root_.GlobalTheory.EtC.unitsF) ⋙ forget (ModuleCat.{1} (ULift.{1} ℤ))) := by
  intro U S hS x hx
  have hG := _root_.GlobalTheory.EtC.GmSec.isSheaf_gamma S hS
  let a : Presieve.FamilyOfElements (Scheme.Γ ⋙ forget CommRingCat) S.arrows :=
    fun V f hf => ((_root_.GlobalTheory.EtC.GmSec.uval (x f hf) : Γ(V, ⊤)ˣ) : Γ(V, ⊤))
  let b : Presieve.FamilyOfElements (Scheme.Γ ⋙ forget CommRingCat) S.arrows :=
    fun V f hf => (((_root_.GlobalTheory.EtC.GmSec.uval (x f hf))⁻¹ : Γ(V, ⊤)ˣ) : Γ(V, ⊤))
  have ha : a.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w
    exact congrArg (fun t => ((_root_.GlobalTheory.EtC.GmSec.uval t : Γ(Z, ⊤)ˣ) : Γ(Z, ⊤)))
      (hx g₁ g₂ h₁ h₂ w)
  have hb : b.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w
    have := congrArg (fun t => (((_root_.GlobalTheory.EtC.GmSec.uval t)⁻¹ : Γ(Z, ⊤)ˣ) : Γ(Z, ⊤)))
      (hx g₁ g₂ h₁ h₂ w)
    simp only [gmSec_uval_map_eq_units_map, ← map_inv] at this
    exact this
  have hA := hG.isAmalgamation ha
  have hB := hG.isAmalgamation hb
  set A := hG.amalgamate a ha
  set B := hG.amalgamate b hb
  have hAB : A * B = 1 := by
    refine hG.isSeparatedFor.ext fun V f hf => ?_
    change (Scheme.Γ.map f.op).hom (A * B) = (Scheme.Γ.map f.op).hom 1
    rw [map_mul, map_one]
    change (Scheme.Γ ⋙ forget CommRingCat).map f.op A *
      (Scheme.Γ ⋙ forget CommRingCat).map f.op B = 1
    rw [hA f hf, hB f hf]
    exact (_root_.GlobalTheory.EtC.GmSec.uval (x f hf)).mul_inv
  have hBA : B * A = 1 := by rw [mul_comm, hAB]
  let u : Γ(U, ⊤)ˣ := ⟨A, B, hAB, hBA⟩
  refine ⟨⟨Additive.ofMul u⟩, fun V f hf => gmSec_eq_of_uval_eq _ _ (Units.ext (hA f hf)),
    fun t ht => gmSec_eq_of_uval_eq _ _ (Units.ext ?_)⟩
  refine hG.isSeparatedFor.ext fun V f hf => ?_
  change ((_root_.GlobalTheory.EtC.GmSec.uval (((Scheme.Γ ⋙ _root_.GlobalTheory.EtC.unitsF) ⋙
      forget (ModuleCat.{1} (ULift.{1} ℤ))).map f.op t) : Γ(V, ⊤)ˣ) : Γ(V, ⊤)) =
    (Scheme.Γ ⋙ forget CommRingCat).map f.op A
  rw [ht f hf, hA f hf]


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct in
theorem _root_.GlobalTheory.EtC.GmSec.gm_sec_bijective :
    ∀ U : Scheme.{0},
      Function.Bijective
        (_root_.GlobalTheory.EtC.ofRings.sec _root_.GlobalTheory.EtC.unitsF U) := by
  intro U
  have hP : Presheaf.IsSheaf Scheme.etaleTopology (Scheme.Γ ⋙ _root_.GlobalTheory.EtC.unitsF) :=
    (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).mpr
      ((isSheaf_iff_isSheaf_of_type _ _).mpr isSheaf_etaleTopology_units)
  haveI := isIso_toSheafify Scheme.etaleTopology hP
  delta _root_.GlobalTheory.EtC.ofRings.sec
  exact ConcreteCategory.bijective_of_isIso
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ _root_.GlobalTheory.EtC.unitsF)).app (op U))

end GlobalTheory.EtC.GmSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockSphereProbZeroSetEqZero
section
open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop

noncomputable section

namespace GlobalTheory.SphereMeanNull

theorem exists_blockSphere_eval_ne_zero {B n : ℕ} (hn : 0 < n) {a : Fin B → ℕ}
    {g : MvPolynomial (Fin B × Fin n) ℂ} (hg0 : g ≠ 0) (hg : IsMultiHomogeneous a g) :
    ∃ u : BlockSphere B n, eval (blockPoint u) g ≠ 0 := by
  obtain ⟨s, hs⟩ := MvPolynomial.ne_zero_iff.mp hg0
  obtain ⟨z, hz1, hz⟩ := exists_torus_coeff_le g s
  set r : ℝ := (Real.sqrt n)⁻¹ with hrdef
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 0 < r := inv_pos.mpr (Real.sqrt_pos.mpr hnR)
  have hr2 : r ^ 2 * n = 1 := by
    rw [hrdef, inv_pow, Real.sq_sqrt hnR.le, inv_mul_cancel₀ hnR.ne']
  let u : BlockSphere B n := fun b => ⟨WithLp.toLp 2 (fun j => (r : ℂ) * z (b, j)), by
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq]
    simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le, hz1, mul_one]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm, hr2,
      Real.sqrt_one]⟩
  have hbp : blockPoint u = fun p => (r : ℂ) * z p := rfl
  have heval : eval (blockPoint u) g = (r : ℂ) ^ (∑ b, a b) * eval z g := by
    rw [hbp]; exact eval_mul_of_isMultiHomogeneous hg _ z
  have hne : eval z g ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (norm_pos_iff.mpr hs) hz)
  exact ⟨u, by rw [heval]; exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hr.ne')) hne⟩

theorem blockSphereProb_zeroSet_eq_zero : ∀ (B n : ℕ) (a : Fin B → ℕ)
    (g : MvPolynomial (Fin B × Fin n) ℂ), 0 < n → g ≠ 0 → IsMultiHomogeneous a g →
    blockSphereProb B n {z | eval (blockPoint z) g = 0} = 0 := by
  intro B n a g hn hg0 hg
  obtain ⟨u, hu⟩ := exists_blockSphere_eval_ne_zero hn hg0 hg
  exact null_of_logBound hn ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable
    (blockSphere_logMean_bound ReciprocityTheory.MultiplicativeHeights.Closed.sj ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable hn B)
    a g u hg hu

end GlobalTheory.SphereMeanNull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMaxPrincipleWeightedFiniteTypeIntStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_max_principle_weighted_finiteType_int : ∀ (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Algebra.FiniteType ℤ B], (letI : TopologicalSpace (B →+* ℂ) := TopologicalSpace.induced (fun x : B →+* ℂ => (x : B → ℂ)) inferInstance; ∀ (ψ : (B →+* ℂ) → ℝ), Continuous ψ → ∀ s : B, s ≠ 0 → ∀ (x₀ : B →+* ℂ) (δ : ℝ), 0 < δ → ∃ (W K : Set (B →+* ℂ)), W ∈ nhds x₀ ∧ IsCompact K ∧ (∀ x ∈ K, x s ≠ 0) ∧ ∀ (N : ℕ) (f : B) (R : ℝ), (∀ x ∈ K, ‖x f‖ * Real.exp (-(N * ψ x)) ≤ R) → ∀ y ∈ W, ‖y f‖ * Real.exp (-(N * ψ y)) ≤ Real.exp (δ * N) * R) := by
  first | exact @GlobalTheory.local_max_principle_int | exact GlobalTheory.local_max_principle_int | (intros; apply GlobalTheory.local_max_principle_int <;> assumption)
end

