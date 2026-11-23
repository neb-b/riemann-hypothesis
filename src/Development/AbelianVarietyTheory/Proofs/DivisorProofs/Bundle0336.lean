module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0298
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0300

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveMultiplicativeGroupSectionsUnitsStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bijective_multiplicativeGroup_sections_units :
    ∀ U : Scheme.{0}, Function.Bijective (ofRings.sec unitsF U) := by
  have hGamma : Presheaf.IsSheaf Scheme.etaleTopology.{0} Scheme.Γ := by
    intro R
    have gammaIso : Scheme.Γ ⋙ coyoneda.obj (op R) ≅ yoneda.obj (Spec R) :=
      NatIso.ofComponents
        (fun U => (Equiv.trans (Quiver.Hom.opEquiv)
          (ΓSpec.adjunction.homEquiv U.unop (op R))).toIso)
        (by
          intro U V f
          ext g
          exact ΓSpec.adjunction.homEquiv_naturality_left f.unop g.op)
    exact Presieve.isSheaf_of_le _ Scheme.etaleTopology_le_proetaleTopology
      (Presieve.isSheaf_iso _ gammaIso.symm
        (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _))
  have hUnits : Presheaf.IsSheaf Scheme.etaleTopology (Scheme.Γ ⋙ unitsF) := by
    apply (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).mpr
    let F := forget₂ CommRingCat.{0} CommMonCat ⋙ CommMonCat.units ⋙
      forget CommGrpCat ⋙ uliftFunctor.{1, 0}
    have hF : Presheaf.IsSheaf Scheme.etaleTopology (Scheme.Γ ⋙ F) :=
      Presheaf.isSheaf_comp_of_isSheaf _ _ F hGamma
    exact hF
  intro U
  have := isIso_toSheafify Scheme.etaleTopology hUnits
  delta ofRings.sec
  exact ConcreteCategory.bijective_of_isIso
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BisimplicialOperatorChainsAcyclicPositiveDegree
section
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ

noncomputable section
namespace GlobalTheory.EZ.Acyc
open GlobalTheory.EZ.AWChain

def cone {a p : ℕ} (α : SimplexCategory.mk p ⟶ SimplexCategory.mk a) :
    SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk a :=
  SimplexCategory.mkHom ⟨fun j => Fin.cases 0 (fun i => α.toOrderHom i) j, by
    intro i j h
    induction i using Fin.cases with
    | zero => exact Fin.zero_le _
    | succ i =>
      induction j using Fin.cases with
      | zero => exact absurd h (by simp [Fin.le_def])
      | succ j => exact α.toOrderHom.monotone (Fin.succ_le_succ_iff.mp h)⟩

theorem cone_zero {a p : ℕ} (α : SimplexCategory.mk p ⟶ SimplexCategory.mk a) :
    (cone α).toOrderHom 0 = 0 := rfl
theorem cone_succ {a p : ℕ} (α : SimplexCategory.mk p ⟶ SimplexCategory.mk a) (j : Fin (p + 1)) :
    (cone α).toOrderHom j.succ = α.toOrderHom j := rfl

abbrev Ix (a b p q : ℕ) : Type :=
  ((op (SimplexCategory.mk a), op (SimplexCategory.mk b)) : SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ) ⟶
    (op (SimplexCategory.mk p), op (SimplexCategory.mk q))

def c1 {a b p q : ℕ} (g : Ix a b p q) : Ix a b (p + 1) q := ((cone g.1.unop).op, g.2)

def c2 {a b p q : ℕ} (g : Ix a b p q) : Ix a b 0 (q + 1) := ((idc a 0).op, (cone g.2.unop).op)

def H1 {a b p q : ℕ} : (bo a b ⟶ bo p q) →+ (bo a b ⟶ bo (p + 1) q) :=
  Finsupp.mapDomain.addMonoidHom (c1 (a := a) (b := b) (p := p) (q := q))

def H2 {a b p q : ℕ} : (bo a b ⟶ bo p q) →+ (bo a b ⟶ bo 0 (q + 1)) :=
  Finsupp.mapDomain.addMonoidHom (c2 (a := a) (b := b) (p := p) (q := q))

theorem bisimplicialChainConeFirstIndex_operatorOfSimplexMaps {a b p q : ℕ} (α : SimplexCategory.mk p ⟶ SimplexCategory.mk a)
    (β : SimplexCategory.mk q ⟶ SimplexCategory.mk b) : H1 (bop α β) = bop (cone α) β := by
  change Finsupp.mapDomain c1 (Finsupp.single ((α.op, β.op) : Ix a b p q) (1 : ℤ)) =
    Finsupp.single (((cone α).op, β.op) : Ix a b (p + 1) q) (1 : ℤ)
  rw [Finsupp.mapDomain_single]
  rfl

theorem bisimplicialChainConeSecondIndex_operatorOfSimplexMaps {a b p q : ℕ} (α : SimplexCategory.mk p ⟶ SimplexCategory.mk a)
    (β : SimplexCategory.mk q ⟶ SimplexCategory.mk b) : H2 (bop α β) = bop (idc a 0) (cone β) := by
  change Finsupp.mapDomain c2 (Finsupp.single ((α.op, β.op) : Ix a b p q) (1 : ℤ)) =
    Finsupp.single (((idc a 0).op, (cone β).op) : Ix a b 0 (q + 1)) (1 : ℤ)
  rw [Finsupp.mapDomain_single]
  rfl

theorem hom_induct {a b p q : ℕ} (P : (bo a b ⟶ bo p q) → Prop) (h0 : P 0)
    (hadd : ∀ f g, P f → P g → P (f + g)) (hsm : ∀ (r : ℤ) f, P f → P (r • f))
    (hb : ∀ α β, P (bop α β)) (f : bo a b ⟶ bo p q) : P f := by
  induction f using Finsupp.induction_linear with
  | zero => exact h0
  | add f g hf hg => exact hadd _ _ hf hg
  | single g r =>
    have e : (Finsupp.single g r : bo a b ⟶ bo p q) = r • bop g.1.unop g.2.unop := by
      change Finsupp.single g r = r • Finsupp.single (g : Ix a b p q) (1 : ℤ)
      rw [Finsupp.smul_single_one]
    rw [e]
    exact hsm _ _ (hb _ _)

theorem idc_self' (n : ℕ) : idc n n = 𝟙 _ := by
  apply hom_ext'; intro j; have hj := j.isLt
  rw [idc_apply]; change min n (j : ℕ) = j; omega

theorem faceFun_succ (i j : ℕ) : faceFun (i + 1) (j + 1) = faceFun i j + 1 := by
  unfold faceFun; split_ifs <;> omega

theorem simplexClampedFaceHom_zero_comp_simplexConeMap {a p : ℕ} (α : SimplexCategory.mk p ⟶ SimplexCategory.mk a) :
    fc (p + 1) p 0 ≫ cone α = α := by
  apply hom_ext'; intro j
  rw [comp_apply']
  have : (fc (p + 1) p 0).toOrderHom j = j.succ := by
    apply Fin.ext; rw [fc_apply, faceFun_ge (Nat.zero_le _)]; simp; omega
  rw [this, cone_succ]

theorem faceSucc_cone {a p : ℕ} (α : SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk a) (i : ℕ) :
    fc (p + 1 + 1) (p + 1) (i + 1) ≫ cone α = cone (fc (p + 1) p i ≫ α) := by
  apply hom_ext'; intro j
  rw [comp_apply']
  induction j using Fin.cases with
  | zero =>
    have : (fc (p + 1 + 1) (p + 1) (i + 1)).toOrderHom 0 = 0 := by
      apply Fin.ext; rw [fc_apply, faceFun_lt (by simp)]; simp
    rw [this, cone_zero, cone_zero]
  | succ j =>
    have hj := j.isLt
    have : (fc (p + 1 + 1) (p + 1) (i + 1)).toOrderHom j.succ = ((fc (p + 1) p i).toOrderHom j).succ := by
      apply Fin.ext
      rw [Fin.val_succ, fc_apply, fc_apply, Fin.val_succ, faceFun_succ]
      have : faceFun i j ≤ j + 1 := by unfold faceFun; split_ifs <;> omega
      omega
    rw [this, cone_succ, cone_succ, comp_apply']

theorem simplexClampedFaceHom_one_comp_simplexConeMap_zero {a : ℕ} (α : SimplexCategory.mk 0 ⟶ SimplexCategory.mk a) :
    fc 1 0 1 ≫ cone α = idc a 0 := by
  apply hom_ext'; intro j
  have hj : (j : ℕ) = 0 := by have := j.isLt; omega
  have e : j = 0 := Fin.ext hj
  subst e
  rw [comp_apply']
  have : (fc 1 0 1).toOrderHom 0 = 0 := by
    apply Fin.ext; rw [fc_apply, faceFun_lt (by simp)]; simp
  rw [this, cone_zero, idc_apply]; simp

theorem face_zero_cone_identity {a : ℕ} (α : SimplexCategory.mk 0 ⟶ SimplexCategory.mk a) : fc 1 0 0 ≫ cone α = α :=
  simplexClampedFaceHom_zero_comp_simplexConeMap (p := 0) α

theorem bisimplicialTotalDifferentialOperator_one_zero_eq_sum (q : ℕ) : dT 1 q 0 q = ∑ i ∈ Finset.range (0 + 1 + 1), ((-1 : ℤ) ^ i) • bop (fc 1 0 i) (idc q q) :=
  dT_h 0 q

theorem idA {a b p q : ℕ} (f : bo a b ⟶ bo (p + 1) q) :
    H1 f ≫ dT (p + 1 + 1) q (p + 1) q = f - H1 (f ≫ dT (p + 1) q p q) := by
  refine hom_induct (fun f => H1 f ≫ dT (p + 1 + 1) q (p + 1) q = f - H1 (f ≫ dT (p + 1) q p q)) ?_ ?_ ?_ ?_ f
  · simp
  · intro f g hf hg; simp only [map_add (f := _), Preadditive.add_comp, Preadditive.add_comp, hf, hg]; abel
  · intro r f hf; simp only [map_zsmul, Preadditive.zsmul_comp, hf, smul_sub]
  · intro α β
    rw [bisimplicialChainConeFirstIndex_operatorOfSimplexMaps, dT_h (p + 1) q, dT_h p q]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, bop_comp, map_sum, map_zsmul, bisimplicialChainConeFirstIndex_operatorOfSimplexMaps]
    rw [Finset.sum_range_succ' _ (p + 1 + 1)]
    simp only [simplexClampedFaceHom_zero_comp_simplexConeMap, faceSucc_cone, pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib, pow_zero,
      one_smul, idc_self', Category.id_comp]
    abel

theorem idB {a b p q : ℕ} (f : bo a b ⟶ bo p (q + 1)) :
    H1 f ≫ dT (p + 1) (q + 1) (p + 1) q = -H1 (f ≫ dT p (q + 1) p q) := by
  refine hom_induct (fun f => H1 f ≫ dT (p + 1) (q + 1) (p + 1) q = -H1 (f ≫ dT p (q + 1) p q)) ?_ ?_ ?_ ?_ f
  · simp
  · intro f g hf hg; simp only [map_add (f := _), Preadditive.add_comp, hf, hg, neg_add]
  · intro r f hf; simp only [map_zsmul, Preadditive.zsmul_comp, hf, smul_neg]
  · intro α β
    rw [bisimplicialChainConeFirstIndex_operatorOfSimplexMaps, dT_v (p + 1) q, dT_v p q]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, Preadditive.comp_neg, bop_comp, map_sum, map_zsmul,
      bisimplicialChainConeFirstIndex_operatorOfSimplexMaps, idc_self', Category.id_comp, pow_succ, mul_neg_one, neg_smul]

theorem idC {a b q : ℕ} (f : bo a b ⟶ bo 0 (q + 1)) :
    H1 f ≫ dT 1 (q + 1) 0 (q + 1) + H2 f ≫ dT 0 (q + 1 + 1) 0 (q + 1) = f - H2 (f ≫ dT 0 (q + 1) 0 q) := by
  refine hom_induct (fun f => H1 f ≫ dT 1 (q + 1) 0 (q + 1) + H2 f ≫ dT 0 (q + 1 + 1) 0 (q + 1) =
    f - H2 (f ≫ dT 0 (q + 1) 0 q)) ?_ ?_ ?_ ?_ f
  · simp
  · intro f g hf hg
    simp only [map_add (f := _), Preadditive.add_comp] at hf hg ⊢
    rw [show H1 f ≫ dT 1 (q + 1) 0 (q + 1) + H1 g ≫ dT 1 (q + 1) 0 (q + 1) +
      (H2 f ≫ dT 0 (q + 1 + 1) 0 (q + 1) + H2 g ≫ dT 0 (q + 1 + 1) 0 (q + 1)) =
      (H1 f ≫ dT 1 (q + 1) 0 (q + 1) + H2 f ≫ dT 0 (q + 1 + 1) 0 (q + 1)) +
      (H1 g ≫ dT 1 (q + 1) 0 (q + 1) + H2 g ≫ dT 0 (q + 1 + 1) 0 (q + 1)) by abel, hf, hg]
    abel
  · intro r f hf
    simp only [map_zsmul, Preadditive.zsmul_comp, ← smul_add, hf, smul_sub]
  · intro α β
    rw [bisimplicialChainConeFirstIndex_operatorOfSimplexMaps, bisimplicialChainConeSecondIndex_operatorOfSimplexMaps, bisimplicialTotalDifferentialOperator_one_zero_eq_sum, dT_v 0 (q + 1), dT_v 0 q]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, bop_comp, map_sum, map_zsmul, bisimplicialChainConeSecondIndex_operatorOfSimplexMaps]
    rw [Finset.sum_range_succ' _ (q + 1 + 1)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, face_zero_cone_identity, simplexClampedFaceHom_one_comp_simplexConeMap_zero, simplexClampedFaceHom_zero_comp_simplexConeMap,
      faceSucc_cone, pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib, pow_zero, one_smul, idc_self',
      Category.id_comp, smul_neg]
    abel

theorem idD {a b q : ℕ} (f : bo a b ⟶ bo 1 q) : H2 (f ≫ dT 1 q 0 q) = 0 := by
  refine hom_induct (fun f => H2 (f ≫ dT 1 q 0 q) = 0) ?_ ?_ ?_ ?_ f
  · simp
  · intro f g hf hg; simp only [map_add (f := _), Preadditive.add_comp, hf, hg, add_zero]
  · intro r f hf; simp only [map_zsmul, Preadditive.zsmul_comp, hf, smul_zero]
  · intro α β
    rw [bisimplicialTotalDifferentialOperator_one_zero_eq_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Preadditive.comp_sum, Preadditive.comp_zsmul, bop_comp, map_sum, map_zsmul, bisimplicialChainConeSecondIndex_operatorOfSimplexMaps,
      Finset.sum_range_succ]

theorem sum_dT {a b : ℕ} (u : ∀ a' b' : ℕ, bo a b ⟶ bo a' b') (c d : ℕ) :
    ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (c + d + 1), u x.1 x.2 ≫ dT x.1 x.2 c d =
      u (c + 1) d ≫ dT (c + 1) d c d + u c (d + 1) ≫ dT c (d + 1) c d := by
  rw [Finset.sum_eq_add (c + 1, d) (c, d + 1) (by simp)]
  · rintro x hx ⟨h1, h2⟩
    rw [dT_zero, Limits.comp_zero]
    · rintro ⟨e1, e2⟩; exact h1 (Prod.ext e1 e2)
    · rintro ⟨e1, e2⟩; exact h2 (Prod.ext e1 e2)
  · intro h; exact absurd (by rw [Finset.HasAntidiagonal.mem_antidiagonal]; omega) h
  · intro h; exact absurd (by rw [Finset.HasAntidiagonal.mem_antidiagonal]; omega) h

def wfill {a b : ℕ} (z : ∀ a' b' : ℕ, bo a b ⟶ bo a' b') : ∀ a' b' : ℕ, bo a b ⟶ bo a' b'
  | 0, 0 => 0
  | 0, q + 1 => H2 (z 0 q)
  | p + 1, q => H1 (z p q)

end GlobalTheory.EZ.Acyc

namespace GlobalTheory.EZ
open GlobalTheory.EZ.Acyc

theorem totChains_acyclic : ∀ a b k : ℕ, 1 ≤ k → ∀ z : ∀ a' b' : ℕ, bo a b ⟶ bo a' b',
    (∀ c d : ℕ, c + d + 1 = k → ∑ x ∈ Finset.HasAntidiagonal.antidiagonal k, z x.1 x.2 ≫ dT x.1 x.2 c d = 0) →
    ∃ w : ∀ a' b' : ℕ, bo a b ⟶ bo a' b', ∀ c d : ℕ, c + d = k →
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (k + 1), w x.1 x.2 ≫ dT x.1 x.2 c d = z c d := by
  intro a b k hk z hz
  refine ⟨wfill z, fun c d hcd => ?_⟩
  subst hcd
  rw [sum_dT]
  have cyc : ∀ c' d', c' + d' + 1 = c + d →
      z (c' + 1) d' ≫ dT (c' + 1) d' c' d' + z c' (d' + 1) ≫ dT c' (d' + 1) c' d' = 0 := by
    intro c' d' h
    have := hz c' d' h
    rw [← h, sum_dT] at this
    exact this
  cases c with
  | succ p =>
    show H1 (z (p + 1) d) ≫ dT (p + 1 + 1) d (p + 1) d + H1 (z p (d + 1)) ≫ dT (p + 1) (d + 1) (p + 1) d = _
    have h2 : H1 (z (p + 1) d ≫ dT (p + 1) d p d) + H1 (z p (d + 1) ≫ dT p (d + 1) p d) = 0 := by
      rw [← map_add (f := _), cyc p d (by omega), map_zero]
    rw [idA, idB, ← sub_eq_add_neg, sub_sub, h2, sub_zero]
  | zero =>
    obtain ⟨q, rfl⟩ : ∃ q, d = q + 1 := ⟨d - 1, by omega⟩
    show H1 (z 0 (q + 1)) ≫ dT 1 (q + 1) 0 (q + 1) + H2 (z 0 (q + 1)) ≫ dT 0 (q + 1 + 1) 0 (q + 1) = _
    rw [idC]
    have h3 : z 0 (q + 1) ≫ dT 0 (q + 1) 0 q = -(z 1 q ≫ dT 1 q 0 q) := by
      have := cyc 0 q (by omega)
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact this
    rw [h3, map_neg, idD, neg_zero, sub_zero]

end GlobalTheory.EZ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDifferentialAdjointCupProductPairing
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

namespace GlobalTheory.PD.CupAdj

variable {k : Type} [Field k] {E : Type} [AddCommGroup E] [Module k E] {ι : Type} [LinearOrder ι]

theorem cech_apply_mem {F : Finset ι → Submodule k E} {n : ℤ} {a : Finset ι → E} (ha : a ∈ cechC F n)
    (s : Finset ι) : a s ∈ (if s.Nonempty ∧ (s.card : ℤ) = n + 1 then F s else ⊥) :=
  (Submodule.mem_pi.1 ha) s (Set.mem_univ _)

theorem cech_apply_eq_zero {F : Finset ι → Submodule k E} {n : ℤ} {a : Finset ι → E} (ha : a ∈ cechC F n)
    {s : Finset ι} (h : ¬ (s.Nonempty ∧ (s.card : ℤ) = n + 1)) : a s = 0 := by
  have := cech_apply_mem ha s
  rw [if_neg h] at this
  exact (Submodule.mem_bot k).1 this

theorem cech_apply_mem_of_subset {F : Finset ι → Submodule k E} (hF : ∀ s t, s.Nonempty → s ⊆ t → F s ≤ F t)
    {n : ℤ} {a : Finset ι → E} (ha : a ∈ cechC F n) {s t : Finset ι} (hst : s ⊆ t) : a s ∈ F t := by
  by_cases h : s.Nonempty ∧ (s.card : ℤ) = n + 1
  · have := cech_apply_mem ha s
    rw [if_pos h] at this
    exact hF s t h.1 hst this
  · rw [cech_apply_eq_zero ha h]; exact zero_mem _

end GlobalTheory.PD.CupAdj

namespace GlobalTheory.PD.CupAdj

theorem cupPair_apply {k : Type} [Field k] {d : ℕ} {E : Type} [AddCommGroup E] [Module k E] {E' : Type}
    [AddCommGroup E'] [Module k E'] (β : E →ₗ[k] E' →ₗ[k] k) (a : Finset (Fin (d+1)) → E)
    (b : Finset (Fin (d+1)) → E') :
    cupPair β a b = ∑ j, β (a (Finset.univ.filter (· ≤ j))) (b (Finset.univ.filter (j ≤ ·))) := by
  simp [cupPair]

theorem deltaL_apply {k : Type} [Field k] {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] [Module k E]
    (a : Finset ι → E) (t : Finset ι) :
    deltaL k ι E a t = ∑ i ∈ t, GlobalTheory.cubeSign t i • a (t.erase i) := rfl

theorem card_le (d : ℕ) (j : Fin (d+1)) : (Finset.univ.filter (· ≤ j)).card = j.val + 1 := by
  rw [show Finset.univ.filter (· ≤ j) = Finset.Iic j by ext; simp, Fin.card_Iic]

theorem card_ge (d : ℕ) (j : Fin (d+1)) : (Finset.univ.filter (j ≤ ·)).card = d + 1 - j.val := by
  rw [show Finset.univ.filter (j ≤ ·) = Finset.Ici j by ext; simp, Fin.card_Ici]

theorem cech_adj (k : Type) [Field k] (d : ℕ) (E : Type) [AddCommGroup E] [Module k E] (E' : Type)
    [AddCommGroup E'] [Module k E'] (A : Finset (Fin (d + 1)) → Submodule k E)
    (B : Finset (Fin (d + 1)) → Submodule k E') (β : E →ₗ[k] E' →ₗ[k] k)
    (hA : ∀ s t, s.Nonempty → s ⊆ t → A s ≤ A t) (hB : ∀ s t, s.Nonempty → s ⊆ t → B s ≤ B t)
    (hβ : ∀ i, (Finset.univ.erase i).Nonempty → ∀ a ∈ A (Finset.univ.erase i), ∀ b ∈ B (Finset.univ.erase i),
      β a b = 0) :
    Adj (cech A) (cech B) (cupPair β) d := by
  intro n
  have van : ∀ {m m' : ℤ} {a : Finset (Fin (d+1)) → E} {b : Finset (Fin (d+1)) → E'},
      a ∈ cechC A m → b ∈ cechC B m' → ∀ i s t, s ⊆ Finset.univ.erase i → t ⊆ Finset.univ.erase i →
      β (a s) (b t) = 0 := by
    intro m m' a b ha hb i s t hs ht
    by_cases hne : s.Nonempty
    · exact hβ i (hne.mono hs) _ (cech_apply_mem_of_subset hA ha hs) _ (cech_apply_mem_of_subset hB hb ht)
    · rw [cech_apply_eq_zero ha (fun h => hne h.1), map_zero, LinearMap.zero_apply]
  by_cases hn : 0 ≤ n ∧ n + 1 ≤ d
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, (Int.toNat_of_nonneg hn.1).symm⟩
    have hmd : m + 1 ≤ d := by exact_mod_cast hn.2
    set j : Fin (d+1) := ⟨m + 1, by omega⟩ with hj
    set j' : Fin (d+1) := ⟨m, by omega⟩ with hj'
    refine ⟨(-1 : ℤˣ) ^ ((Finset.univ.filter (· ≤ j)).filter (· < j)).card, ?_⟩
    intro a ha b hb
    change cupPair β (deltaL k _ E a) b = _ • cupPair β a (deltaL k _ E' b)
    have L1 : cupPair β (deltaL k _ E a) b =
        β (deltaL k _ E a (Finset.univ.filter (· ≤ j))) (b (Finset.univ.filter (j ≤ ·))) := by
      rw [cupPair_apply]
      refine Finset.sum_eq_single j (fun j0 _ hj0 => ?_) (by simp)
      rw [cech_apply_eq_zero hb (s := Finset.univ.filter (j0 ≤ ·)), map_zero]
      rintro ⟨-, h⟩
      have := j0.isLt
      rw [card_ge, Nat.cast_sub (by omega)] at h
      push_cast at h
      apply hj0; ext; simp only [hj]; omega
    have L2 : cupPair β a (deltaL k _ E' b) =
        β (a (Finset.univ.filter (· ≤ j'))) (deltaL k _ E' b (Finset.univ.filter (j' ≤ ·))) := by
      rw [cupPair_apply]
      refine Finset.sum_eq_single j' (fun j0 _ hj0 => ?_) (by simp)
      rw [cech_apply_eq_zero ha (s := Finset.univ.filter (· ≤ j0)), map_zero, LinearMap.zero_apply]
      rintro ⟨-, h⟩
      rw [card_le] at h
      push_cast at h
      apply hj0; ext; simp only [hj']; omega
    have L3 : β (deltaL k _ E a (Finset.univ.filter (· ≤ j))) (b (Finset.univ.filter (j ≤ ·))) =
        GlobalTheory.cubeSign (Finset.univ.filter (· ≤ j)) j •
          β (a ((Finset.univ.filter (· ≤ j)).erase j)) (b (Finset.univ.filter (j ≤ ·))) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [deltaL_apply, map_sum, LinearMap.sum_apply]
      refine (Finset.sum_eq_single j (fun i hi hij => ?_) (by simp)).trans ?_
      · rw [map_zsmul, LinearMap.smul_apply]
        have hi' : i < j := lt_of_le_of_ne (by simpa using hi) hij
        rw [van ha hb i _ _ ?_ ?_, smul_zero]
        · intro x hx
          simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          exact ⟨hx.1, trivial⟩
        · intro x hx
          simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          exact ⟨fun h => by subst h; exact absurd hx (not_le.2 hi'), trivial⟩
      · rw [map_zsmul, LinearMap.smul_apply]
    have L4 : β (a (Finset.univ.filter (· ≤ j'))) (deltaL k _ E' b (Finset.univ.filter (j' ≤ ·))) =
        β (a (Finset.univ.filter (· ≤ j'))) (b ((Finset.univ.filter (j' ≤ ·)).erase j')) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [deltaL_apply, map_sum]
      refine (Finset.sum_eq_single j' (fun i hi hij => ?_) (by simp)).trans ?_
      · rw [map_zsmul]
        have hi' : j' < i := lt_of_le_of_ne (by simpa using hi) (Ne.symm hij)
        rw [van ha hb i _ _ ?_ ?_, smul_zero]
        · intro x hx
          simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          exact ⟨fun h => by subst h; exact absurd hx (not_le.2 hi'), trivial⟩
        · intro x hx
          simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          exact ⟨hx.1, trivial⟩
      · have : GlobalTheory.cubeSign (Finset.univ.filter (j' ≤ ·)) j' = 1 := by
          rw [GlobalTheory.cubeSign]
          have : ((Finset.univ.filter (j' ≤ ·)).filter (· < j')) = ∅ := by
            ext x; simp
          rw [this]; simp
        rw [this, one_smul]
    have e1 : (Finset.univ.filter (· ≤ j)).erase j = Finset.univ.filter (· ≤ j') := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, Fin.ext_iff, Fin.le_iff_val_le_val, hj, hj']
      omega
    have e2 : Finset.univ.filter (j ≤ ·) = (Finset.univ.filter (j' ≤ ·)).erase j' := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, Fin.ext_iff, Fin.le_iff_val_le_val, hj, hj']
      omega
    rw [L1, L2, L3, L4, e1, e2, GlobalTheory.cubeSign, Units.smul_def]
    push_cast
    rfl
  · refine ⟨1, ?_⟩
    intro a ha b hb
    rw [one_smul]
    rcases not_and_or.1 hn with h | h
    · have : a = 0 := by
        funext s
        refine cech_apply_eq_zero ha ?_
        rintro ⟨hs, hc⟩
        have := hs.card_pos
        omega
      change cupPair β (deltaL k _ E a) b = cupPair β a (deltaL k _ E' b)
      simp [this]
    · have : b = 0 := by
        funext s
        refine cech_apply_eq_zero hb ?_
        rintro ⟨hs, hc⟩
        have := hs.card_pos
        omega
      change cupPair β (deltaL k _ E a) b = cupPair β a (deltaL k _ E' b)
      simp [this]

end GlobalTheory.PD.CupAdj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechIsCxOfMono
section
set_option autoImplicit false

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

theorem cech_isCx_of_mono : ∀ (k : Type) [Field k] (ι : Type) [LinearOrder ι] (E : Type) [AddCommGroup E] [Module k E]
    (A : Finset ι → Submodule k E), (∀ s t, s.Nonempty → s ⊆ t → A s ≤ A t) → (cech A).IsCx := by
  intro k _ ι _ E _ _ A hA n a ha
  have ha' : ∀ s, a s ∈ (if s.Nonempty ∧ (s.card : ℤ) = n + 1 then A s else ⊥) :=
    fun s => (Submodule.mem_pi.1 ha) s (Set.mem_univ _)
  refine ⟨?_, ?_⟩
  · show GlobalTheory.DI.delta a ∈ cechC A (n + 1)
    refine Submodule.mem_pi.2 fun t _ => ?_
    show ∑ i ∈ t, GlobalTheory.cubeSign t i • a (t.erase i) ∈ _
    split_ifs with ht
    · refine Submodule.sum_mem _ fun i _ => zsmul_mem ?_ _
      have h := ha' (t.erase i)
      split_ifs at h with h2
      · exact hA _ _ h2.1 (Finset.erase_subset _ _) h
      · rw [Submodule.mem_bot] at h; rw [h]; exact zero_mem _
    · rw [Submodule.mem_bot]
      refine Finset.sum_eq_zero fun i hi => ?_
      have h := ha' (t.erase i)
      split_ifs at h with h2
      · exfalso
        apply ht
        refine ⟨⟨i, hi⟩, ?_⟩
        have h3 := Finset.card_erase_add_one hi
        have h4 := h2.2
        omega
      · rw [Submodule.mem_bot] at h; rw [h, smul_zero]
  · exact GlobalTheory.DI.delta_delta a

end GlobalTheory.PD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLevelRepresentableStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_representable_cech_level_of_stable : ∀ (P : MorphismProperty Scheme.{0}) [P.IsStableUnderBaseChange] [P.IsMultiplicative] (V W : Scheme.{0}) (f : V ⟶ W), P f → ∀ k : SimplexCategoryᵒᵖ, ∃ (Z : Scheme.{0}) (π : Z ⟶ V) (e : yoneda.obj Z ≅ (cech f).obj k), P π ∧ e.hom ≫ (cechAug f).app k = yoneda.map (π ≫ f) := by
  first | (exact @GlobalTheory.EtC.cech_level_representable) | (exact GlobalTheory.EtC.cech_level_representable) | (intros; apply GlobalTheory.EtC.cech_level_representable  <;> assumption)
end

