module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TwoStepUnipotentCompactModSubring
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0186
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0714

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalRationalTranslate
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open Formalism.UG (cT cT_mul cT_one)

namespace GlobalTheory.EisCT

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}


omit [NumberField E] in
theorem mem_unipRad_iff_dual {C D : Matrix (Fin n) (Fin r) E} (xy : cT (σ : E →+* E) C * J * D = 1) (g : GAd σ J) :
    g ∈ unipRad σ J C ↔ ((matHom _ σ J g).1 - 1) * adMat F C = 0 ∧
      ∃ B : Matrix (Fin r) (Fin n) (AF F ⊗[F] E),
        ((matHom _ σ J g).1 - 1) * adMat F (1 - D * (cT (σ : E →+* E) C * J)) = adMat F C * B := by
  constructor
  · intro hg
    simp only [Matrix.sub_mul _ (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)), Matrix.one_mul,
      sub_eq_iff_eq_add, zero_add]
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨h1, -, h3⟩ := hg
      rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
      have hT : cT (σ : E →+* E) C * J * (1 - D * (cT (σ : E →+* E) C * J)) = 0 := by
        rw [Matrix.mul_sub, ← Matrix.mul_assoc _ D, xy, Matrix.mul_one, Matrix.one_mul, sub_self]
      choose a ha using fun k => h3 (fun j => (1 - D * (cT (σ : E →+* E) C * J) : Matrix (Fin n) (Fin n) E) j k)
        (funext fun j => congrFun (congrFun hT j) k)
      refine ⟨h1, Matrix.of fun i k => a k i, ?_⟩
      rw [← sub_eq_iff_eq_add, ← Matrix.one_mul (adMat F (1 - _)), ← Matrix.mul_assoc, Matrix.mul_one, ← Matrix.sub_mul]
      ext i k
      exact congrFun (ha k) i
    | one => exact ⟨by simp, 0, by simp⟩
    | mul a b _ _ ha hb =>
      obtain ⟨a1, A, a2⟩ := ha
      obtain ⟨b1, B, b2⟩ := hb
      refine ⟨by rw [map_mul, Units.val_mul, Matrix.mul_assoc, b1, a1], B + A, ?_⟩
      rw [map_mul, Units.val_mul, Matrix.mul_assoc, b2, Matrix.mul_add, ← Matrix.mul_assoc, a1, a2, Matrix.mul_add,
        add_assoc]
    | inv a _ ha =>
      obtain ⟨a1, A, a2⟩ := ha
      have i1 : (matHom _ σ J a⁻¹).1 * adMat F C = adMat F C := by
        conv_lhs => rw [← a1]
        rw [map_inv, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      refine ⟨i1, -A, ?_⟩
      have := congrArg ((matHom _ σ J a⁻¹).1 * ·) a2
      rw [Matrix.mul_add, ← Matrix.mul_assoc _ (adMat F C), i1, ← Matrix.mul_assoc, ← Units.val_mul, ← map_mul,
        inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul] at this
      rw [Matrix.mul_neg]
      conv_rhs => rw [this]
      abel
  · rintro ⟨h1, B, h2⟩
    refine Subgroup.subset_closure ⟨h1, ?_, fun x hx => ⟨B *ᵥ fun i => inclR (F := F) (AF F) (x i), ?_⟩⟩
    · have hg : cT (sigR (AF F) σ) (matHom _ σ J g).1 * adMat F J * (matHom _ σ J g).1 = adMat F J := g.2
      have c1 : cT (sigR (AF F) σ) (adMat F C) = adMat F (cT (σ : E →+* E) C) := rfl
      rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
      rw [adMat, Matrix.map_mul, ← adMat, ← c1, Matrix.mul_sub, Matrix.mul_one, sub_eq_zero]
      conv_lhs => rw [← h1, cT_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT _ (matHom _ σ J g).1)]
      exact congrArg _ hg
    · have e : adMat F (1 - D * (cT (σ : E →+* E) C * J)) *ᵥ (fun i => inclR (F := F) (AF F) (x i)) =
          fun i => inclR (F := F) (AF F) (x i) := by
        funext i
        have := RingHom.map_mulVec (inclR (F := F) (AF F)) (1 - D * (cT (σ : E →+* E) C * J)) x i
        rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, sub_zero, Matrix.one_mulVec] at this
        exact this.symm
      rw [Matrix.mulVec_mulVec, ← h2, ← Matrix.mulVec_mulVec, e]

end GlobalTheory.EisCT

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLatticeStableIffConjIntegral
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

noncomputable section

namespace GlobalTheory.InertUnitOrb.LatStable

theorem mulVec_int_iff {E : Type} [Field E] [NumberField E] {n : ℕ} (w : Pl E)
    (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) :
    (∀ v : Fin n → w.adicCompletion E, (∀ i, Valued.v (v i) ≤ 1) → ∀ i, Valued.v ((M *ᵥ v) i) ≤ 1) ↔
      ∀ i j, Valued.v (M i j) ≤ 1 := by
  have hmem : ∀ x : w.adicCompletion E, Valued.v x ≤ 1 ↔ x ∈ Formalism.UG.Ov E w := fun x =>
    (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 E) (K := E) (v := w)).symm
  constructor
  · intro h i j
    have := h (Pi.single j 1) (fun k => by
      by_cases hk : k = j
      · subst hk; simp
      · simp [Pi.single_apply, hk]) i
    simpa [Matrix.mulVec_single] using this
  · intro h v hv i
    rw [hmem]
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ ((hmem _).1 (h i k)) ((hmem _).1 (hv k))

theorem mem_KGL_of_int {E : Type} [Field E] [NumberField E] {n : ℕ} (w : Pl E) (M : GLw n w)
    (h1 : ∀ i j, Valued.v ((M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ 1)
    (h2 : ∀ i j, Valued.v (((M⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ 1) :
    M ∈ GlobalTheory.LFun.KGL w (n := n) := by
  have hmem : ∀ x : w.adicCompletion E, Valued.v x ≤ 1 ↔ x ∈ Formalism.UG.Ov E w := fun x =>
    (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 E) (K := E) (v := w)).symm
  let N : Matrix (Fin n) (Fin n) (Formalism.UG.Ov E w) := fun i j => ⟨_, (hmem _).1 (h1 i j)⟩
  let N' : Matrix (Fin n) (Fin n) (Formalism.UG.Ov E w) := fun i j => ⟨_, (hmem _).1 (h2 i j)⟩
  have hinj : Function.Injective ((Formalism.UG.Ov E w).subtype.mapMatrix :
      Matrix (Fin n) (Fin n) (Formalism.UG.Ov E w) →+* Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    intro a b hab
    exact Matrix.ext fun i j => Subtype.ext (congrFun (congrFun hab i) j)
  have hN : (Formalism.UG.Ov E w).subtype.mapMatrix N = (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    ext i j; rfl
  have hN' : (Formalism.UG.Ov E w).subtype.mapMatrix N' = ((M⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    ext i j; rfl
  refine ⟨⟨N, N', hinj ?_, hinj ?_⟩, ?_⟩
  · rw [map_mul, hN, hN', map_one]; exact M.mul_inv
  · rw [map_mul, hN, hN', map_one]; exact M.inv_mul
  · apply Units.ext
    simp only [Formalism.UG.bc, Units.coe_map, MonoidHom.coe_coe]
    exact hN

end GlobalTheory.InertUnitOrb.LatStable

namespace GlobalTheory.InertUnitOrb.LatStable

theorem mem_KGL_of_unitary {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) {n : ℕ} (w : Pl E)
    (hw : ¬ IsSplitAt w) (M : GLw n w) (hM : M ∈ UL n w)
    (h1 : ∀ i j, Valued.v ((M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ 1) :
    M ∈ GlobalTheory.LFun.KGL w (n := n) := by
  have hcj := (GlobalTheory.ConjAtPlace.main E hU w).2.2.1
  rw [UL, if_neg hw] at hM
  have hM' : Formalism.UG.cT (cj w) (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * 1 *
      (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = 1 := hM
  have hinv : ((M⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Formalism.UG.cT (cj w) (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    have := congrArg (· * ((M⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))) hM'
    simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv] at this
    exact this.symm
  refine mem_KGL_of_int w M h1 fun i j => ?_
  rw [hinv]
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
  rw [hcj]
  exact h1 j i

theorem e_mulVec {K F : Type} [Field K] [Field F] (e : K ≃+* F) {n : ℕ} (Q : Matrix (Fin n) (Fin n) F)
    (u : Fin n → K) (i : Fin n) : e ((Q.map e.symm *ᵥ u) i) = (Q *ᵥ fun j => e (u j)) i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

end GlobalTheory.InertUnitOrb.LatStable

namespace GlobalTheory.InertUnitOrb.LatStable

theorem unitLat_stable_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (γ : UL n w), (∀ y, ψ (B.g * y) = ((((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y) → ∀ q : UL n w, ((∀ y ∈ unitLat e B ψ q, B.g * y ∈ unitLat e B ψ q) ↔ q⁻¹ * γ * q ∈ KL n w) := by
  intro E _ _ _ hU w hw K e _ hint n B ψ γ hg q
  let ψ' : B.A → Fin n → w.adicCompletion E := fun y i => e (ψ y i)
  have hsurj : Function.Surjective ψ' := fun u => ⟨ψ.symm fun i => e.symm (u i), by funext i; simp [ψ']⟩
  set Qi := (((q⁻¹ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hQi
  set Qm := (((q : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hQm
  set Gm := (((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hGm
  set Mm := (((q⁻¹ * γ * q : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hMm'
  have hMm : Mm = Qi * Gm * Qm := rfl
  have hQiQm : Qi * Qm = 1 := by
    rw [hQi, hQm, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  have hQmQi : Qm * Qi = 1 := by
    rw [hQi, hQm, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
  have hmemL : ∀ y, y ∈ unitLat e B ψ q ↔ ∀ i, Valued.v ((Qi *ᵥ ψ' y) i) ≤ 1 := by
    intro y
    show (∀ i, ((Qi.map e.symm) *ᵥ ψ y) i ∈ (algebraMap K.O K.E).range) ↔ _
    refine forall_congr' fun i => ?_
    rw [hint, e_mulVec]
  have hgψ : ∀ y, ψ' (B.g * y) = Gm *ᵥ ψ' y := by
    intro y; funext i
    simp only [ψ']
    rw [hg, e_mulVec]
  have hstab : (∀ y ∈ unitLat e B ψ q, B.g * y ∈ unitLat e B ψ q) ↔
      ∀ v : Fin n → w.adicCompletion E, (∀ i, Valued.v (v i) ≤ 1) → ∀ i, Valued.v ((Mm *ᵥ v) i) ≤ 1 := by
    constructor
    · intro hst v hv
      obtain ⟨y, hy⟩ := hsurj (Qm *ᵥ v)
      have hyL : y ∈ unitLat e B ψ q := (hmemL y).2 (by rw [hy, Matrix.mulVec_mulVec, hQiQm, Matrix.one_mulVec]; exact hv)
      have := (hmemL _).1 (hst y hyL)
      rw [hgψ, hy, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at this
      rw [hMm]; exact this
    · intro h y hy
      rw [hmemL] at hy ⊢
      rw [hgψ]
      have key : Qi *ᵥ (Gm *ᵥ ψ' y) = Mm *ᵥ (Qi *ᵥ ψ' y) := by
        simp only [hMm, Matrix.mulVec_mulVec, Matrix.mul_assoc, hQmQi, Matrix.mul_one]
      rw [key]
      exact h _ hy
  rw [hstab, mulVec_int_iff, KL, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    exact mem_KGL_of_unitary hU w hw _ (q⁻¹ * γ * q).2 h
  · rintro ⟨N, hN⟩ i j
    have hmem : ∀ x : w.adicCompletion E, Valued.v x ≤ 1 ↔ x ∈ Formalism.UG.Ov E w := fun x =>
      (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 E) (K := E) (v := w)).symm
    rw [hmem, hMm', ← hN]
    exact ((N : Matrix (Fin n) (Fin n) (Formalism.UG.Ov E w)) i j).2

end GlobalTheory.InertUnitOrb.LatStable
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuePulledBackSectionEqImageFieldExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section
namespace GlobalTheory.ValuePullback

theorem valAt_abPull : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (t : SecA A (FractionRing R) k) (x : TFK (R := R) (FractionRing R) ⟶ A.A) (fr : FrAt x) (x' : TFK (R := R) F ⟶ A.A) (fr' : FrAt x'), x'.left = spMap (algebraMap (FractionRing R) F) ≫ x.left → fr.IsGen → (∀ z J, Good A.L z J → val fr' (𝟙 _) z J = val fr (spMap (algebraMap (FractionRing R) F)) z J) → ∀ c : FractionRing R, ValAt t x fr c → ValAt (GlobalTheory.TorsionExt.abPull (FractionRing R) F A k t) x' fr' (algebraMap (FractionRing R) F c) := by
  intro R _ _ A F _ _ k t x fr x' fr' hx _ hv c h z J hJ
  obtain rfl : x' = GlobalTheory.TorsionExt.fieldMap (R := R) (FractionRing R) F ≫ x := Over.OverMorphism.ext hx
  let p : (TFK (R := R) F).left ⟶ (TFK (R := R) (FractionRing R)).left :=
    (GlobalTheory.TorsionExt.fieldMap (R := R) (FractionRing R) F).left
  have e : ptSecT A.A (GlobalTheory.TorsionExt.fieldMap (R := R) (FractionRing R) F ≫ x) ≫
      GlobalTheory.TorsionExt.fieldMap (R := R) (FractionRing R) F ▷ A.A =
      GlobalTheory.TorsionExt.fieldMap (R := R) (FractionRing R) F ≫ ptSecT A.A x := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [ptSecT]
  have e' : (ptSecT A.A (GlobalTheory.TorsionExt.fieldMap (R := R) (FractionRing R) F ≫ x)).left ≫
      (GlobalTheory.TorsionExt.fieldMap (R := R) (FractionRing R) F ▷ A.A).left = p ≫ (ptSecT A.A x).left :=
    congrArg (fun q => q.left) e
  refine (GlobalTheory.FieldBaseChange.sval_pullOver _ _ _ _ hJ).trans ?_
  rw [e']
  obtain ⟨hJ', h₁, -, -⟩ := GlobalTheory.values_natural _ _ _ _ A.L (Fin 1)
    (fun _ => (snd (TFK (R := R) (FractionRing R)) A.A).left) (fun _ => (k : ℤ)) (ptSecT A.A x).left p z J hJ
  obtain ⟨-, -, h₂, h₃⟩ := GlobalTheory.values_natural _ _ _ _ A.L (Fin 1)
    (fun _ => x.left) (fun _ => (k : ℤ)) (𝟙 _) p z J hJ
  refine (h₁ _).trans ((congrArg (p.stalkMap z).hom (h (p z) _ hJ')).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) ?_ ?_)))
  · refine (h₃ _).symm.trans ?_
    rw [Category.comp_id]
    refine (gs_eq p z ⊤ trivial _).trans (Eq.trans ?_ (gs_eq (𝟙 _) z ⊤ trivial _).symm)
    refine congrArg _ ?_
    exact (congrArg (fun q => q.hom c)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap (FractionRing R) F)))).symm
  · refine (h₂ _).symm.trans (congrArg Units.val ?_)
    rw [Category.comp_id]
    have p₁ : val (powFrame A.A A.L x fr k) p z J = val fr p z J ^ (k : ℤ) := map_zpow _ _ _
    have p₂ : val (powFrame A.A A.L _ fr' k) (𝟙 _) z J = val fr' (𝟙 _) z J ^ (k : ℤ) := map_zpow _ _ _
    exact p₁.trans ((congrArg (· ^ (k : ℤ)) (hv z J hJ).symm).trans p₂.symm)

end GlobalTheory.ValuePullback
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeHermitianSignature
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.WittFrameSig

open Matrix

theorem Jpq_mul_self (r s : ℕ) : Formalism.UG.Jpq r s * Formalism.UG.Jpq r s = 1 := by
  simp [Formalism.UG.Jpq, fromBlocks_multiply]

theorem le_of_isotropic_diag {n r s k : ℕ} (hn : r + s = n) (J₀ : Matrix (Fin n) (Fin n) ℂ)
    (A : Matrix (Fin n) (Fin r ⊕ Fin s) ℂ) (hA : Aᴴ * J₀ * A = Formalism.UG.Jpq r s)
    (X Y : Matrix (Fin n) (Fin k) ℂ) (hxx : Xᴴ * J₀ * X = 0) (hxy : Xᴴ * J₀ * Y = 1) : k ≤ r ∧ k ≤ s := by
  let e : Fin n ≃ Fin r ⊕ Fin s := (finCongr hn.symm).trans finSumFinEquiv.symm
  set B : Matrix (Fin r ⊕ Fin s) (Fin n) ℂ := Formalism.UG.Jpq r s * Aᴴ * J₀ with hB
  have hBA : B * A = 1 := by
    rw [hB, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, hA, Jpq_mul_self]
  have hAB : A * B = 1 := (Matrix.mul_eq_one_comm_of_equiv e).2 hBA
  have hJ : Bᴴ * Formalism.UG.Jpq r s * B = J₀ := by
    calc Bᴴ * Formalism.UG.Jpq r s * B = Bᴴ * (Aᴴ * J₀ * A) * B := by rw [hA]
      _ = (A * B)ᴴ * J₀ * (A * B) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = J₀ := by rw [hAB]; simp
  refine GlobalTheory.WittSignature.le_of_isotropic_standard (B * X) (Yᴴ * J₀ᴴ * A) ?_ ?_
  · calc Yᴴ * J₀ᴴ * A * (B * X) = Yᴴ * J₀ᴴ * (A * B) * X := by simp only [Matrix.mul_assoc]
      _ = (Xᴴ * J₀ * Y)ᴴ := by rw [hAB]; simp [conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hxy, conjTranspose_one]
  · calc (B * X)ᴴ * Formalism.UG.Jpq r s * (B * X) = Xᴴ * (Bᴴ * Formalism.UG.Jpq r s * B) * X := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hJ, hxx]

end GlobalTheory.WittFrameSig

namespace GlobalTheory.WittFrameSig

open Matrix

theorem wittFrame_le_signature : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E), GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • X.J.map σ) Xf Yf →
      r₀ ≤ r ∧ r₀ ≤ s := by
  intro F E _ _ _ _ _ σ B n X r s hB hX r₀ Xf Yf hW
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  set τ : E →+* ℂ := (B.emb w).1 with hτ
  have hc : ∀ x, τ (σ x) = star (τ x) := hB.cm.2.2.2 τ
  obtain ⟨hrs, A, hA⟩ := hX.sig w
  have hmap : ∀ {a b : ℕ} (P : Matrix (Fin n) (Fin a) E) (Q : Matrix (Fin n) (Fin b) E),
      (Formalism.UG.cT (σ : E →+* E) P * ((1 : E) • X.J.map σ) * Q).map τ =
        (P.map τ)ᴴ * (X.J.map τ).map (starRingEnd ℂ) * Q.map τ := by
    intro a b P Q
    rw [one_smul, Matrix.map_mul, Matrix.map_mul]
    congr 2
    · ext i j
      simp [Formalism.UG.cT, conjTranspose_apply, hc]
    · ext i j
      simp [hc]
  have hA' : Aᴴ * (X.J.map τ).map (starRingEnd ℂ) * A = Formalism.UG.Jpq r s := by
    have h := congrArg (fun M => M.map (starRingEnd ℂ)) hA
    simp only [Matrix.map_mul] at h
    have hD : (fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).map (starRingEnd ℂ) = fromBlocks 1 0 0 (-1) := by
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply] <;> split_ifs <;> simp
    rw [hD] at h
    rw [Formalism.UG.Jpq, ← h]
    congr 2 <;> ext i j <;> simp [conjTranspose_apply]
  refine le_of_isotropic_diag hrs _ A hA' (Xf.map τ) (Yf.map τ) ?_ ?_
  · rw [← hmap, hW.xx, Matrix.map_zero _ (map_zero _)]
  · rw [← hmap, hW.xy, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.WittFrameSig
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordAppend
section
noncomputable section

namespace GlobalTheory.ArchDecay

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical

variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

def infAd (a : mixedEmbedding.mixedSpace F) : AF F :=
  LinearMap.inl F (Ainf F) (Af F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a)

def arch (x : κ → AF F) : κ → mixedEmbedding.mixedSpace F := fun i => evI F (x i)

def dD (v : κ → mixedEmbedding.mixedSpace F) (f : (κ → AF F) → ℂ) (x : κ → AF F) : ℂ :=
  deriv (fun t : ℝ => f (x + fun i => infAd F (t • v i))) 0

def mM (l : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) (f : (κ → AF F) → ℂ) (x : κ → AF F) : ℂ :=
  (l (arch F x) : ℂ) * f x


variable (κ) in
abbrev Op : Type := (κ → mixedEmbedding.mixedSpace F) ⊕ ((κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ)

def app (o : Op F κ) (f : (κ → AF F) → ℂ) : (κ → AF F) → ℂ := Sum.elim (fun v => dD F v f) (fun l => mM F l f) o

def size (o : Op F κ) : ℝ := Sum.elim (fun v => ‖v‖) (fun l => ‖l‖) o

def word (w : List (Op F κ)) (f : (κ → AF F) → ℂ) : (κ → AF F) → ℂ := w.foldr (fun o g => app F o g) f

def wordD (w : List (κ → mixedEmbedding.mixedSpace F)) (f : (κ → AF F) → ℂ) : (κ → AF F) → ℂ :=
  word F (w.map Sum.inl) f

def Per (m : ℕ) (f : (κ → AF F) → ℂ) : Prop :=
  ∀ x z : κ → AF F, (∀ i, ∃ a : AF F, evI F a = 0 ∧ (∀ v, evFin F v a ∈ v.adicCompletionIntegers F) ∧
    z i = (m : AF F) * a) → f (x + z) = f x

@[simp] theorem word_cons (o : Op F κ) (w : List (Op F κ)) (f : (κ → AF F) → ℂ) :
    word F (o :: w) f = app F o (word F w f) := rfl

theorem word_append (w w' : List (Op F κ)) (f : (κ → AF F) → ℂ) : word F (w ++ w') f = word F w (word F w' f) := by
  simp [word, List.foldr_append]

end GlobalTheory.ArchDecay
end
end

