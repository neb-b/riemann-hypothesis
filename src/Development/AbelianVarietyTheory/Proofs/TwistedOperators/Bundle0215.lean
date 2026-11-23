module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0090
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0196

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdPrimesSquarefreeConjugateIdealProd
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel

namespace GlobalTheory

theorem primeProd_conjI_eq_map {E : Type} [Field E] [NumberField E] [IsCMField E] (I : Ideal (𝓞 E)) :
    conjI I = I.map (RingOfIntegers.mapRingHom ((IsCMField.complexConj E).toRingEquiv.toRingHom)) := by
  unfold conjI
  show _ = Ideal.span _
  congr 1
  ext a
  constructor
  · rintro ⟨b, hb, h⟩
    refine ⟨b, hb, ?_⟩
    apply RingOfIntegers.ext
    rw [h]
    rfl
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, rfl⟩

theorem primeProd_squarefree_le_conj : ∀ (D : D7) (P : Finset (Formalism.L2.DIV.Pl D.host.E)), Squarefree (∏ PP ∈ P, PP.asIdeal) ∧ (∀ PP' : Formalism.L2.DIV.Pl D.host.E, (∏ PP ∈ P, PP.asIdeal) ≤ PP'.asIdeal ↔ PP' ∈ P) ∧ conjI (∏ PP ∈ P, PP.asIdeal) = ∏ PP ∈ P, conjI PP.asIdeal := by
  intro D P
  refine ⟨?_, ?_, ?_⟩
  · have hprod : (∏ PP ∈ P, PP.asIdeal) = (P.val.map (fun PP : Formalism.L2.DIV.Pl D.host.E => PP.asIdeal)).prod := by
      rw [Finset.prod_eq_multiset_prod]
    have hprime : ∀ p ∈ P.val.map (fun PP : Formalism.L2.DIV.Pl D.host.E => PP.asIdeal), Prime p := by
      intro p hp
      obtain ⟨PP, -, rfl⟩ := Multiset.mem_map.1 hp
      exact PP.prime
    have hne : (∏ PP ∈ P, PP.asIdeal) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro PP _
      exact PP.ne_bot
    rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hne, hprod,
      UniqueFactorizationMonoid.normalizedFactors_prod_of_prime hprime]
    exact (Multiset.nodup_map_iff_of_injective (fun a b h => HeightOneSpectrum.ext h)).2 P.nodup
  · intro PP'
    constructor
    · intro hle
      obtain ⟨PP, hPP, hle'⟩ := (Ideal.IsPrime.prod_le PP'.isPrime).1 hle
      have : PP.asIdeal = PP'.asIdeal := PP.isMaximal.eq_of_le PP'.isPrime.ne_top hle'
      have h2 : PP = PP' := HeightOneSpectrum.ext this
      exact h2 ▸ hPP
    · intro h
      exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ h)
  · simp only [primeProd_conjI_eq_map]
    exact map_prod (Ideal.mapHom _) _ _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReframeFunctionOnHomsNormOneCovolumeOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdSpan.ReVec

variable {D : D7}

def reWEquiv (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) : WO S T ≃+ WO S T where
  toFun := reW S T b
  invFun := reWi S T b
  left_inv := reWi_reW S T b
  right_inv := reW_reWi S T b
  map_add' := reW_add S T b

theorem continuous_reW (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) :
    Continuous (reW S T b) := by
  haveI : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1
  exact continuous_id.matrix_mul continuous_const

theorem continuous_reWi (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) :
    Continuous (reWi S T b) := by
  haveI : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1
  exact continuous_id.matrix_mul continuous_const

theorem reW_mem_ratL_iff (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (x : WO S T) :
    reW S T b x ∈ ratL T S ↔ x ∈ ratL T S := by
  have key : ∀ (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (N : Matrix (Fin S.rank) (Fin S.rank) D.host.E),
      x ∈ ratL T S → HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) (β := Matrix (Fin S.rank) (Fin S.rank) (AE D))
        (γ := Matrix (Fin T.rank) (Fin S.rank) (AE D)) x (N.map (incA D)) ∈ ratL T S := by
    rintro x N ⟨γ, rfl⟩
    refine ⟨γ * N, ?_⟩
    show (γ * N).map (incA D) = _
    exact Matrix.map_mul (f := incA D)
  constructor
  · intro h
    have h2 := key _ (frP S b) h
    have : HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) (reW S T b x) ((frP S b).map (incA D)) = x :=
      reWi_reW S T b x
    rwa [this] at h2
  · exact key x _

theorem reframeFunctionOnHoms_norm_one_covolumeOne (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (f : WO S T → ℂ) :
    AllSome (fun p : Measure (WO S T) × Set (WO S T) => IsCovolOne (ratL T S) p.1 p.2) (fun p => nrm2 p.1 p.2 f = 1) → AllSome (fun p : Measure (WO (reS S b) T) × Set (WO (reS S b) T) => IsCovolOne (ratL T (reS S b)) p.1 p.2) (fun p => nrm2 p.1 p.2 (reF S T b f) = 1) := by
  rintro ⟨⟨p0, hp0⟩, hall⟩
  have he : Continuous (reWEquiv S T b) := continuous_reW S T b
  have he' : Continuous (reWEquiv S T b).symm := continuous_reWi S T b
  have hr : ∀ x, reWEquiv S T b x ∈ ratL T S ↔ x ∈ ratL T S := reW_mem_ratL_iff S T b
  have hr' : ∀ x, (reWEquiv S T b).symm x ∈ ratL T S ↔ x ∈ ratL T S := fun x => by
    rw [← hr, AddEquiv.apply_symm_apply]
  refine ⟨⟨(p0.1.map (reWEquiv S T b).symm, (reWEquiv S T b).symm '' p0.2),
    (GlobalTheory.Unf.ParCont.isCovolOne_map hp0 (reWEquiv S T b).symm he' he hr').1⟩, ?_⟩
  have aux : ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 →
      nrm2 μ 𝓕 (fun x => f (reWEquiv S T b x)) = 1 := by
    intro μ 𝓕 hp
    obtain ⟨h1, hemb⟩ := GlobalTheory.Unf.ParCont.isCovolOne_map hp (reWEquiv S T b) he he' hr
    have h2 := hall (μ.map (reWEquiv S T b), reWEquiv S T b '' 𝓕) h1
    simp only [nrm2] at h2 ⊢
    rw [hemb.setIntegral_map, Set.preimage_image_eq _ (reWEquiv S T b).injective] at h2
    exact h2
  rintro ⟨μ', 𝓕'⟩ hp
  exact aux μ' 𝓕' hp

end GlobalTheory.AdSpan.ReVec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexIntegralMatricesDiagonalUniformizerPow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DiagIdx

open GlobalTheory.InertHomIdx

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem relIndex_pi_pi' {ι G : Type} [Fintype ι] [AddCommGroup G] (A B : ι → AddSubgroup G) :
    (AddSubgroup.pi Set.univ A).relIndex (AddSubgroup.pi Set.univ B) = ∏ i, (A i).relIndex (B i) := by
  let g : (∀ i, B i) →+ (AddSubgroup.pi Set.univ B) :=
    { toFun := fun v => ⟨fun i => (v i : G), fun i _ => (v i).2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hg : Function.Surjective g := fun x => ⟨fun i => ⟨x.1 i, x.2 i (Set.mem_univ i)⟩, rfl⟩
  have hc : ((AddSubgroup.pi Set.univ A).addSubgroupOf (AddSubgroup.pi Set.univ B)).comap g =
      AddSubgroup.pi Set.univ fun i => (A i).addSubgroupOf (B i) := by
    ext v
    simp [g, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]
  rw [AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hg, hc]
  simp_rw [AddSubgroup.relIndex, AddSubgroup.index, ← Nat.card_pi]
  refine Nat.card_congr ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientAddGroup.leftRel_pi]

def twist₂ (ϖ : L) (d : ℤ) : AddSubgroup L :=
  (Formalism.UG.intL L).toAddSubgroup.map (AddMonoidHom.mulLeft (ϖ ^ d))

theorem relIndex_twO (ϖ : L) (Q : ℕ) (h0 : ϖ ≠ 0) (h1 : Valued.v ϖ ≤ 1)
    (hQ : ∀ e : ℕ, ((Formalism.UG.intL L).toAddSubgroup.map (AddMonoidHom.mulLeft (ϖ ^ e))).relIndex
      (Formalism.UG.intL L).toAddSubgroup = Q ^ e) (d : ℤ) :
    (Formalism.UG.intL L).toAddSubgroup.relIndex (twist₂ ϖ d) = Q ^ (max (-d) 0).toNat := by
  rcases le_or_gt 0 d with hd | hd
  · have : max (-d) 0 = 0 := max_eq_right (by omega)
    rw [this, Int.toNat_zero, pow_zero, AddSubgroup.relIndex_eq_one]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hd
    change Valued.v (ϖ ^ (k : ℤ) * x) ≤ 1
    rw [zpow_natCast, map_mul, map_pow]
    exact mul_le_one' (pow_le_one' h1 k) hx
  · obtain ⟨e, he⟩ : ∃ e : ℕ, d = -(e : ℤ) := ⟨(-d).toNat, by omega⟩
    subst he
    have hm : max (-(-(e : ℤ))) 0 = e := by omega
    rw [hm, Int.toNat_natCast, ← hQ e]
    have hinj : Function.Injective (AddMonoidHom.mulLeft (ϖ ^ e)) :=
      mul_right_injective₀ (pow_ne_zero e h0)
    rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hinj]
    congr 1
    rw [twist₂, AddSubgroup.map_map]
    convert AddSubgroup.map_id _
    ext x
    simp [_root_.zpow_neg, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero e h0)]

end GlobalTheory.DiagIdx

namespace GlobalTheory.DiagIdx

open GlobalTheory.InertHomIdx

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem intMat_eq_pi (r n : ℕ) :
    intMat L r n =
      (AddSubgroup.pi Set.univ (fun _ : Fin r => AddSubgroup.pi Set.univ
        (fun _ : Fin n => (Formalism.UG.intL L).toAddSubgroup))).map
        (Matrix.ofAddEquiv : (Fin r → Fin n → L) ≃+ Matrix (Fin r) (Fin n) L).toAddMonoidHom := by
  ext X
  rw [AddSubgroup.mem_map_equiv, AddSubgroup.mem_pi, mem_intMat]
  simp only [Set.mem_univ, true_implies, AddSubgroup.mem_pi]
  exact Iff.rfl

theorem map_diag_eq_pi (ϖ : L) (h0 : ϖ ≠ 0) (r n : ℕ) (d : Fin r → ℤ) :
    (intMat L r n).map (lmul (Matrix.diagonal (fun i => ϖ ^ d i))) =
      (AddSubgroup.pi Set.univ (fun i : Fin r => AddSubgroup.pi Set.univ
        (fun _ : Fin n => twist₂ ϖ (d i)))).map
        (Matrix.ofAddEquiv : (Fin r → Fin n → L) ≃+ Matrix (Fin r) (Fin n) L).toAddMonoidHom := by
  ext Y
  rw [AddSubgroup.mem_map_equiv, AddSubgroup.mem_pi]
  simp only [Set.mem_univ, true_implies, AddSubgroup.mem_pi, twist₂, AddSubgroup.mem_map]
  constructor
  · rintro ⟨X, hX, hXY⟩ i j
    refine ⟨X i j, hX i j, ?_⟩
    rw [← hXY]
    change ϖ ^ d i * X i j = (Matrix.diagonal (fun i => ϖ ^ d i) * X) i j
    rw [Matrix.diagonal_mul]
  · intro hY
    refine ⟨Matrix.of fun i j => (ϖ ^ d i)⁻¹ * Y i j, fun i j => ?_, ?_⟩
    · obtain ⟨x, hx, hxe⟩ := hY i j
      change ϖ ^ d i * x = Y i j at hxe
      change (ϖ ^ d i)⁻¹ * Y i j ∈ Formalism.UG.intL L
      rw [← hxe, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ h0), one_mul]
      exact hx
    · ext i j
      change (Matrix.diagonal (fun i => ϖ ^ d i) * Matrix.of fun i j => (ϖ ^ d i)⁻¹ * Y i j) i j = Y i j
      rw [Matrix.diagonal_mul, Matrix.of_apply, ← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ h0), one_mul]

theorem sum_toNat {r : ℕ} (d : Fin r → ℤ) :
    ∑ i, (max (-d i) 0).toNat = (∑ i, max (-d i) 0).toNat := by
  have h : ((∑ i, (max (-d i) 0).toNat : ℕ) : ℤ) = ∑ i, max (-d i) 0 := by
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Int.toNat_of_nonneg (le_max_right _ _)
  rw [← h, Int.toNat_natCast]

theorem relIndex_intMat_diag : ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (Q : ℕ), ϖ ≠ 0 → Valued.v ϖ ≤ 1 → (∀ e : ℕ, ((Formalism.UG.intL L).toAddSubgroup.map (AddMonoidHom.mulLeft (ϖ ^ e))).relIndex (Formalism.UG.intL L).toAddSubgroup = Q ^ e) → ∀ (r n : ℕ) (d : Fin r → ℤ), (GlobalTheory.InertHomIdx.intMat L r n).relIndex ((GlobalTheory.InertHomIdx.intMat L r n).map (GlobalTheory.InertHomIdx.lmul (Matrix.diagonal (fun i => ϖ ^ d i)))) = Q ^ (n * (∑ i, max (-d i) 0).toNat) := by
  intro L _ _ ϖ Q h0 h1 hQ r n d
  rw [map_diag_eq_pi ϖ h0, intMat_eq_pi,
    AddSubgroup.relIndex_map_map_of_injective _ _ (AddEquiv.injective _), relIndex_pi_pi']
  simp_rw [relIndex_pi_pi', relIndex_twO ϖ Q h0 h1 hQ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← pow_mul, Finset.prod_pow_eq_pow_sum, ← sum_toNat, Finset.mul_sum,
    mul_comm n]

end GlobalTheory.DiagIdx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexIntegralMatricesLeftMulUnitaryKUInvarian
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.InertHomIdx


open Formalism.UG in
theorem intMat_map_lmul_of_mem_range {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
    {r n : ℕ} {g : GL (Fin r) L} (hg : g ∈ (Formalism.UG.bc (n := Fin r) (intL L).subtype).range) :
    (intMat L r n).map (lmul (n := n) (g : Matrix (Fin r) (Fin r) L)) = intMat L r n := by
  obtain ⟨h, rfl⟩ := hg
  have hint : ∀ (a : GL (Fin r) (intL L)) (X : Matrix (Fin r) (Fin n) L), X ∈ intMat L r n →
      lmul (n := n) ((Formalism.UG.bc (n := Fin r) (intL L).subtype a : GL (Fin r) L) : Matrix (Fin r) (Fin r) L) X
        ∈ intMat L r n := by
    intro a X hX i j
    rw [lmul_apply, Matrix.mul_apply]
    refine Subring.sum_mem _ fun k _ => Subring.mul_mem _ ?_ (hX k j)
    exact ((a : Matrix (Fin r) (Fin r) (intL L)) i k).2
  apply le_antisymm
  · rintro _ ⟨X, hX, rfl⟩
    exact hint h X hX
  · intro X hX
    refine ⟨lmul (n := n) ((Formalism.UG.bc (n := Fin r) (intL L).subtype h⁻¹ : GL (Fin r) L) : Matrix (Fin r) (Fin r) L) X,
      hint h⁻¹ X hX, ?_⟩
    simp only [lmul_apply]
    rw [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mul]

theorem relIndex_intMat_lmul_KU {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
    (c : L →+* L) (r n : ℕ) (t k₁ k₂ : GU c r) (hk₁ : k₁ ∈ KU c r) (hk₂ : k₂ ∈ KU c r) :
    (intMat L r n).relIndex ((intMat L r n).map (lmul (k₁ * t * k₂).1.1)) =
      (intMat L r n).relIndex ((intMat L r n).map (lmul t.1.1)) := by
  have h₁ := intMat_map_lmul_of_mem_range (n := n) ((Subgroup.mem_subgroupOf.mp hk₁)).2
  have h₂ := intMat_map_lmul_of_mem_range (n := n) ((Subgroup.mem_subgroupOf.mp hk₂)).2
  have hcomp : (lmul (n := n) (k₁ * t * k₂).1.1) =
      (lmul (n := n) k₁.1.1).comp ((lmul (n := n) t.1.1).comp (lmul (n := n) k₂.1.1)) := by
    ext X : 1
    simp only [lmul_apply, AddMonoidHom.comp_apply, Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]
  have hinj : Function.Injective (lmul (n := n) k₁.1.1) := by
    intro X Y hXY
    have := congrArg (fun Z => ((k₁.1⁻¹ : GL (Fin r) L) : Matrix (Fin r) (Fin r) L) * Z) hXY
    simpa only [lmul_apply, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul] using this
  rw [hcomp, ← AddSubgroup.map_map, ← AddSubgroup.map_map, h₂]
  calc _ = ((intMat L r n).map (lmul (n := n) k₁.1.1)).relIndex
        (((intMat L r n).map (lmul (n := n) t.1.1)).map (lmul (n := n) k₁.1.1)) := by rw [h₁]
    _ = _ := AddSubgroup.relIndex_map_map_of_injective _ _ hinj

end GlobalTheory.InertHomIdx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexUniformizerPowMulIntegersEqSqPow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.UnramIntIndex

theorem le_exp_neg_one_of_lt_one {a : WithZero (Multiplicative ℤ)} (ha : a < 1) :
    a ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  rcases eq_or_ne a 0 with rfl | h
  · exact zero_le'
  · obtain ⟨m, rfl⟩ := WithZero.ne_zero_iff_exists.mp h
    rw [← WithZero.coe_one, WithZero.coe_lt_coe] at ha
    rw [WithZero.coe_le_coe]
    have h1 : Multiplicative.toAdd m < 0 := ha
    show Multiplicative.toAdd m ≤ -1
    omega

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mem_maximalIdeal_iff (y : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) :
    y ∈ IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring ↔
      Valued.v (y : L) < 1 := by
  have hy : Valued.v (y : L) ≤ 1 := y.2
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hn
    refine lt_of_le_of_ne hy fun h1 => hn ?_
    have h0 : (y : L) ≠ 0 := by
      intro h0
      rw [h0, map_zero] at h1
      exact zero_ne_one h1
    have hinv : Valued.v ((y : L)⁻¹) ≤ 1 := by rw [map_inv₀, h1, inv_one]
    refine IsUnit.of_mul_eq_one (⟨(y : L)⁻¹, hinv⟩ : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) ?_
    exact Subtype.ext (mul_inv_cancel₀ h0)
  · rintro hlt ⟨u, rfl⟩
    obtain ⟨z, hz⟩ : ∃ z, (u : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) * z = 1 :=
      ⟨_, u.mul_inv⟩
    have h11 : (((u : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) : L)) * (z : L) = 1 :=
      congrArg Subtype.val hz
    have h1 := congrArg Valued.v h11
    rw [map_mul, map_one] at h1
    have h2 : Valued.v (z : L) ≤ 1 := z.2
    exact absurd h1 (ne_of_lt (lt_of_le_of_lt (mul_le_of_le_one_right' h2) hlt))

theorem relIndex_mul_uniformizer (ϖ : L) (c : L →+* L) (q : ℕ) (h : IsUnramInv ϖ c q) :
    ((Formalism.UG.intL L).toAddSubgroup.map (AddMonoidHom.mulLeft ϖ)).relIndex
      (Formalism.UG.intL L).toAddSubgroup = q ^ 2 := by
  obtain ⟨-, -, -, h4, -, -, h7⟩ := h
  set V := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring with hV
  have h0 : ϖ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h4
    exact WithZero.zero_ne_coe h4
  have hlt : Valued.v ϖ < 1 := by
    rw [h4, ← WithZero.coe_one, WithZero.coe_lt_coe]
    show (-1 : ℤ) < 0
    omega
  have hI : (IsLocalRing.maximalIdeal V).toAddSubgroup.index = q ^ 2 := h7
  let f : V →+ L := V.subtype.toAddMonoidHom
  have hf : Function.Injective f := Subtype.val_injective
  have e1 : (IsLocalRing.maximalIdeal V).toAddSubgroup.map f =
      (Formalism.UG.intL L).toAddSubgroup.map (AddMonoidHom.mulLeft ϖ) := by
    ext x
    simp only [AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : Valued.v (y : L) < 1 := (mem_maximalIdeal_iff y).1 hy
      have hle := le_exp_neg_one_of_lt_one hy'
      refine ⟨ϖ⁻¹ * (y : L), ?_, ?_⟩
      · show Valued.v (ϖ⁻¹ * (y : L)) ≤ 1
        rw [map_mul, map_inv₀, inv_mul_le_iff₀ (zero_lt_iff.mpr (by simpa using h0)), mul_one, h4]
        exact hle
      · show ϖ * (ϖ⁻¹ * (y : L)) = (y : L)
        field_simp
    · rintro ⟨o, ho, rfl⟩
      have ho' : Valued.v o ≤ 1 := ho
      have hm : Valued.v (ϖ * o) < 1 := by
        rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' ho') hlt
      exact ⟨⟨ϖ * o, hm.le⟩, (mem_maximalIdeal_iff _).2 hm, rfl⟩
  have e2 : (⊤ : AddSubgroup V).map f = (Formalism.UG.intL L).toAddSubgroup := by
    ext x
    simp only [AddSubgroup.mem_map, AddSubgroup.mem_top, true_and]
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [← e1, ← e2, AddSubgroup.relIndex_map_map_of_injective _ _ hf, AddSubgroup.relIndex_top_right]
  exact hI

theorem relIndex_mul_uniformizer_pow {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
    (ϖ : L) (c : L →+* L) (q : ℕ) (h : IsUnramInv ϖ c q) (e : ℕ) :
    ((Formalism.UG.intL L).toAddSubgroup.map (AddMonoidHom.mulLeft (ϖ ^ e))).relIndex
      (Formalism.UG.intL L).toAddSubgroup = (q ^ 2) ^ e := by
  have hbase := relIndex_mul_uniformizer ϖ c q h
  obtain ⟨-, -, -, h4, -⟩ := h
  have h0 : ϖ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h4
    exact WithZero.zero_ne_coe h4
  have hϖ : ϖ ∈ Formalism.UG.intL L := by
    show Valued.v ϖ ≤ 1
    rw [h4, ← WithZero.coe_one, WithZero.coe_le_coe]
    show (-1 : ℤ) ≤ 0
    omega
  set O := (Formalism.UG.intL L).toAddSubgroup with hO
  have hmulle : ∀ a ∈ Formalism.UG.intL L, O.map (AddMonoidHom.mulLeft a) ≤ O := by
    rintro a ha _ ⟨o, ho, rfl⟩
    exact (Formalism.UG.intL L).mul_mem ha ho
  induction e with
  | zero =>
    have : O.map (AddMonoidHom.mulLeft (ϖ ^ 0)) = O := by
      ext x
      simp [AddSubgroup.mem_map]
    rw [this]
    simp
  | succ e ih =>
    have hinj : Function.Injective (AddMonoidHom.mulLeft (ϖ ^ e)) :=
      mul_right_injective₀ (pow_ne_zero e h0)
    have hcomp : O.map (AddMonoidHom.mulLeft (ϖ ^ (e + 1))) =
        (O.map (AddMonoidHom.mulLeft ϖ)).map (AddMonoidHom.mulLeft (ϖ ^ e)) := by
      ext x
      simp only [AddSubgroup.mem_map, AddMonoidHom.coe_mulLeft]
      constructor
      · rintro ⟨o, ho, rfl⟩
        exact ⟨ϖ * o, ⟨o, ho, rfl⟩, by rw [pow_succ, mul_assoc]⟩
      · rintro ⟨_, ⟨o, ho, rfl⟩, rfl⟩
        exact ⟨o, ho, by rw [pow_succ, mul_assoc]⟩
    have hstep : (O.map (AddMonoidHom.mulLeft (ϖ ^ (e + 1)))).relIndex
        (O.map (AddMonoidHom.mulLeft (ϖ ^ e))) = q ^ 2 := by
      rw [hcomp, AddSubgroup.relIndex_map_map_of_injective _ _ hinj]
      exact hbase
    have hle1 : O.map (AddMonoidHom.mulLeft (ϖ ^ (e + 1))) ≤ O.map (AddMonoidHom.mulLeft (ϖ ^ e)) := by
      rw [hcomp]
      exact AddSubgroup.map_mono (hmulle ϖ hϖ)
    have hle2 := hmulle (ϖ ^ e) (pow_mem hϖ e)
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ hle1 hle2, hstep, ih]
    exact (pow_succ' _ _).symm

end GlobalTheory.UnramIntIndex
end
end

