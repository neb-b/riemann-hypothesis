module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnitUpperRightBlockOfHeisenbergDerivativeSolut
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHomeomorphWittFlagCoordinates
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MixPer

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ}

def flagCoordMap (d : HypDec S S₀ ρ) (p : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ)) : flagN d :=
  ⟨d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2),
    mul_mem (d.levi_mem_NFlag p.1.2) (mul_mem (d.nB_mem_NFlag p.2.1) (d.nC_mem_NFlag p.2.2))⟩

theorem flagCoordMap_bijective (d : HypDec S S₀ ρ) : Function.Bijective (flagCoordMap d) := by
  refine ⟨fun p q h => ?_, fun n => ?_⟩
  · rcases p with ⟨⟨u, hu⟩, b, c⟩
    rcases q with ⟨⟨v, hv⟩, b', c'⟩
    have e : d.levi u * (d.nB b * d.nC c) = d.levi v * (d.nB b' * d.nC c') :=
      congrArg Subtype.val h
    have eX := congrArg (fun g => d.pX * (mt S g * d.jX)) e
    simp only [mt_mul, Matrix.mul_assoc, d.nC_jX, d.nB_jX, d.levi_jX] at eX
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul, Matrix.one_mul] at eX
    have huv : u = v := Units.ext eX
    subst v
    have e' := mul_left_cancel e
    have e0 := congrArg (fun g => d.pX * (mt S g * d.j0)) e'
    simp only [mt_mul, Matrix.mul_assoc, d.nC_j0, d.nB_j0, Matrix.mul_add, d.pX_j0,
      cancel₂ d.pX_jX, Matrix.one_mul, zero_add] at e0
    subst b'
    have eY := congrArg (fun g => d.pX * (mt S g * d.jY)) (mul_left_cancel e')
    simp only [d.nC_jY, Matrix.mul_add, d.pX_jY, cancel₂ d.pX_jX, Matrix.one_mul, zero_add] at eY
    exact Prod.ext rfl (Prod.ext rfl (Subtype.ext eY))
  · obtain ⟨T, B, hT, hX, h0⟩ := exists_blocks d n.2
    obtain ⟨u, hu, huT⟩ := Decomp.exists_unit hT
    let b := (u⁻¹).1 * B
    let g := d.levi u * d.nB b
    have hgX : mt S g * d.jX = mt S n.1 * d.jX := by
      dsimp only [g]
      rw [mt_mul, Matrix.mul_assoc, d.nB_jX, d.levi_jX, hX, huT, Matrix.mul_add, Matrix.mul_one]
    have hg0 : mt S g * d.j0 = mt S n.1 * d.j0 := by
      dsimp only [g, b]
      rw [mt_mul, Matrix.mul_assoc, d.nB_j0, h0, Matrix.mul_add,
        d.wittDecomp_levi_inclAnisotropic, ← Matrix.mul_assoc (mt S (d.levi u)), d.levi_jX,
        Matrix.mul_assoc d.jX, ← Matrix.mul_assoc u.1, Units.mul_inv, Matrix.one_mul]
    let k := g⁻¹ * n.1
    have hkX : mt S k * d.jX = d.jX := by
      dsimp only [k]
      rw [mt_mul, Matrix.mul_assoc, ← hgX, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
    have hk0 : mt S k * d.j0 = d.j0 := by
      dsimp only [k]
      rw [mt_mul, Matrix.mul_assoc, ← hg0, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
    have gram {m l : ℕ} (X : Mx D S.rank m) (Y : Mx D S.rank l) :
        adj (mt S k * X) * (gA S * (mt S k * Y)) = adj X * (gA S * Y) := by
      rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S) _ Y,
        ← Matrix.mul_assoc (adj (mt S k)), GlobalTheory.MixModel.mt_unitary]
    have pY : d.pY * (mt S k * d.jY) = 1 := by
      rw [d.pY_eq, Matrix.mul_assoc, ← hkX, gram, d.gram_XY]
    have p0 : d.p0 * (mt S k * d.jY) = 0 := by
      rw [d.p0_eq, Matrix.mul_assoc, Matrix.mul_assoc, ← hk0, gram, d.gram_0Y, Matrix.mul_zero]
    let C := d.pX * (mt S k * d.jY)
    have hkY : mt S k * d.jY = d.jY + d.jX * C := by
      conv_lhs => rw [← Matrix.one_mul (mt S k * d.jY), ← d.sum_eq_one]
      rw [Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
        pY, p0, Matrix.mul_zero, add_zero, Matrix.mul_one, add_comm]
    have hC := gram d.jY d.jY
    rw [hkY, d.gram_YY] at hC
    simp only [adj_add, adj_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, d.gram_YY,
      d.gram_XY, cancel₃ d.gram_XX, cancel₃ d.gram_YX, Matrix.zero_mul, Matrix.mul_zero,
      Matrix.one_mul, Matrix.mul_one, add_zero, zero_add] at hC
    let c : skewA D ρ := ⟨C, eq_neg_of_add_eq_zero_left hC⟩
    have hk : k = d.nC c := d.ga_ext (hkX.trans (d.nC_jX c).symm)
      (hk0.trans (d.nC_j0 c).symm) (hkY.trans (d.nC_jY c).symm)
    refine ⟨(⟨u, hu⟩, b, c), Subtype.ext ?_⟩
    change d.levi u * (d.nB b * d.nC c) = n.1
    rw [← mul_assoc, ← hk]
    exact mul_inv_cancel_left g n.1

theorem pX_mt_flagCoord (d : HypDec S S₀ ρ) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank) (c : skewA D ρ) :
    d.pX * Formalism.L2.Theta.mt S (d.levi u * (d.nB b * d.nC c)) =
      u.1 * (d.pX + c.1 * d.pY + b * d.p0 - (half D • (b * plus S₀ b)) * d.pY) := by
  rw [mt_mul, mt_mul, ← Matrix.mul_assoc, d.pX_levi, Matrix.mul_assoc, ← Matrix.mul_assoc d.pX, d.pX_nB]
  congr 1
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, d.pX_nC, d.wittDecomp_projAnisotropic_unipotentSkew, d.pY_nC]

theorem flagCoord_jX (d : HypDec S S₀ ρ) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank) (c : skewA D ρ) :
    d.pX * (Formalism.L2.Theta.mt S (d.levi u * (d.nB b * d.nC c)) * d.jX) = u.1 := by
  rw [← Matrix.mul_assoc, pX_mt_flagCoord]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, d.pX_jX, d.pY_jX, d.p0_jX, Matrix.mul_zero,
    Matrix.mul_one, add_zero, sub_zero]

theorem flagCoordinate_at_base (d : HypDec S S₀ ρ) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank) (c : skewA D ρ) :
    d.pX * (Formalism.L2.Theta.mt S (d.levi u * (d.nB b * d.nC c)) * d.j0) = u.1 * b := by
  rw [← Matrix.mul_assoc, pX_mt_flagCoord]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, d.pX_j0, d.pY_j0, d.p0_j0, Matrix.mul_zero,
    Matrix.mul_one, add_zero, sub_zero, zero_add]

theorem flagCoord_jY (d : HypDec S S₀ ρ) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank) (c : skewA D ρ) :
    d.pX * (Formalism.L2.Theta.mt S (d.levi u * (d.nB b * d.nC c)) * d.jY) =
      u.1 * (c.1 - half D • (b * plus S₀ b)) := by
  rw [← Matrix.mul_assoc, pX_mt_flagCoord]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, d.pX_jY, d.pY_jY, d.p0_jY, Matrix.mul_zero,
    Matrix.mul_one, add_zero, zero_add, Matrix.mul_sub]

theorem flagCoord_inv_jX (d : HypDec S S₀ ρ) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank) (c : skewA D ρ) :
    d.pX * (Formalism.L2.Theta.mt S (d.levi u * (d.nB b * d.nC c))⁻¹ * d.jX) = (u⁻¹).1 := by
  set g := d.levi u * (d.nB b * d.nC c)
  have h1 : Formalism.L2.Theta.mt S g * d.jX = d.jX * u.1 := by
    simp only [g, mt_mul, Matrix.mul_assoc, d.nC_jX, d.nB_jX, d.levi_jX]
  have h2 : Formalism.L2.Theta.mt S g⁻¹ * d.jX = d.jX * (u⁻¹).1 := by
    calc Formalism.L2.Theta.mt S g⁻¹ * d.jX = Formalism.L2.Theta.mt S g⁻¹ * (d.jX * u.1 * (u⁻¹).1) := by
          rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = d.jX * (u⁻¹).1 := by
          rw [← h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
  rw [h2, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul]

end GlobalTheory.MixPer

namespace GlobalTheory.MixPer

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ}

theorem flagCoord_b (d : HypDec S S₀ ρ) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank) (c : skewA D ρ) :
    (u⁻¹).1 * (d.pX * (Formalism.L2.Theta.mt S (d.levi u * (d.nB b * d.nC c)) * d.j0)) = b := by
  rw [flagCoordinate_at_base, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

theorem flagCoord_c (d : HypDec S S₀ ρ) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank) (c : skewA D ρ) :
    (u⁻¹).1 * (d.pX * (Formalism.L2.Theta.mt S (d.levi u * (d.nB b * d.nC c)) * d.jY)) + half D • (b * plus S₀ b) = c.1 := by
  rw [flagCoord_jY, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, sub_add_cancel]

end GlobalTheory.MixPer

namespace GlobalTheory.MixPer

theorem flagCoord_homeo : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ),
    ∃ e : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) ≃ₜ flagN d,
      ∀ p, (e p : GA D S) = d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2) := by
  intro D S S₀ ρ d
  have := (lattice_Mx D ρ ρ).1
  let e0 := Equiv.ofBijective _ (flagCoordMap_bijective d)
  have key : ∀ n : flagN d, (n : GA D S) =
      d.levi (e0.symm n).1.1 * (d.nB (e0.symm n).2.1 * d.nC (e0.symm n).2.2) := fun n =>
    congrArg Subtype.val (e0.apply_symm_apply n).symm
  have hM : Continuous fun n : flagN d => Formalism.L2.Theta.mt S (n : GA D S) :=
    (continuous_mt S).comp continuous_subtype_val
  have hMi : Continuous fun n : flagN d => Formalism.L2.Theta.mt S (n : GA D S)⁻¹ :=
    (continuous_mt S).comp continuous_subtype_val.inv
  have hU : ∀ n : flagN d, ((e0.symm n).1.1).val = d.pX * (Formalism.L2.Theta.mt S (n : GA D S) * d.jX) := by
    intro n; rw [key n, flagCoord_jX]
  have hUi : ∀ n : flagN d, (((e0.symm n).1.1)⁻¹).val =
      d.pX * (Formalism.L2.Theta.mt S (n : GA D S)⁻¹ * d.jX) := by
    intro n; rw [key n, flagCoord_inv_jX]
  have hB : ∀ n : flagN d, (e0.symm n).2.1 =
      d.pX * (Formalism.L2.Theta.mt S (n : GA D S)⁻¹ * d.jX) * (d.pX * (Formalism.L2.Theta.mt S (n : GA D S) * d.j0)) := by
    intro n; rw [← hUi n]; conv_rhs => rw [key n]
    exact (flagCoord_b d _ _ _).symm
  have hC : ∀ n : flagN d, ((e0.symm n).2.2).val =
      d.pX * (Formalism.L2.Theta.mt S (n : GA D S)⁻¹ * d.jX) * (d.pX * (Formalism.L2.Theta.mt S (n : GA D S) * d.jY)) +
        half D • ((e0.symm n).2.1 * plus S₀ (e0.symm n).2.1) := by
    intro n; rw [← hUi n]; conv_rhs => rw [key n]
    exact (flagCoord_c d _ _ _).symm
  have cU : Continuous fun n : flagN d => ((e0.symm n).1.1).val := by
    simp only [hU]; exact continuous_const.matrix_mul (hM.matrix_mul continuous_const)
  have cUi : Continuous fun n : flagN d => (((e0.symm n).1.1)⁻¹).val := by
    simp only [hUi]; exact continuous_const.matrix_mul (hMi.matrix_mul continuous_const)
  have cB : Continuous fun n : flagN d => (e0.symm n).2.1 := by
    simp only [hB]
    exact (continuous_const.matrix_mul (hMi.matrix_mul continuous_const)).matrix_mul
      (continuous_const.matrix_mul (hM.matrix_mul continuous_const))
  have cC : Continuous fun n : flagN d => ((e0.symm n).2.2).val := by
    have hp : Continuous fun n : flagN d => (e0.symm n).2.1 * plus S₀ (e0.symm n).2.1 :=
      cB.matrix_mul (continuous_const.matrix_mul (continuous_adj.comp cB))
    simp only [hC]
    exact ((continuous_const.matrix_mul (hMi.matrix_mul continuous_const)).matrix_mul
      (continuous_const.matrix_mul (hM.matrix_mul continuous_const))).add (hp.const_smul (half D))
  refine ⟨{ toEquiv := e0, continuous_toFun := ?_, continuous_invFun := ?_ }, fun p => rfl⟩
  · show Continuous (flagCoordMap d)
    exact Continuous.subtype_mk ((d.continuous_levi.comp (continuous_subtype_val.comp continuous_fst)).mul
      ((d.continuous_nB.comp (continuous_fst.comp continuous_snd)).mul
        (d.continuous_nC.comp (continuous_snd.comp continuous_snd)))) _
  · refine Continuous.prodMk ?_ (Continuous.prodMk cB ?_)
    · exact continuous_induced_rng.2 (Units.continuous_iff.2 ⟨cU, cUi⟩)
    · exact continuous_induced_rng.2 cC

end GlobalTheory.MixPer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSignCompatibleNumberingDecreasingEnumerati
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

noncomputable section
namespace GlobalTheory.ArchRec.EnumBlocks

theorem signed_eq {p q : ℕ} {l₁ l₂ : List ℚ} (c : ℚ) (h₁ : l₁.length = p) (h₂ : l₂.length = q) :
    signed l₁ l₂ c = Finset.univ.image fun a : Ix p q => (ofBlocks l₁ l₂ a + c, a.isLeft) := by
  subst h₁ h₂
  ext ⟨x, b⟩
  simp only [signed, Finset.mem_union, List.mem_toFinset, List.mem_map, Prod.mk.injEq, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨y, hy, rfl, rfl⟩ | ⟨y, hy, rfl, rfl⟩)
    · obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hy
      exact ⟨.inl i, by simp [ofBlocks], rfl⟩
    · obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hy
      exact ⟨.inr i, by simp [ofBlocks], rfl⟩
  · rintro ⟨a | a, rfl, rfl⟩
    · exact Or.inl ⟨_, by simp [ofBlocks], rfl, by simp⟩
    · exact Or.inr ⟨_, by simp [ofBlocks], rfl, by simp⟩

theorem sameBlock_iff {p q : ℕ} (a b : Ix p q) : sameBlock a b ↔ b.isLeft = a.isLeft := by
  rcases a with a | a <;> rcases b with b | b <;> simp [sameBlock]

theorem card_filter_equiv {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (P : β → Prop) (Q : α → Prop)
    [DecidablePred P] [DecidablePred Q] (h : ∀ b, P (e b) ↔ Q b) :
    (Finset.univ.filter P).card = (Finset.univ.filter Q).card :=
  (Finset.card_equiv e (fun b => by simp [h])).symm

theorem lowK_numbered {n p q : ℕ} {ε : Fin n → Bool} {lamM : Fin n → ℝ} (e : Ix p q ≃ Fin n)
    (hε : ∀ a, ε (e a) = a.isLeft) (R : Ix p q → Ix p q → Prop) (hR : ∀ a b, e a < e b ↔ R a b) (a : Ix p q)
    [DecidableRel R] :
    Formalism.QuantumDeterminants.lowK ε lamM (e a) = lamM (e a) +
      ((((Finset.univ.filter fun b => ¬ sameBlock a b ∧ R a b).card : ℝ) -
        ((Finset.univ.filter fun b => ¬ sameBlock a b ∧ R b a).card : ℝ)) / 2 -
       (((Finset.univ.filter fun b => sameBlock a b ∧ R a b).card : ℝ) -
        ((Finset.univ.filter fun b => sameBlock a b ∧ R b a).card : ℝ)) / 2) := by
  classical
  have hs : ∀ b, ε (e b) = ε (e a) ↔ sameBlock a b := fun b => by rw [hε, hε, sameBlock_iff]
  have hn : ∀ b, ε (e b) ≠ ε (e a) ↔ ¬ sameBlock a b := fun b => not_congr (hs b)
  have n1 := card_filter_equiv e (fun j => e a < j ∧ ε j ≠ ε (e a)) (fun b => ¬ sameBlock a b ∧ R a b)
    fun b => by rw [hR, hn]; exact and_comm
  have n2 := card_filter_equiv e (fun j => j < e a ∧ ε j ≠ ε (e a)) (fun b => ¬ sameBlock a b ∧ R b a)
    fun b => by rw [hR, hn]; exact and_comm
  have c1 := card_filter_equiv e (fun j => e a < j ∧ ε j = ε (e a)) (fun b => sameBlock a b ∧ R a b)
    fun b => by rw [hR, hs]; exact and_comm
  have c2 := card_filter_equiv e (fun j => j < e a ∧ ε j = ε (e a)) (fun b => sameBlock a b ∧ R b a)
    fun b => by rw [hR, hs]; exact and_comm
  simp only [Formalism.QuantumDeterminants.lowK, Pi.add_apply, Pi.sub_apply, Formalism.REAL.rhoN, Formalism.REAL.rhoC]
  rw [n1, n2, c1, c2]
  ring

theorem core {n p q : ℕ} {L : Ix p q → ℚ} (hL : Function.Injective L) {c s : ℚ} (hs : s = 1 ∨ s = -1)
    {ε : Fin n → Bool} {lamM : Fin n → ℝ}
    (hE : IsEnum (Finset.univ.image fun a : Ix p q => (s * (L a + c), a.isLeft)) lamM ε) :
    ∃ e : Ix p q ≃ Fin n, IsOrd ε lamM L c (s : ℝ) e := by
  classical
  obtain ⟨hanti, r, hr, hS⟩ := hE
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  have hf : Function.Injective fun a : Ix p q => (s * (L a + c), a.isLeft) := fun a b h =>
    hL (add_right_cancel (mul_left_cancel₀ hs0 (congrArg Prod.fst h)))
  have hg : Function.Injective fun i => (r i, ε i) := fun i j h =>
    hanti.injective (by rw [hr, hr, show r i = r j from congrArg Prod.fst h])
  have ex : ∀ a : Ix p q, ∃ i, (r i, ε i) = (s * (L a + c), a.isLeft) := fun a => by
    have : (s * (L a + c), a.isLeft) ∈ Finset.univ.image fun i => (r i, ε i) := by
      rw [← hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 this
    exact ⟨i, hi⟩
  choose f hfi using ex
  have finj : Function.Injective f := fun a b h => hf (by
    show (s * (L a + c), a.isLeft) = (s * (L b + c), b.isLeft)
    rw [← hfi a, ← hfi b, h])
  have fsurj : Function.Surjective f := fun i => by
    have : (r i, ε i) ∈ Finset.univ.image fun a : Ix p q => (s * (L a + c), a.isLeft) := by
      rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    obtain ⟨a, -, ha⟩ := Finset.mem_image.1 this
    exact ⟨a, hg ((hfi a).trans ha)⟩
  let e : Ix p q ≃ Fin n := Equiv.ofBijective f ⟨finj, fsurj⟩
  have he : ∀ a, (r (e a), ε (e a)) = (s * (L a + c), a.isLeft) := hfi
  have hε : ∀ a, ε (e a) = a.isLeft := fun a => congrArg Prod.snd (he a)
  have hr' : ∀ a, r (e a) = s * (L a + c) := fun a => congrArg Prod.fst (he a)
  have hlam : ∀ a, lamM (e a) = (s : ℝ) * ((L a + c : ℚ) : ℝ) := fun a => by
    rw [hr, hr']; push_cast; ring
  have hlt : ∀ a b, e a < e b ↔ s * L b < s * L a := fun a b => by
    have h0 : e a < e b ↔ lamM (e b) < lamM (e a) := ⟨fun h => hanti h, fun h => by
      by_contra hn
      exact absurd (hanti.antitone (not_lt.1 hn)) (not_le.2 h)⟩
    rw [h0, hlam, hlam]
    rw [← Rat.cast_mul, ← Rat.cast_mul, Rat.cast_lt, mul_add, mul_add, add_lt_add_iff_right]
  refine ⟨e, hε, hlam, fun a => ?_⟩
  rcases hs with rfl | rfl
  · rw [lowK_numbered e hε (fun a b => L b < L a) (fun a b => by simpa using hlt a b) a, hlam]
    simp only [blattner, rhoNC]
    push_cast
    ring
  · rw [lowK_numbered e hε (fun a b => L a < L b) (fun a b => by simpa using hlt a b) a, hlam]
    simp only [blattner, rhoNC]
    push_cast
    ring

theorem parOf_eq {p q : ℕ} {l₁ l₂ : List ℚ} (br cj : Bool) (c : ℚ) (h₁ : l₁.length = p) (h₂ : l₂.length = q) :
    parOf br cj l₁ l₂ c = Finset.univ.image fun a : Ix p q =>
      ((if br = cj then 1 else -1 : ℚ) * (ofBlocks l₁ l₂ a + c), a.isLeft) := by
  classical
  unfold parOf dualPar
  rw [signed_eq c h₁ h₂]
  split_ifs
  · simp
  · rw [Finset.image_image]
    refine Finset.image_congr fun a _ => ?_
    simp

theorem exists_isOrd (n p q : ℕ) (l₁ l₂ : List ℚ) (c : ℚ) (br cj : Bool) (ε : Fin n → Bool) (lamM : Fin n → ℝ)
    (h₁ : l₁.length = p) (h₂ : l₂.length = q) (hP : IsParam (ofBlocks l₁ l₂ : Ix p q → ℚ))
    (hE : IsEnum (parOf br cj l₁ l₂ c) lamM ε) :
    ∃ e : Ix p q ≃ Fin n, IsOrd ε lamM (ofBlocks l₁ l₂) c (sg br cj) e := by
  rw [parOf_eq br cj c h₁ h₂] at hE
  have hs : (if br = cj then 1 else -1 : ℚ) = 1 ∨ (if br = cj then 1 else -1 : ℚ) = -1 := by
    split_ifs <;> simp
  have := core hP.1 hs hE
  have hc : (((if br = cj then 1 else -1 : ℚ)) : ℝ) = sg br cj := by
    unfold sg; split_ifs <;> simp
  rwa [hc] at this

end GlobalTheory.ArchRec.EnumBlocks
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryTorusTraceFormOfHermitian
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

namespace GlobalTheory.TrEll.HermTrace

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

theorem fld_induction (P : PPol σ n) (p : Fld P → Prop) (h0 : ∀ e, p (algebraMap E (Fld P) e))
    (hadd : ∀ a b, p a → p b → p (a + b)) (hmul : ∀ a, p a → p (a * alpha P)) (l : Fld P) : p l := by
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective (g := P.1) l
  induction q using Polynomial.induction_on with
  | C a => exact h0 a
  | add a b ha hb => rw [map_add (f := _)]; exact hadd _ _ ha hb
  | monomial k a ha => rw [pow_succ, ← mul_assoc, map_mul]; exact hmul _ ha

theorem star_star (hσ : ∀ e, σ (σ e) = e) (P : PPol σ n) (l : Fld P) : star' P (star' P l) = l := by
  induction l using fld_induction with
  | h0 e => rw [star'_algebraMap, star'_algebraMap, hσ]
  | hadd a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  | hmul a ha => rw [map_mul, map_mul, ha, star'_alpha, map_inv₀, star'_alpha, inv_inv]

theorem trace_star (hσ : ∀ e, σ (σ e) = e) (P : PPol σ n) (l : Fld P) :
    Algebra.trace E (Fld P) (star' P l) = σ (Algebra.trace E (Fld P) l) := by
  let e₁ : E ≃+* E := RingEquiv.ofRingHom (σ : E →+* E) (σ : E →+* E) (RingHom.ext hσ) (RingHom.ext hσ)
  let e₂ : Fld P ≃+* Fld P := RingEquiv.ofRingHom (star' P : Fld P →+* Fld P) (star' P : Fld P →+* Fld P)
    (RingHom.ext (star_star hσ P)) (RingHom.ext (star_star hσ P))
  have h := Algebra.trace_eq_of_equiv_equiv e₁ e₂ (RingHom.ext fun e => (star'_algebraMap P e).symm) l
  have h' : Algebra.trace E (Fld P) l = σ (Algebra.trace E (Fld P) (star' P l)) := h
  rw [h', hσ]

section Form

variable {A : Type} [CommRing A] (s : A →+* A) (J : Matrix (Fin n) (Fin n) A)

theorem hform_eq (a b : Fin n → A) : Formalism.UG.hform s J a b = (s ∘ a) ⬝ᵥ (J *ᵥ b) := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_unitary (M : Matrix (Fin n) (Fin n) A) (h : Formalism.UG.cT s M * J * M = J) (a b : Fin n → A) :
    Formalism.UG.hform s J (M *ᵥ a) (M *ᵥ b) = Formalism.UG.hform s J a b := by
  have e : s ∘ (M *ᵥ a) = (s ∘ a) ᵥ* Formalism.UG.cT s M := by
    funext i
    simp [Formalism.UG.cT, Matrix.mulVec, Matrix.vecMul, dotProduct, mul_comm]
  rw [hform_eq, hform_eq, e, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

theorem hform_add_left (a a' b : Fin n → A) :
    Formalism.UG.hform s J (a + a') b = Formalism.UG.hform s J a b + Formalism.UG.hform s J a' b := by
  simp [Formalism.UG.hform, add_mul, Finset.sum_add_distrib]

theorem hform_add_right (a b b' : Fin n → A) :
    Formalism.UG.hform s J a (b + b') = Formalism.UG.hform s J a b + Formalism.UG.hform s J a b' := by
  simp [Formalism.UG.hform, mul_add, Finset.sum_add_distrib]

theorem hform_smul_left (c : A) (a b : Fin n → A) :
    Formalism.UG.hform s J (c • a) b = s c * Formalism.UG.hform s J a b := by
  simp [Formalism.UG.hform, Finset.mul_sum, mul_assoc]

theorem hform_smul_right (c : A) (a b : Fin n → A) :
    Formalism.UG.hform s J a (c • b) = c * Formalism.UG.hform s J a b := by
  simp only [Formalism.UG.hform, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_symm (hs : ∀ e, s (s e) = e) (hJ : ∀ i j, s (J j i) = J i j) (a b : Fin n → A) :
    Formalism.UG.hform s J b a = s (Formalism.UG.hform s J a b) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.UG.hform, map_sum, map_mul, hs, hJ]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_single (i j : Fin n) : Formalism.UG.hform s J (Pi.single i 1) (Pi.single j 1) = J i j := by
  simp [Formalism.UG.hform, Pi.single_apply, apply_ite s]

end Form

theorem exists_trace_form : ∀ (F E : Type) [Field F] [Field E] [CharZero E] [Algebra F E] (σ : E →ₐ[F] E), (∀ e, σ (σ e) = e) → ∀ (n : ℕ) (P : PPol σ n) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (A : Matrix (Fin n) (Fin n) E), Formalism.UG.cT (σ : E →+* E) A * J * A = J → ∀ φ : Fld P ≃ₗ[E] (Fin n → E), (∀ y, A *ᵥ φ y = φ (alpha P * y)) → ∃ x : Fld P, x ≠ 0 ∧ star' P x = x ∧ ∀ y y', Formalism.UG.hform (σ : E →+* E) J (φ y') (φ y) = Algebra.trace E (Fld P) (x * y * star' P y') := by
  intro F E _ _ _ _ σ hσ n P J hJ A hA φ hφ
  set s : E →+* E := (σ : E →+* E) with hs
  have h1 : ∀ y y', Formalism.UG.hform s J (φ (alpha P * y')) (φ (alpha P * y)) = Formalism.UG.hform s J (φ y') (φ y) :=
    fun y y' => by rw [← hφ, ← hφ, hform_unitary s J A hA]
  have h2 : ∀ l y y', Formalism.UG.hform s J (φ (l * y')) (φ y) = Formalism.UG.hform s J (φ y') (φ (star' P l * y)) := by
    intro l
    induction l using fld_induction with
    | h0 e =>
      intro y y'
      rw [star'_algebraMap, ← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_smul, hform_smul_left,
        hform_smul_right]
      rfl
    | hadd a b ha hb =>
      intro y y'
      rw [add_mul, map_add (f := _), hform_add_left, ha, hb, map_add (f := _), add_mul, map_add (f := _), hform_add_right]
    | hmul a ha =>
      intro y y'
      rw [mul_assoc, ha, map_mul (star' P), star'_alpha, ← h1 (star' P a * (alpha P)⁻¹ * y) y']
      congr 2
      field_simp [alpha_ne_zero P]
  let f : Module.Dual E (Fld P) :=
    { toFun := fun y => Formalism.UG.hform s J (φ 1) (φ y)
      map_add' := fun a b => by rw [map_add (f := _), hform_add_right]
      map_smul' := fun c a => by rw [map_smul, hform_smul_right]; rfl }
  have hnd := traceForm_nondegenerate E (Fld P)
  let x : Fld P := ((Algebra.traceForm E (Fld P)).toDual hnd).symm f
  have hx : ∀ y, Algebra.trace E (Fld P) (x * y) = Formalism.UG.hform s J (φ 1) (φ y) := fun y => by
    have := LinearMap.BilinForm.toDual_def hnd (m := x) (n := y)
    rw [Algebra.traceForm_apply] at this
    rw [← this, LinearEquiv.apply_symm_apply]
    rfl
  have h3 : ∀ y y', Formalism.UG.hform s J (φ y') (φ y) = Algebra.trace E (Fld P) (x * y * star' P y') := fun y y' => by
    rw [mul_assoc, hx, mul_comm y, ← h2, mul_one]
  refine ⟨x, fun h0 => ?_, ?_, h3⟩
  · have hn : 0 < n := P.2.2.2.1 ▸ P.2.2.1.natDegree_pos
    have hz : J = 0 := by
      ext i j
      rw [← hform_single s J i j, ← φ.apply_symm_apply (Pi.single i 1), ← φ.apply_symm_apply (Pi.single j 1), h3, h0]
      simp
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact hJ.2 (by rw [hz, Matrix.det_zero])
  · rw [← sub_eq_zero]
    refine hnd.1 _ fun z => ?_
    have a := hform_symm s J hσ hJ.1 (φ z) (φ 1)
    rw [h3, h3, map_one, mul_one, mul_one] at a
    have b := trace_star hσ P (x * star' P z)
    rw [map_mul, star_star hσ] at b
    rw [Algebra.traceForm_apply, sub_mul, map_sub, b, a, sub_eq_zero]
    rfl

end GlobalTheory.TrEll.HermTrace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnitUpperRightBlockOfHeisenbergDerivativeSolutStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_upperRightBlock_of_heisenbergDerivative_solution : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ q, (∀ x, β x q = 0) → q = 0) →
    ∀ (J : (V × V) →ₗ[ℝ] (V × V)) (g : V → ℂ), Continuous g → g ≠ 0 →
    (∀ w x, GlobalTheory.GaussLine.dHeis β (J w) g x = Complex.I * GlobalTheory.GaussLine.dHeis β w g x) →
    IsUnit (GlobalTheory.FockFamily.blockB J) := by
  first | exact @GlobalTheory.FockFamily.isUnit_blockB_of_solution | exact GlobalTheory.FockFamily.isUnit_blockB_of_solution | (intros; apply GlobalTheory.FockFamily.isUnit_blockB_of_solution <;> assumption)
end

