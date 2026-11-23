module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RhoThreeOfOfDeterminantCharacterFiniteOrderType
section
noncomputable section

namespace GlobalTheory.KerJ.RhoThree

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.Host GlobalTheory.KerJ NumberField Classical

theorem embT_mem (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : embT D τ x ∈ Qbar := by
  have hx : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
  have : IsAlgebraic ℚ ((embT D τ).toRatAlgHom x) := hx.algHom _
  exact (mem_algebraicClosure_iff).2 this

theorem norm_emb_unitary (D : D7) (φ : D.host.E →+* ℂ) (z : letI := D.host.cmStar; unitary D.host.E) :
    ‖φ (z : D.host.E)‖ = 1 := by
  let := D.host.cmStar
  have : IsCMField D.host.E := D.host.isCMField_hostE
  have h1 : star (z : D.host.E) * (z : D.host.E) = 1 := z.2.1
  have h2 : φ (star (z : D.host.E)) = starRingEnd ℂ (φ (z : D.host.E)) :=
    IsCMField.complexEmbedding_complexConj D.host.E φ _
  have h3 : starRingEnd ℂ (φ (z : D.host.E)) * φ (z : D.host.E) = 1 := by
    rw [← h2, ← map_mul, h1, map_one]
  have h4 : ‖φ (z : D.host.E)‖ * ‖φ (z : D.host.E)‖ = 1 := by
    have := congrArg norm h3
    rwa [norm_mul, RCLike.norm_conj, norm_one] at this
  nlinarith [norm_nonneg (φ (z : D.host.E))]

theorem algebraic_modulus_one_of_finiteOrder_char (D : D7) (ρ : D.Dt →* ℂˣ) (s : D.what₂.Tau → ℤ) (t : D.Dt) (h : ℕ)
    (z : letI := D.host.cmStar; unitary D.host.E) (hp : PowRat D t h z)
    (hU : ∀ k ∈ D.UO, ∃ n : ℕ, 0 < n ∧ ρ k ^ n = 1)
    (hz : ((ρ (D.e1Dt z) : ℂˣ) : ℂ) = ∏ τ, (embT D τ (z : D.host.E)) ^ (s τ)) :
    Mod1E ((ρ t : ℂˣ) : ℂ) := by
  obtain ⟨h0, k, hk, e⟩ := hp
  obtain ⟨n, hn, h1⟩ := hU k hk
  have e1 : ρ t ^ (h * n) = ρ (D.e1Dt z) ^ n := by
    rw [pow_mul, ← map_pow, e, map_mul, mul_pow, h1, mul_one]
  have e2 : ((ρ t : ℂˣ) : ℂ) ^ (h * n) = (∏ τ, (embT D τ (z : D.host.E)) ^ (s τ)) ^ n := by
    rw [← hz, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, e1]
  have hpos : 0 < h * n := Nat.mul_pos h0 hn
  have hw : (∏ τ, (embT D τ (z : D.host.E)) ^ (s τ)) ∈ Qbar :=
    prod_mem fun τ _ => zpow_mem (embT_mem D τ _) _
  have hm : ((ρ t : ℂˣ) : ℂ) ∈ Qbar := by
    have h2 : ((ρ t : ℂˣ) : ℂ) ^ (h * n) ∈ Qbar := e2 ▸ pow_mem hw n
    exact (mem_algebraicClosure_iff).2 (((mem_algebraicClosure_iff).1 h2).of_pow hpos)
  refine ⟨hm, fun r => ?_⟩
  have e3 : (⟨((ρ t : ℂˣ) : ℂ), hm⟩ : Qbar) ^ (h * n) =
      (∏ τ, (⟨embT D τ (z : D.host.E), embT_mem D τ _⟩ : Qbar) ^ (s τ)) ^ n := by
    apply Subtype.ext
    push_cast
    exact e2
  have h3 : ‖r ⟨((ρ t : ℂˣ) : ℂ), hm⟩‖ ^ (h * n) = 1 := by
    rw [← norm_pow, ← map_pow, e3, map_pow, map_prod, norm_pow, norm_prod]
    rw [Finset.prod_eq_one, one_pow]
    intro τ _
    have h4 := norm_emb_unitary D (r.comp ((embT D τ).codRestrict Qbar (embT_mem D τ))) z
    rw [map_zpow₀, norm_zpow, show r ⟨embT D τ (z : D.host.E), embT_mem D τ _⟩ =
      (r.comp ((embT D τ).codRestrict Qbar (embT_mem D τ))) (z : D.host.E) from rfl, h4, one_zpow]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hpos.ne').1 h3

theorem zpow_hom_apply {G : Type*} [CommGroup G] (f : G →* ℂˣ) (a : ℤ) (x : G) : (f ^ a) x = f x ^ a :=
  map_zpow (MonoidHom.eval x) f a

theorem half_cast (R : Ranks) (j : ℕ) : (((R.N j / 2 : ℕ) : ℤ) : ℚ) = (R.N j : ℚ) / 2 := by
  obtain ⟨a, ha⟩ : Even (R.N j) := R.k_even.add (R.t_odd.add_one.mul_left j)
  have h1 : R.N j / 2 = a := by omega
  rw [h1, ha]
  push_cast
  ring

theorem prod_type {ι : Type*} [Fintype ι] (x : ι → ℂ) (hx : ∀ τ, x τ ≠ 0) (e : ι → ℤ) (b c : ℤ) :
    (∏ τ, x τ ^ e τ) ^ b * (∏ τ, (x τ)⁻¹) ^ c = ∏ τ, x τ ^ (b * e τ - c) := by
  rw [← Finset.prod_zpow, ← Finset.prod_zpow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← zpow_mul, inv_zpow, ← zpow_neg, mul_comm (e τ) b, sub_eq_add_neg, zpow_add₀ (hx τ)]

theorem emb_ne (D : D7) (τ : D.what₂.Tau) (z : letI := D.host.cmStar; unitary D.host.E) :
    embT D τ (z : D.host.E) ≠ 0 := by
  intro h0
  have := norm_emb_unitary D (embT D τ) z
  rw [h0, norm_zero] at this
  exact zero_ne_one this

theorem rhoThreeOf_of_mtType : ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (mt : ℕ → D.Dt →* ℂˣ),
    MtType u mt → rhoThreeOf D C mt := by
  intro D u C mt hT i hi
  obtain ⟨hU, e, he, hz⟩ := hT i hi
  have eS : ∀ τ, C.sSharp i τ = e τ - ((D.R.N (i + 1) / 2 : ℕ) : ℤ) := fun τ => by
    apply Int.cast_injective (α := ℚ)
    rw [C.sSharp_eq i hi τ, Int.cast_sub, he τ, half_cast]
    simp only [sExp']
  have eD : ∀ τ, C.sDiv i τ = e τ - ((D.R.N i / 2 : ℕ) : ℤ) := fun τ => by
    apply Int.cast_injective (α := ℚ)
    rw [C.sDiv_eq i hi τ, Int.cast_sub, he τ, half_cast]
    simp only [sExp, Nat.add_sub_cancel]
  have hk : ∀ k ∈ D.UO, rhoOf D mt i k = (mt (i + 1) k)⁻¹ ∧ rhoOf' D mt i k = mt (i + 1) k := fun k hk => by
    constructor
    · simp [rhoOf, zpow_hom_apply, D.chiD_UO k hk]
    · simp [rhoOf', zpow_hom_apply, D.chiD_UO k hk]
  have hV : ∀ z : (letI := D.host.cmStar; unitary D.host.E),
      ((rhoOf D mt i (D.e1Dt z) : ℂˣ) : ℂ) = ∏ τ, (embT D τ (z : D.host.E)) ^ (-C.sSharp i τ) ∧
      ((rhoOf' D mt i (D.e1Dt z) : ℂˣ) : ℂ) = ∏ τ, (embT D τ (z : D.host.E)) ^ (C.sDiv i τ) := fun z => by
    have hc : ((D.chiD (D.e1Dt z) : ℂˣ) : ℂ) = ∏ τ, (embT D τ (z : D.host.E))⁻¹ := D.rest_detCharacter_on_unitary_eq z
    constructor
    · have h1 := prod_type (fun τ => embT D τ (z : D.host.E)) (fun τ => emb_ne D τ z) e (-1)
        (-((D.R.N (i + 1) / 2 : ℕ) : ℤ))
      simp only [rhoOf, MonoidHom.mul_apply, zpow_hom_apply, Units.val_mul, Units.val_zpow_eq_zpow_val, MonoidHom.inv_apply,
        Units.val_inv_eq_inv_val, hc, hz z]
      rw [← zpow_neg_one, h1]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [eS τ]
      congr 1
      ring
    · have h1 := prod_type (fun τ => embT D τ (z : D.host.E)) (fun τ => emb_ne D τ z) e 1
        (((D.R.N i / 2 : ℕ) : ℤ))
      simp only [rhoOf', MonoidHom.mul_apply, zpow_hom_apply, Units.val_mul, Units.val_zpow_eq_zpow_val, hc, hz z]
      rw [← zpow_one (∏ τ, embT D τ (z : D.host.E) ^ e τ), h1]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [eD τ]
      congr 1
      ring
  have hU1 : ∀ k ∈ D.UO, ∃ n : ℕ, 0 < n ∧ rhoOf D mt i k ^ n = 1 := fun k hk' => by
    obtain ⟨n, hn, h1⟩ := hU k hk'
    exact ⟨n, hn, by rw [(hk k hk').1, inv_pow, h1, inv_one]⟩
  have hU2 : ∀ k ∈ D.UO, ∃ n : ℕ, 0 < n ∧ rhoOf' D mt i k ^ n = 1 := fun k hk' => by
    obtain ⟨n, hn, h1⟩ := hU k hk'
    exact ⟨n, hn, by rw [(hk k hk').2, h1]⟩
  refine ⟨fun t h z hp => ⟨algebraic_modulus_one_of_finiteOrder_char D _ _ t h z hp hU1 (hV z).1, algebraic_modulus_one_of_finiteOrder_char D _ _ t h z hp hU2 (hV z).2⟩, fun k hk' => ?_, hV⟩
  obtain ⟨n, hn, h1⟩ := hU k hk'
  exact ⟨n, hn, by rw [(hk k hk').1, inv_pow, h1, inv_one], by rw [(hk k hk').2, h1]⟩

end GlobalTheory.KerJ.RhoThree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightedFibreSumsEq
section
open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial

namespace GlobalTheory
namespace OrbitDoubleCount

def transporterEquiv {Γ Y : Type} [Group Γ] [MulAction Γ Y] (v : Y) (δ : Γ) :
    {γ : Γ // γ • (δ • v) = v} ≃ MulAction.stabilizer Γ v where
  toFun γ := ⟨γ.1 * δ, by rw [MulAction.mem_stabilizer_iff, mul_smul]; exact γ.2⟩
  invFun s := ⟨s.1 * δ⁻¹, by
    rw [mul_smul, inv_smul_smul]; exact MulAction.mem_stabilizer_iff.mp s.2⟩
  left_inv γ := by ext; simp
  right_inv s := by ext; simp

theorem transporter_isEmpty {Γ Y : Type} [Group Γ] [MulAction Γ Y] (u v : Y)
    (h : u ∉ MulAction.orbit Γ v) : IsEmpty {γ : Γ // γ • u = v} :=
  ⟨fun γ => h ⟨γ.1⁻¹, by
    show γ.1⁻¹ • v = u
    rw [inv_smul_eq_iff]; exact γ.2.symm⟩⟩

theorem transporter_finite {Γ Y : Type} [Group Γ] [MulAction Γ Y] (u v : Y)
    [Finite (MulAction.stabilizer Γ v)] : Finite {γ : Γ // γ • u = v} := by
  by_cases h : u ∈ MulAction.orbit Γ v
  · obtain ⟨δ, rfl⟩ := h
    exact Finite.of_equiv _ (transporterEquiv v δ).symm
  · haveI := transporter_isEmpty u v h
    infer_instance

theorem sum_transporter {Γ Y I' : Type} [Group Γ] [MulAction Γ Y] [Fintype I'] (y : I' → Y)
    (hy : ∀ u : Y, ∃! i, u ∈ MulAction.orbit Γ (y i))
    (hf : ∀ i, Finite (MulAction.stabilizer Γ (y i))) (u : Y) :
    ∑ j, ((Nat.card (MulAction.stabilizer Γ (y j)) : ℂ))⁻¹ *
      (Nat.card {γ : Γ // γ • u = y j} : ℂ) = 1 := by
  obtain ⟨j, hj, huniq⟩ := hy u
  rw [Finset.sum_eq_single j]
  · obtain ⟨δ, rfl⟩ := hj
    haveI := hf j
    have h1 : Nat.card {γ : Γ // γ • (δ • y j) = y j} = Nat.card (MulAction.stabilizer Γ (y j)) :=
      Nat.card_congr (transporterEquiv (y j) δ)
    have h2 : (Nat.card (MulAction.stabilizer Γ (y j)) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := MulAction.stabilizer Γ (y j))).ne'
    show _ * (Nat.card {γ : Γ // γ • (δ • y j) = y j} : ℂ) = 1
    rw [h1, inv_mul_cancel₀ h2]
  · intro k _ hk
    haveI := transporter_isEmpty (Γ := Γ) u (y k) (fun h => hk (huniq k h))
    simp
  · simp

def pairEquiv {Γ X Y Z : Type} [Group Γ] [MulAction Γ Y] (p : Z → X) (q : Z → Y) (x₀ : X) (y₀ : Y) :
    (Σ z : {z | p z = x₀}, {γ : Γ // γ • q z.1 = y₀}) ≃
      {t : Z × Γ // p t.1 = x₀ ∧ t.2 • q t.1 = y₀} where
  toFun s := ⟨(s.1.1, s.2.1), s.1.2, s.2.2⟩
  invFun t := ⟨⟨t.1.1, t.2.1⟩, ⟨t.1.2, t.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem fibre_sum {Γ X Y Z I' : Type} [Group Γ] [MulAction Γ Y] [Fintype I']
    (p : Z → X) (q : Z → Y) (x₀ : X) (y : I' → Y) (φ : Z → ℂ)
    (hy : ∀ u : Y, ∃! i, u ∈ MulAction.orbit Γ (y i))
    (hf : ∀ i, Finite (MulAction.stabilizer Γ (y i))) (hx : {z | p z = x₀}.Finite) :
    ∑ᶠ z ∈ {z | p z = x₀}, φ z = ∑ j, ((Nat.card (MulAction.stabilizer Γ (y j)) : ℂ))⁻¹ *
      ∑ᶠ t : {t : Z × Γ // p t.1 = x₀ ∧ t.2 • q t.1 = y j}, φ t.1.1 := by
  haveI : Fintype {z | p z = x₀} := hx.fintype
  have key : ∀ j, ∑ᶠ t : {t : Z × Γ // p t.1 = x₀ ∧ t.2 • q t.1 = y j}, φ t.1.1 =
      ∑ z : {z | p z = x₀}, (Nat.card {γ : Γ // γ • q z.1 = y j} : ℂ) * φ z.1 := by
    intro j
    haveI := hf j
    haveI : ∀ z : {z | p z = x₀}, Fintype {γ : Γ // γ • q z.1 = y j} := fun z =>
      @Fintype.ofFinite _ (transporter_finite _ _)
    rw [← finsum_comp_equiv (pairEquiv p q x₀ (y j)), finsum_eq_sum_of_fintype, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun z _ => ?_
    show ∑ _γ : {γ : Γ // γ • q z.1 = y j}, φ z.1 = _
    rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, nsmul_eq_mul]
  simp_rw [key, Finset.mul_sum]
  rw [Finset.sum_comm, ← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, sum_transporter y hy hf, one_mul]

def swapEquiv {Γ X Y Z : Type} [Group Γ] [MulAction Γ X] [MulAction Γ Y] [MulAction Γ Z]
    (p : Z → X) (q : Z → Y) (hp : ∀ (γ : Γ) z, p (γ • z) = γ • p z)
    (hq : ∀ (γ : Γ) z, q (γ • z) = γ • q z) (x₀ : X) (y₀ : Y) :
    {t : Z × Γ // p t.1 = x₀ ∧ t.2 • q t.1 = y₀} ≃ {t : Z × Γ // q t.1 = y₀ ∧ t.2 • p t.1 = x₀} where
  toFun t := ⟨(t.1.2 • t.1.1, t.1.2⁻¹), by rw [hq]; exact t.2.2, by
    show t.1.2⁻¹ • p (t.1.2 • t.1.1) = x₀
    rw [hp, inv_smul_smul]; exact t.2.1⟩
  invFun t := ⟨(t.1.2 • t.1.1, t.1.2⁻¹), by rw [hp]; exact t.2.2, by
    show t.1.2⁻¹ • q (t.1.2 • t.1.1) = y₀
    rw [hq, inv_smul_smul]; exact t.2.1⟩
  left_inv t := by ext <;> simp
  right_inv t := by ext <;> simp

end OrbitDoubleCount


open OrbitDoubleCount in
theorem weighted_fibre_sums_eq : ∀ {Γ X Y Z I I' : Type} [Group Γ] [MulAction Γ X] [MulAction Γ Y] [MulAction Γ Z] [Fintype I] [Fintype I'] (p : Z → X) (q : Z → Y) (x : I → X) (y : I' → Y) (φ : Z → ℂ), (∀ (γ : Γ) z, p (γ • z) = γ • p z) → (∀ (γ : Γ) z, q (γ • z) = γ • q z) → (∀ u : X, ∃! i, u ∈ MulAction.orbit Γ (x i)) → (∀ u : Y, ∃! i, u ∈ MulAction.orbit Γ (y i)) → (∀ i, Finite (MulAction.stabilizer Γ (x i))) → (∀ i, Finite (MulAction.stabilizer Γ (y i))) → (∀ i, {z | p z = x i}.Finite) → (∀ i, {z | q z = y i}.Finite) → (∀ (γ : Γ) z, φ (γ • z) = φ z) → ∑ i, ((Nat.card (MulAction.stabilizer Γ (x i)) : ℂ))⁻¹ * ∑ᶠ z ∈ {z | p z = x i}, φ z = ∑ i, ((Nat.card (MulAction.stabilizer Γ (y i)) : ℂ))⁻¹ * ∑ᶠ z ∈ {z | q z = y i}, φ z := by
  intro Γ X Y Z I I' _ _ _ _ _ _ p q x y φ hp hq hx hy fx fy gx gy hφ
  have h1 := fun i => fibre_sum p q (x i) y φ hy fy (gx i)
  have h2 := fun j => fibre_sum q p (y j) x φ hx fx (gy j)
  simp_rw [h1, h2, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [mul_left_comm]
  congr 2
  rw [← finsum_comp_equiv (swapEquiv p q hp hq (x i) (y j))]
  exact finsum_congr fun t => (hφ _ _).symm

end GlobalTheory
end

