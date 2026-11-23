module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0155
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralTateInertiaCyclotomicTwistTorsion
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0152
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumParsevalQExpansionHorizontalLine
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

def hch (n : ℕ) (x : ℝ) : ℂ := cexp (2 * π * Complex.I * n * x)

theorem hch_norm (n : ℕ) (x : ℝ) : ‖hch n x‖ = 1 := by
  have : (2 * π * Complex.I * n * x : ℂ) = ((2 * π * n * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [hch, this, Complex.norm_exp_ofReal_mul_I]

theorem hch_cont (n : ℕ) : Continuous (hch n) := by unfold hch; fun_prop

theorem hch_orth (m n : ℕ) : ∫ x in (0 : ℝ)..1, conj (hch m x) * hch n x = if m = n then 1 else 0 := by
  have e : ∀ x : ℝ, conj (hch m x) * hch n x = cexp ((2 * π * Complex.I * ((n : ℂ) - m)) * x) := fun x => by
    rw [hch, hch, ← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_natCast, map_ofNat]
    ring
  simp only [e]
  split_ifs with h
  · simp [h]
  · have h0 : ((n : ℂ) - m) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast Ne.symm h)
    have hc : (2 * π * Complex.I * ((n : ℂ) - m)) ≠ 0 := mul_ne_zero Complex.two_pi_I_ne_zero h0
    rw [integral_exp_mul_complex hc]
    have := Complex.exp_int_mul_two_pi_mul_I ((n : ℤ) - m)
    push_cast at this
    rw [mul_comm] at this
    simp [this]

theorem hasSum_parseval_unit (a b : ℕ → ℂ) (ha : Summable fun n => ‖a n‖) (hb : Summable fun n => ‖b n‖)
    (F G : ℝ → ℂ) (hF : ∀ x, HasSum (fun n => a n * hch n x) (F x))
    (hG : ∀ x, HasSum (fun n => b n * hch n x) (G x)) :
    HasSum (fun n => conj (b n) * a n) (∫ x in (0 : ℝ)..1, conj (G x) * F x) := by
  let T : ℕ × ℕ → ℝ → ℂ := fun p x => conj (b p.1 * hch p.1 x) * (a p.2 * hch p.2 x)
  have hT : ∀ p, Continuous (T p) := fun p =>
    (Complex.continuous_conj.comp (continuous_const.mul (hch_cont p.1))).mul
      (continuous_const.mul (hch_cont p.2))
  have hn : ∀ p x, ‖T p x‖ = ‖b p.1‖ * ‖a p.2‖ := fun p x => by
    simp [T, hch_norm]
  have h := hasSum_integral_of_summable_integral_norm (μ := volume.restrict (Set.Ioc (0 : ℝ) 1)) (F := T)
    (fun p => (hT p).integrableOn_Ioc) (by
      refine (summable_mul_of_summable_norm' hb.norm hb ha.norm ha).congr fun p => ?_
      simp only [hn]
      simp)
  have hs : ∀ x, ∑' p, T p x = conj (G x) * F x := fun x => by
    have h1 : HasSum (fun n => conj (b n * hch n x)) (conj (G x)) := by
      simpa using (Complex.hasSum_conj'.2 (hG x))
    have h2 := tsum_mul_tsum_of_summable_norm h1.summable.norm (hF x).summable.norm
    rw [h1.tsum_eq, (hF x).tsum_eq] at h2
    exact h2.symm
  have hi : ∀ p, ∫ x in Set.Ioc (0 : ℝ) 1, T p x = conj (b p.1) * a p.2 * if p.1 = p.2 then 1 else 0 := fun p => by
    rw [← hch_orth, ← intervalIntegral.integral_of_le zero_le_one, ← intervalIntegral.integral_const_mul]
    congr 1
    funext x
    simp only [T, map_mul]
    ring
  simp only [hs, hi] at h
  rw [← intervalIntegral.integral_of_le zero_le_one] at h
  have hinj : Function.Injective fun n : ℕ => (n, n) := fun _ _ h => (Prod.ext_iff.1 h).1
  have := (hinj.hasSum_iff (f := fun p : ℕ × ℕ => conj (b p.1) * a p.2 * if p.1 = p.2 then 1 else 0) (fun p hp => by
    rw [if_neg, mul_zero]
    intro h
    exact hp ⟨p.1, Prod.ext rfl h⟩)).2 h
  refine cast (congrArg (HasSum · _) (funext fun n => ?_)) this
  simp

theorem qs_line (a : ℕ → ℂ) (ha : PolyB a) (y : ℝ) (hy : 0 < y) (x : ℝ) :
    HasSum (fun n : ℕ => (a n * (Real.exp (-2 * π * n * y) : ℝ)) * hch n x)
      (qs a (ofComplex (x + y * Complex.I))) := by
  have him : 0 < ((x : ℂ) + y * Complex.I).im := by simpa using hy
  have hterm : ∀ n : ℕ, a n * cexp (2 * π * Complex.I * n * (ofComplex ((x : ℂ) + y * Complex.I) : ℂ)) =
      (a n * (Real.exp (-2 * π * n * y) : ℝ)) * hch n x := fun n => by
    rw [ofComplex_apply_of_im_pos him, UpperHalfPlane.coe_mk, hch, Complex.ofReal_exp, mul_assoc (a n), ← Complex.exp_add]
    congr 2
    push_cast
    linear_combination (2 * π * n * y : ℂ) * Complex.I_mul_I
  have hs := ((_root_.GlobalTheory.EisM.qs_summable_continuous a ha).1 (ofComplex ((x : ℂ) + y * Complex.I))).of_norm
  have := hs.hasSum
  simp only [qs]
  simpa only [hterm] using this

theorem parseval_line : ∀ (h b : ℕ → ℂ) (y : ℝ), PolyB h → PolyB b → 0 < y →
    HasSum (fun n : ℕ => conj (h n) * b n * (Real.exp (-4 * π * n * y) : ℝ))
      (∫ x in (0 : ℝ)..1, conj (qs h (ofComplex (x + y * Complex.I))) * qs b (ofComplex (x + y * Complex.I))) := by
  intro h b y hh hb hy
  have sm : ∀ a : ℕ → ℂ, PolyB a → Summable fun n : ℕ => ‖a n * (Real.exp (-2 * π * n * y) : ℝ)‖ := fun a ha => by
    have := (qs_line a ha y hy 0).summable.norm
    simpa [hch_norm] using this
  have H := hasSum_parseval_unit _ _ (sm b hb) (sm h hh) _ _ (qs_line b hb y hy) (qs_line h hh y hy)
  refine cast (congrArg (HasSum · _) (funext fun n => ?_)) H
  have : Real.exp (-4 * π * n * y) = Real.exp (-2 * π * n * y) * Real.exp (-2 * π * n * y) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [this, map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
  ring

end GlobalTheory.EisM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharacterSlashSumIndepReps
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.RepInd

theorem exists_inj (L : ℕ) (Δ : Set M2) {ι κ : Type} (β : ι → M2) (β' : κ → M2)
    (hβ : LRep L Δ β) (hβ' : LRep L Δ β') :
    ∃ σ : κ → ι, Function.Injective σ ∧ ∃ g : κ → Gamma0 L,
      ∀ j, β' j = (((g j : SL(2, ℤ)) : M2)) * β (σ j) := by
  have hmem : ∀ j, ∃ p : Gamma0 L × ι, ((p.1 : SL(2, ℤ)) : M2) * β p.2 = β' j := by
    intro j
    have h1 : β' j ∈ Δ := by
      have := hβ'.mapsTo (Set.mem_univ ((1 : Gamma0 L), j))
      simpa using this
    obtain ⟨p, -, hp⟩ := hβ.surjOn h1
    exact ⟨p, hp⟩
  choose p hp using hmem
  refine ⟨fun j => (p j).2, ?_, fun j => (p j).1, fun j => (hp j).symm⟩
  intro j j' hjj
  have key : (((((p j).1 * ((p j').1)⁻¹ : Gamma0 L) : SL(2, ℤ)) : M2)) * β' j'
      = (((1 : Gamma0 L) : SL(2, ℤ)) : M2) * β' j := by
    rw [← hp j', ← hp j]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Matrix.SpecialLinearGroup.coe_mul,
      Subgroup.coe_one, Matrix.SpecialLinearGroup.coe_one, one_mul]
    simp only at hjj
    rw [hjj, ← mul_assoc, mul_assoc (((p j).1 : SL(2, ℤ)) : M2)]
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, mul_one]
  have := hβ'.injOn (Set.mem_univ (((p j).1 * ((p j').1)⁻¹), j')) (Set.mem_univ ((1 : Gamma0 L), j)) key
  exact (congrArg Prod.snd this).symm

end GlobalTheory.EisM.RepInd

namespace GlobalTheory.EisM.RepInd

theorem term_eq (k L N : ℕ) (ε : DirichletCharacter ℂ N) (β : M2) (γ : Gamma0 L) (f : ℍ → ℂ)
    (hk : 1 ≤ k) (hNL : N ∣ L) (hdet : 0 < β.det) (hN : (N : ℤ) ∣ β 1 0) (hf : Inv k L (ch ε) f) (τ : ℍ) :
    ch ε (((((γ : SL(2, ℤ)) : M2)) * β) 0 0) * slz k ((((γ : SL(2, ℤ)) : M2)) * β) f τ
      = ch ε (β 0 0) * slz k β f τ := by
  obtain ⟨hc, -, hinv, -, -⟩ := _root_.GlobalTheory.EisM.slz_props k f hk
  set g : SL(2, ℤ) := (γ : SL(2, ℤ)) with hg
  have hgL : (L : ℤ) ∣ g 1 0 := by
    have := (Gamma0_mem).1 γ.2
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this
  have hgN : (N : ℤ) ∣ g 1 0 := dvd_trans (Int.natCast_dvd_natCast.2 hNL) hgL
  have hgdet : 0 < (g : M2).det := by simp
  rw [hc _ _ hgdet hdet, (hinv L (ch ε)).1 hf g hgL]
  have hlin : slz k β (fun τ => ch ε (g 1 1) * f τ) τ = ch ε (g 1 1) * slz k β f τ := by
    simp only [slz]; ring
  rw [hlin]
  have hdetg : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.2
    rw [Matrix.det_fin_two] at this
    exact this
  have h00 : ((((g : M2)) * β) 0 0 : ZMod N) = (g 0 0 : ZMod N) * (β 0 0 : ZMod N) := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    have : ((β 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hN
    push_cast
    rw [this]; simp
  have h1 : (g 0 0 : ZMod N) * (g 1 1 : ZMod N) = 1 := by
    have : ((g 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hgN
    have h2 : ((g 0 0 * g 1 1 - g 0 1 * g 1 0 : ℤ) : ZMod N) = 1 := by rw [hdetg]; simp
    push_cast at h2
    rw [this, mul_zero, sub_zero] at h2
    exact h2
  simp only [ch]
  rw [h00, map_mul]
  have : ε (g 0 0 : ZMod N) * ε (g 1 1 : ZMod N) = 1 := by rw [← map_mul, h1, map_one]
  calc ε (g 0 0 : ZMod N) * ε (β 0 0 : ZMod N) * (ε (g 1 1 : ZMod N) * slz k β f τ)
      = (ε (g 0 0 : ZMod N) * ε (g 1 1 : ZMod N)) * (ε (β 0 0 : ZMod N) * slz k β f τ) := by ring
    _ = ε (β 0 0 : ZMod N) * slz k β f τ := by rw [this, one_mul]

theorem hsum_indep : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (Δ : Set M2) (ι κ : Type) [Fintype ι] [Fintype κ] (β : ι → M2) (β' : κ → M2) (f : ℍ → ℂ), 1 ≤ k → N ∣ L → (∀ δ ∈ Δ, 0 < δ.det ∧ (N : ℤ) ∣ δ 1 0) → LRep L Δ β → LRep L Δ β' → Inv k L (ch ε) f → hsum k (ch ε) β f = hsum k (ch ε) β' f := by
  intro k L N ε Δ ι κ _ _ β β' f hk hNL hΔ hβ hβ' hf
  obtain ⟨σ, hσ, g, hg⟩ := exists_inj L Δ β β' hβ hβ'
  obtain ⟨σ', hσ', -, -⟩ := exists_inj L Δ β' β hβ' hβ
  have hcard : Fintype.card κ = Fintype.card ι :=
    le_antisymm (Fintype.card_le_of_injective σ hσ) (Fintype.card_le_of_injective σ' hσ')
  have hbij : Function.Bijective σ := (Fintype.bijective_iff_injective_and_card σ).2 ⟨hσ, hcard⟩
  have hin : ∀ i, β i ∈ Δ := fun i => by
    have := hβ.mapsTo (Set.mem_univ ((1 : Gamma0 L), i))
    simpa using this
  funext τ
  simp only [hsum]
  symm
  refine Fintype.sum_bijective σ hbij _ _ ?_
  intro j
  rw [hg j]
  exact term_eq k L N ε (β (σ j)) (g j) f hk hNL (hΔ _ (hin _)).1 (hΔ _ (hin _)).2 hf τ

end GlobalTheory.EisM.RepInd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeSumPotentialsCocycleEq
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.DictHk

theorem mat_mul {Γ : Subgroup SL(2, ℤ)} (a b : Γ) :
    GlobalTheory.HeckeFamilyMatrices.mat ((a * b : Γ) : SL(2, ℤ)) = GlobalTheory.HeckeFamilyMatrices.mat a * GlobalTheory.HeckeFamilyMatrices.mat b := rfl

theorem mat_mul_inv {Γ : Subgroup SL(2, ℤ)} (a : Γ) :
    GlobalTheory.HeckeFamilyMatrices.mat a * GlobalTheory.HeckeFamilyMatrices.mat ((a⁻¹ : Γ) : SL(2, ℤ)) = 1 := by
  rw [← mat_mul, mul_inv_cancel]; rfl

theorem mat_one {Γ : Subgroup SL(2, ℤ)} : GlobalTheory.HeckeFamilyMatrices.mat ((1 : Γ) : SL(2, ℤ)) = 1 := rfl

theorem cancel_right {Γ : Subgroup SL(2, ℤ)} {A B : Matrix (Fin 2) (Fin 2) ℤ} (a : Γ)
    (h : A * GlobalTheory.HeckeFamilyMatrices.mat a = B * GlobalTheory.HeckeFamilyMatrices.mat a) : A = B := by
  have := congrArg (· * GlobalTheory.HeckeFamilyMatrices.mat ((a⁻¹ : Γ) : SL(2, ℤ))) h
  simpa only [Matrix.mul_assoc, mat_mul_inv, Matrix.mul_one] using this

theorem det_pos {Γ : Subgroup SL(2, ℤ)} {α : Matrix (Fin 2) (Fin 2) ℤ} {ι : Type}
    {δ : ι → Matrix (Fin 2) (Fin 2) ℤ} (hα : 0 < α.det) (hδ : GlobalTheory.HeckeFamilyMatrices.IsDCReps Γ α δ) (i : ι) :
    0 < (δ i).det := by
  obtain ⟨γ₁, γ₂, h⟩ := hδ.1 i
  rw [h, det_mul, det_mul]
  simpa using hα

theorem exists_perm {Γ : Subgroup SL(2, ℤ)} {α : Matrix (Fin 2) (Fin 2) ℤ} {ι : Type} [Fintype ι]
    {δ : ι → Matrix (Fin 2) (Fin 2) ℤ} (hδ : GlobalTheory.HeckeFamilyMatrices.IsDCReps Γ α δ) (γ : Γ) :
    ∃ π : Equiv.Perm ι, ∀ i, ∃ γ' : Γ, δ i * GlobalTheory.HeckeFamilyMatrices.mat γ = GlobalTheory.HeckeFamilyMatrices.mat γ' * δ (π i) := by
  classical
  have hf : ∀ i, ∃ j, ∃ γ' : Γ, δ i * GlobalTheory.HeckeFamilyMatrices.mat γ = GlobalTheory.HeckeFamilyMatrices.mat γ' * δ j := by
    intro i
    obtain ⟨γ₁, γ₂, h⟩ := hδ.1 i
    obtain ⟨j, ⟨γ', h'⟩, -⟩ := hδ.2 γ₁ (γ₂ * γ)
    refine ⟨j, γ', ?_⟩
    rw [h, ← h', mat_mul, Matrix.mul_assoc]
  choose f g hfg using hf
  have hinj : Function.Injective f := by
    intro i i' hii
    obtain ⟨γ₁, γ₂, h⟩ := hδ.1 i
    obtain ⟨k, -, hk⟩ := hδ.2 γ₁ γ₂
    have e1 : i = k := hk i ⟨1, by rw [mat_one, Matrix.one_mul, h]⟩
    have e2 : i' = k := by
      refine hk i' ⟨g i * (g i')⁻¹, ?_⟩
      rw [← h]
      apply cancel_right γ
      rw [hfg i, Matrix.mul_assoc, hfg i', ← hii, ← Matrix.mul_assoc, ← mat_mul, inv_mul_cancel_right]
    rw [e1, e2]
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), fun i => ⟨g i, hfg i⟩⟩

theorem incr {N l w : ℕ} {ι : Type} [Fintype ι] {δ : ι → Matrix (Fin 2) (Fin 2) ℤ}
    (hdet : ∀ i, 0 < (δ i).det) {F : ℂ → MvPolynomial (Fin 2) ℂ} (hF : F ∈ Pot ℂ w (Gam N l))
    (γ : GlobalTheory.HeckeFamilyMatrices.Lev N l) (π : Equiv.Perm ι) (g : ι → GlobalTheory.HeckeFamilyMatrices.Lev N l)
    (hg : ∀ i, δ i * GlobalTheory.HeckeFamilyMatrices.mat γ = GlobalTheory.HeckeFamilyMatrices.mat (g i) * δ (π i)) (z : ℂ) (hz : z ∈ Hs) :
    slP (GlobalTheory.HeckeFamilyMatrices.mat γ) ((∑ i, opP ℂ (δ i) F) (mob (ofSL γ) z)) - (∑ i, opP ℂ (δ i) F) z =
      ∑ i, slP (δ (π i)) (slP (GlobalTheory.HeckeFamilyMatrices.mat (g i)) (F (mob (ofSL (g i)) Complex.I)) - F Complex.I) := by
  obtain ⟨hmem, hmul, -, -, hSL, htoGQ⟩ := GlobalTheory.KZ.mob_laws
  obtain ⟨hslmul, -⟩ := GlobalTheory.KZ.polySlash_laws ℂ
  have hI : Complex.I ∈ Hs := by simp [Hs]
  have h1 : ∀ a : GlobalTheory.HeckeFamilyMatrices.Lev N l, 0 < (GlobalTheory.HeckeFamilyMatrices.mat a).det := fun a => by simp
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_apply, map_sum]
  rw [← Equiv.sum_comp π (fun i => opP ℂ (δ i) F z), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨p, hp⟩ := hF.2 (g i) (g i).2
  have hz' := hmem (toGQ (δ (π i))) z hz
  rw [hp _ hI, ← hp _ hz']
  simp only [opP, LinearMap.coe_mk, AddHom.coe_mk, map_sub]
  rw [sub_left_inj]
  have hL : mob (toGQ (δ i)) (mob (ofSL γ) z) = mob (toGQ (δ i * GlobalTheory.HeckeFamilyMatrices.mat γ)) z := by
    rw [htoGQ _ _ (hdet i) (h1 γ), hSL, hmul _ _ _ hz]
  have hR : mob (ofSL (g i)) (mob (toGQ (δ (π i))) z) =
      mob (toGQ (GlobalTheory.HeckeFamilyMatrices.mat (g i) * δ (π i))) z := by
    rw [htoGQ _ _ (h1 (g i)) (hdet (π i)), hSL, hmul _ _ _ hz]
  have hs1 := hslmul (δ i) (GlobalTheory.HeckeFamilyMatrices.mat γ) (F (mob (toGQ (δ i * GlobalTheory.HeckeFamilyMatrices.mat γ)) z))
  have hs2 := hslmul (GlobalTheory.HeckeFamilyMatrices.mat (g i)) (δ (π i)) (F (mob (toGQ (GlobalTheory.HeckeFamilyMatrices.mat (g i) * δ (π i))) z))
  rw [hL, hR, ← hs1, ← hs2, hg i]

theorem dict_hk : ∀ (N l w : ℕ) (α : Matrix (Fin 2) (Fin 2) ℤ) (ι : Type) [Fintype ι]
    (δ : ι → Matrix (Fin 2) (Fin 2) ℤ), 0 < N → 0 < l → 0 < α.det →
    GlobalTheory.HeckeFamilyMatrices.IsDCReps (GlobalTheory.HeckeFamilyMatrices.Lev N l) α δ → ∀ F ∈ Pot ℂ w (Gam N l),
    (∑ i, opP ℂ (δ i) F) ∈ Pot ℂ w (Gam N l) ∧
      cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) (∑ i, opP ℂ (δ i) F) =
        GlobalTheory.HeckeFamilyMatrices.hk (GlobalTheory.HeckeFamilyMatrices.Lev N l) w δ (cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F) := by
  intro N l w α ι _ δ _ _ hα hδ F hF
  have hdet := det_pos hα hδ
  obtain ⟨-, -, hslhom, -⟩ := GlobalTheory.KZ.polySlash_laws ℂ
  have hI : Complex.I ∈ Hs := by simp [Hs]
  refine ⟨⟨fun z => ?_, fun γ hγ => ?_⟩, ?_⟩
  · simp only [Finset.sum_apply]
    exact MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => hslhom _ w _ (hF.1 _)
  · obtain ⟨π, hπ⟩ := exists_perm hδ (⟨γ, hγ⟩ : GlobalTheory.HeckeFamilyMatrices.Lev N l)
    choose g hg using hπ
    exact ⟨_, fun z hz => incr hdet hF ⟨γ, hγ⟩ π g hg z hz⟩
  · funext γ
    have hex := exists_perm hδ γ
    simp only [GlobalTheory.HeckeFamilyMatrices.hk, LinearMap.pi_apply, dif_pos hex, LinearMap.sum_apply, Finset.sum_apply,
      LinearMap.comp_apply, LinearMap.proj_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [cocP, incr hdet hF γ hex.choose (fun i => (hex.choose_spec i).choose)
      (fun i => (hex.choose_spec i).choose_spec) _ hI, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(_root_.GlobalTheory.KZ.H3.deh_homog_iso w).1 _ _ ((hslhom _ w _ (hF.1 _)).sub (hF.1 _))]
    rfl

end GlobalTheory.KZ.DictHk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnImRpowUnitStripBelowOne
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem stripLow_integrableOn_im_rpow : ∀ (s : ℝ), 0 < s →
    IntegrableOn (fun τ : ℍ => τ.im ^ (s + 1)) {τ | τ ∈ strip ∧ τ.im < 1} := by
  intro s hs
  have hmeasIm : Measurable (fun τ : ℍ => τ.im) := UpperHalfPlane.continuous_im.measurable
  have hf : Measurable (fun τ : ℍ => τ.im ^ (s + 1)) := hmeasIm.pow_const _
  have hT : MeasurableSet {τ : ℍ | τ.im < 1} := measurableSet_lt hmeasIm measurable_const
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  set F : ℍ → ENNReal := Set.indicator {τ : ℍ | τ.im < 1} (fun τ => ‖τ.im ^ (s + 1)‖ₑ) with hFdef
  have hFm : Measurable F := hf.enorm.indicator hT
  have h1 : ∫⁻ τ in {τ | τ ∈ strip ∧ τ.im < 1}, ‖τ.im ^ (s + 1)‖ₑ = ∫⁻ τ in strip, F τ := by
    rw [hFdef, lintegral_indicator hT, Measure.restrict_restrict hT]
    congr 2
    ext τ
    simp [and_comm]
  rw [h1, (_root_.GlobalTheory.EisM.strip_iterated).1 F hFm]
  have h2 : ∀ y ∈ Set.Ioi (0:ℝ), (∫⁻ x in Set.Ico (0 : ℝ) 1, F (ofComplex (x + y * Complex.I))) *
      ENNReal.ofReal (1 / y ^ 2) = Set.indicator (Set.Iio 1) (fun y : ℝ => ENNReal.ofReal (y ^ (s - 1))) y := by
    intro y hy
    have hy0 : (0:ℝ) < y := hy
    have him : ∀ x : ℝ, (ofComplex ((x:ℂ) + y * Complex.I)).im = y := by
      intro x
      rw [ofComplex_apply_of_im_pos (by simpa using hy0)]
      simp [UpperHalfPlane.im]
    have hin : ∀ x : ℝ, F (ofComplex ((x:ℂ) + y * Complex.I)) =
        Set.indicator (Set.Iio 1) (fun y : ℝ => ENNReal.ofReal (y ^ (s + 1))) y := by
      intro x
      simp only [hFdef, Set.indicator, Set.mem_setOf_eq, him, Set.mem_Iio]
      split_ifs
      · exact Real.enorm_eq_ofReal (Real.rpow_nonneg hy0.le _)
      · rfl
    simp_rw [hin]
    rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ico]
    simp only [sub_zero, ENNReal.ofReal_one, mul_one]
    by_cases h : y < 1
    · simp only [Set.indicator, Set.mem_Iio, h, if_true]
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hy0.le _)]
      congr 1
      have : y ^ (s + 1) = y ^ (s - 1) * y ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hy0]; norm_num; ring_nf
      rw [this]; field_simp
    · simp [Set.indicator, h]
  rw [setLIntegral_congr_fun measurableSet_Ioi h2, lintegral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio, Set.Iio_inter_Ioi]
  have hI : IntegrableOn (fun y : ℝ => y ^ (s - 1)) (Set.Ioo 0 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by linarith)
  exact hI.lintegral_lt_top

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralTateInertiaCyclotomicTwistTorsionStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.KZ GlobalTheory.Glue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_tate_inertia_cyclotomic_twist_torsion : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 →
  ∀ (j : ℕ), 1 ≤ j → ∀ F : Finset Ω, ∃ c : ℕ, ∀ (n : ℕ) (x : Ω), x ∈ A →
  (∀ s ∈ Ine (F := ℚ) A, (∀ y ∈ F, s y = y) → CgA A l n (s x) ((((cycMod ℚ Ω l n s : ZMod (l ^ n)).val : ℕ) : Ω) ^ j * x)) →
  CgA A l n ((l : Ω) ^ c * x) 0 := by
  first | exact @GlobalTheory.IntTate.integral_tate_inertia | exact GlobalTheory.IntTate.integral_tate_inertia | (intros; apply GlobalTheory.IntTate.integral_tate_inertia <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsRightGamma0CosetDecompositionHeckeUStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRightGamma0CosetDecomposition_heckeU : ∀ L l : ℕ, 0 < L → l.Prime → l ∣ L → RRep L (DU L l) (fun j : Fin l => (repL L l (some j)).adjugate) := by
  first | exact @GlobalTheory.EisM.RightRepU.rrep | exact GlobalTheory.EisM.RightRepU.rrep | (intros; apply GlobalTheory.EisM.RightRepU.rrep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerIntegerDecompositionByTauStatement
section
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerTower_integer_decomposition_by_tau : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo (p := p) Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ (N : ℕ) (y : Ω), IsInt (p := p) y →
    (∀ g ∈ Ggeo (p := p) Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g y = y) →
  ∃ o w : Ω, IsInt (p := p) o ∧ (∀ g ∈ Ggeo (p := p) Ω, g o = o) ∧ IsInt (p := p) w ∧
    (∀ g ∈ Ggeo (p := p) Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g w = w) ∧
    (T.ζ 1 - 1) * y = (T.ζ 1 - 1) * o + (τ w - w) := by
  first | exact @GlobalTheory.K5.Decomp.decomp | exact GlobalTheory.K5.Decomp.decomp | (intros; apply GlobalTheory.K5.Decomp.decomp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIntModuleFiniteOfSeparatedOfFiniteQuotientA
section
namespace GlobalTheory

theorem padicInt_module_finite_of_separated_of_finite_quotient (l : ℕ) [Fact l.Prime] (X : Type)
    [AddCommGroup X] [Module ℤ_[l] X]
    (hfin : Finite (X ⧸ LinearMap.range (LinearMap.lsmul ℤ_[l] X ((l : ℤ_[l]) ^ 1))))
    (hsep : ∀ x : X, (∀ r : ℕ, ∃ y, (l : ℤ_[l]) ^ r • y = x) → x = 0) :
    Module.Finite ℤ_[l] X := by
  have hI : IsLocalRing.maximalIdeal ℤ_[l] = Ideal.span {(l : ℤ_[l])} :=
    PadicInt.maximalIdeal_eq_span_p
  have : IsHausdorff (IsLocalRing.maximalIdeal ℤ_[l]) X := by
    refine ⟨fun x hx => hsep x fun r => ?_⟩
    have h := hx r
    rw [SModEq.zero, hI, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at h
    obtain ⟨y, -, hy⟩ := h
    exact ⟨y, hy⟩
  have hE : (IsLocalRing.maximalIdeal ℤ_[l] • ⊤ : Submodule ℤ_[l] X) =
      LinearMap.range (LinearMap.lsmul ℤ_[l] X ((l : ℤ_[l]) ^ 1)) := by
    ext x
    rw [hI, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    simp [LinearMap.mem_range]
  have : Module.Finite ℤ_[l] (X ⧸ (IsLocalRing.maximalIdeal ℤ_[l] • ⊤ : Submodule ℤ_[l] X)) := by
    rw [hE]
    exact Module.Finite.of_finite
  exact finite_of_isHausdorff_of_finite_quotient (IsLocalRing.maximalIdeal ℤ_[l]) X

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumSlTwoSmulStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularizedEisensteinLatticeSum_slTwo_smul : ∀ (j L : ℕ) (v : ℤ × ℤ) (Φ Φ' : ℤ × ℤ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ), (∀ x : ℤ × ℤ, Φ' (x.1 * γ 0 0 + x.2 * γ 1 0, x.1 * γ 0 1 + x.2 * γ 1 1) = Φ x) → lat j 0 L v Φ (γ • τ) = (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ^ j * lat j 0 L (v.1 * γ 0 0 + v.2 * γ 1 0, v.1 * γ 0 1 + v.2 * γ 1 1) Φ' τ := by
  first | exact @GlobalTheory.EisM.lat_smul | exact GlobalTheory.EisM.lat_smul | (intros; apply GlobalTheory.EisM.lat_smul <;> assumption)
end

