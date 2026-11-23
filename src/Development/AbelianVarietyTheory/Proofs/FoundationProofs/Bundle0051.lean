module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.EqZeroOrSingleOfDegreeLtTwo
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUOperatorPreservesModularFormGamma1InterGamma0
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem isBoundedAt_finsetSum {ι : Type*} (s : Finset ι) (c : OnePoint ℝ) (k : ℤ) {F : ι → ℍ → ℂ}
    (h : ∀ i ∈ s, c.IsBoundedAt (F i) k) : c.IsBoundedAt (∑ i ∈ s, F i) k := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro g _
    rw [Finset.sum_empty, SlashAction.zero_slash]
    exact zero_form_isBoundedAtImInfty
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem uOp_modularForm : ∀ (N l q : ℕ) (k : ℤ), 0 < N → 0 < l → q.Prime → q ∣ N * l →
    ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k, ∃ g : ModularForm (GlobalTheory.Hk.lev N l) k,
      ⇑g = GlobalTheory.Hk.uOp q ⇑f := by
  intro N l q k hN hl hq hqd f
  have hq0 : 0 < q := hq.pos
  have hinv : ∀ γ ∈ lev N l, (⇑f) ∣[k] γ = ⇑f := fun γ hγ => by
    rw [SL_slash]; exact f.slash_action_eq' _ ⟨γ, hγ, rfl⟩
  have hU := _root_.GlobalTheory.Hk.uOp_slash_lev N l q k (⇑f) hN hl hq hqd hinv
  refine ⟨{ toFun := uOp q ⇑f
            slash_action_eq' := ?_
            holo' := (_root_.GlobalTheory.Hk.hecke_mdiff q k 1 (⇑f) hq0 f.holo').1
            bdd_at_cusps' := ?_ }, rfl⟩
  · intro γ hγ
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hγ
    have := hU s hs
    rw [SL_slash] at this
    exact this
  · intro c hc
    rw [_root_.GlobalTheory.Hk.uOp_eq_sum_slash q k (⇑f) hq0]
    exact isBoundedAt_finsetSum _ c k fun j _ => _root_.GlobalTheory.Hk.slash_rat_isBoundedAt N l k _ hN hl (by
      simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.det_fin_two_of]; exact_mod_cast hq0) f c hc

end GlobalTheory.Hk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergIntertwiningSumCompOfIntermediateLatti
section
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

theorem sumOp_comp_of_between : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ (A B C : Submodule R X), SelfDual γ A → SelfDual γ B → SelfDual γ C → idx A B ≠ 0 → idx B C ≠ 0 → B ≤ (B ⊓ A) ⊔ (B ⊓ C) → idx A C = idx A B * idx B C ∧ ∀ v, Fixes W A v → sumOp W B C (sumOp W A B v) = sumOp W A C v := by
  intro R X M _ _ _ _ _ σ w γ W h A B C hA hB hC hAB hBC hle
  have hdec : ∀ b ∈ B, ∃ c, c ∈ B ∧ c ∈ C ∧ b - c ∈ A := by
    intro b hb
    obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.1 (hle hb)
    exact ⟨c, hc.1, hc.2, by simpa using ha.2⟩
  have hAC : ∀ x, x ∈ A → x ∈ C → x ∈ B := by
    intro x hxA hxC
    refine (hB x).2 fun b hb => ?_
    obtain ⟨c, -, hcC, hcA⟩ := hdec b hb
    have e : b = (b - c) + c := by abel
    rw [e, h.add_right, h.iso hA hxA hcA, h.iso hC hxC hcC, one_mul]
  obtain ⟨tAB, tAB2, -⟩ := GlobalTheory.FinWeil.sumOp_transversal h A B hB
  obtain ⟨tBC, tBC2, -⟩ := GlobalTheory.FinWeil.sumOp_transversal h B C hC
  obtain ⟨tAC, -, -⟩ := GlobalTheory.FinWeil.sumOp_transversal h A C hC
  obtain ⟨⟨n, f0, hf0B, hf0⟩, hfix, -⟩ := tAB2 hAB
  obtain ⟨⟨m, g, hgC, hg⟩, -, -⟩ := tBC2 hBC
  choose f hfB hfC hfA using fun i => hdec (f0 i) (hf0B i)
  have hf : ∀ b ∈ B, ∃! i, b - f i ∈ A := by
    intro b hb
    have key : ∀ i, b - f i ∈ A ↔ b - f0 i ∈ A := by
      intro i
      have e : b - f i = (b - f0 i) + (f0 i - f i) := by abel
      rw [e]
      exact A.add_mem_iff_left (hfA i)
    simp only [key]
    exact hf0 b hb
  have hkC : ∀ p : Fin m × Fin n, g p.1 + f p.2 ∈ C := fun p => C.add_mem (hgC _) (hfC _)
  have hk : ∀ x ∈ C, ∃! p : Fin m × Fin n, x - (g p.1 + f p.2) ∈ A := by
    intro x hx
    obtain ⟨j, hj, hju⟩ := hg x hx
    obtain ⟨i, hi, hiu⟩ := hf _ hj
    refine ⟨(j, i), by simpa [sub_add_eq_sub_sub] using hi, ?_⟩
    rintro ⟨j', i'⟩ hp
    have hp' : x - (g j' + f i') ∈ A := hp
    have h1 : x - (g j' + f i') ∈ B := hAC _ hp' (C.sub_mem hx (hkC (j', i')))
    have h2 : x - g j' ∈ B := by
      have e : x - g j' = (x - (g j' + f i')) + f i' := by abel
      rw [e]
      exact B.add_mem h1 (hfB i')
    obtain rfl : j' = j := hju j' h2
    obtain rfl : i' = i := hiu i' (by simpa [sub_add_eq_sub_sub] using hp')
    rfl
  have z : ∀ D : Submodule R X, Fixes W D 0 := fun D a _ => map_zero _
  refine ⟨?_, fun v hv => ?_⟩
  · rw [(tAC 0 (z A) _ (fun p : Fin m × Fin n => g p.1 + f p.2) hkC hk).2, (tAB 0 (z A) _ f hfB hf).2,
      (tBC 0 (z B) _ g hgC hg).2, Fintype.card_prod, mul_comm]
  · rw [(tBC _ (hfix v hv) _ g hgC hg).1, (tAB v hv _ f hfB hf).1,
      (tAC v hv _ (fun p : Fin m × Fin n => g p.1 + f p.2) hkC hk).1, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => h.comp_of_mem hC (hgC j) (hfC i) v

end GlobalTheory.FinWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergIntertwiningSumsCompEqIndex
section
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil


open Classical in
open scoped BigOperators in
theorem _root_.GlobalTheory.FinWeil.sumOp_sumOp_eq_idx_smul : ∀ {R X M : Type} [CommRing R]
    [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R}
    {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, _root_.GlobalTheory.FinWeil.IsHeis σ w γ W →
    ∀ (A B : Submodule R X), _root_.GlobalTheory.FinWeil.SelfDual γ A → _root_.GlobalTheory.FinWeil.SelfDual γ B →
    _root_.GlobalTheory.FinWeil.idx A B ≠ 0 →
    _root_.GlobalTheory.FinWeil.idx B A = _root_.GlobalTheory.FinWeil.idx A B ∧
      ∀ v, _root_.GlobalTheory.FinWeil.Fixes W A v →
        _root_.GlobalTheory.FinWeil.sumOp W B A (_root_.GlobalTheory.FinWeil.sumOp W A B v) =
          (_root_.GlobalTheory.FinWeil.idx A B : ℂ) • v := by
  intro R X M _ _ _ _ _ σ w γ W hW A B hA hB hAB
  obtain ⟨hidx, -, hsum⟩ := _root_.GlobalTheory.FinWeil.perfect_pairing_quotients hW B.toAddSubgroup A.toAddSubgroup
    A.toAddSubgroup B.toAddSubgroup (fun a _ => hB a)
    (fun t _ => (hA t).trans (forall₂_congr fun a _ =>
      ⟨hW.swap_eq_one, hW.swap_eq_one⟩)) hAB
  refine ⟨hidx, fun v hv => ?_⟩
  have hfinB : (A.toAddSubgroup.addSubgroupOf B.toAddSubgroup).FiniteIndex := ⟨hAB⟩
  have hfinA : (B.toAddSubgroup.addSubgroupOf A.toAddSubgroup).FiniteIndex := by
    refine ⟨?_⟩
    change B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0
    rw [hidx]; exact hAB
  letI := Fintype.ofFinite (B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup)
  letI := Fintype.ofFinite (A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup)
  unfold _root_.GlobalTheory.FinWeil.sumOp
  set_option synthInstance.maxHeartbeats 100000 in
    simp_rw [finsum_eq_sum_of_fintype, map_sum] at hsum ⊢
  have hcomm : ∀ a ∈ A, ∀ b : X, W a (W b v) = γ a b • W b v := by
    intro a ha b
    rw [hW.comm, hv a ha]
  calc ∑ q : A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup,
        ∑ p : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup,
          W (Quotient.out q).1 (W (Quotient.out p).1 v)
      = ∑ p : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup,
          (∑ q : A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup,
            γ (Quotient.out q).1 (Quotient.out p).1) • W (Quotient.out p).1 v := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_smul]
        exact Finset.sum_congr rfl fun q _ => hcomm _ (Quotient.out q).2 _
    _ = ∑ p : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup,
          if p = 0 then (_root_.GlobalTheory.FinWeil.idx A B : ℂ) • v else 0 := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [hsum _ (Quotient.out p).2]
        have hmem : (Quotient.out p).1 ∈ A.toAddSubgroup ↔ p = 0 := by
          conv_rhs => rw [← QuotientAddGroup.out_eq' p]
          rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
        by_cases hp : p = 0
        · rw [if_pos (hmem.2 hp), if_pos hp, hv _ (hmem.2 hp)]
          exact congrArg (fun n : ℕ => (n : ℂ) • v) hidx
        · rw [if_neg (mt hmem.1 hp), if_neg hp, zero_smul]
    _ = (_root_.GlobalTheory.FinWeil.idx A B : ℂ) • v := by
        rw [Finset.sum_ite_eq']
        simp

end GlobalTheory.FinWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaFixesAdjoinKummerRootsAndValuesEq
section
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory.InertKummer

theorem valuation_eq_one_of_mem {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {x : Ω} (hx : x ∈ B) (hx' : x⁻¹ ∈ B)
    (h0 : x ≠ 0) : B.valuation x = 1 := by
  have hu : IsUnit (⟨x, hx⟩ : B) :=
    isUnit_iff_exists_inv.mpr ⟨⟨x⁻¹, hx'⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩
  exact (B.valuation_eq_one_iff ⟨x, hx⟩).mp hu

theorem inert_fixes_adjoin_and_kum_eq : ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N →
    ∀ (a b : K) (α β : Ω), a ∈ FunctionField.ringOfIntegers k K → a⁻¹ ∈ FunctionField.ringOfIntegers k K →
      b ∈ FunctionField.ringOfIntegers k K → b⁻¹ ∈ FunctionField.ringOfIntegers k K → a ≠ 0 → b ≠ 0 →
      α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
      ∀ θ θ₀ : Ω, θ ≠ 0 → θ₀ ≠ 0 → θ ^ N ∈ IntermediateField.adjoin K {α, β} → θ₀ ^ N ∈ Set.range (algebraMap K Ω) →
      ∀ B : ValuationSubring Ω, GlobalTheory.NeedB.Over (FunctionField.ringOfIntegers k K).toSubring B →
      ∀ g : Ω ≃ₐ[K] Ω, GlobalTheory.NeedB.Inert B g → ∀ c ∈ IntermediateField.adjoin K {α, β}, c ≠ 0 →
        B.valuation (θ ^ N / (θ₀ ^ N * c ^ N)) = 1 →
        g ∈ (IntermediateField.adjoin K {α, β}).fixingSubgroup ∧ GlobalTheory.NeedB.kum (N := N) ζ θ g = GlobalTheory.NeedB.kum ζ θ₀ g := by
  intro k K Ω _ _ _ _ _ _ _ _ _ _ _ N ζ hN hζ a b α β ha ha' hb hb' ha0 hb0 hα hβ θ θ₀ hθ hθ₀ hθE hθ₀K B hB g hg c hcE hc0 hv
  haveI : NeZero N := ⟨hN.ne'⟩

  have hunit : ∀ x : K, x ∈ FunctionField.ringOfIntegers k K → x⁻¹ ∈ FunctionField.ringOfIntegers k K → x ≠ 0 →
      B.valuation (algebraMap K Ω x) = 1 := by
    intro x hx hx' hx0
    refine valuation_eq_one_of_mem B (hB x hx) ?_ ((_root_.map_ne_zero _).mpr hx0)
    rw [← map_inv₀]; exact hB _ hx'

  have hNK0 : (N : K) ≠ 0 := by
    have : ((algebraMap k[X] K).comp Polynomial.C) (N : k) = (N : K) := map_natCast _ _
    rw [← this]; exact (_root_.map_ne_zero _).mpr (by exact_mod_cast hN.ne')
  have hNmem : (N : K) ∈ FunctionField.ringOfIntegers k K := Subalgebra.natCast_mem _ N
  have hNinv : (N : K)⁻¹ ∈ FunctionField.ringOfIntegers k K := by
    have : ((algebraMap k[X] K).comp Polynomial.C) ((N : k)⁻¹) = (N : K)⁻¹ := by
      rw [map_inv₀, map_natCast]
    rw [← this]
    exact Subalgebra.algebraMap_mem _ _
  have hvN : B.valuation (N : Ω) = 1 := by
    have := hunit _ hNmem hNinv hNK0
    rwa [map_natCast] at this

  have hroot : ∀ (γ : Ω) (x : K), x ∈ FunctionField.ringOfIntegers k K → x⁻¹ ∈ FunctionField.ringOfIntegers k K → x ≠ 0 →
      γ ^ N = algebraMap K Ω x → g γ = γ := by
    intro γ x hx hx' hx0 hγ
    refine GlobalTheory.inert_fixes_root_of_unit_ratio K Ω B g N 1 γ hN hvN hg (map_one g) one_ne_zero ?_ ?_
    · rw [hγ]; exact g.commutes x
    · rw [one_pow, div_one, hγ]; exact hunit x hx hx' hx0
  have hgα : g α = α := hroot α a ha ha' ha0 hα
  have hgβ : g β = β := hroot β b hb hb' hb0 hβ
  have hfix : g ∈ (IntermediateField.adjoin K {α, β}).fixingSubgroup := by
    have hz : Subgroup.zpowers g ≤ (IntermediateField.adjoin K {α, β}).fixingSubgroup := by
      rw [← IntermediateField.le_iff_le, IntermediateField.adjoin_le_iff]
      intro x hx
      have hgx : g x = x := by
        rcases hx with rfl | hx
        · exact hgα
        · rw [Set.mem_singleton_iff.mp hx]; exact hgβ
      have hs : g ∈ MulAction.stabilizer (Ω ≃ₐ[K] Ω) x := hgx
      intro f
      have hf : (f : Ω ≃ₐ[K] Ω) ∈ MulAction.stabilizer (Ω ≃ₐ[K] Ω) x := Subgroup.zpowers_le.mpr hs f.2
      exact hf
    exact hz (Subgroup.mem_zpowers g)
  have hfixE : ∀ x ∈ IntermediateField.adjoin K {α, β}, g x = x := fun x hx => hfix ⟨x, hx⟩
  refine ⟨hfix, ?_⟩

  have hgθN : g (θ ^ N) = θ ^ N := hfixE _ hθE
  have hgθ₀N : g (θ₀ ^ N) = θ₀ ^ N := by
    obtain ⟨y, hy⟩ := hθ₀K; rw [← hy]; exact g.commutes y
  have hq : g (θ / θ₀) = θ / θ₀ := by
    refine GlobalTheory.inert_fixes_root_of_unit_ratio K Ω B g N c (θ / θ₀) hN hvN hg (hfixE c hcE) hc0 ?_ ?_
    · rw [div_pow, map_div₀, hgθN, hgθ₀N]
    · rw [div_pow, div_div]; exact hv
  have hq' : g θ₀ = g θ * θ₀ / θ := by
    rw [map_div₀] at hq
    have hgθ₀0 : g θ₀ ≠ 0 := (_root_.map_ne_zero g).mpr hθ₀
    rw [div_eq_div_iff hgθ₀0 hθ₀] at hq
    rw [eq_div_iff hθ, hq, mul_comm]

  have hξ : (g θ / θ) ^ N = 1 := by
    rw [div_pow, ← map_pow, hgθN, div_self (pow_ne_zero _ hθ)]
  obtain ⟨i, hiN, hi⟩ := hζ.eq_pow_of_pow_eq_one hξ
  have hval : ((i : ZMod N)).val = i := ZMod.val_cast_of_lt hiN
  have h1 : g θ = ζ ^ ((i : ZMod N)).val * θ := by
    rw [hval, hi]; field_simp
  have h2 : g θ₀ = ζ ^ ((i : ZMod N)).val * θ₀ := by
    rw [hq', h1]; field_simp
  rw [kum_eq_of hζ hθ _ h1, kum_eq_of hζ hθ₀ _ h2]

end GlobalTheory.InertKummer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspidalAtAllCuspsSL2SlashIntMatrix
section
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices

private def toGLQ (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((Int.castRingHom ℚ).mapMatrix M)
    (by rw [← RingHom.map_det]; simpa using hM)

private lemma toGL_eq_map (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) :
    toGL M = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (toGLQ M hM) := by
  ext i j
  rw [toGL_val M hM]
  simp [toGLQ, Matrix.GeneralLinearGroup.map]

lemma isCusp_SL2Z_toGL_smul (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) {c : OnePoint ℝ}
    (hc : IsCusp c 𝒮ℒ) : IsCusp (toGL M • c) 𝒮ℒ := by
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c, rfl⟩ := hc
  rw [toGL_eq_map M hM]
  exact ⟨toGLQ M hM • c, by rw [← Rat.coe_castHom, OnePoint.map_smul]⟩

theorem cuspAll_slash_toGL : ∀ (k : ℤ) (M : Matrix (Fin 2) (Fin 2) ℤ) (G : ℍ → ℂ), 0 < M.det →
    CuspAll k G → CuspAll k (G ∣[k] toGL M) := by
  intro k M G hM hG
  refine ⟨MDifferentiable.slash hG.1 k (toGL M), fun c hc => ?_⟩
  rw [← OnePoint.IsZeroAt.smul_iff]
  exact hG.2 _ (isCusp_SL2Z_toGL_smul M hM.ne' hc)

end GlobalTheory.HeckeFamilyMatrices
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDlogCoef
section
open GlobalTheory.K5 Polynomial

noncomputable section
namespace GlobalTheory.K5.DlogCoef

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

theorem smul_mk (J : Ideal (On p n)) (a b : On p n) :
    a • (Ideal.Quotient.mk J b) = Ideal.Quotient.mk J (a * b) := by
  first
  | rfl
  | exact (Submodule.Quotient.mk_smul _ _ _).symm
  | simp [Algebra.smul_def]

theorem deriv_pow (J : Ideal (On p n)) (D : Derivation (O0 p) (On p n) (On p n ⧸ J))
    (r c : On p n) (h : D r = Ideal.Quotient.mk J (c * r)) (i : ℕ) :
    D (r ^ i) = Ideal.Quotient.mk J ((i : On p n) * c * r ^ i) := by
  induction i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Derivation.leibniz, ih, h, smul_mk, smul_mk, ← (Ideal.Quotient.mk J).map_add]
    congr 1
    push_cast
    ring

end GlobalTheory.K5.DlogCoef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsExpEqOfSubstLg
section
open MvPowerSeries ReciprocityTheory.PGsh

namespace GlobalTheory.FGDepth

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

private theorem jacobian_logFGL_lg_eq_one {d : ℕ} (G : LogFGL v d) :
    FormalSeries.jacobian G.lg = 1 := by
  ext i j
  rw [FormalSeries.jacobian_apply, G.lg_lin i j, Matrix.one_apply]

private theorem exists_subst_inverse_logFGL_lg {d : ℕ} (G : LogFGL v d) :
    ∃ w : Fin d → MvPowerSeries (Fin d) C, (∀ j, constantCoeff (w j) = 0) ∧
      (∀ i, subst w (G.lg i) = X i) ∧ ∀ j, subst G.lg (w j) = X j :=
  FormalSeries.exists_subst_inverse G.lg_const (B := 1)
    (by rw [jacobian_logFGL_lg_eq_one, Matrix.mul_one]) (by rw [jacobian_logFGL_lg_eq_one, Matrix.one_mul])

theorem isExp_expOf {d : ℕ} (G : LogFGL v d) : IsExp G (expOf G) := by
  obtain ⟨w, hw0, hw1, -⟩ := exists_subst_inverse_logFGL_lg G
  exact Classical.epsilon_spec (p := IsExp G) ⟨w, hw0, hw1⟩

theorem isExp_eq_of_subst_lg {d : ℕ} (G : LogFGL v d) {w : Fin d → MvPowerSeries (Fin d) C}
    (h2 : ∀ j, subst G.lg (w j) = X j) {e : Fin d → MvPowerSeries (Fin d) C} (he : IsExp G e) :
    e = w := by
  obtain ⟨he0, he1⟩ := he
  have hlg : HasSubst G.lg := hasSubst_of_constantCoeff_zero G.lg_const
  have hes : HasSubst e := hasSubst_of_constantCoeff_zero he0
  funext j
  calc e j = subst e (X j : MvPowerSeries (Fin d) C) := (subst_X hes j).symm
    _ = subst e (subst G.lg (w j)) := by rw [h2 j]
    _ = subst (fun s => subst e (G.lg s)) (w j) := subst_comp_subst_apply hlg hes (w j)
    _ = subst (X : Fin d → MvPowerSeries (Fin d) C) (w j) := by simp only [he1]
    _ = w j := by rw [subst_self]; rfl

theorem isExp_unique {d : ℕ} (G : LogFGL v d) {e : Fin d → MvPowerSeries (Fin d) C}
    (he : IsExp G e) : e = expOf G := by
  obtain ⟨w, -, -, hw2⟩ := exists_subst_inverse_logFGL_lg G
  rw [isExp_eq_of_subst_lg G hw2 he, isExp_eq_of_subst_lg G hw2 (isExp_expOf G)]

theorem subst_lg_expOf {d : ℕ} (G : LogFGL v d) (a : Fin d) :
    subst G.lg (expOf G a) = (X a : MvPowerSeries (Fin d) C) := by
  obtain ⟨w, -, -, hw2⟩ := exists_subst_inverse_logFGL_lg G
  rw [isExp_eq_of_subst_lg G hw2 (isExp_expOf G)]
  exact hw2 a

theorem expOf_spec {d : ℕ} (G : LogFGL v d) :
    IsExp G (expOf G) ∧ (∀ e, IsExp G e → e = expOf G) ∧
      ∀ a, subst G.lg (expOf G a) = (X a : MvPowerSeries (Fin d) C) :=
  ⟨isExp_expOf G, fun _ he => isExp_unique G he, subst_lg_expOf G⟩

end GlobalTheory.FGDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntPrimeDivRootOfUnitySubOnePow
section
open GlobalTheory.K5 GlobalTheory.KumDlog

namespace GlobalTheory.K5.PDiv

open Polynomial

theorem prod_one_sub_pow_dvd {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]
    (ζ : Ω) (hζ : IsIntegral (O0 p) ζ) (S : Finset Ω) (hS : ∀ μ ∈ S, ∃ i : ℕ, ζ ^ i = μ) :
    ∃ c : Ω, IsIntegral (O0 p) c ∧ ∏ μ ∈ S, (1 - μ) = (ζ - 1) ^ S.card * c := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, isIntegral_one, by simp⟩
  | insert a S ha ih =>
    obtain ⟨c, hc, e⟩ := ih (fun μ hμ => hS μ (Finset.mem_insert_of_mem hμ))
    obtain ⟨i, rfl⟩ := hS _ (Finset.mem_insert_self _ _)
    refine ⟨-(∑ k ∈ Finset.range i, ζ ^ k) * c, ?_, ?_⟩
    · refine IsIntegral.mul (IsIntegral.neg ?_) hc
      have : (∑ k ∈ Finset.range i, ζ ^ k) ∈ integralClosure (O0 p) Ω :=
        Subalgebra.sum_mem _ fun k _ => Subalgebra.pow_mem _ hζ k
      exact this
    · rw [Finset.prod_insert ha, e, Finset.card_insert_of_notMem ha, pow_succ]
      have g := geom_sum_mul ζ i
      linear_combination ((ζ - 1) ^ S.card * c) * g

theorem pdiv : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    ∀ (T : Tower p Ω) (j s : ℕ), 1 ≤ j → s ≤ Nat.totient (p ^ j) →
      IsInt (p := p) ((p : Ω) / (T.ζ j - 1) ^ s) := by
  intro p _ Ω _ _ T j s hj hs
  classical
  have hprim := T.prim j
  have hpos : 0 < p ^ j := pow_pos (Fact.out : p.Prime).pos j
  have hζ : IsIntegral (O0 p) (T.ζ j) := ⟨X ^ (p ^ j) - C 1, monic_X_pow_sub_C 1 hpos.ne', by simp [hprim.pow_eq_one]⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hne : T.ζ (j' + 1) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    exact hprim.ne_one (Nat.one_lt_pow (by omega) (Fact.out : p.Prime).one_lt)
  have hp : (p : Ω) = ∏ μ ∈ primitiveRoots (p ^ (j' + 1)) Ω, (1 - μ) := by
    rw [← eval_one_cyclotomic_prime_pow (R := Ω) j', cyclotomic_eq_prod_X_sub_primitiveRoots hprim,
      eval_prod]
    simp
  obtain ⟨c, hc, e⟩ := prod_one_sub_pow_dvd (T.ζ (j' + 1)) hζ (primitiveRoots (p ^ (j' + 1)) Ω)
    (fun μ hμ => by
      have hμ' := (mem_primitiveRoots hpos).1 hμ
      obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hμ'.pow_eq_one
      exact ⟨i, hi⟩)
  rw [hprim.card_primitiveRoots] at e
  have key : (p : Ω) / (T.ζ (j' + 1) - 1) ^ s =
      (T.ζ (j' + 1) - 1) ^ (Nat.totient (p ^ (j' + 1)) - s) * c := by
    rw [div_eq_iff (pow_ne_zero _ hne), hp, e, mul_right_comm, ← pow_add, Nat.sub_add_cancel hs]
  rw [IsInt, key]
  exact IsIntegral.mul (IsIntegral.pow (IsIntegral.sub hζ isIntegral_one) _) hc

end GlobalTheory.K5.PDiv
end

