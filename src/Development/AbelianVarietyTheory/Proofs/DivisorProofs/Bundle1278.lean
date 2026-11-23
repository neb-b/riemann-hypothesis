module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1251
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1188
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1042
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1252
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1253
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothOfDefectZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0158
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1254
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfVectorMultiplicationsMemFiltrationLatti
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

namespace GlobalTheory.HSShort.Sys

variable {F A : Type} [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A]

theorem word_succ {K B : Type} [Field K] [AddCommGroup B] [Module K B] {N : ℕ} (mul : (Fin N → K) →ₗ[K] Module.End K B)
    {t : ℕ} (u : Fin (t + 1) → Fin N → K) : word mul u = mul (u 0) * word mul (fun i => u i.succ) := by
  simp [word, List.ofFn_succ]

theorem word_zero {K B : Type} [Field K] [AddCommGroup B] [Module K B] {N : ℕ} (mul : (Fin N → K) →ₗ[K] Module.End K B)
    (u : Fin 0 → Fin N → K) : word mul u = 1 := by
  simp [word]

theorem mul_mem_V_succ (S : Sys F A) (hS : S.Hyp) {j : ℕ} (hj : j < S.T) (u : Fin S.N → F) {x : A} (hx : x ∈ S.V j) :
    S.mul u x ∈ S.V (j + 1) := by
  have key : ∀ m ∈ S.M j, ∀ u : Fin S.N → F, S.mul u (m : A) ∈ S.V (j + 1) := by
    intro m hm u
    have hu : u ∈ Submodule.span F (Set.range S.w.col) := hS.lat.spans ▸ Submodule.mem_top
    let L : (Fin S.N → F) →ₗ[F] A := (LinearMap.applyₗ (m : A)) ∘ₗ S.mul
    have hle : Submodule.span F (Set.range S.w.col) ≤ (S.V (j + 1)).comap L := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      obtain ⟨g, -, hg⟩ := hS.stable j hj k m hm
      show L (S.w.col k) ∈ S.V (j + 1)
      simp only [L, LinearMap.coe_comp, Function.comp_apply, LinearMap.applyₗ_apply_apply]
      rw [← hg]
      exact g.2
    exact hle hu
  let P : Submodule F (S.V j) := (S.V (j + 1)).comap (S.mul u ∘ₗ (S.V j).subtype)
  have hP : Submodule.span F (S.M j : Set (S.V j)) ≤ P := by
    rw [Submodule.span_le]
    intro m hm
    exact key m hm u
  have hx' : (⟨x, hx⟩ : S.V j) ∈ Submodule.span F (S.M j : Set (S.V j)) :=
    (hS.full j hj.le).span ▸ Submodule.mem_top
  exact hP hx'

theorem word_mem (S : Sys F A) (hS : S.Hyp) (j t : ℕ) (hjt : j + t ≤ S.T) :
    (∀ (u : Fin t → Fin S.N → F), ∀ x ∈ S.V j, word S.mul u x ∈ S.V (j + t)) ∧
      ∀ (e : Fin t → Fin S.n), ∀ x ∈ S.M j, ∃ g ∈ S.M (j + t), (g : A) = word S.mul (fun i => S.w.col (e i)) x := by
  induction t with
  | zero =>
    refine ⟨fun u x hx => ?_, fun e x hx => ⟨x, hx, ?_⟩⟩
    · simpa [word_zero] using hx
    · simp [word_zero]
  | succ t ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hlt : j + t < S.T := by omega
    refine ⟨fun u x hx => ?_, fun e x hx => ?_⟩
    · rw [word_succ, Module.End.mul_apply]
      exact mul_mem_V_succ S hS hlt (u 0) (ih1 (fun i => u i.succ) x hx)
    · obtain ⟨g', hg', hg'e⟩ := ih2 (fun i => e i.succ) x hx
      obtain ⟨g, hg, hge⟩ := hS.stable (j + t) hlt (e 0) g' hg'
      refine ⟨g, hg, ?_⟩
      rw [word_succ, Module.End.mul_apply, hge, hg'e]

end GlobalTheory.HSShort.Sys

namespace GlobalTheory.HSShort

theorem wordMem : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (j t : ℕ), j + t ≤ S.T → (∀ (u : Fin t → Fin S.N → F), ∀ x ∈ S.V j, word S.mul u x ∈ S.V (j + t)) ∧ ∀ (e : Fin t → Fin S.n), ∀ x ∈ S.M j, ∃ g ∈ S.M (j + t), (g : A) = word S.mul (fun i => S.w.col (e i)) x :=
  fun _ _ _ _ _ _ _ _ S hS j t hjt => S.word_mem hS j t hjt

end GlobalTheory.HSShort
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientPieceFinrankLeH0Statement
section
open NumberField MvPolynomial GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.CompHt
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_piece_finrank_le_h0 : ∀ (k : Type) [Field k] (S : LinSys k), S.IsVariety → ∀ m : ℕ, Module.finrank k (quotPiece S.imageIdeal (m : ℤ)) ≤ lbH0 k (lbPow S.L m) := by
  first | exact @GlobalTheory.Adelic.LinSys.finrank_quotient_piece_le_sections | exact GlobalTheory.Adelic.LinSys.finrank_quotient_piece_le_sections | (intros; apply GlobalTheory.Adelic.LinSys.finrank_quotient_piece_le_sections <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RapidDecaySmallestRatioAbsorbsHeightAndCharacter
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.RapidDecayReal

theorem height_le (a : ℕ) (N : ℕ) (r : Fin a → ℝ) (hr : ∀ i, 0 < r i) (K : ℝ)
    (hb : ∀ i, r i ≤ K ∧ (r i)⁻¹ ≤ K) :
    (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N ≤ (1 + 2 * a * K) ^ N := by
  have h0 : 0 ≤ 1 + ∑ i, r i + ∑ i, (r i)⁻¹ := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => (hr i).le)
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => (inv_pos.2 (hr i)).le)
    linarith
  apply pow_le_pow_left₀ h0
  have h1 : ∑ i, r i ≤ ∑ _i : Fin a, K := Finset.sum_le_sum (fun i _ => (hb i).1)
  have h2 : ∑ i, (r i)⁻¹ ≤ ∑ _i : Fin a, K := Finset.sum_le_sum (fun i _ => (hb i).2)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1 h2
  linarith

theorem char_ge (a : ℕ) (lam : Fin a → ℝ) (L : ℕ) (hL : ∑ i, |lam i| ≤ L) (r : Fin a → ℝ)
    (hr : ∀ i, 0 < r i) (K : ℝ) (hK : 1 ≤ K) (hb : ∀ i, r i ≤ K ∧ (r i)⁻¹ ≤ K) :
    (K ^ L)⁻¹ ≤ ∏ i, r i ^ lam i := by
  have hK0 : 0 < K := by linarith
  have hi : ∀ i, K ^ (-|lam i|) ≤ r i ^ lam i := by
    intro i
    rcases le_or_gt 0 (lam i) with h | h
    · rw [abs_of_nonneg h, Real.rpow_neg hK0.le, ← Real.inv_rpow hK0.le]
      apply Real.rpow_le_rpow (inv_nonneg.2 hK0.le) _ h
      rw [inv_le_comm₀ hK0 (hr i)]; exact (hb i).2
    · rw [abs_of_neg h, neg_neg]
      have e1 : K ^ lam i = (K⁻¹) ^ (-lam i) := by
        rw [Real.inv_rpow hK0.le, Real.rpow_neg hK0.le, inv_inv]
      have e2 : r i ^ lam i = ((r i)⁻¹) ^ (-lam i) := by
        rw [Real.inv_rpow (hr i).le, Real.rpow_neg (hr i).le, inv_inv]
      rw [e1, e2]
      apply Real.rpow_le_rpow (inv_nonneg.2 hK0.le) _ (by linarith)
      exact inv_anti₀ (hr i) (hb i).1
  calc (K ^ L)⁻¹ = K ^ (-(L : ℝ)) := by rw [Real.rpow_neg hK0.le, Real.rpow_natCast]
    _ ≤ K ^ (∑ i, -|lam i|) := by
        apply Real.rpow_le_rpow_of_exponent_le hK
        rw [Finset.sum_neg_distrib]; linarith
    _ = ∏ i, K ^ (-|lam i|) := Real.rpow_sum_of_pos hK0 _ _
    _ ≤ ∏ i, r i ^ lam i :=
        Finset.prod_le_prod₀ (fun i _ => Real.rpow_nonneg hK0.le _) (fun i _ => hi i)

theorem key (a : ℕ) (lam : Fin a → ℝ) (L N : ℕ) (hL : ∑ i, |lam i| ≤ L) (C0 : ℝ) (hC0 : 1 ≤ C0)
    (r : Fin a → ℝ) (hr : ∀ i, 0 < r i) (ρ : ℝ) (hρ : 1 ≤ ρ)
    (hb : ∀ i, r i ≤ C0 * ρ ^ a ∧ (r i)⁻¹ ≤ C0 * ρ ^ a) :
    (ρ ^ (a * N + a * L))⁻¹ * (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N ≤
      ((1 + 2 * a * C0) ^ N * C0 ^ L) * ∏ i, r i ^ lam i := by
  set P := ρ ^ a with hPdef
  have hP : 1 ≤ P := one_le_pow₀ hρ
  have hC00 : 0 < C0 := by linarith
  have hP0 : 0 < P := by linarith
  have hK : 1 ≤ C0 * P := by nlinarith
  have h1 := height_le a N r hr (C0 * P) hb
  have h2 := char_ge a lam L hL r hr (C0 * P) hK hb
  have h3 : (1 + 2 * (a : ℝ) * (C0 * P)) ^ N ≤ ((1 + 2 * a * C0) * P) ^ N := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith
  have hm : ρ ^ (a * N + a * L) = P ^ N * P ^ L := by
    rw [hPdef, ← pow_mul, ← pow_mul, ← pow_add]
  rw [hm]
  calc (P ^ N * P ^ L)⁻¹ * (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N
      ≤ (P ^ N * P ^ L)⁻¹ * ((1 + 2 * a * C0) * P) ^ N :=
        mul_le_mul_of_nonneg_left (h1.trans h3) (by positivity)
    _ = ((1 + 2 * a * C0) ^ N * C0 ^ L) * ((C0 * P) ^ L)⁻¹ := by
        rw [mul_pow, mul_pow]
        field_simp
    _ ≤ ((1 + 2 * a * C0) ^ N * C0 ^ L) * ∏ i, r i ^ lam i :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

end GlobalTheory.RapidDecayReal


open GlobalTheory.RapidDecayReal in
theorem GlobalTheory.rapidDecay_real : ∀ (a : ℕ) (t : ℝ), 0 < t → ∀ (lam : Fin a → ℝ) (N : ℕ), ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ r : Fin a → ℝ, (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → ∏ i, r i = 1 → (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N ≤ C * ∏ i, r i ^ lam i ∨ ∃ i j : Fin a, (j : ℕ) = i + 1 ∧ (r j / r i) ^ m * (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N ≤ C * ∏ i, r i ^ lam i := by
  intro a t ht lam N
  obtain ⟨C0, hC0, hC⟩ := _root_.GlobalTheory.coneCoord_le_pow_of_prod_eq_one a t ht
  set L := ⌈∑ i, |lam i|⌉₊ with hLdef
  have hL : ∑ i, |lam i| ≤ L := Nat.le_ceil _
  refine ⟨a * N + a * L, (1 + 2 * a * C0) ^ N * C0 ^ L, by positivity, ?_⟩
  intro r hr hcone hprod
  by_cases hall : ∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ r j
  · left
    have hb := hC r 1 hr hcone hprod le_rfl (fun i j hij => by rw [one_mul]; exact hall i j hij)
    have := key a lam L N hL C0 hC0 r hr 1 le_rfl hb
    simpa using this
  · right
    push_neg at hall
    obtain ⟨i, j, hij, hlt⟩ := hall
    set S := (Finset.univ : Finset (Fin a × Fin a)).filter (fun p => (p.2 : ℕ) = p.1 + 1) with hS
    have hne : S.Nonempty := ⟨(i, j), by simp [hS, hij]⟩
    obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image S (fun p => r p.1 / r p.2) hne
    have hpadj : (p.2 : ℕ) = p.1 + 1 := by simpa [hS] using hp
    have hij' : r i / r j ≤ r p.1 / r p.2 := hmax (i, j) (by simp [hS, hij])
    have hρ : 1 ≤ r p.1 / r p.2 := by
      have : 1 < r i / r j := by rw [one_lt_div (hr j)]; exact hlt
      linarith
    have hadj : ∀ i' j' : Fin a, (j' : ℕ) = i' + 1 → r i' ≤ (r p.1 / r p.2) * r j' := by
      intro i' j' h'
      have := hmax (i', j') (by simp [hS, h'])
      rwa [div_le_iff₀ (hr j')] at this
    have hb := hC r _ hr hcone hprod hρ hadj
    refine ⟨p.1, p.2, hpadj, ?_⟩
    have := key a lam L N hL C0 hC0 r hr _ hρ hb
    rw [← inv_div (r p.1) (r p.2), inv_pow]
    exact this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionCycleFormulaProjectiveStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_section_cycle_formula_projective : ∀ (κ : Type) [Field κ] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [Algebra κ Γ(X, ⊤)], IsProjOver (strHom κ (X := X)) → ∀ (n : ℕ), topologicalKrullDim X ≤ (n + 1 : ℕ) → ∀ (M : LB X) (hM : M.IsLB) (P : Fin n → LB X), (∀ i, (P i).IsLB) → ∀ (r : M.ι → X.functionFieldˣ) (hr : IsRatSec M r), interNum κ (structureModule X) (Fin.cons M P : Fin (n + 1) → LB X) = ∑ᶠ w, (divOfRatSec hM hr).mult w * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P := by
  first | exact @GlobalTheory.ratSec_cycle_formula | exact GlobalTheory.ratSec_cycle_formula | (intros; apply GlobalTheory.ratSec_cycle_formula <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexIdealSmulFractionalIdealEqAbsNormNumberF
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

namespace GlobalTheory.FracIdealIndex

theorem relIndex_smul_eq_absNorm : ∀ (F : Type) [Field F] [NumberField F] (I : Submodule (𝓞 F) F) (p : Ideal (𝓞 F)), p ≠ ⊥ → I ≠ ⊥ → (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ y ∈ I, c • y ∈ (1 : Submodule (𝓞 F) F)) → (p • I).toAddSubgroup.relIndex I.toAddSubgroup = Ideal.absNorm p := by
  intro F _ _ I p hp hI ⟨c, hc0, hc⟩
  have hc' : (c : F) ≠ 0 := by exact_mod_cast hc0
  let f : F →ₗ[𝓞 F] F := c • LinearMap.id
  have hf : ∀ y, f y = c • y := fun y => rfl
  have hfi : Function.Injective f := fun y z h => by
    simp only [hf, Algebra.smul_def] at h
    exact mul_left_cancel₀ (by simpa using hc') h
  let g : 𝓞 F →ₗ[𝓞 F] F := Algebra.linearMap (𝓞 F) F
  have hgi : Function.Injective g := fun y z h => by
    simpa [g] using h
  have hle : Submodule.map f I ≤ LinearMap.range g := by
    rw [← Submodule.one_eq_range]
    rintro _ ⟨y, hy, rfl⟩
    exact hc y hy
  let J : Ideal (𝓞 F) := (Submodule.map f I).comap g
  have hJ : Submodule.map g J = Submodule.map f I := Submodule.map_comap_eq_of_le hle
  have hJ0 : J ≠ ⊥ := by
    intro h
    apply hI
    have : Submodule.map f I = ⊥ := by rw [← hJ, h, Submodule.map_bot]
    exact Submodule.map_injective_of_injective hfi (this.trans (Submodule.map_bot f).symm)
  have hpJ : Submodule.map g (p * J) = Submodule.map f (p • I) := by
    rw [← Ideal.smul_eq_mul, Submodule.map_smul'', Submodule.map_smul'', hJ]
  have e1 : (p • I).toAddSubgroup.relIndex I.toAddSubgroup =
      (p * J).toAddSubgroup.relIndex J.toAddSubgroup := by
    have a1 := AddSubgroup.relIndex_map_map_of_injective (p • I).toAddSubgroup I.toAddSubgroup
      (f := (f : F →+ F)) hfi
    have a2 := AddSubgroup.relIndex_map_map_of_injective (p * J).toAddSubgroup J.toAddSubgroup
      (f := (g : 𝓞 F →+ F)) hgi
    rw [← Submodule.map_toAddSubgroup, ← Submodule.map_toAddSubgroup] at a1 a2
    rw [← a1, ← a2, hpJ, hJ]
  have hle2 : p * J ≤ J := by first | exact Ideal.mul_le_left | exact Ideal.mul_le_right
  have hidx : (p * J).toAddSubgroup.relIndex J.toAddSubgroup * Ideal.absNorm J = Ideal.absNorm (p * J) :=
    by simpa only [Ideal.absNorm_eq_index] using
      AddSubgroup.relIndex_mul_index (H := (p * J).toAddSubgroup) (K := J.toAddSubgroup) hle2
  have hN : Ideal.absNorm J ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hJ0
  rw [e1]
  rw [map_mul] at hidx
  exact mul_right_cancel₀ hN hidx

end GlobalTheory.FracIdealIndex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexSupSpanSingletonEqAbsNorm
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory

theorem relIndex_sup_span_singleton_eq_absNorm
    (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
    [IsScalarTower (𝓞 F) F V] (N₀ : Submodule (𝓞 F) V) (u : V) (p : Ideal (𝓞 F))
    (hp : p.IsMaximal) (hu : u ∉ N₀) (hpu : ∀ π ∈ p, π • u ∈ N₀) :
    N₀.toAddSubgroup.relIndex (N₀ ⊔ Submodule.span (𝓞 F) {u}).toAddSubgroup
      = Ideal.absNorm p := by
  set M := N₀ ⊔ Submodule.span (𝓞 F) {u} with hM
  set K : Submodule (𝓞 F) M := N₀.comap M.subtype with hK
  have huM : u ∈ M := Submodule.mem_sup_right (Submodule.mem_span_singleton_self u)

  let g : 𝓞 F →ₗ[𝓞 F] M := LinearMap.toSpanSingleton (𝓞 F) M ⟨u, huM⟩
  let f : 𝓞 F →ₗ[𝓞 F] M ⧸ K := K.mkQ ∘ₗ g
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨⟨x, hx⟩, rfl⟩ := K.mkQ_surjective y
    obtain ⟨n, hn, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
    refine ⟨a, ?_⟩
    show K.mkQ (g a) = K.mkQ ⟨n + a • u, hx⟩
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    show (g a - ⟨n + a • u, hx⟩ : M).1 ∈ N₀
    simp [g, LinearMap.toSpanSingleton_apply]
    exact hn
  have hker : LinearMap.ker f = p := by
    have hmem : ∀ a, a ∈ LinearMap.ker f ↔ a • u ∈ N₀ := by
      intro a
      simp only [LinearMap.mem_ker, f, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, hK, Submodule.mem_comap, Submodule.subtype_apply, g,
        LinearMap.toSpanSingleton_apply, SetLike.val_smul]
    symm
    apply hp.eq_of_le
    · intro htop
      apply hu
      have : (1 : 𝓞 F) ∈ LinearMap.ker f := by
        change (1 : 𝓞 F) ∈ (LinearMap.ker f : Submodule (𝓞 F) (𝓞 F))
        rw [show (LinearMap.ker f : Submodule (𝓞 F) (𝓞 F)) = ⊤ from htop]
        trivial
      simpa using (hmem 1).mp this
    · intro a ha
      exact (hmem a).mpr (hpu a ha)
  have e : (𝓞 F ⧸ p) ≃ₗ[𝓞 F] M ⧸ K := by
    have := f.quotKerEquivOfSurjective hf
    rw [hker] at this
    exact this
  have hidx : N₀.toAddSubgroup.relIndex M.toAddSubgroup = Nat.card (M ⧸ K) := by
    rw [AddSubgroup.relIndex, AddSubgroup.index_eq_card]
    rfl
  rw [hidx, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr e.toEquiv).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidLineBundleIsoDescentAlongGaloisCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GaloisLBDescent

theorem lbIso_of_galoisCover : ∀ (S S₁ Y : Scheme.{0}) (π₁ : S₁ ⟶ S) (Ga : Type) [Group Ga] (ρ₁ : Ga → (S₁ ⟶ S₁)) (f : S ⟶ Y) (A' : Over S₁) (A : Over S) (B : Over Y) [GrpObj A'] [GrpObj A] [IsCommMonObj A] [GrpObj B] (φ₁ : A'.left ⟶ A.left) (φ : A.left ⟶ B.left) (PA : RigLB A) (PB : RigLB B) (L' : LB A'.left), IsAbelianScheme A → GlobalTheory.ZM.IsGaloisCover Ga ρ₁ π₁ → IsGrpPullback A' A π₁ φ₁ → IsGrpPullback A B f φ → L'.IsLB → LBIso L' (PA.L.pull φ₁) → LBIso L' (PB.L.pull (φ₁ ≫ φ)) → LBIso PA.L (PB.L.pull φ) := by
  intro S S₁ Y π₁ Ga _ ρ₁ f A' A B _ _ _ _ φ₁ φ PA PB L' hA hG h₁ h hL' i₁ i₂
  have := hG.fin
  have := hG.etale
  have := hG.onto
  have hPA := PA.isLB
  have h₂ := pull_isLB PB.isLB φ
  have hN := LB.isLB_div h₂ hPA
  have cN : CechPic.cls _ hN = CechPic.pull φ (CechPic.cls _ PB.isLB) - CechPic.cls _ hPA :=
    CechPic.cls_div h₂ hPA hN
  have zA : CechPic.pull (eSec A) (CechPic.cls _ PA.isLB) = 0 :=
    (CechPic.cls_eq_zero_iff (pull_isLB PA.isLB _)).2 ⟨_, PA.rigGen⟩
  have zB : CechPic.pull (eSec B) (CechPic.cls _ PB.isLB) = 0 :=
    (CechPic.cls_eq_zero_iff (pull_isLB PB.isLB _)).2 ⟨_, PB.rigGen⟩
  have c₁ : CechPic.cls _ hL' = CechPic.pull φ₁ (CechPic.cls _ PA.isLB) :=
    (CechPic.cls_eq_iff hL' (pull_isLB PA.isLB _)).2 i₁
  have c₂ : CechPic.cls _ hL' = CechPic.pull (φ₁ ≫ φ) (CechPic.cls _ PB.isLB) :=
    (CechPic.cls_eq_iff hL' (pull_isLB PB.isLB _)).2 i₂
  refine GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange GlobalTheory.SemiRigid.globalFns S S₁ π₁ A _ hA hN
    inferInstance inferInstance inferInstance ((CechPic.cls_eq_zero_iff (pull_isLB hN _)).1 ?_)
    ((CechPic.cls_eq_zero_iff (pull_isLB hN _)).1 ?_)
  · have he : eSec A ≫ φ = f ≫ eSec B := GlobalTheory.PolBaseChange.eSec_comm h
    rw [CechPic.cls_pull hN, cN, map_sub, ← CechPic.pull_comp, zA, he, CechPic.pull_comp, zB, map_zero,
      sub_zero]
  · rw [CechPic.cls_pull hN, cN, ← h₁.1.isoPullback_inv_fst, CechPic.pull_comp, map_sub,
      ← CechPic.pull_comp φ₁ φ, ← c₁, ← c₂, sub_self, map_zero]

end GlobalTheory.GaloisLBDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowsInSpanOfRankNormalFormStatement
section
open ValuativeRel Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rows_in_span_of_rank_normal_form : ∀ (K : Type) [Field K] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (r : ℕ) (X : Matrix A D K) (H : Matrix (Fin r) A K) (Q : Matrix D (Fin r) K), X.rank ≤ r → IsUnit (H * X * Q) → ∀ i, ∃ s : Fin r → K, X i = s ᵥ* (H * X) := by
  first | exact @GlobalTheory.rows_mem_span_of_isUnit_mul | exact GlobalTheory.rows_mem_span_of_isUnit_mul | (intros; apply GlobalTheory.rows_mem_span_of_isUnit_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatBoxDecompositionStatement
section
open ValuativeRel Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_bruhat_box_decomposition : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ Φ ∈ GlobalTheory.WeilM.SB (Matrix A D k), ∃ m₁ : ℕ, ∀ m ≥ m₁, ∃ s : Finset (Matrix A D k), Φ = ∑ c ∈ s, Φ c • GlobalTheory.RankCoinv.boxFn ϖ c (fun _ => m) ∧ ∀ c ∈ s, ∀ X ∈ GlobalTheory.RankCoinv.box ϖ c (fun _ => m), Φ X = Φ c := by
  first | exact @GlobalTheory.RankCoinv.Decomp.exists_sum_boxFn | exact GlobalTheory.RankCoinv.Decomp.exists_sum_boxFn | (intros; apply GlobalTheory.RankCoinv.Decomp.exists_sum_boxFn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfArtinianSquareZeroLiftingNoetherianBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SmoothCrit

theorem smooth_of_lift (A R : Type) [CommRing A] [IsNoetherianRing A] [CommRing R] (g : A →+* R) (hg : g.FiniteType)
    (H : (∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (β : A →+* C) (φ₀ : R →+* C₀), φ₀.comp (g) = π.comp β → ∃ φ : R →+* C, π.comp φ = φ₀ ∧ φ.comp (g) = β)) : g.Smooth := by
  algebraize [g]
  have : Algebra.FinitePresentation A R := Algebra.FinitePresentation.of_finiteType.mp hg
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp (inferInstance : Algebra.FiniteType A R)
  letI := f.toRingHom.toAlgebra
  haveI : IsScalarTower A (MvPolynomial (Fin n) A) R := IsScalarTower.of_algebraMap_eq fun a => (f.commutes a).symm
  have hs : Function.Surjective (algebraMap (MvPolynomial (Fin n) A) R) := hf
  have hmax : ∀ (m : Ideal R) [m.IsMaximal], Algebra.IsSmoothAt A m := by
    intro m _
    letI : Field (R ⧸ m) := Ideal.Quotient.field m
    have key := _root_.GlobalTheory.injective_cotangentComplexBaseChange_of_forms_extend A (MvPolynomial (Fin n) A) R (R ⧸ m) fun ℓ => _root_.GlobalTheory.LiftDeriv.exists_derivation_extending A (MvPolynomial (Fin n) A) R (R ⧸ m) hs Ideal.Quotient.mk_surjective H ℓ
    exact (GlobalTheory.SS.DefectZero.isSmoothAt_iff_injective A (MvPolynomial (Fin n) A) R (R ⧸ m) hs m
      (Ideal.mk_ker).symm).mpr key
  have hU : Algebra.smoothLocus A R = Set.univ := by
    refine Set.eq_univ_iff_forall.mpr fun q => ?_
    obtain ⟨m, hm, hqm⟩ := Ideal.exists_le_maximal q.asIdeal q.2.ne_top
    have hm' : (⟨m, hm.isPrime⟩ : PrimeSpectrum R) ∈ Algebra.smoothLocus A R := @hmax m hm
    exact ((PrimeSpectrum.le_iff_specializes q ⟨m, hm.isPrime⟩).mp hqm).mem_open Algebra.isOpen_smoothLocus hm'
  exact ⟨Algebra.smoothLocus_eq_univ_iff.mp hU, inferInstance⟩

theorem smooth_of_artinian_lift : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (X : Scheme.{0}) (s : X ⟶ Sp B), LocallyOfFiniteType s → (∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (t : Sp C ⟶ Sp B) (x₀ : Sp C₀ ⟶ X), x₀ ≫ s = spMap π ≫ t → ∃ x : Sp C ⟶ X, spMap π ≫ x = x₀ ∧ x ≫ s = t) → Smooth s := by
  intro B _ _ X s hs H
  constructor
  intro U hU V hV e
  haveI : IsNoetherianRing Γ(Sp B, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  exact smooth_of_lift _ _ _ (HasRingHomProperty.appLE @LocallyOfFiniteType s hs ⟨U, hU⟩ ⟨V, hV⟩ e) (_root_.GlobalTheory.lift_ringHom_of_scheme_lift B X s H U hU V hV e)

end GlobalTheory.SmoothCrit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPolynomialsToProductVariablesCompMulLeftXStatement
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorPolynomialsToProductVariables_comp_mulLeft_X : ∀ (W Λ : Type) [Fintype W] [DecidableEq W] (w : W) (l : Λ),
    GlobalTheory.CCRFock.polMap W Λ ∘ₗ GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial Λ ℂ) w
                 (LinearMap.mulLeft ℂ (MvPolynomial.X l)) =
      LinearMap.mulLeft ℂ (MvPolynomial.X (w, l)) ∘ₗ GlobalTheory.CCRFock.polMap W Λ := by
  first | exact @GlobalTheory.CCRFock.polMap_comp_atPl_mulLeft_X | exact GlobalTheory.CCRFock.polMap_comp_atPl_mulLeft_X | (intros; apply GlobalTheory.CCRFock.polMap_comp_atPl_mulLeft_X <;> assumption)
end

