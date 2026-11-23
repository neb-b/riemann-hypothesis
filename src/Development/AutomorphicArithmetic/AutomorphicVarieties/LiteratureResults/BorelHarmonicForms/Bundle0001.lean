module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0468

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.AvgPos
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open MeasureTheory
open scoped TensorProduct ComplexOrder

theorem UpperTheory.V.Lit.Bor.avgPos :
    UpperTheory.V.Lit.Bor.AvgPos := by
  intro K _ _ _ _ _ d ρ hρ
  classical
  letI : MeasurableSpace K := borel K
  haveI : BorelSpace K := ⟨rfl⟩
  let μ : Measure K := Measure.haar
  have hint : ∀ f : K → ℂ, Continuous f → Integrable f μ := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hc : ∀ i j, Continuous fun h : K => ρ h⁻¹ i j := fun i j => (hρ i j).comp continuous_inv
  let F : K → Matrix (Fin d) (Fin d) ℂ := fun h => (ρ h⁻¹)ᴴ * ρ h⁻¹
  have hFc : ∀ a b, Continuous fun h => F h a b := by
    intro a b
    simp only [F, Matrix.mul_apply, Matrix.conjTranspose_apply]
    exact continuous_finsetSum _ fun l _ => (continuous_star.comp (hc l a)).mul (hc l b)
  have hlin : ∀ (A C : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d),
      (A * Matrix.of (fun a b => ∫ h, F h a b ∂μ) * C) i j = ∫ h, (A * F h * C) i j ∂μ := by
    intro A C i j
    simp only [Matrix.mul_apply, Matrix.of_apply]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [integral_mul_const, integral_finsetSum]
      · congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [integral_const_mul]
      · intro a _
        exact hint _ (continuous_const.mul (hFc a b))
    · intro b _
      exact hint _ ((continuous_finsetSum _ fun a _ => continuous_const.mul (hFc a b)).mul
        continuous_const)
  refine ⟨Matrix.of fun a b => ∫ h, F h a b ∂μ, ?_, ?_⟩
  · rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨?_, ?_⟩
    · refine Matrix.IsHermitian.ext fun i j => ?_
      simp only [Matrix.of_apply]
      rw [show star (∫ h, F h j i ∂μ) = ∫ h, star (F h j i) ∂μ from integral_conj.symm]
      congr 1
      funext h
      exact (Matrix.isHermitian_conjTranspose_mul_self (ρ h⁻¹)).apply i j
    · intro x hx
      have hq : ∀ h, star x ⬝ᵥ (F h *ᵥ x) = star (ρ h⁻¹ *ᵥ x) ⬝ᵥ (ρ h⁻¹ *ᵥ x) := by
        intro h
        rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
      have hdot : star x ⬝ᵥ (Matrix.of (fun a b => ∫ h, F h a b ∂μ) *ᵥ x) =
          ∫ h, star x ⬝ᵥ (F h *ᵥ x) ∂μ := by
        simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
        rw [integral_finsetSum]
        · refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_finsetSum]
          · refine Finset.sum_congr rfl fun j _ => ?_
            rw [integral_const_mul, integral_mul_const]
          · intro j _
            exact hint _ (continuous_const.mul ((hFc i j).mul continuous_const))
        · intro i _
          exact hint _ (continuous_finsetSum _ fun j _ =>
            continuous_const.mul ((hFc i j).mul continuous_const))
      have hre : ∀ h, star (ρ h⁻¹ *ᵥ x) ⬝ᵥ (ρ h⁻¹ *ᵥ x) =
          ((star (ρ h⁻¹ *ᵥ x) ⬝ᵥ (ρ h⁻¹ *ᵥ x)).re : ℂ) := by
        intro h
        have h0 := (Complex.le_def.mp (dotProduct_star_self_nonneg (ρ h⁻¹ *ᵥ x))).2
        rw [Complex.zero_im] at h0
        apply Complex.ext
        · rw [Complex.ofReal_re]
        · rw [Complex.ofReal_im]
          exact h0.symm
      have hyc : ∀ l, Continuous fun h => (ρ h⁻¹ *ᵥ x) l := by
        intro l
        simp only [Matrix.mulVec, dotProduct]
        exact continuous_finsetSum _ fun j _ => (hc l j).mul continuous_const
      have hdc : Continuous fun h => star (ρ h⁻¹ *ᵥ x) ⬝ᵥ (ρ h⁻¹ *ᵥ x) := by
        simp only [dotProduct, Pi.star_apply]
        exact continuous_finsetSum _ fun l _ => (continuous_star.comp (hyc l)).mul (hyc l)
      rw [hdot]
      simp only [hq]
      rw [congrArg (integral μ) (funext hre), integral_complex_ofReal, Complex.zero_lt_real]
      rw [integral_pos_iff_support_of_nonneg]
      · have hsupp : Function.support (fun h => (star (ρ h⁻¹ *ᵥ x) ⬝ᵥ (ρ h⁻¹ *ᵥ x)).re) =
            Set.univ := by
          ext h
          simp only [Function.mem_support, Set.mem_univ, iff_true]
          intro h0
          have hz : star (ρ h⁻¹ *ᵥ x) ⬝ᵥ (ρ h⁻¹ *ᵥ x) = 0 := by
            rw [hre h, h0, Complex.ofReal_zero]
          rw [dotProduct_star_self_eq_zero] at hz
          apply hx
          have e : ρ h *ᵥ (ρ h⁻¹ *ᵥ x) = x := by
            rw [Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec]
          rw [← e, hz, Matrix.mulVec_zero]
        rw [hsupp]
        exact Measure.measure_univ_pos.mpr (NeZero.ne μ)
      · intro h
        have := (Complex.le_def.mp (dotProduct_star_self_nonneg (ρ h⁻¹ *ᵥ x))).1
        simpa using this
      · exact (Complex.continuous_re.comp hdc).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
  · intro k
    ext i j
    rw [hlin]
    have hF : ∀ h, (ρ k)ᴴ * F h * ρ k = F (k⁻¹ * h) := by
      intro h
      simp only [F, _root_.mul_inv_rev, inv_inv, map_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    simp only [hF]
    exact integral_mul_left_eq_self (fun h => F h i j) k⁻¹
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.AvgProj
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem avg_abs {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ K V)
    (h : ∀ v, ∃ N : Subgroup K, N.Normal ∧ N.FiniteIndex ∧ ∀ n ∈ N, ρ n v = v) :
    ∃ p : Module.End ℂ V, (∀ v u, ρ u (p v) = p v) ∧ (∀ v, (∀ u, ρ u v = v) → p v = v) ∧
      ∀ T : Module.End ℂ V, (∀ u, Commute T (ρ u)) → Commute T p := by
  classical
  obtain ⟨avg, havg⟩ : ∃ avg : Subgroup K → Module.End ℂ V,
      ∀ N, avg N = (N.index : ℂ)⁻¹ • ∑ᶠ q : K ⧸ N, ρ q.out := ⟨_, fun _ => rfl⟩
  have hform : ∀ (N : Subgroup K) [Fintype (K ⧸ N)] (v : V),
      avg N v = (N.index : ℂ)⁻¹ • ∑ q : K ⧸ N, ρ q.out v := by
    intro N _ v
    rw [havg, finsum_eq_sum_of_fintype, LinearMap.smul_apply, LinearMap.sum_apply]
  have hcard : ∀ (N : Subgroup K) [N.FiniteIndex] [Fintype (K ⧸ N)],
      (Fintype.card (K ⧸ N) : ℂ) = N.index ∧ (N.index : ℂ) ≠ 0 := by
    intro N _ _
    refine ⟨by rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card], ?_⟩
    exact_mod_cast Subgroup.index_ne_zero_of_finite
  have hlift : ∀ (N : Subgroup K) (v : V), (∀ n ∈ N, ρ n v = v) →
      ∀ g : K, ρ ((g : K ⧸ N).out) v = ρ g v := by
    intro N v hv g
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N g
    rw [hn, map_mul, Module.End.mul_apply, hv _ n.2]
  have hconj : ∀ (N : Subgroup K) [N.Normal] (v : V), (∀ n ∈ N, ρ n v = v) →
      ∀ k : K, ∀ n ∈ N, ρ n (ρ k v) = ρ k v := by
    intro N hN v hv k n hn
    have h1 : k⁻¹ * n * k ∈ N := by
      simpa using hN.conj_mem n hn k⁻¹
    have h2 : n * k = k * (k⁻¹ * n * k) := by group
    rw [← Module.End.mul_apply, ← map_mul, h2, map_mul, Module.End.mul_apply, hv _ h1]
  have hinv : ∀ (N : Subgroup K) [N.Normal] [N.FiniteIndex] (v : V), (∀ n ∈ N, ρ n v = v) →
      ∀ u : K, ρ u (avg N v) = avg N v := by
    intro N _ _ v hv u
    letI : Fintype (K ⧸ N) := Subgroup.fintypeQuotientOfFiniteIndex
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hform N v, map_smul, map_sum]
    congr 1
    have hq : ∀ q : K ⧸ N, ρ u (ρ q.out v) = ρ ((u • q).out) v := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H g =>
        rw [hlift N v hv, MulAction.Quotient.smul_mk, hlift N v hv, smul_eq_mul, map_mul,
          Module.End.mul_apply]
    simp only [hq]
    exact Equiv.sum_comp (MulAction.toPerm u) (fun q : K ⧸ N => ρ q.out v)
  have hfixed : ∀ (N : Subgroup K) [N.FiniteIndex] (v : V), (∀ u, ρ u v = v) → avg N v = v := by
    intro N _ v hv
    letI : Fintype (K ⧸ N) := Subgroup.fintypeQuotientOfFiniteIndex
    rw [hform N v]
    simp only [hv, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, (hcard N).1, inv_mul_cancel₀ (hcard N).2, one_smul]
  have hshift : ∀ (N : Subgroup K) [N.Normal] [N.FiniteIndex] (v : V), (∀ n ∈ N, ρ n v = v) →
      ∀ k : K, avg N (ρ k v) = avg N v := by
    intro N _ _ v hv k
    letI : Fintype (K ⧸ N) := Subgroup.fintypeQuotientOfFiniteIndex
    rw [hform N (ρ k v), hform N v]
    congr 1
    have hq : ∀ q : K ⧸ N, ρ q.out (ρ k v) = ρ ((q * (k : K ⧸ N)).out) v := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H g =>
        rw [hlift N _ (hconj N v hv k), ← QuotientGroup.mk_mul, hlift N v hv, map_mul,
          Module.End.mul_apply]
    simp only [hq]
    exact Equiv.sum_comp (Equiv.mulRight (k : K ⧸ N)) (fun q : K ⧸ N => ρ q.out v)
  let A : Submodule ℂ V := Submodule.span ℂ {x | ∃ k u, ρ k u - u = x}
  have hdiff : ∀ (N : Subgroup K) [N.FiniteIndex] (v : V), v - avg N v ∈ A := by
    intro N _ v
    letI : Fintype (K ⧸ N) := Subgroup.fintypeQuotientOfFiniteIndex
    have e : v - avg N v = (N.index : ℂ)⁻¹ • ∑ q : K ⧸ N, (v - ρ q.out v) := by
      rw [hform N v, Finset.sum_sub_distrib, smul_sub, Finset.sum_const, Finset.card_univ,
        ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, (hcard N).1, inv_mul_cancel₀ (hcard N).2, one_smul]
    rw [e]
    refine A.smul_mem _ (A.sum_mem fun q _ => ?_)
    rw [← neg_sub]
    exact A.neg_mem (Submodule.subset_span ⟨q.out, v, rfl⟩)
  have hcomm : ∀ (N : Subgroup K) [N.FiniteIndex] (T : Module.End ℂ V),
      (∀ u, Commute T (ρ u)) → ∀ v, T (avg N v) = avg N (T v) := by
    intro N _ T hT v
    letI : Fintype (K ⧸ N) := Subgroup.fintypeQuotientOfFiniteIndex
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hform N v, hform N (T v), map_smul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← Module.End.mul_apply, (hT q.out).eq, Module.End.mul_apply]
  have hkill : ∀ a ∈ A, ∃ N : Subgroup K, N.Normal ∧ N.FiniteIndex ∧
      ∀ N' : Subgroup K, N'.Normal → N'.FiniteIndex → N' ≤ N →
        (∀ n ∈ N', ρ n a = a) ∧ avg N' a = 0 := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, u, rfl⟩ := hx
      obtain ⟨N, hN, hNf, hu⟩ := h u
      refine ⟨N, hN, hNf, fun N' hN' hN'f hle => ?_⟩
      have hu' : ∀ n ∈ N', ρ n u = u := fun n hn => hu n (hle hn)
      refine ⟨fun n hn => ?_, ?_⟩
      · rw [map_sub, hconj N' u hu' k n hn, hu' n hn]
      · rw [map_sub, hshift N' u hu' k, sub_self]
    | zero =>
      refine ⟨⊤, inferInstance, inferInstance, fun N' _ _ _ => ⟨fun n _ => map_zero _, map_zero _⟩⟩
    | add x y _ _ hx hy =>
      obtain ⟨N1, h1n, h1f, h1⟩ := hx
      obtain ⟨N2, h2n, h2f, h2⟩ := hy
      refine ⟨N1 ⊓ N2, inferInstance, inferInstance, fun N' hN' hN'f hle => ?_⟩
      obtain ⟨a1, b1⟩ := h1 N' hN' hN'f (hle.trans inf_le_left)
      obtain ⟨a2, b2⟩ := h2 N' hN' hN'f (hle.trans inf_le_right)
      refine ⟨fun n hn => ?_, ?_⟩
      · rw [map_add (f := _), a1 n hn, a2 n hn]
      · rw [map_add (f := _), b1, b2, add_zero]
    | smul c x _ hx =>
      obtain ⟨N1, h1n, h1f, h1⟩ := hx
      refine ⟨N1, h1n, h1f, fun N' hN' hN'f hle => ?_⟩
      obtain ⟨a1, b1⟩ := h1 N' hN' hN'f hle
      refine ⟨fun n hn => ?_, ?_⟩
      · rw [map_smul, a1 n hn]
      · rw [map_smul, b1, smul_zero]
  have hzero : ∀ w ∈ A, (∀ u, ρ u w = w) → w = 0 := by
    intro w hw hfix
    obtain ⟨N, hN, hNf, hN'⟩ := hkill w hw
    rw [← hfixed N w hfix]
    exact (hN' N hN hNf le_rfl).2
  choose Nv hNv hNvf hNvfix using h
  let pf : V → V := fun v => avg (Nv v) v
  have hagree : ∀ (N : Subgroup K) [N.Normal] [N.FiniteIndex] (v : V), (∀ n ∈ N, ρ n v = v) →
      avg N v = pf v := by
    intro N _ _ v hv
    haveI := hNv v
    haveI := hNvf v
    rw [← sub_eq_zero]
    apply hzero
    · have e : avg N v - pf v = (v - pf v) - (v - avg N v) := by abel
      rw [e]
      exact A.sub_mem (hdiff _ v) (hdiff N v)
    · intro u
      rw [map_sub, hinv N v hv u, hinv (Nv v) v (hNvfix v) u]
  let p : Module.End ℂ V :=
    { toFun := pf
      map_add' := fun v w => by
        haveI := hNv v; haveI := hNvf v; haveI := hNv w; haveI := hNvf w
        have hv : ∀ n ∈ Nv v ⊓ Nv w, ρ n v = v := fun n hn => hNvfix v n hn.1
        have hw : ∀ n ∈ Nv v ⊓ Nv w, ρ n w = w := fun n hn => hNvfix w n hn.2
        have hvw : ∀ n ∈ Nv v ⊓ Nv w, ρ n (v + w) = v + w := fun n hn => by
          rw [map_add (f := _), hv n hn, hw n hn]
        rw [← hagree _ _ hvw, ← hagree _ _ hv, ← hagree _ _ hw, map_add (f := _)]
      map_smul' := fun c v => by
        haveI := hNv v; haveI := hNvf v
        have hcv : ∀ n ∈ Nv v, ρ n (c • v) = c • v := fun n hn => by
          rw [map_smul, hNvfix v n hn]
        rw [RingHom.id_apply, ← hagree _ _ hcv, map_smul] }
  refine ⟨p, fun v u => ?_, fun v hv => ?_, fun T hT => ?_⟩
  · haveI := hNv v; haveI := hNvf v
    exact hinv (Nv v) v (hNvfix v) u
  · haveI := hNvf v
    exact hfixed (Nv v) v hv
  · refine LinearMap.ext fun v => ?_
    haveI := hNv v; haveI := hNvf v
    have hTv : ∀ n ∈ Nv v, ρ n (T v) = T v := fun n hn => by
      rw [← Module.End.mul_apply, ← (hT n).eq, Module.End.mul_apply, hNvfix v n hn]
    show T (pf v) = pf (T v)
    rw [← hagree (Nv v) (T v) hTv]
    exact hcomm (Nv v) T hT v

theorem UpperTheory.V.Lit.Bor.avgProj :
    UpperTheory.V.Lit.Bor.AvgProj := by
  intro G V _ _ _ _ _ ρ U hU hopen
  haveI : CompactSpace U := isCompact_iff_compactSpace.mp hU
  let ρU : Representation ℂ U V := ρ.comp U.subtype
  have h : ∀ v, ∃ N : Subgroup U, N.Normal ∧ N.FiniteIndex ∧ ∀ n ∈ N, ρU n v = v := by
    intro v
    let S : Subgroup U :=
      { carrier := {u | ρ (u : G) v = v}
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq, Subgroup.coe_mul, map_mul, Module.End.mul_apply] at *
          rw [hb, ha]
        one_mem' := by simp
        inv_mem' := fun {a} ha => by
          simp only [Set.mem_setOf_eq, Subgroup.coe_inv] at *
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
    have hS : IsOpen (S : Set U) := (hopen v).preimage continuous_subtype_val
    haveI : Finite (U ⧸ S) := Subgroup.quotient_finite_of_isOpen S hS
    haveI : S.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    exact ⟨S.normalCore, inferInstance, inferInstance, fun n hn => S.normalCore_le hn⟩
  obtain ⟨p, h1, h2, h3⟩ := avg_abs ρU h
  exact ⟨p, fun v u hu => h1 v ⟨u, hu⟩, fun v hv => h2 v (fun u => hv u u.2),
    fun T hT => h3 T (fun u => hT u u.2)⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.BasicEx
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem basic_of_ne_zero {E : Type} [Field E] {a : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M]
    (κ : Kinf E a → Module.End ℂ M) (q : ℕ) :
    ∀ ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M, ω ≠ 0 → IsCochain κ ω →
      ∃ (q : ℕ) (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M), ω ≠ 0 ∧ IsCochain κ ω ∧ IsBasic ω := by
  let Z : Herm E a := ⟨1, IsSelfAdjoint.one _⟩
  have hZ : ∀ k, adHerm k Z = Z := fun k => Subtype.ext (by
    change k.1 * 1 * star k.1 = 1
    rw [mul_one]; exact k.2.2)
  induction q with
  | zero => exact fun ω h0 h1 => ⟨0, ω, h0, h1, fun _ i => i.elim0⟩
  | succ q ih =>
    intro ω h0 h1
    by_cases hc : ω.curryLeft Z = 0
    · refine ⟨q + 1, ω, h0, h1, fun X i hi => ?_⟩
      have hi' : X i = Z := Subtype.ext hi
      have key : ∀ Y : Fin (q + 1) → Herm E a, Y 0 = Z → ω Y = 0 := fun Y hY => by
        have h := DFunLike.congr_fun hc (Fin.tail Y)
        have e : Matrix.vecCons Z (Fin.tail Y) = Y := by rw [← hY]; exact Fin.cons_self_tail Y
        rw [← e]
        exact h
      by_cases hi0 : (0 : Fin (q + 1)) = i
      · exact key X (hi0 ▸ hi')
      · have h := ω.map_swap X hi0
        rw [key _ (by simpa using hi')] at h
        exact neg_eq_zero.1 h.symm
    · refine ih _ hc fun k X => ?_
      change ω (Matrix.vecCons Z _) = κ k (ω (Matrix.vecCons Z X))
      rw [← h1]
      congr 1
      funext j
      refine Fin.cases ?_ (fun j => ?_) j <;> simp [hZ]

theorem UpperTheory.V.Lit.Bor.basicEx :
    UpperTheory.V.Lit.Bor.BasicEx := by
  intro E _ _ _ a M _ _ _ _ κ L h
  rcases h with ⟨ω, h1, -, h0⟩ | ⟨q, ω, h1, -, h2⟩
  · exact basic_of_ne_zero κ 0 ω h0 h1
  · refine basic_of_ne_zero κ _ ω (fun h => h2 0 (fun k X => by simp) ?_) h1
    rw [h]
    exact AlternatingMap.ext fun X => by simp [dCo_apply]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2Variant
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.derivative_right_translate_L2 :
    UpperTheory.V.Lit.Bor.DerivativeRightTranslateL2 := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ _ φ ψ hφ hψ c hψc hc hc0 hcadd hder
  have hf : Continuous fun s : ℝ => (GlobalTheory.AutomorphicL2Unitary.R Γ μ (c s)) hψ.toL2 :=
    (GlobalTheory.AutomorphicL2Unitary.continuous_R hψ.toL2).comp hc
  have hI := hf.integral_hasStrictDerivAt 0 0
  have hE : (fun s : ℝ => (GlobalTheory.AutomorphicL2Unitary.R Γ μ (c s)) hφ.toL2) =
      fun t => (∫ s in (0 : ℝ)..t, (GlobalTheory.AutomorphicL2Unitary.R Γ μ (c s)) hψ.toL2) + hφ.toL2 := by
    funext t
    rw [← GlobalTheory.CompanionTheory.TransDeriv.R_sub_eq_integral hφ hψ hψc hc hc0 hcadd hder t]
    abel
  rw [hE]
  have h := hI.hasDerivAt.add_const hφ.toL2
  simpa [hc0] using h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.EllFacts
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem ell_toL {E : Type} [Field E] [NumberField E] {a : ℕ} (X : Matrix (Fin a) (Fin a) (Cinf E)) :
    ell E a (toL X) = (∑ w : InfinitePlace E, (X.trace w).re) / ((a : ℝ) * Fintype.card (InfinitePlace E)) := by
  simp [ell, Matrix.trace, Finset.sum_apply]

private theorem ell_br {E : Type} [Field E] [NumberField E] {a : ℕ} (X Y : Matrix (Fin a) (Fin a) (Cinf E)) :
    ell E a (toL (X * Y - Y * X)) = 0 := by
  rw [ell_toL, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
  simp

theorem UpperTheory.V.Lit.Bor.ellFacts :
    UpperTheory.V.Lit.Bor.EllFacts := by
  intro E _ _ _ a
  refine ⟨fun ha => ?_, ell_br, fun k X => ?_, fun A _ _ _ _ L r hL X Y => ?_⟩
  · have h1 : (a : ℝ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
    have h2 : (Fintype.card (InfinitePlace E) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    change ell E a (toL 1) = 1
    rw [ell_toL, div_eq_one_iff_eq (mul_ne_zero h1 h2)]
    simp [mul_comm]
  · rw [ell_toL, ell_toL, Matrix.trace_mul_cycle, k.2.1, one_mul]
  · have h := hL X Y
    simp only [shift_apply, ell_br, mul_zero, zero_smul, add_zero, ← h, mul_add, add_mul, smul_mul_assoc, mul_smul_comm,
      one_mul, mul_one, smul_add, smul_smul]
    rw [mul_comm (r * ell E a (toL Y))]
    abel
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.ExpOfDeriv
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem exp_of_deriv (f : ℝ → ℂ) (c : ℂ) (hf : ∀ u, HasDerivAt f (c * f u) u) (t : ℝ) :
    f t = Complex.exp (c * t) * f 0 := by
  have h1 : ∀ u : ℝ, HasDerivAt (fun v : ℝ => Complex.exp (-c * v) * f v) 0 u := fun u => by
    have h2 : HasDerivAt (fun v : ℝ => -c * (v : ℂ)) (-c) u := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := u)).const_mul (-c)
    exact (h2.cexp.fun_mul (hf u)).congr_deriv (by ring)
  have h3 := is_const_of_deriv_eq_zero (fun u => (h1 u).differentiableAt) (fun u => (h1 u).deriv) t 0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at h3
  rw [← h3, ← mul_assoc, ← Complex.exp_add]
  simp

section
variable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)

private noncomputable def sc (t : ℝ) : GL (Fin a) (Cinf E) :=
  Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => (t : ℂ))

private theorem sc_zero : sc E a 0 = 1 := by
  have h : (expU fun _ : InfinitePlace E => ((0 : ℝ) : ℂ)) = 1 := Units.ext (funext fun _ => by simp [expU])
  rw [sc, h, map_one]

private theorem sc_deriv : HasDerivAt (fun t => toL (sc E a t).val) (oneL E a) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => Complex.exp (t : ℂ)) 1 0 := by
    simpa using (Complex.hasDerivAt_exp ((0 : ℝ) : ℂ)).comp_ofReal
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun w => ?_
  have e : (fun t : ℝ => toL (sc E a t).val i j w) = fun t : ℝ => Complex.exp (t : ℂ) * oneL E a i j w := by
    funext t
    by_cases h : i = j
    · subst h
      simp [sc, toL, oneL, expU, Matrix.scalar_apply]
    · simp [sc, toL, oneL, Matrix.scalar_apply, h]
  rw [e]
  exact (h1.mul_const _).congr_deriv (one_mul _)

end

theorem UpperTheory.V.Lit.Bor.aInv :
    UpperTheory.V.Lit.Bor.AInv := by
  intro E _ _ _ a φ c hφ t g
  have h := exp_of_deriv (fun u => φ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a u)) c (fun u => by
    have h1 := hasDerivAt_curve φ (g * GlobalTheory.UnitaryBC.splitCentre E a u) (sc E a) (oneL E a) (sc_zero E a) (sc_deriv E a)
    have h2 : lieD (oneL E a) φ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a u) = c * φ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a u) :=
      congrArg (fun ψ : Sm E a => ψ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a u)) hφ
    rw [h2] at h1
    have h3 := HasDerivAt.comp_sub_const u u (by rw [sub_self]; exact h1)
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
    have e := CuspidalL2GL.splitCentre_add (E := E) (a := a) u (x - u)
    rw [add_sub_cancel] at e
    simp only [e, mul_assoc]
    rfl) t
  rw [CuspidalL2GL.splitCentre_comm]
  simpa only [CuspidalL2GL.splitCentre_zero, mul_one] using h
end

