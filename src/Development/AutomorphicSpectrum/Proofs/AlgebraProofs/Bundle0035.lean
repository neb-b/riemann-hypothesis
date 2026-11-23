module

public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import Development.WeilBound.CoreStatements.HodgeTatePoints.RiRank
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0029
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0020
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0022
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0029
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0031
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0026
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0030
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0019
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0028
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0013

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalCharacterIdealPowers
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open PositivityTheory.HtPt.Ri (wsum wsum_eq mem_xIdeal v_card_sub_one)
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem r_decomp_relay : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable (F := F) AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ c : ℕ → R, (∀ m, xIdeal AA.carrier (σ ^ m) = Ideal.span {c m}) → augIdeal AA.carrier = Submodule.span R ((fun m (a : F) => algebraMap R C (c m * (σ ^ m) a)) '' (Finset.Icc 1 (p ^ f - 1) : Set ℕ)) ∧ AA.carrier = Submodule.span R {(1 : F → C)} ⊔ augIdeal AA.carrier ∧ HasColen R v AA.carrier (∏ m ∈ Finset.Icc 1 (p ^ f - 1), v (algebraMap R C (c m))) := by
  intro p _ C _ _ _ v R _ _ hv hpv F _ _ _ _ f hcard AA hM σ hσ c hc
  have wsum_one (χ : MulChar F R) {g : F → C} (hg : g ∈ AA.carrier)
      (h0 : wsum χ g 0 = 0) :
      ∃ r ∈ xIdeal AA.carrier χ, algebraMap R C r = wsum χ g 1 := by
    have heq : wsum χ g = ∑ a : F, χ⁻¹ a • fun x => g (a • x) := by
      funext x
      simp [wsum, Finset.sum_apply, Algebra.smul_def]
    have hm : wsum χ g ∈ AA.carrier := by
      rw [heq]
      exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hM a g hg)
    obtain ⟨r, hr⟩ := AA.le_int hm 1
    refine ⟨r, (mem_xIdeal _ _ _).2 ?_, hr⟩
    convert hm using 1
    funext a
    rw [wsum_eq χ g h0 a, hr, mul_comm]
  obtain ⟨hord, -, -, -, hsep⟩ := GlobalTheory.CompanionTheory.Ar.GR.FundGen.main p C v R hv hpv F f hcard σ hσ
  set n := p ^ f - 1 with hn
  have hcardn : Fintype.card F = n + 1 := by
    rw [hcard, hn, Nat.sub_add_cancel (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos)]
  have hn1 : 1 ≤ n := by
    have := Fintype.one_lt_card (α := F)
    omega
  have hσn : σ ^ n = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one σ
  have hpow : ∀ m, m ≠ 0 → ∀ z : F, (σ ^ m) z = σ z ^ m := fun m hm z => MulChar.pow_apply' σ hm z
  have hIcc : ∀ g : ℕ → C, ∑ m ∈ Finset.Icc 1 n, g m = ∑ i ∈ Finset.range n, g (i + 1) := by
    intro g
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, add_comm 1]
  have horth : ∀ z : F, ∑ m ∈ Finset.Icc 1 n, algebraMap R C ((σ ^ m) z) = if z = 1 then (n : C) else 0 := by
    intro z
    by_cases hz1 : z = 1
    · subst hz1
      simp
    rw [ite_eq_right hz1]
    by_cases hz0 : z = 0
    · subst hz0
      refine Finset.sum_eq_zero fun m _ => ?_
      rw [MulChar.map_nonunit _ not_isUnit_zero, map_zero]
    have hsz := hsep z 1 hz1
    have hζ1 : algebraMap R C (σ z) ≠ 1 := by
      intro h
      rw [map_sub, h, map_one, map_one, sub_self, map_zero] at hsz
      exact zero_ne_one hsz
    have hζn : algebraMap R C (σ z) ^ n = 1 := by
      rw [← map_pow, ← hpow n (by omega), hσn, MulChar.one_apply (Ne.isUnit hz0), map_one]
    rw [hIcc]
    have e : ∀ i, algebraMap R C ((σ ^ (i + 1)) z) = algebraMap R C (σ z) * algebraMap R C (σ z) ^ i := by
      intro i
      rw [hpow _ (Nat.succ_ne_zero i), map_pow, pow_succ, mul_comm]
    simp_rw [e, ← Finset.mul_sum, geom_sum_eq hζ1, hζn, sub_self, zero_div, mul_zero]
  have hb : ∀ m, (fun a : F => algebraMap R C (c m * (σ ^ m) a)) ∈ AA.carrier := by
    intro m
    have := (mem_xIdeal AA.carrier (σ ^ m) (c m)).mp (by rw [hc m]; exact Ideal.mem_span_singleton_self _)
    simpa only [map_mul] using this
  have hn0 : (n : C) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  obtain ⟨qi, hqi⟩ : ∃ qi : R, algebraMap R C qi = (n : C)⁻¹ := by
    have h5 := v_card_sub_one (R := R) (F := F) p hv hpv
    rw [hcardn, Nat.cast_succ, add_sub_cancel_right] at h5
    exact hv.exists_of_le_one (by rw [map_inv₀, h5, inv_one])
  have hI : augIdeal AA.carrier = Submodule.span R ((fun m (a : F) => algebraMap R C (c m * (σ ^ m) a)) '' (Finset.Icc 1 (p ^ f - 1) : Set ℕ)) := by
    apply le_antisymm
    · intro g hg
      simp only [augIdeal, Submodule.mem_inf, LinearMap.mem_ker] at hg
      have hgA := hg.1
      have hg0 : g 0 = 0 := hg.2
      have hk : ∀ m, ∃ k : R, wsum (σ ^ m) g 1 = algebraMap R C (k * c m) := by
        intro m
        obtain ⟨r, hr, hr1⟩ := wsum_one (σ ^ m) hgA (by simp [wsum, hg0])
        rw [hc m] at hr
        obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.mp hr
        exact ⟨k, hr1.symm⟩
      choose k hk using hk
      have e4 : ∀ a : F, ∑ m ∈ Finset.Icc 1 n, algebraMap R C ((σ ^ m)⁻¹ a) = if a = 1 then (n : C) else 0 := by
        intro a
        simp_rw [MulChar.inv_apply']
        rw [horth a⁻¹]
        simp [inv_eq_one]
      have hg_eq : g = ∑ m ∈ Finset.Icc 1 n, (qi * k m) • (fun a : F => algebraMap R C (c m * (σ ^ m) a)) := by
        funext x
        rw [Finset.sum_apply]
        simp only [Pi.smul_apply, Algebra.smul_def, map_mul, hqi]
        have hw : ∀ m ∈ Finset.Icc 1 n, wsum (σ ^ m) g x = algebraMap R C ((σ ^ m) x) * (algebraMap R C (k m) * algebraMap R C (c m)) := by
          intro m _
          rw [wsum_eq (σ ^ m) g (by simp [wsum, hg0]) x, hk m, map_mul]
        have hsum : ∑ m ∈ Finset.Icc 1 n, wsum (σ ^ m) g x = (n : C) * g x := by
          simp only [wsum]
          calc ∑ m ∈ Finset.Icc 1 n, ∑ a, algebraMap R C ((σ ^ m)⁻¹ a) * g (a * x)
              = ∑ a, (∑ m ∈ Finset.Icc 1 n, algebraMap R C ((σ ^ m)⁻¹ a)) * g (a * x) := by
                rw [Finset.sum_comm]
                simp_rw [Finset.sum_mul]
            _ = _ := by
                simp_rw [e4]
                simp [ite_mul]
        rw [Finset.sum_congr rfl hw] at hsum
        calc g x = (n : C)⁻¹ * ((n : C) * g x) := by field_simp
          _ = _ := by
            rw [← hsum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun m _ => ?_
            ring
      rw [hg_eq]
      exact Submodule.sum_mem _ fun m hm => Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, Finset.mem_coe.mpr hm, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨m, hm, rfl⟩
      simp only [augIdeal, SetLike.mem_coe, Submodule.mem_inf, LinearMap.mem_ker]
      refine ⟨hb m, ?_⟩
      show algebraMap R C (c m * (σ ^ m) 0) = 0
      rw [MulChar.map_nonunit _ not_isUnit_zero, mul_zero, map_zero]
  have hII : AA.carrier = Submodule.span R {(1 : F → C)} ⊔ augIdeal AA.carrier := by
    apply le_antisymm
    · intro g hg
      obtain ⟨r, hr⟩ : ∃ r : R, algebraMap R C r = g 0 := AA.le_int hg 0
      rw [← add_sub_cancel (r • (1 : F → C)) g]
      refine Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)) ?_
      simp only [augIdeal, Submodule.mem_inf, LinearMap.mem_ker]
      refine ⟨AA.carrier.sub_mem hg (AA.carrier.smul_mem r AA.one_mem), ?_⟩
      show (g - r • (1 : F → C)) 0 = 0
      simp [Algebra.smul_def, ← hr]
    · refine sup_le ?_ (fun g hg => by simp only [augIdeal, Submodule.mem_inf] at hg; exact hg.1)
      rw [Submodule.span_le, Set.singleton_subset_iff]
      exact AA.one_mem
  refine ⟨hI, hII, ?_⟩
  let e := Fintype.equivFinOfCardEq hcardn
  have hre : ∀ g : ℕ → C, ∑ j : F, g (e j : ℕ) = g 0 + ∑ m ∈ Finset.Icc 1 n, g m := by
    intro g
    rw [e.sum_comp (fun k : Fin (n + 1) => g k), Fin.sum_univ_eq_sum_range g (n + 1), Finset.sum_range_succ', hIcc, add_comm]
  have hreP : ∀ g : ℕ → NNReal, ∏ j : F, g (e j : ℕ) = g 0 * ∏ m ∈ Finset.Icc 1 n, g m := by
    intro g
    rw [e.prod_comp (fun k : Fin (n + 1) => g k), Fin.prod_univ_eq_prod_range g (n + 1), Finset.prod_range_succ',
      ← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range, mul_comm]
    simp only [Nat.add_sub_cancel, add_comm 1]
  let TR : Matrix F F R := Matrix.of fun x j => if (e j : ℕ) = 0 then 1 else (σ ^ (e j : ℕ)) x
  let UR : Matrix F F R := Matrix.of fun j y => if (e j : ℕ) = 0 then (if y = 0 then 1 else 0)
    else if y = 0 then (if (e j : ℕ) = n then -1 else 0) else qi * (σ ^ (e j : ℕ))⁻¹ y
  let d : F → C := fun j => if (e j : ℕ) = 0 then 1 else algebraMap R C (c (e j))
  let T := TR.map (algebraMap R C)
  let U := UR.map (algebraMap R C)
  have hTU : T * U = 1 := by
    ext x y
    rw [Matrix.mul_apply]
    simp only [T, U, Matrix.map_apply, Matrix.of_apply, TR, UR]
    have h6 := hre (fun k => algebraMap R C (if k = 0 then 1 else (σ ^ k) x) *
      algebraMap R C (if k = 0 then (if y = 0 then 1 else 0) else if y = 0 then (if k = n then -1 else 0) else qi * (σ ^ k)⁻¹ y))
    simp only at h6
    rw [h6]
    rw [Finset.sum_congr rfl (g := fun m => algebraMap R C ((σ ^ m) x) * algebraMap R C (if y = 0 then (if m = n then -1 else 0) else qi * (σ ^ m)⁻¹ y))
      (fun m hm => by rw [ite_eq_right (by simp at hm; omega), ite_eq_right (by simp at hm; omega)])]
    by_cases hy : y = 0
    · subst hy
      simp only [ite_true, map_one, apply_ite (algebraMap R C), map_neg, map_zero, mul_ite, mul_neg, mul_one, mul_zero]
      rw [Finset.sum_ite_eq' (Finset.Icc 1 n) n, ite_eq_left (Finset.mem_Icc.mpr ⟨hn1, le_rfl⟩), hσn]
      by_cases hx : x = 0
      · subst hx
        rw [MulChar.map_nonunit (1 : MulChar F R) (not_isUnit_zero (M₀ := F)), map_zero, neg_zero, add_zero,
          Matrix.one_apply_eq]
      · rw [MulChar.one_apply (Ne.isUnit hx), map_one, Matrix.one_apply_ne hx]
        ring
    · simp only [ite_eq_right hy, ite_true, map_zero, mul_zero, zero_add, map_mul, hqi]
      have e5 : ∀ m, algebraMap R C ((σ ^ m) x) * ((n : C)⁻¹ * algebraMap R C ((σ ^ m)⁻¹ y)) =
          (n : C)⁻¹ * algebraMap R C ((σ ^ m) (x * y⁻¹)) := by
        intro m
        rw [MulChar.inv_apply', map_mul (σ ^ m) x, map_mul]
        ring
      simp_rw [e5]
      rw [← Finset.mul_sum, horth, Matrix.one_apply]
      by_cases hxy : x = y
      · subst hxy
        rw [mul_inv_cancel₀ hy, ite_eq_left rfl, ite_eq_left rfl, inv_mul_cancel₀ hn0]
      · rw [ite_eq_right (by rwa [mul_inv_eq_one₀ hy]), ite_eq_right hxy, mul_zero]
  have hdetTU : T.det * U.det = 1 := by rw [← Matrix.det_mul, hTU, Matrix.det_one]
  have hTdet : T.det = algebraMap R C TR.det := (RingHom.map_det _ _).symm
  have hUdet : U.det = algebraMap R C UR.det := (RingHom.map_det _ _).symm
  have hvT : v T.det = 1 := by
    have h1 := congrArg v hdetTU
    rw [map_mul, map_one, hUdet] at h1
    have hT1 : v T.det ≤ 1 := by
      rw [hTdet]
      exact hv.map_le_one _
    have hU1 := hv.map_le_one UR.det
    refine le_antisymm hT1 ?_
    calc (1 : NNReal) = v T.det * v (algebraMap R C UR.det) := h1.symm
      _ ≤ v T.det * 1 := by gcongr
      _ = v T.det := mul_one _
  have hcol : ∀ j, (fun x => (T * Matrix.diagonal d) x j) =
      fun x => if (e j : ℕ) = 0 then 1 else algebraMap R C (c (e j) * (σ ^ (e j : ℕ)) x) := by
    intro j
    funext x
    rw [Matrix.mul_diagonal]
    simp only [T, d, TR, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp [map_mul, mul_comm]
  refine ⟨T * Matrix.diagonal d, ?_, ?_⟩
  · apply le_antisymm
    · rw [hII, hI, sup_le_iff]
      constructor
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        apply Submodule.subset_span
        refine ⟨e.symm ⟨0, by omega⟩, (hcol _).trans ?_⟩
        funext x
        simp
      · rw [Submodule.span_le]
        rintro _ ⟨m, hm, rfl⟩
        have hm' : 1 ≤ m ∧ m ≤ n := by simpa using hm
        apply Submodule.subset_span
        refine ⟨e.symm ⟨m, by omega⟩, (hcol _).trans ?_⟩
        funext x
        simp only [Equiv.apply_symm_apply]
        split_ifs with h0
        · exact absurd (h0 : m = 0) (by omega)
        · rfl
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      show (fun x => (T * Matrix.diagonal d) x j) ∈ AA.carrier
      rw [hcol j]
      by_cases hj : (e j : ℕ) = 0
      · simp only [hj, ite_true]
        exact AA.one_mem
      · simp only [hj, ite_false]
        exact hb _
  · rw [Matrix.det_mul, Matrix.det_diagonal, map_mul, hvT, one_mul, map_prod]
    have h7 := hreP (fun k => v (if k = 0 then 1 else algebraMap R C (c k)))
    simp only at h7
    rw [show (∏ j, v (d j)) = ∏ j, v (if (e j : ℕ) = 0 then 1 else algebraMap R C (c (e j))) from rfl, h7]
    simp only [↓reduceIte, map_one, one_mul]
    refine Finset.prod_congr rfl fun m hm => ?_
    rw [ite_eq_right (by simp at hm; omega)]

end GlobalTheory.CompanionTheory.Ar.GR
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeLatticeDualEigenDecomposition
section
open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExG.DualFil

section
variable {E : Type} [Field E] [NumberField E] {C : Type} [Field C] {W : Type} [AddCommGroup W]
  [Module C W]

theorem eigProj_comp_bar [Fintype (E →+* C)] (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* C)
    (ρ : 𝓞 E →+* Module.End C W) (hsum : ∀ y, ∑ s, HT.eigProj ρ s y = y)
    (hσ : ∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) (hbar : ∀ a, bar (bar a) = a) (x : W) :
    HT.eigProj (ρ.comp (bar : 𝓞 E →+* 𝓞 E)) σ x = HT.eigProj ρ σ' x := by
  classical
  conv_lhs => rw [← hsum x]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_single σ']
  · apply HT.LatBasic.eigProj_of_mem
    rw [HT.LatBasic.mem_eigSp]
    intro a
    have h := HT.LatBasic.mem_eigSp.1 (HT.LatBasic.eigProj_mem ρ σ' x) (bar a)
    rw [hσ, hbar] at h
    exact h
  · intro s _ hs
    refine HT.LatBasic.eigProj_of_eigenSub_ne
      (χ := (s.comp (algebraMap (𝓞 E) E)).comp (bar : 𝓞 E →+* 𝓞 E)) ?_ ?_
    · intro e
      apply hs
      apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
      refine RingHom.ext fun a => ?_
      have h := DFunLike.congr_fun e (bar a)
      have h2 : σ ((bar a : 𝓞 E) : E) = s (a : E) := by
        simpa [hbar] using h
      change s (a : E) = σ' (a : E)
      rw [hσ, h2]
    · rw [GlobalTheory.EigenSplit.mem_eigenSub]
      intro a
      exact HT.LatBasic.mem_eigSp.1 (HT.LatBasic.eigProj_mem ρ s x) (bar a)
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem eigProj_zero_form (bar : 𝓞 E ≃+* 𝓞 E) (σ : E →+* C) (ρ : 𝓞 E →+* Module.End C W)
    (ρH : 𝓞 E →+* Module.End C (W × Module.Dual C W))
    (hact : ∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) (φ : Module.Dual C W) :
    HT.eigProj ρH σ (0, φ) = (0, φ ∘ₗ HT.eigProj (ρ.comp (bar : 𝓞 E →+* 𝓞 E)) σ) := by
  simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply, hact]
  refine Prod.ext ?_ ?_
  · simp [Prod.fst_sum]
  · ext x
    simp [Prod.snd_sum, LinearMap.sum_apply]

end

theorem span_iff_proj : ∀ (E : Type) [Field E] [NumberField E] (V C : Type) [CommRing V] [Field C] [Algebra V C] [Fintype (E →+* C)] (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* C) (W : Type) [AddCommGroup W] [Module C W] [Module V W] [IsScalarTower V C W] (ρ : 𝓞 E →+* Module.End C W) (ρH : 𝓞 E →+* Module.End C (W × Module.Dual C W)) (HV : Submodule V (W × Module.Dual C W)) (Lie : Submodule V W) (n : ℕ) (w : Fin n → W) (ψ : Fin n → W × Module.Dual C W), (∀ y, ∑ s, HT.eigProj ρ s y = y) → (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) → (∀ φ : Module.Dual C W, (0, φ) ∈ HV ↔ ∀ e ∈ Lie, φ e ∈ (algebraMap V C).range) → Submodule.span C (Set.range w) = HT.eigSp ρ σ' → (∀ j, w j ∈ Lie) → (∀ j, ψ j ∈ HT.eigSp ρH σ ∧ (ψ j).1 = 0 ∧ ∀ j', (ψ j).2 (w j') = if j = j' then 1 else 0) → (∀ j, ∃ φ : Module.Dual C W, (∀ y ∈ Lie, φ y ∈ (algebraMap V C).range) ∧ ∀ k, φ (w k) = if k = j then 1 else 0) → ∀ y, y ∈ Submodule.span V (Set.range ψ) ↔ ∃ φ : Module.Dual C W, ((0, φ) : W × Module.Dual C W) ∈ HV ∧ HT.eigProj ρH σ (0, φ) = y := by
  intro E _ _ V C _ _ _ _ bar σ σ' W _ _ _ _ ρ ρH HV Lie n w ψ hsum hσ hbar _ hact hlat hspan hwL hψ hint y
  classical

  have hform : ∀ φ : Module.Dual C W, HT.eigProj ρH σ (0, φ) = (0, φ ∘ₗ HT.eigProj ρ σ') := by
    intro φ
    rw [eigProj_zero_form bar σ ρ ρH hact φ]
    refine Prod.ext rfl ?_
    ext x
    simp only [LinearMap.comp_apply]
    rw [eigProj_comp_bar bar σ σ' ρ hsum hσ hbar x]
  have hψe : ∀ j, ψ j = (0, (ψ j).2) := fun j => Prod.ext (hψ j).2.1 rfl

  have hχ : ∀ j x, (ψ j).2 x = (ψ j).2 (HT.eigProj ρ σ' x) := by
    intro j x
    have h := HT.LatBasic.eigProj_of_mem (hψ j).1
    rw [hψe j, hform] at h
    have h2 := congrArg (fun z : W × Module.Dual C W => z.2 x) h
    exact h2.symm

  have hexp : ∀ x, HT.eigProj ρ σ' x = ∑ j, (ψ j).2 x • w j := by
    intro x
    have hm : HT.eigProj ρ σ' x ∈ Submodule.span C (Set.range w) := by
      rw [hspan]; exact HT.LatBasic.eigProj_mem ρ σ' x
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun C).1 hm
    have hcj : ∀ j, (ψ j).2 x = c j := by
      intro j
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hχ j x, ← hc, map_sum]
      simp [(hψ j).2.2]
    simp only [hcj]
    exact hc.symm

  have key : ∀ φ : Module.Dual C W, HT.eigProj ρH σ (0, φ) = ∑ j, φ (w j) • ψ j := by
    intro φ
    rw [hform]
    refine Prod.ext ?_ ?_
    · simp [Prod.fst_sum, (hψ _).2.1]
    · ext x
      simp only [LinearMap.comp_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hexp x, map_sum, Prod.snd_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [mul_comm]

  have hsm : ∀ (v : V) (z : W × Module.Dual C W), v • z = algebraMap V C v • z := by
    intro v z
    refine Prod.ext ?_ ?_
    · simp
    · ext x
      simp [Algebra.smul_def]
  constructor
  · intro hy
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun V).1 hy
    choose φ hφ1 hφ2 using hint
    refine ⟨∑ j, algebraMap V C (c j) • φ j, ?_, ?_⟩
    · rw [hlat]
      intro e he
      rw [LinearMap.sum_apply]
      refine Subring.sum_mem _ fun j _ => ?_
      rw [LinearMap.smul_apply, smul_eq_mul]
      exact Subring.mul_mem _ ⟨c j, rfl⟩ (hφ1 j e he)
    · rw [key]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hk : (∑ j, algebraMap V C (c j) • φ j) (w k) = algebraMap V C (c k) := by
        rw [LinearMap.sum_apply]
        simp only [LinearMap.smul_apply, hφ2, smul_eq_mul, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq]
        simp
      rw [hsm, hk]
  · rintro ⟨φ, h0, rfl⟩
    rw [key]
    refine Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨v, hv⟩ := (hlat φ).1 h0 (w j) (hwL j)
    rw [← hv, ← hsm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end GlobalTheory.CompanionTheory.Ar.Flat.ExG.DualFil
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ImportsAlt
section
namespace GlobalTheory.CompanionTheory.CommAlg.JoinPullbackAlt

open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
  (mseg joinCoord IsPull SameGeneric)

theorem main :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
      [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (x : (Σ k, ι k) → Ω) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
      (z : (Σ k, ι' k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V]
      (E E' : ChartBundle O (mseg x) N V), SameGeneric O x E E' →
      ∃ EB E'B : ChartBundle O (mseg (joinCoord x z)) N V,
        IsPull O x z E EB ∧ IsPull O x z E' E'B ∧ SameGeneric O (joinCoord x z) EB E'B := by
  classical
  intro O _ _ _ Ω _ _ K _ ι _ x K' _ ι' _ z N V _ _ E E' hE
  obtain ⟨EB, hEB⟩ := (GlobalTheory.CompanionTheory.Ar.Num.PullExists.main O Ω K ι x N V E).1 K' ι' z
  obtain ⟨E'B, hE'B⟩ := (GlobalTheory.CompanionTheory.Ar.Num.PullExists.main O Ω K ι x N V E').1 K' ι' z
  exact ⟨EB, E'B, hEB, hE'B,
    (GlobalTheory.CompanionTheory.Ar.Num.PullPreserve.pull_preserve O Ω K ι x N V E E' K' ι' z EB E'B hEB hE'B).2.1 hE⟩

end GlobalTheory.CompanionTheory.CommAlg.JoinPullbackAlt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IntegralPointCompleteValuedField
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem exists_complete_algClosed_center_of_height_one : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CharZero A] (p : ℕ) [Fact p.Prime] (𝔮 : Ideal A), 𝔮.IsPrime → 𝔮.height = 1 → (p : A) ∈ 𝔮 → ∃ (C O : Type) (_ : Field C) (_ : IsAlgClosed C) (_ : CharZero C) (_ : CommRing O) (_ : IsDomain O) (_ : Algebra O C) (v : Valuation C NNReal) (φ : A →+* O), v.Integers O ∧ v (p : C) < 1 ∧ IsAdicComplete (Ideal.span {(p : O)}) O ∧ Function.Injective φ ∧ ∀ a, a ∈ 𝔮 ↔ v (algebraMap O C (φ a)) < 1 :=
  @PositivityTheory.HtPt.Gc.test_field

end GlobalTheory.CompanionTheory.Ar.HT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsoPowOneLawFormulaStatement
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iso_pow_one_law_formula : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (B₂ : FB R d O) (φ ψ : Pt R 1 d) (lam : PS R 2 d) (n : ℕ), IsIso B B₂ φ ψ lam → pow1 B₂ n * ev (n := 2) ![comp1 (B₂.A.act (n : O)) (pt R d 0), pt R d 1] lam = lam ^ n * ev (n := 2) ![comp1 φ (pt R d 0), comp1 φ (pt R d 1)] (pow1 B n) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.iso_pow_one_law | exact GlobalTheory.CompanionTheory.Ar.Conj.iso_pow_one_law | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.iso_pow_one_law <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFactsOfNormalHolds
section
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem lattice_facts_of_normal : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → p.Prime → IsNoetherianRing R → IsFractionRing R Ω → IsIntegrallyClosedIn R Ω → ∀ φ : Equiv.Perm Sg, D.TestFacts R p w χ φ → D.Good₁ R p χ → D.Good₂ R p χ → D.Facts R p w χ φ := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hc hb hp hn hf hi φ ht h1 h2
  have hleaf := GlobalTheory.T.hodge_annihilator_lattice_holds D R p w χ hc hb hp hn hf hi φ ht h1
  have hseq := _root_.GlobalTheory.CompanionTheory.Ar.Num.HodgeAnnihilatorSequence.main D R p w χ hc hb hp hn hf hi φ ht h1 h2
  obtain ⟨hdx, honto, hinj⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.HaSteps.main D R p w χ hc hb hp hn hf hi φ ht h1 h2
  exact
    { le_af := hleaf
      im := fun τ => (hseq τ).1
      ker := fun τ => (hseq τ).2
      dx := hdx
      onto := honto
      inj := hinj }

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamilyInjectiveModel
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.Ar.FamPull

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω), Function.Injective (algebraMap O Ω) → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), IsLatticeFamily O (joinCoord x z) p w χ φ (pullFamily O x z D) ∧ ((∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg (joinCoord x z) c ≠ 0 → (pullFamily O x z D c).Good₁ (chartRing O (mseg (joinCoord x z)) c) p (fun τ a => algebraMap O Ω (χ τ a))) ∧ ((∀ c, mseg x c ≠ 0 → ∀ τ, mulLat (algebraMap O Ω w) (stdLat (chartRing O (mseg x) c) _) ≤ (D c).af (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) → (∀ c, mseg (joinCoord x z) c ≠ 0 → ∀ τ, mulLat (algebraMap O Ω w) (stdLat (chartRing O (mseg (joinCoord x z)) c) _) ≤ (pullFamily O x z D c).af (chartRing O (mseg (joinCoord x z)) c) p (fun a => algebraMap O Ω (χ τ a))) ∧ ((∀ c, mseg x c ≠ 0 → (D c).Good₂ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg (joinCoord x z) c ≠ 0 → (pullFamily O x z D c).Good₂ (chartRing O (mseg (joinCoord x z)) c) p (fun τ a => algebraMap O Ω (χ τ a))))) ∧ ((∀ τ i, ∃ (u : Ω) (a : _ → ℤ), u ≠ 0 ∧ IsLine O x u a fun c => (D c).xId (fun a => algebraMap O Ω (χ τ a)) i) → (∀ τ i, ∃ (u : Ω) (a : _ → ℤ), u ≠ 0 ∧ IsLine O (joinCoord x z) u a fun c => (pullFamily O x z D c).xId (fun a => algebraMap O Ω (χ τ a)) i))) ∧ ∀ (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (Fin (s τ) → Ω)), HasBundles O x D Lie W Om OmHT → ∃ (Lie' W' : ∀ τ, ChartBundle O (mseg (joinCoord x z)) (r τ) (Fin (r τ) → Ω)) (Om' OmHT' : ∀ τ, ChartBundle O (mseg (joinCoord x z)) (s τ) (Fin (s τ) → Ω)), HasBundles O (joinCoord x z) (pullFamily O x z D) Lie' W' Om' OmHT' ∧ ∀ τ, IsPull O x z (Lie τ) (Lie' τ) ∧ IsPull O x z (W τ) (W' τ) ∧ IsPull O x z (Om τ) (Om' τ) ∧ IsPull O x z (OmHT τ) (OmHT' τ) :=
  @PositivityTheory.Xgn.t_fam_pull

end GlobalTheory.CompanionTheory.Ar.FamPull
end

