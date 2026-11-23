module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0037
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEmbeddingWeight
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0039
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNmSectionsFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

namespace NmSectionsFinite

variable {K : Type} [Fintype K] {ι : K → Type} [∀ κ, Fintype (ι κ)] {Ω : Type} [Field Ω]

noncomputable def expo (d : K → ℕ) : K →₀ ℕ := Finsupp.equivFunOnFinite.symm d

@[simp] theorem coe_expo (d : K → ℕ) : ⇑(expo d) = d := Finsupp.coe_equivFunOnFinite_symm d

theorem mapDomain_fst_apply (μ : (Σ κ, ι κ) →₀ ℕ) (κ : K) :
    μ.mapDomain Sigma.fst κ = ∑ i, μ ⟨κ, i⟩ := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum_fintype _ _ (fun _ => by simp), Fintype.sum_sigma]
  simp [Finsupp.single_apply]


omit [Fintype K] [∀ κ, Fintype (ι κ)] in
theorem mConeMap_monomial (y : (Σ κ, ι κ) → Ω) (μ : (Σ κ, ι κ) →₀ ℕ) (r : ℤ) :
    mConeMap y (monomial μ r) = monomial (μ.mapDomain Sigma.fst) (aeval y (monomial μ r)) := by
  rw [mConeMap, aeval_monomial, aeval_monomial, monomial_eq,
    Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_mul, map_prod, map_pow,
    MvPolynomial.algebraMap_apply]
  ring

theorem mConeMap_of_homog (y : (Σ κ, ι κ) → Ω) {g : MRing ι} {d : K → ℕ} (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d) :
    mConeMap y g = monomial (expo d) (aeval y g) := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [mConeMap_monomial]
  have hμd : μ.mapDomain Sigma.fst = expo d := by
    ext κ
    rw [mapDomain_fst_apply, coe_expo, hg μ hμ κ]
  rw [hμd]

def formRing (y : (Σ κ, ι κ) → Ω) : Subalgebra ℤ (MvPolynomial K Ω) where
  carrier := {F | ∀ m : K →₀ ℕ, AddMonoidAlgebra.coeff F m ∈ secM y ⇑m}
  mul_mem' := by
    classical
    intro F G hF hG m
    rw [coeff_mul]
    refine sum_mem fun x hx => ?_
    have hm : ⇑x.1 + ⇑x.2 = ⇑m := by rw [← Finsupp.coe_add, (Finset.HasAntidiagonal.mem_antidiagonal.mp hx)]
    rw [← hm]
    exact secM_mul_mem y (hF x.1) (hG x.2)
  add_mem' := by
    intro F G hF hG m
    rw [MvPolynomial.coeff_add]
    exact add_mem (hF m) (hG m)
  algebraMap_mem' := by
    classical
    intro n m
    rw [MvPolynomial.algebraMap_apply, coeff_C]
    split_ifs with h
    · subst h
      have h1 : (1 : Ω) ∈ secM y ⇑(0 : K →₀ ℕ) :=
        Submodule.subset_span ⟨1, ProjLine.isMultiHomog_one, map_one _⟩
      have := zsmul_mem h1 n
      simpa using this
    · exact zero_mem _

theorem mConeMap_mem_formRing (y : (Σ κ, ι κ) → Ω) (f : MRing ι) : mConeMap y f ∈ formRing y := by
  classical
  induction f using MvPolynomial.induction_on with
  | C n =>
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
    exact Subalgebra.algebraMap_mem _ n
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p q hp =>
    rw [map_mul]
    refine Subalgebra.mul_mem _ hp fun m => ?_
    rw [mConeMap, aeval_X, coeff_C_mul, coeff_X]
    split_ifs with h
    · subst h
      refine Submodule.subset_span ⟨X q, ?_, by simp⟩
      convert ProjLine.isMultiHomog_X (ι := ι) q using 1
      funext κ
      simp [Finsupp.single_apply, eq_comm]
    · simp

theorem monomial_mem_range (y : (Σ κ, ι κ) → Ω) {d : K → ℕ} {v : Ω} (hv : v ∈ secM y d) :
    monomial (expo d) v ∈ (mConeMap y).range := by
  change v ∈ Submodule.span ℤ _ at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    exact ⟨g, mConeMap_of_homog y hg⟩
  | zero => simp
  | add x z _ _ hx hz => rw [map_add]; exact add_mem hx hz
  | smul n x _ hx => rw [map_zsmul]; exact zsmul_mem hx n

theorem proof (h : KH.CondStatement) : NmSectionsFinite.Statement := by
  unfold NmSectionsFinite.Statement
  intro K _ ι _ Ω _ y a ha hy hbir τ₂
  classical
  obtain ⟨k, c, -, hc0, hc⟩ := h K ι Ω y a ha hy hbir
  set R := (mConeMap y).range
  have : IsNoetherianRing R :=
    isNoetherianRing_of_surjective (MRing ι) R (mConeMap y).rangeRestrict.toRingHom
      (mConeMap y).rangeRestrict_surjective

  set G : Set (MvPolynomial K Ω) := {F | ∃ τ, τ₂ ≤ τ ∧ ∃ s ∈ chartLatNm y (fun κ => (a κ : ℤ)) τ,
    F = monomial (expo fun κ => τ * a κ) s}
  set u : MvPolynomial K Ω := monomial (expo fun κ => k * a κ) (aeval y c)
  have hinj : Function.Injective (LinearMap.mulLeft R u) := by
    intro F F' hF
    simp only [LinearMap.mulLeft_apply] at hF
    exact mul_left_cancel₀ (by simpa [u] using hc0) hF
  have hmap : (Submodule.span R G).map (LinearMap.mulLeft R u) ≤ Submodule.span R {1} := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨F, ⟨τ, -, s, hs, rfl⟩, rfl⟩
    rw [LinearMap.mulLeft_apply, monomial_mul]
    have hdeg : expo (fun κ => k * a κ) + expo (fun κ => τ * a κ) = expo fun κ => (τ + k) * a κ := by
      ext κ; simp; ring
    rw [hdeg]
    obtain ⟨g, hg⟩ := monomial_mem_range y (hc τ s hs)
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    exact ⟨⟨_, g, rfl⟩, by rw [Subalgebra.smul_def, smul_eq_mul, mul_one]; exact hg⟩
  have hfg : (Submodule.span R G).FG := by
    refine Submodule.fg_of_fg_map_injective _ hinj ?_
    have := isNoetherian_of_fg_of_noetherian (Submodule.span R {(1 : MvPolynomial K Ω)})
      (Submodule.fg_span_singleton 1)
    exact isNoetherian_submodule.mp inferInstance _ hmap
  obtain ⟨t, htG, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset G).mp hfg
  choose d hd e he hte using fun j : t => htG j.2
  refine ⟨t, inferInstance, d, e, max τ₂ (Finset.univ.sup d), fun j => ⟨hd j,
    le_max_of_le_right (Finset.le_sup (Finset.mem_univ j)), he j⟩, ?_⟩
  intro τ hτ s hs
  have hdτ : ∀ j, d j ≤ τ := fun j =>
    le_trans (le_max_of_le_right (Finset.le_sup (Finset.mem_univ j))) hτ
  have hmem : monomial (expo fun κ => τ * a κ) s ∈ Submodule.span R (t : Set (MvPolynomial K Ω)) := by
    rw [← hspan]
    exact Submodule.subset_span ⟨τ, le_trans (le_max_left _ _) hτ, s, hs, rfl⟩
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.mp hmem
  have hR : ∀ F, ((f F : R) : MvPolynomial K Ω) ∈ formRing y := by
    intro F
    obtain ⟨g, hg⟩ := (f F).2
    rw [← hg]
    exact mConeMap_mem_formRing y g
  refine ⟨fun j => AddMonoidAlgebra.coeff ((f j : R) : MvPolynomial K Ω) (expo fun κ => (τ - d j) * a κ), fun j => ?_, ?_⟩
  · simpa using hR j (expo fun κ => (τ - d j) * a κ)
  · have hc' := congrArg (AddMonoidAlgebra.coeff · (expo fun κ => τ * a κ)) hf
    rw [coeff_monomial, if_pos rfl] at hc'
    rw [← hc', coeff_sum, ← Finset.sum_coe_sort t]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Subalgebra.smul_def, smul_eq_mul]
    set p := ((f j : R) : MvPolynomial K Ω)
    rw [hte j]
    rw [coeff_mul_monomial', if_pos]
    · congr 2
      ext κ
      simp [Nat.sub_mul]
    · intro κ
      simpa using Nat.mul_le_mul_right (a κ) (hdτ j)

end NmSectionsFinite

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNmSectionsRankBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

namespace NmSectionsRankBound

variable {K : Type} [Fintype K] {ι : K → Type} [∀ κ, Fintype (ι κ)] {Ω : Type} [Field Ω]


omit [∀ κ, Fintype (ι κ)] in
theorem shift_mem (y : (Σ κ, ι κ) → Ω) (c : ∀ κ, ι κ) (a a' : K → ℤ) (τ τ' : ℕ) (e : K → ℕ)
    (he : ∀ κ, (τ : ℤ) * a κ + e κ = τ' * a' κ) {s : Ω} (hs : s ∈ chartLatNm y a τ) :
    (∏ κ, y ⟨κ, c κ⟩ ^ e κ) * s ∈ chartLatNm y a' τ' := by
  intro c' hc'
  have hmem : ∀ κ, y ⟨κ, c κ⟩ / y ⟨κ, c' κ⟩ ∈ chartRingZ y c' := fun κ =>
    Algebra.subset_adjoin ⟨⟨κ, c κ⟩, rfl⟩
  have hk : ∀ κ, y ⟨κ, c' κ⟩ ^ (-((τ' : ℤ) * a' κ)) =
      y ⟨κ, c' κ⟩ ^ (-((τ : ℤ) * a κ)) * (y ⟨κ, c' κ⟩ ^ e κ)⁻¹ := by
    intro κ
    rw [← he κ, neg_add, zpow_add₀ (hc' κ), zpow_neg (y ⟨κ, c' κ⟩) (e κ : ℤ), zpow_natCast]
  have heq : (∏ κ, y ⟨κ, c κ⟩ ^ e κ) * s * ∏ κ, y ⟨κ, c' κ⟩ ^ (-((τ' : ℤ) * a' κ)) =
      (s * ∏ κ, y ⟨κ, c' κ⟩ ^ (-((τ : ℤ) * a κ))) * ∏ κ, (y ⟨κ, c κ⟩ / y ⟨κ, c' κ⟩) ^ e κ := by
    simp only [hk, div_pow, Finset.prod_mul_distrib, Finset.prod_div_distrib, Finset.prod_inv_distrib]
    ring
  rw [heq]
  refine Subalgebra.mul_mem _ (hs c' hc') (Subalgebra.prod_mem _ fun κ _ => Subalgebra.pow_mem _ ?_ _)
  exact (integralClosure (chartRingZ y c') Ω).algebraMap_mem ⟨_, hmem κ⟩

theorem proof (h₁ : NmSectionsFinite.Statement) (h₂ : SecMRankBound.Statement) :
    NmSectionsRankBound.Statement := by
  intro K _ ι _ Ω _ y D a hvar hbir
  classical

  have hy : ∀ κ, ∃ i, y ⟨κ, i⟩ ≠ 0 := by
    intro κ
    obtain ⟨i, hi⟩ := hvar.2.1.2.2 κ
    refine ⟨i, fun h0 => hi ?_⟩
    simp [mCoordIdeal, RingHom.mem_ker, mConeMap, h0]

  have hchar : CharZero Ω := by
    refine charZero_of_inj_zero fun n hn => ?_
    have hmem : (n : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
      simp [mCoordIdeal, RingHom.mem_ker, mConeMap]
      rw [← map_natCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hn, map_zero]
    rw [hvar.2.2.1, Ideal.mem_bot] at hmem
    exact_mod_cast hmem
  choose c hc using hy
  set b : K → ℕ := fun κ => (a κ).toNat + 1 with hb
  have hb1 : ∀ κ, 1 ≤ b κ := fun κ => Nat.le_add_left 1 _
  have hab : ∀ κ, a κ ≤ (b κ : ℤ) := fun κ => by simp only [hb]; push_cast; omega
  obtain ⟨J, _, d, e, τ₁, -, hgen⟩ := h₁ K ι Ω y b hb1 (fun κ => ⟨c κ, hc κ⟩) hbir 0
  obtain ⟨hfin, C, hC0, hC⟩ := h₂ K ι Ω y D b hvar hb1

  have hbig : ∀ τ, τ₁ ≤ τ → Module.Finite ℤ (chartLatNm y (fun κ => (b κ : ℤ)) τ) ∧
      (Module.finrank ℤ (chartLatNm y (fun κ => (b κ : ℤ)) τ) : ℝ) ≤
        Fintype.card J * C * ((τ : ℝ) + 1) ^ D := by
    intro τ hτ
    let M : J → AddSubgroup Ω := fun j => secM y (fun κ => (τ - d j) * b κ)
    let Φ : (∀ j, M j) →ₗ[ℤ] Ω :=
      ∑ j, (LinearMap.mulRight ℤ (e j)).comp ((M j).subtype.toIntLinearMap.comp (LinearMap.proj j))
    have hle : ∀ s ∈ chartLatNm y (fun κ => (b κ : ℤ)) τ, s ∈ LinearMap.range Φ := by
      intro s hs
      obtain ⟨r, hr, rfl⟩ := hgen τ hτ s hs
      exact ⟨fun j => ⟨r j, hr j⟩, by simp [Φ, M]⟩
    let f : chartLatNm y (fun κ => (b κ : ℤ)) τ →ₗ[ℤ] LinearMap.range Φ :=
      LinearMap.codRestrict _ (chartLatNm y (fun κ => (b κ : ℤ)) τ).subtype.toIntLinearMap
        (fun x => hle x x.2)
    have hinj : Function.Injective f := fun x x' hxx => by
      have h := congrArg Subtype.val hxx
      exact Subtype.ext h
    have : ∀ j, Module.Finite ℤ (M j) := fun j => hfin (τ - d j)
    have : ∀ j, Module.IsTorsionFree ℤ (M j) := fun j =>
      Function.Injective.moduleIsTorsionFree (M j).subtype Subtype.val_injective (fun _ _ => rfl)
    refine ⟨Module.Finite.of_injective f hinj, ?_⟩
    have h1 : Module.finrank ℤ (chartLatNm y (fun κ => (b κ : ℤ)) τ) ≤ ∑ j, Module.finrank ℤ (M j) :=
      (LinearMap.finrank_le_finrank_of_injective hinj).trans
        ((LinearMap.finrank_range_le Φ).trans_eq (Module.finrank_pi_fintype ℤ))
    calc (Module.finrank ℤ (chartLatNm y (fun κ => (b κ : ℤ)) τ) : ℝ)
        ≤ ∑ j, (Module.finrank ℤ (M j) : ℝ) := by exact_mod_cast h1
      _ ≤ ∑ _j : J, C * ((τ : ℝ) + 1) ^ D := by
          refine Finset.sum_le_sum fun j _ => (hC (τ - d j)).trans ?_
          gcongr
          exact_mod_cast Nat.sub_le τ (d j)
      _ = Fintype.card J * C * ((τ : ℝ) + 1) ^ D := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

  have hmap : ∀ τ, ∃ f : chartLatNm y a τ →ₗ[ℤ] chartLatNm y (fun κ => (b κ : ℤ)) (max τ τ₁),
      Function.Injective f := by
    intro τ
    set τ' := max τ τ₁
    set ex : K → ℕ := fun κ => ((τ' : ℤ) * b κ - τ * a κ).toNat
    have hex : ∀ κ, (τ : ℤ) * a κ + ex κ = τ' * (b κ : ℤ) := by
      intro κ
      have h0 : (τ : ℤ) * a κ ≤ τ' * b κ :=
        calc (τ : ℤ) * a κ ≤ τ * b κ := mul_le_mul_of_nonneg_left (hab κ) (by positivity)
          _ ≤ τ' * b κ := mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left τ τ₁) (by positivity)
      simp only [ex]
      rw [Int.toNat_of_nonneg (by linarith)]
      ring
    set u : Ω := ∏ κ, y ⟨κ, c κ⟩ ^ ex κ
    have hu : u ≠ 0 := Finset.prod_ne_zero_iff.mpr fun κ _ => pow_ne_zero _ (hc κ)
    let F : chartLatNm y a τ →+ chartLatNm y (fun κ => (b κ : ℤ)) τ' :=
      ((AddMonoidHom.mulLeft u).comp (chartLatNm y a τ).subtype).codRestrict _
        (fun x => shift_mem y c a _ τ τ' ex hex x.2)
    refine ⟨F.toIntLinearMap, fun x x' hxx => ?_⟩
    have h : u * (x : Ω) = u * x' := congrArg Subtype.val hxx
    exact Subtype.ext (mul_left_cancel₀ hu h)
  refine ⟨fun τ => ?_, Fintype.card J * C * ((τ₁ : ℝ) + 1) ^ D, by positivity, fun τ => ?_⟩
  · obtain ⟨f, hf⟩ := hmap τ
    have := (hbig (max τ τ₁) (le_max_right _ _)).1
    exact Module.Finite.of_injective f hf
  · obtain ⟨f, hf⟩ := hmap τ
    obtain ⟨hF, hR⟩ := hbig (max τ τ₁) (le_max_right _ _)
    have h1 : (Module.finrank ℤ (chartLatNm y a τ) : ℝ) ≤
        Module.finrank ℤ (chartLatNm y (fun κ => (b κ : ℤ)) (max τ τ₁)) := by
      exact_mod_cast LinearMap.finrank_le_finrank_of_injective hf
    have h2 : ((max τ τ₁ : ℕ) : ℝ) + 1 ≤ ((τ₁ : ℝ) + 1) * ((τ : ℝ) + 1) := by
      rcases le_total τ τ₁ with h | h
      · rw [max_eq_right h]; nlinarith [(Nat.cast_nonneg τ : (0 : ℝ) ≤ τ), (Nat.cast_nonneg τ₁ : (0 : ℝ) ≤ τ₁)]
      · rw [max_eq_left h]; nlinarith [(Nat.cast_nonneg τ : (0 : ℝ) ≤ τ), (Nat.cast_nonneg τ₁ : (0 : ℝ) ≤ τ₁)]
    calc (Module.finrank ℤ (chartLatNm y a τ) : ℝ)
        ≤ Fintype.card J * C * (((max τ τ₁ : ℕ) : ℝ) + 1) ^ D := h1.trans hR
      _ ≤ Fintype.card J * C * ((((τ₁ : ℝ) + 1) * ((τ : ℝ) + 1)) ^ D) := by
          gcongr
      _ = Fintype.card J * C * ((τ₁ : ℝ) + 1) ^ D * ((τ : ℝ) + 1) ^ D := by rw [mul_pow]; ring

end NmSectionsRankBound

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPiecesAdditive
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology Set MeasureTheory Manifold EmbeddingWeight

noncomputable section

namespace PiecesAdditiveAlt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_weight {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) {J : Type} [Fintype J]
    {S : J → Set ((Σ k, ι k) → ℂ)} (hS : ∀ i, IsClosed (S i))
    (hsm : ∀ i (t : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, t k ≠ 0) → z ∈ S i →
      (fun p => t p.1 * z p) ∈ S i)
    (huniq : ∀ z ∈ mcPts P, ∃! i, z ∈ S i) (i : J) :
    ∃ u : ((Σ k, ι k) → ℂ) → ℝ,
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} ∧
      (∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → u (fun p => c p.1 * z p) = u z) ∧
      ∀ z ∈ mcPts P, u z = (S i).indicator (fun _ => (1 : ℝ)) z := by
  classical
  let T : J → Set ((Σ k, ι k) → ℂ) := fun j => mcPts P ∩ S j ∩ {z | ∀ k, blockNormSq z k = 1}
  let C : J → Set ((Σ k, ι k × ι k) → ℂ) := fun j => projPt '' T j
  have hT : ∀ j, IsCompact (T j) := by
    intro j
    refine isCompact_sphere.of_isClosed_subset ?_ inter_subset_right
    have : T j = ({z | ∀ f ∈ P, eval z (map (Int.castRingHom ℂ) f) = 0} ∩ S j) ∩
        {z | ∀ k, blockNormSq z k = 1} := by
      ext z
      simp only [T, mcPts, mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨⟨⟨-, h1⟩, h2⟩, h3⟩
        exact ⟨⟨h1, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨⟨⟨fun k => ?_, h1⟩, h2⟩, h3⟩
        by_contra hcon
        push Not at hcon
        have := h3 k
        simp [blockNormSq, hcon] at this
    rw [this]
    exact ((isClosed_zeros P).inter (hS j)).inter isCompact_sphere.isClosed
  have hC : ∀ j, IsCompact (C j) := fun j =>
    (hT j).image_of_continuousOn (contDiffOn_projPt.continuousOn.mono fun z hz => hz.1.1.1)
  have hmem : ∀ j, ∀ z ∈ mcPts P, z ∈ S j → projPt z ∈ C j := by
    intro j z hz hzj
    obtain ⟨c, hc, hc1⟩ := exists_smul_sphere hz.1
    exact ⟨_, ⟨⟨mcPts_smul hP c hc hz, hsm j c z hc hzj⟩, hc1⟩, projPt_smul c hc z⟩
  have hdisj : ∀ j j', j ≠ j' → Disjoint (C j) (C j') := by
    intro j j' hne
    rw [Set.disjoint_left]
    rintro e ⟨z, ⟨⟨hzP, hzs⟩, -⟩, rfl⟩ ⟨w, ⟨⟨hwP, hwt⟩, -⟩, hw⟩
    obtain ⟨c, hc, rfl⟩ := exists_smul_of_projPt_eq hzP.1 hwP.1 hw.symm
    exact hne ((huniq _ hwP).unique (hsm j c z hc hzs) hwt)
  obtain ⟨f, h0, h1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    𝓘(ℝ, (Σ k, ι k × ι k) → ℂ) (n := ⊤)
    (isClosed_biUnion_finset fun j _ => (hC j).isClosed) (hC i).isClosed
    (Set.disjoint_iUnion₂_left.2 fun j hj => hdisj j i (Finset.ne_of_mem_erase hj))
  refine ⟨fun z => f (projPt z), ?_, fun c z hc => by simp only [projPt_smul c hc], ?_⟩
  · exact (contMDiff_iff_contDiff.mp f.contMDiff).comp_contDiffOn contDiffOn_projPt
  · intro z hz
    obtain ⟨j, hj, -⟩ := huniq z hz
    by_cases hji : j = i
    · subst hji
      rw [Set.indicator_of_mem hj]
      exact h1.self_of_nhdsSet _ (hmem j z hz hj)
    · have hzi : z ∉ S i := fun h => hji ((huniq z hz).unique hj h)
      rw [Set.indicator_of_notMem hzi]
      exact h0.self_of_nhdsSet _
        (Set.mem_iUnion₂.2 ⟨j, Finset.mem_erase.2 ⟨hji, Finset.mem_univ _⟩, hmem j z hz hj⟩)


omit [∀ k, Fintype (ι k)] in
theorem sheetDensity_sum (P : Ideal (MRing ι)) {e : ℕ}
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    {J : Type} [Fintype J] (c : J → ℝ) (g : J → ((Σ k, ι k) → ℂ) → ℝ) (y : Fin e → ℂ)
    (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ φ (fun z => ∑ i, c i * g i z) y w = ∑ i, c i * sheetDensity P Ψ φ (g i) y w := by
  unfold sheetDensity
  split_ifs with hγ
  · rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  · simp

theorem integrable_piece (hInt : PtsIntegrableStatement) {P : Ideal (MRing ι)} {e : ℕ}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (hL : ∀ j, IsSmoothHerm (L j))
    {J : Type} [Fintype J] {S : J → Set ((Σ k, ι k) → ℂ)} (hS : ∀ i, IsClosed (S i))
    (hsm : ∀ i (t : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, t k ≠ 0) → z ∈ S i →
      (fun p => t p.1 * z p) ∈ S i)
    (huniq : ∀ z ∈ mcPts P, ∃! i, z ∈ S i) (i : J) :
    Integrable (fun y => ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y,
      sheetDensity P Ψ (pot L) ((S i).indicator fun _ => (1 : ℝ)) y w) := by
  obtain ⟨u, hus, hui, hu⟩ := exists_weight hP.2.1.2.1 hS hsm huniq i
  let B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := HermLine.ofWeight u hui
  have hB : IsSmoothHerm B := Real.contDiff_exp.comp_contDiffOn hus.neg
  have hlog : ∀ z, logNorm B 1 z = u z := by
    intro z
    simp [logNorm, B, HermLine.ofWeight]
  have hhom : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (1 : MRing ι) 0 := by
    intro m hm k
    rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
    subst hm
    simp
  have hnot : (1 : MRing ι) ∉ P := fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).2 h)
  have hsec : IsSectionOn P B 1 := ⟨0, fun k => by simp [B, HermLine.ofWeight], hhom, hnot⟩
  refine (hInt K ι P e Ψ L B 1 hP hΨ hL hB hsec).congr (Eventually.of_forall fun y => ?_)
  refine finsum_mem_congr rfl fun w _ => ?_
  exact GroundTheory.Heights₂.Heights.Inter.DiagRAux.sheetDensity_congr_mcPts P Ψ (fun _ _ _ => rfl)
    (fun z hz => (hlog z).trans (hu z hz)) y w

end PiecesAdditiveAlt


open PiecesAdditiveAlt in
theorem PiecesAdditive.proof (hInt : PtsIntegrableStatement) : PiecesAdditive.Statement := by
  intro K _ ι _ P e L J _ S c hP hL hS hsm huniq
  classical
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    have hlin : ∀ y, (∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P hΨ.choose y, sheetDensity P hΨ.choose (pot L)
        (fun z => ∑ i, c i * (S i).indicator (fun _ => (1 : ℝ)) z) y w) =
        ∑ i, c i * ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P hΨ.choose y,
          sheetDensity P hΨ.choose (pot L) ((S i).indicator fun _ => (1 : ℝ)) y w := by
      intro y
      have hfin := fibreFinite K ι P e _ hP hΨ.choose_spec y
      simp only [finsum_mem_eq_finite_toFinset_sum _ hfin, sheetDensity_sum, Finset.mul_sum]
      exact Finset.sum_comm
    simp only [hlin]
    rw [integral_finsetSum _ fun i _ =>
      (integrable_piece hInt hP hΨ.choose_spec hL hS hsm huniq i).const_mul (c i)]
    simp only [integral_const_mul]
  · simp

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsCoordArithOfFnField
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def CoordArithOfFnField.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (d : ℕ),
    Nonempty K' → (∀ k, ∃ i, y' ⟨k, i⟩ ≠ 0) → blockFnField y = blockFnField y' →
    IsArithVar (mCoordIdeal y) d → IsArithVar (mCoordIdeal y') d

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

