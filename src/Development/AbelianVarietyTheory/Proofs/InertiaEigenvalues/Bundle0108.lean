module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0117
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0076
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0062

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PreimageDiagOneGeneralLinearEmbeddingIntegralGLS
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.JR.GLift

theorem embHom_apply_cc {F : Type} [CommRing F] {r : ℕ} (a : Matrix (Fin r) (Fin r) F) (i j : Fin r) :
    GlobalTheory.JR.Step.embHom r F a (Fin.castSucc i) (Fin.castSucc j) = a i j := by
  simp [GlobalTheory.JR.Step.embHom, finSumFinEquiv_symm_apply_castSucc]

theorem embHom_apply_cl {F : Type} [CommRing F] {r : ℕ} (a : Matrix (Fin r) (Fin r) F) (i : Fin r) :
    GlobalTheory.JR.Step.embHom r F a (Fin.castSucc i) (Fin.last r) = 0 := by
  simp [GlobalTheory.JR.Step.embHom, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]

theorem embHom_apply_lc {F : Type} [CommRing F] {r : ℕ} (a : Matrix (Fin r) (Fin r) F) (j : Fin r) :
    GlobalTheory.JR.Step.embHom r F a (Fin.last r) (Fin.castSucc j) = 0 := by
  simp [GlobalTheory.JR.Step.embHom, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]

theorem embHom_apply_ll {F : Type} [CommRing F] {r : ℕ} (a : Matrix (Fin r) (Fin r) F) :
    GlobalTheory.JR.Step.embHom r F a (Fin.last r) (Fin.last r) = 1 := by
  simp [GlobalTheory.JR.Step.embHom, finSumFinEquiv_symm_last]

theorem coe_emb {F : Type} [CommRing F] {r : ℕ} (g : GL (Fin r) F) :
    ((GlobalTheory.JR.Step.emb r F g : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) =
      GlobalTheory.JR.Step.embHom r F (g : Matrix (Fin r) (Fin r) F) := rfl

theorem coe_emb_inv {F : Type} [CommRing F] {r : ℕ} (g : GL (Fin r) F) :
    (((GlobalTheory.JR.Step.emb r F g)⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) =
      GlobalTheory.JR.Step.embHom r F ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) := by
  rw [← map_inv]; rfl

theorem emb_preimage_glO : ∀ (F : Type) [NormedField F] (r : ℕ),
    ⇑(GlobalTheory.JR.Step.emb r F) ⁻¹' glO (r + 1) F = glO r F := by
  intro F _ r
  ext g
  simp only [Set.mem_preimage, glO, Set.mem_setOf_eq, coe_emb, coe_emb_inv]
  constructor
  · intro h i j
    have := h (Fin.castSucc i) (Fin.castSucc j)
    rwa [embHom_apply_cc, embHom_apply_cc] at this
  · intro h i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [embHom_apply_ll]
    · simp [embHom_apply_lc]
    · simp [embHom_apply_cl]
    · rw [embHom_apply_cc, embHom_apply_cc]; exact h i j

end GlobalTheory.JR.GLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdTsumEqTsumIndicatorEnnreal
section
open Filter Topology
open scoped ENNReal

namespace GlobalTheory.EulerSum

variable {I X : Type} [Zero X]

noncomputable def ofFinset (S : Finset I) (y : S → X) : I →₀ X := by
  classical
  exact Finsupp.onFinset S (fun i => if h : i ∈ S then y ⟨i, h⟩ else 0) (by
    intro i hi; by_contra h; exact hi (dif_neg h))

theorem ofFinset_apply (S : Finset I) (y : S → X) (i : S) : ofFinset S y i = y i := by
  classical
  simp [ofFinset, Finsupp.onFinset_apply, i.2]

theorem ofFinset_apply_of_notMem (S : Finset I) (y : S → X) {i : I} (h : i ∉ S) :
    ofFinset S y i = 0 := by
  classical
  simp [ofFinset, Finsupp.onFinset_apply, h]

theorem ofFinset_injective (S : Finset I) : Function.Injective (ofFinset (X := X) S) := by
  intro y z h; funext i; rw [← ofFinset_apply S y i, ← ofFinset_apply S z i, h]

theorem support_ofFinset_subset (S : Finset I) (y : S → X) : (ofFinset S y).support ⊆ S := by
  intro i hi
  by_contra h
  exact (Finsupp.mem_support_iff.1 hi) (ofFinset_apply_of_notMem S y h)

theorem mem_range_ofFinset (S : Finset I) (l : I →₀ X) (hl : l.support ⊆ S) :
    l ∈ Set.range (ofFinset S) := by
  refine ⟨fun i => l i, ?_⟩
  ext i
  by_cases h : i ∈ S
  · exact ofFinset_apply S _ ⟨i, h⟩
  · rw [ofFinset_apply_of_notMem S _ h]
    exact (Finsupp.notMem_support_iff.1 (fun hi => h (hl hi))).symm

theorem prod_ofFinset {M : Type} [CommMonoid M] (f : I → X → M) (hf0 : ∀ v, f v 0 = 1)
    (S : Finset I) (y : S → X) : (ofFinset S y).prod f = ∏ i : S, f i (y i) := by
  rw [Finsupp.prod_of_support_subset _ (support_ofFinset_subset S y) f (fun i _ => hf0 i),
    ← Finset.prod_coe_sort S]
  exact Finset.prod_congr rfl fun i _ => by rw [ofFinset_apply]

theorem tsum_indicator_support_subset {R : Type} [CommSemiring R] [TopologicalSpace R]
    (f : I → X → R) (hf0 : ∀ v, f v 0 = 1) (S : Finset I) :
    ∑' l : I →₀ X, ({l : I →₀ X | l.support ⊆ S}.indicator (fun l => l.prod f) l) =
      ∑' y : S → X, ∏ i : S, f i (y i) := by
  refine ((ofFinset_injective S).tsum_eq ?_).symm.trans ?_
  · intro l hl
    by_contra h
    exact hl (Set.indicator_of_notMem (fun hs => h (mem_range_ofFinset S l hs)) _)
  · refine tsum_congr fun y => ?_
    rw [Set.indicator_of_mem (show ofFinset S y ∈ {l : I →₀ X | l.support ⊆ S} from
      support_ofFinset_subset S y), prod_ofFinset f hf0]

theorem prod_tsum_eq_tsum_indicator_ennreal (f : I → X → ℝ≥0∞) (hf0 : ∀ v, f v 0 = 1)
    (S : Finset I) :
    ∏ v ∈ S, ∑' x, f v x =
      ∑' l : I →₀ X, ({l : I →₀ X | l.support ⊆ S}.indicator (fun l => l.prod f) l) := by
  rw [tsum_indicator_support_subset f hf0 S,
    GlobalTheory.VolBoxMajorant.tsum_pi_prod_ennreal' (fun (i : S) x => f i x),
    Finset.prod_coe_sort S (fun v => ∑' x, f v x)]

theorem prod_tsum_eq_tsum_indicator (f : I → X → ℂ) (hf0 : ∀ v, f v 0 = 1)
    (hv : ∀ v, Summable fun x => ‖f v x‖) (S : Finset I) :
    ∏ v ∈ S, ∑' x, f v x =
      ∑' l : I →₀ X, ({l : I →₀ X | l.support ⊆ S}.indicator (fun l => l.prod f) l) := by
  classical
  rw [tsum_indicator_support_subset f hf0 S,
    (GlobalTheory.hasSum_pi_prod_of_summable_norm S (fun _ => X) (fun i x => f i x)
      (fun i => hv i)).tsum_eq,
    Finset.prod_coe_sort S (fun v => ∑' x, f v x)]

theorem hasProd_tsum_finsupp_ennreal (f : I → X → ℝ≥0∞) (hf0 : ∀ v, f v 0 = 1) :
    HasProd (fun v => ∑' x, f v x) (∑' l : I →₀ X, l.prod f) := by
  classical
  have hmono : Monotone (fun S : Finset I => ∏ v ∈ S, ∑' x, f v x) := by
    intro S T hST
    exact Finset.prod_le_prod_of_subset_of_one_le' hST
      (fun v _ _ => (hf0 v).symm.le.trans (ENNReal.le_tsum 0))
  have hsup : ⨆ S : Finset I, ∏ v ∈ S, ∑' x, f v x = ∑' l : I →₀ X, l.prod f := by
    simp_rw [prod_tsum_eq_tsum_indicator_ennreal f hf0]
    refine le_antisymm (iSup_le fun S => ENNReal.tsum_le_tsum fun l => ?_) ?_
    · exact Set.indicator_le_self _ _ l
    · rw [ENNReal.tsum_eq_iSup_sum]
      refine iSup_le fun T => le_iSup_of_le (T.biUnion Finsupp.support) ?_
      calc ∑ l ∈ T, l.prod f
          = ∑ l ∈ T, ({l : I →₀ X | l.support ⊆ T.biUnion Finsupp.support}.indicator
              (fun l => l.prod f) l) :=
            Finset.sum_congr rfl fun l hl =>
              (Set.indicator_of_mem (show l ∈ {l : I →₀ X | l.support ⊆ T.biUnion Finsupp.support}
                from Finset.subset_biUnion_of_mem Finsupp.support hl) (fun l : I →₀ X => l.prod f)).symm
        _ ≤ _ := ENNReal.sum_le_tsum T
  have := tendsto_atTop_iSup hmono
  rw [hsup] at this
  exact this

theorem tsum_finsupp_eq_tprod_ennreal (f : I → X → ℝ≥0∞) (hf0 : ∀ v, f v 0 = 1) :
    ∑' l : I →₀ X, l.prod f = ∏' v, ∑' x, f v x :=
  (hasProd_tsum_finsupp_ennreal f hf0).tprod_eq.symm

theorem summable_norm_local (f : I → X → ℂ)
    (hsum : Summable fun p : I × {x : X // x ≠ 0} => ‖f p.1 p.2‖) (v : I) :
    Summable fun x => ‖f v x‖ := by
  have h1 : Summable fun x : {x : X // x ≠ 0} => ‖f v x‖ :=
    ((summable_prod_of_nonneg fun _ => norm_nonneg _).1 hsum).1 v
  haveI : Finite ↥({x : X | x ≠ 0}ᶜ) :=
    ((Set.finite_singleton (0 : X)).subset (by intro x hx; simpa using hx)).to_subtype
  exact (summable_subtype_and_compl (s := {x : X | x ≠ 0})).1 ⟨h1, Summable.of_finite⟩

theorem summable_norm_finsupp_prod (f : I → X → ℂ) (hf0 : ∀ v, f v 0 = 1)
    (hsum : Summable fun p : I × {x : X // x ≠ 0} => ‖f p.1 p.2‖) :
    Summable fun l : I →₀ X => ‖l.prod f‖ := by
  classical
  have hP := (summable_prod_of_nonneg fun _ => norm_nonneg _).1 hsum
  let a : I → ℝ := fun v => ∑' x : {x : X // x ≠ 0}, ‖f v x‖
  have hA : Summable a := hP.2
  have ha0 : ∀ v, 0 ≤ a v := fun v => tsum_nonneg fun _ => norm_nonneg _
  let g : I → X → ℝ≥0∞ := fun v x => ENNReal.ofReal ‖f v x‖
  have hg0 : ∀ v, g v 0 = 1 := by intro v; simp [g, hf0 v]
  have hgv : ∀ v, ∑' x, g v x = ENNReal.ofReal (1 + a v) := by
    intro v
    rw [ENNReal.tsum_eq_add_tsum_ite 0, hg0, ENNReal.ofReal_add zero_le_one (ha0 v),
      ENNReal.ofReal_one, ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hP.1 v)]
    congr 1
    refine Eq.trans ?_ (tsum_subtype {x : X | x ≠ 0} (fun x => ENNReal.ofReal ‖f v x‖)).symm
    refine tsum_congr fun x => ?_
    by_cases hx : x = 0 <;> simp [hx, g]
  have hprod : ∀ l : I →₀ X, ENNReal.ofReal ‖l.prod f‖ = l.prod g := by
    intro l
    simp only [Finsupp.prod, norm_prod, g]
    exact ENNReal.ofReal_prod_of_nonneg fun _ _ => norm_nonneg _
  refine summable_of_sum_le (c := Real.exp (∑' v, a v)) (fun _ => norm_nonneg _) fun T => ?_
  have hS := prod_tsum_eq_tsum_indicator_ennreal g hg0 (T.biUnion Finsupp.support)
  rw [← ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le,
    ENNReal.ofReal_sum_of_nonneg fun _ _ => norm_nonneg _]
  calc ∑ l ∈ T, ENNReal.ofReal ‖l.prod f‖
      = ∑ l ∈ T, ({l : I →₀ X | l.support ⊆ T.biUnion Finsupp.support}.indicator
          (fun l => l.prod g) l) :=
        Finset.sum_congr rfl fun l hl => by
          rw [hprod, Set.indicator_of_mem (show l ∈ {l : I →₀ X | l.support ⊆ T.biUnion Finsupp.support}
            from Finset.subset_biUnion_of_mem Finsupp.support hl) (fun l : I →₀ X => l.prod g)]
    _ ≤ _ := ENNReal.sum_le_tsum T
    _ = ∏ v ∈ T.biUnion Finsupp.support, ∑' x, g v x := hS.symm
    _ = ENNReal.ofReal (∏ v ∈ T.biUnion Finsupp.support, (1 + a v)) := by
        rw [ENNReal.ofReal_prod_of_nonneg fun v _ => by linarith [ha0 v]]
        exact Finset.prod_congr rfl fun v _ => hgv v
    _ ≤ ENNReal.ofReal (Real.exp (∑' v, a v)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc ∏ v ∈ T.biUnion Finsupp.support, (1 + a v)
            ≤ ∏ v ∈ T.biUnion Finsupp.support, Real.exp (a v) :=
              Finset.prod_le_prod₀ (fun v _ => by linarith [ha0 v])
                fun v _ => by linarith [Real.add_one_le_exp (a v)]
          _ = Real.exp (∑ v ∈ T.biUnion Finsupp.support, a v) := (Real.exp_sum _ _).symm
          _ ≤ Real.exp (∑' v, a v) := Real.exp_le_exp.2 (hA.sum_le_tsum _ (fun v _ => ha0 v))

theorem hasProd_tsum_finsupp (f : I → X → ℂ) (hf0 : ∀ v, f v 0 = 1)
    (hsum : Summable fun p : I × {x : X // x ≠ 0} => ‖f p.1 p.2‖) :
    HasProd (fun v => ∑' x, f v x) (∑' l : I →₀ X, l.prod f) := by
  classical
  have hN := summable_norm_finsupp_prod f hf0 hsum
  have key : (fun S : Finset I => ∏ v ∈ S, ∑' x, f v x) = fun S =>
      ∑' l : I →₀ X, ({l : I →₀ X | l.support ⊆ S}.indicator (fun l => l.prod f) l) :=
    funext (prod_tsum_eq_tsum_indicator f hf0 (summable_norm_local f hsum))
  show Tendsto (fun S : Finset I => ∏ v ∈ S, ∑' x, f v x) atTop _
  rw [key]
  refine tendsto_tsum_of_dominated_convergence (bound := fun l : I →₀ X => ‖l.prod f‖) hN
    (fun l => ?_) (Eventually.of_forall fun S l => norm_indicator_le_norm_self _ _)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop l.support] with S hS
  exact (Set.indicator_of_mem (show l ∈ {l : I →₀ X | l.support ⊆ S} from hS)
    (fun l : I →₀ X => l.prod f)).symm

theorem euler_product_intVec {I : Type} (n : ℕ) (f : I → (Fin n → ℤ) → ℂ)
    (hf0 : ∀ v, f v 0 = 1)
    (hsum : Summable fun p : I × {x : Fin n → ℤ // x ≠ 0} => ‖f p.1 p.2‖) :
    (Summable fun l : I →₀ (Fin n → ℤ) => ‖l.prod f‖) ∧
      HasProd (fun v => ∑' x, f v x) (∑' l : I →₀ (Fin n → ℤ), l.prod f) ∧
      ∑' l : I →₀ (Fin n → ℤ), l.prod f = ∏' v, ∑' x, f v x :=
  ⟨summable_norm_finsupp_prod f hf0 hsum, hasProd_tsum_finsupp f hf0 hsum,
    (hasProd_tsum_finsupp f hf0 hsum).tprod_eq.symm⟩

theorem euler_product_intVec_ennreal {I : Type} (n : ℕ) (f : I → (Fin n → ℤ) → ℝ≥0∞)
    (hf0 : ∀ v, f v 0 = 1) :
    HasProd (fun v => ∑' x, f v x) (∑' l : I →₀ (Fin n → ℤ), l.prod f) ∧
      ∑' l : I →₀ (Fin n → ℤ), l.prod f = ∏' v, ∑' x, f v x :=
  ⟨hasProd_tsum_finsupp_ennreal f hf0, tsum_finsupp_eq_tprod_ennreal f hf0⟩

end GlobalTheory.EulerSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProductLatticePositionsAndTerms
section
noncomputable section

namespace GlobalTheory.UnitLemma.Desc

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

section Prod

variable {R A₁ A₂ : Type} [CommRing R] [CommRing A₁] [CommRing A₂] [Algebra R A₁] [Algebra R A₂]

theorem aeval_prod_fst (x : A₁ × A₂) (f : R[X]) : (aeval x f).1 = aeval x.1 f :=
  (aeval_algHom_apply (AlgHom.fst R A₁ A₂) x f).symm

theorem aeval_prod_snd (x : A₁ × A₂) (f : R[X]) : (aeval x f).2 = aeval x.2 f :=
  (aeval_algHom_apply (AlgHom.snd R A₁ A₂) x f).symm

theorem isIntegral_pair_one {r : A₁} (hr : IsIntegral R r) : IsIntegral R ((r, 1) : A₁ × A₂) := by
  obtain ⟨f, hf, hfr⟩ := hr
  refine ⟨f * (X - C 1), hf.mul (monic_X_sub_C 1), ?_⟩
  rw [← aeval_def, map_mul]
  rw [← aeval_def] at hfr
  ext
  · rw [Prod.fst_mul, aeval_prod_fst, hfr, zero_mul]; rfl
  · rw [Prod.snd_mul, aeval_prod_snd (f := X - C 1)]; simp

theorem isIntegral_one_pair {r : A₂} (hr : IsIntegral R r) : IsIntegral R ((1, r) : A₁ × A₂) := by
  obtain ⟨f, hf, hfr⟩ := hr
  refine ⟨f * (X - C 1), hf.mul (monic_X_sub_C 1), ?_⟩
  rw [← aeval_def, map_mul]
  rw [← aeval_def] at hfr
  ext
  · rw [Prod.fst_mul, aeval_prod_fst (f := X - C 1)]; simp
  · rw [Prod.snd_mul, aeval_prod_snd, hfr, zero_mul]; rfl

theorem isIntegral_fst {x : A₁ × A₂} (hx : IsIntegral R x) : IsIntegral R x.1 := hx.map (AlgHom.fst R A₁ A₂)

theorem isIntegral_snd {x : A₁ × A₂} (hx : IsIntegral R x) : IsIntegral R x.2 := hx.map (AlgHom.snd R A₁ A₂)

end Prod

theorem dlt_map {ι κ A : Type} [CommMonoid A] (π : κ → A) (e : ι ↪ κ) (I : Finset ι) (f : A → ℚ) (y : A) :
    dlt π (I.map e) f y = dlt (π ∘ e) I f y := by
  unfold dlt
  symm
  refine Finset.sum_bij (fun J _ => J.map e) (fun J hJ => ?_) (fun J₁ _ J₂ _ h => Finset.map_injective e h)
    (fun J hJ => ?_) (fun J _ => ?_)
  · exact Finset.mem_powerset.2 (Finset.map_subset_map.2 (Finset.mem_powerset.1 hJ))
  · obtain ⟨u, hu, rfl⟩ := Finset.subset_map_iff.1 (Finset.mem_powerset.1 hJ)
    exact ⟨u, Finset.mem_powerset.2 hu, rfl⟩
  · simp [Finset.prod_map, Finset.card_map]

theorem dlt_empty {ι A : Type} [CommMonoid A] (π : ι → A) (f : A → ℚ) (y : A) : dlt π ∅ f y = f y := by
  simp [dlt]

theorem pos_term_prod : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (ι₁ ι₂ : Type) (e₁ π₁ : ι₁ → B₁.A) (e₂ π₂ : ι₂ → B₂.A) (S₁ : Finset ι₁) (S₂ : Finset ι₂) (a : K.O) (N : ℕ) (M : Submodule K.O (B₁.A × B₂.A)) (p : ι₁ ⊕ ι₂ → ℤ) (u₁ : B₁.A) (u₂ : B₂.A), (Pos (B₁.prod B₂) a (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) N M p → Pos B₁ a e₁ N (M.comap (LinearMap.inl K.O B₁.A B₂.A)) (p ∘ Sum.inl) ∧ Pos B₂ a e₂ N (M.map (LinearMap.snd K.O B₁.A B₂.A)) (p ∘ Sum.inr)) ∧ term (B₁.prod B₂) (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A))) (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr) (eS (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) (S₁.map Function.Embedding.inl) * (show (B₁.prod B₂).A from (u₁, u₂))) (eS (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) (S₂.map Function.Embedding.inr) * 1) M = term B₁ π₁ S₁ ∅ (eS B₁ e₁ S₁ * u₁) (eS B₁ e₁ ∅ * 1) (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * term B₂ π₂ ∅ S₂ (eS B₂ e₂ ∅ * u₂) (eS B₂ e₂ S₂ * 1) (M.map (LinearMap.snd K.O B₁.A B₂.A)) := by
  intro K B₁ B₂ ι₁ ι₂ e₁ π₁ e₂ π₂ S₁ S₂ a N M p u₁ u₂
  refine ⟨fun h => ⟨fun i => ⟨fun r hr => ?_, fun m hm => ?_⟩, fun j => ⟨fun r hr => ?_, fun m hm => ?_⟩⟩, ?_⟩
  · have := (h (Sum.inl i)).1 (r, 1) (isIntegral_pair_one hr)
    have key : (LinearMap.inl K.O B₁.A B₂.A) (al K a ^ ((p ∘ Sum.inl) i + N) • (e₁ i * r)) =
        al K a ^ (p (Sum.inl i) + N) • (((e₁ i, 0) : B₁.A × B₂.A) * (r, 1)) :=
      Prod.ext rfl (by show (0 : B₂.A) = al K a ^ (p (Sum.inl i) + N) • ((0 : B₂.A) * 1); simp)
    rw [Submodule.mem_comap, key]
    exact this
  · exact isIntegral_fst ((h (Sum.inl i)).2 (m, 0) hm)
  · have := (h (Sum.inr j)).1 (1, r) (isIntegral_one_pair hr)
    exact ⟨_, this, rfl⟩
  · obtain ⟨m', hm', rfl⟩ := hm
    exact isIntegral_snd ((h (Sum.inr j)).2 m' hm')
  · have hT : ∀ (z : B₁.A × B₂.A), z ∈ M → ∀ t : B₂.A,
        Algebra.trace K.E (B₁.A × B₂.A) (((0 : B₁.A), t) * z) = Algebra.trace K.E B₂.A (t * z.2) := by
      intro z _ t
      rw [Algebra.trace_prod_apply]
      simp
    have hD : ∀ t : B₂.A, InDual (B₁.prod B₂) ((0 : B₁.A), t) M ↔ InDual B₂ t (M.map (LinearMap.snd K.O B₁.A B₂.A)) := by
      intro t
      constructor
      · rintro h z ⟨z', hz', rfl⟩
        show Algebra.trace K.E B₂.A (t * z'.2) ∈ _
        rw [← hT z' hz' t]
        exact h z' hz'
      · intro h z hz
        convert h z.2 ⟨z, hz, rfl⟩ using 1
        exact hT z hz t
    have hE1 : eS (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A)))
        (S₁.map Function.Embedding.inl) = ((eS B₁ e₁ S₁, 0) : B₁.A × B₂.A) := by
      unfold eS
      rw [Finset.sum_map]
      show (∑ x ∈ S₁, ((e₁ x, 0) : B₁.A × B₂.A)) = (∑ i ∈ S₁, e₁ i, 0)
      ext <;> simp [Prod.fst_sum, Prod.snd_sum]
    have hE2 : eS (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A)))
        (S₂.map Function.Embedding.inr) = ((0, eS B₂ e₂ S₂) : B₁.A × B₂.A) := by
      unfold eS
      rw [Finset.sum_map]
      show (∑ x ∈ S₂, ((0, e₂ x) : B₁.A × B₂.A)) = (0, ∑ i ∈ S₂, e₂ i)
      ext <;> simp [Prod.fst_sum, Prod.snd_sum]
    have keyM : ∀ y : B₁.A, indM (B₁.prod B₂) M (LinearMap.inl K.O B₁.A B₂.A y) =
        indM B₁ (M.comap (LinearMap.inl K.O B₁.A B₂.A)) y := fun y => by
      unfold indM
      classical
      exact if_congr Iff.rfl rfl rfl
    have keyD : ∀ t : B₂.A, indD (B₁.prod B₂) M (((0 : B₁.A), t) : B₁.A × B₂.A) =
        indD B₂ (M.map (LinearMap.snd K.O B₁.A B₂.A)) t := fun t => by
      unfold indD
      classical
      exact if_congr (hD t) rfl rfl
    unfold term
    rw [dlt_map, dlt_map, dlt_empty, dlt_empty, hE1, hE2]
    have h0 : ∀ (B : InvAlg K) (e : ι₁ → B.A), eS B e ∅ = 0 := fun _ _ => by simp [eS]
    have h0' : ∀ (B : InvAlg K) (e : ι₂ → B.A), eS B e ∅ = 0 := fun _ _ => by simp [eS]
    rw [h0, h0', zero_mul, zero_mul]
    have hm0 : indM B₂ (M.map (LinearMap.snd K.O B₁.A B₂.A)) 0 = 1 := by simp [indM]
    have hd0 : indD B₁ (M.comap (LinearMap.inl K.O B₁.A B₂.A)) 0 = 1 := by
      simp [indD, InDual]
    rw [hm0, hd0, mul_one, one_mul]
    congr 1
    · unfold dlt
      refine Finset.sum_congr rfl fun J _ => ?_
      congr 1
      unfold indM
      have : (∏ j ∈ J, (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A)) ∘ Sum.inl) j) *
          (((eS B₁ e₁ S₁, 0) : B₁.A × B₂.A) * (u₁, u₂)) =
          LinearMap.inl K.O B₁.A B₂.A ((∏ j ∈ J, π₁ j) * (eS B₁ e₁ S₁ * u₁)) := by
        ext <;> simp [Prod.fst_prod, Prod.snd_prod]
      exact (congrArg (indM (B₁.prod B₂) M) this).trans (keyM _)
    · unfold dlt
      refine Finset.sum_congr rfl fun J _ => ?_
      congr 1
      have : (∏ j ∈ J, (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A)) ∘ Sum.inr) j) *
          (((0, eS B₂ e₂ S₂) : B₁.A × B₂.A) * 1) = ((0 : B₁.A), (∏ j ∈ J, π₂ j) * (eS B₂ e₂ S₂ * 1)) := by
        ext <;> simp [Prod.fst_prod, Prod.snd_prod]
      exact (congrArg (indD (B₁.prod B₂) M) this).trans (keyD _)

end GlobalTheory.UnitLemma.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PsiKMulNLEqOneOnIntegralLattice
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.NormInt

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem traceE [U : Unram F E] (z : E) : algebraMap F E (Algebra.trace F E z) = z + star z := by
  have := U.charZero
  obtain ⟨b, d, hb0, hs, hd, hd0⟩ := Unram.exists_basis_antifixed F E
  have h2 := (IsUnit.mk0 (2 : F) two_ne_zero)
  exact (quadratic_star_structure b d hb0 hs hd U.star_fix (IsUnit.mk0 d hd0) h2).2.2.1 z

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.K) (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∀ y : A.L, (∀ i, ‖j y i‖ ≤ 1) → A.psiK ψ (x * A.NL y) = 1 := by
  intro F E _ _ _ _ U A ψ hψ x r j hj y hy
  have := U.charZero
  have := U.ultraE
  have hE2 : Module.Finite F E := Module.finite_of_finrank_pos (by rw [U.finrank_eq]; norm_num)
  obtain ⟨⟨c⟩, hinj, hN, htr, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  have : Module.Free A.K A.L := Module.Free.of_basis c
  have : Module.Finite A.K A.L := Module.Finite.of_basis c
  have : Module.Free E A.L := Module.Free.of_basis (A.push.out.basis (Module.Free.chooseBasis F A.K))
  have : Module.Finite E A.L := Module.Finite.of_basis (A.push.out.basis (Module.Free.chooseBasis F A.K))
  set s : E := star (j y) ⬝ᵥ j y with hs_def

  have hs1 : ‖s‖ ≤ 1 := by
    rw [hs_def, dotProduct]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [Pi.star_apply, norm_mul, U.norm_star]
    exact mul_le_one₀ (hy i) (norm_nonneg _) (hy i)

  have hss : star s = s := by
    rw [hs_def, dotProduct, star_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.star_apply, star_mul', star_star, mul_comm]
  have hsL : s = Algebra.trace E A.L (algebraMap A.K A.L x * star y * y) := hj y y
  set T : F := Algebra.trace F A.K (x * A.NL y) with hT
  have hz : algebraMap A.K A.L (x * A.NL y) = algebraMap A.K A.L x * star y * y := by
    rw [map_mul, hN, mul_assoc, mul_comm y]
  have htK : ∀ k : A.K, Algebra.trace A.K A.L (algebraMap A.K A.L k) = 2 • k := by
    intro k
    apply hinj
    rw [htr, A.star_K, map_nsmul, two_nsmul]
  have h1 : Algebra.trace F A.L (algebraMap A.K A.L (x * A.NL y)) = 2 • T := by
    rw [← Algebra.trace_trace (S := A.K), htK, map_nsmul]
  have h2 : Algebra.trace F A.L (algebraMap A.K A.L (x * A.NL y)) = Algebra.trace F E s := by
    rw [← Algebra.trace_trace (S := E), hz, hsL]
  have h3 : algebraMap F E T = s := by
    have e := congrArg (algebraMap F E) (h1.symm.trans h2)
    rw [traceE, hss, map_nsmul, two_nsmul, ← two_mul, ← two_mul] at e
    have : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
    have h20 : (2 : E) ≠ 0 := two_ne_zero
    exact mul_left_cancel₀ h20 e
  have hT1 : ‖T‖ ≤ 1 := by rw [← norm_algebraMap' E T, h3]; exact hs1
  exact hψ.1 T hT1

end GlobalTheory.JR.NormInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelIndexUnitStabilizerIntegralUnitsNeZero
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.StabIndex

theorem relIndex_ne_zero : ∀ (K : UQ) (B : InvAlg K) (L : Submodule K.O B.A), IsLat K.O K.E L → ∀ c : K.O, c ≠ 0 →
    (∀ u : B.A, IsIntegral K.O u → ∀ y ∈ L, algebraMap K.O B.A c * u * y ∈ L) →
    (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) ≠ 0 := by
  intro K B L hL c hc h
  have hfin : {M : Submodule K.O B.A | mulLat K.O (algebraMap K.O B.A (c * c)) L ≤ M ∧ M ≤ L}.Finite :=
    GlobalTheory.T.finite_submodules_between_mulLeftImage_lattice K B L hL (c * c) (mul_ne_zero hc hc)
  exact relIndex_ne_zero_of_between K B L c hc hfin h

end GlobalTheory.UnitLemma.StabIndex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitIndicatorHermitianBlockLiftLastBasisOfNormLeStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitIndicatorHermitianBlock_liftLastBasis_of_norm_le_one : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] {r : ℕ} (X : Hn r F E) (ν : E) (l : F), ‖ν‖ ≤ 1 → unitU (r + 1) F E (GlobalTheory.JR.Step.liftH X ν l) = (if ‖l‖ ≤ 1 then 1 else 0) * unitU r F E X := by
  first | exact @GlobalTheory.JR.Step.unitU_liftH_of_norm_le_one | exact GlobalTheory.JR.Step.unitU_liftH_of_norm_le_one | (intros; apply GlobalTheory.JR.Step.unitU_liftH_of_norm_le_one <;> assumption)
end

