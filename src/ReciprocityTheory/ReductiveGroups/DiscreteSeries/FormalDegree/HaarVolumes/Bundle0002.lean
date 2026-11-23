module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.TriDens
public import Lemmata.CurryModusPonens.CurryMp

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.ChartWRA
section
noncomputable section

open Finset Matrix MeasureTheory Set

namespace ReciprocityTheory.ChartRestriction.DS

namespace ChartWRAux

theorem mp_curry (ι κ : Type*) [Fintype ι] [Fintype κ] :
    MeasurePreserving (Function.curry : (ι × κ → ℂ) → ι → κ → ℂ) volume volume := by
  first | exact Bl.CurryModusPonens.goal1 .. | (apply Bl.CurryModusPonens.goal1 <;> assumption) | (intros; apply Bl.CurryModusPonens.goal1 <;> assumption)

theorem mp_perm4 {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] (μa : Measure α) (μb : Measure β) (μc : Measure γ) (μd : Measure δ)
    [SigmaFinite μa] [SigmaFinite μb] [SigmaFinite μc] [SigmaFinite μd] :
    MeasurePreserving (fun p : (α × β) × (γ × δ) => ((p.2.1, p.1.1), (p.1.2, p.2.2)))
      ((μa.prod μb).prod (μc.prod μd)) ((μc.prod μa).prod (μb.prod μd)) := by
  have h1 := measurePreserving_prodAssoc μa μb (μc.prod μd)
  have h2 := (MeasurePreserving.id μa).prod
    ((measurePreserving_prodAssoc μb μc μd).symm _)
  have h3 := (MeasurePreserving.id μa).prod
    (((Measure.measurePreserving_swap (μ := μb) (ν := μc))).prod (MeasurePreserving.id μd))
  have h4 := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μc μb μd)
  have h5 := (measurePreserving_prodAssoc μa μc (μb.prod μd)).symm _
  have h6 := (Measure.measurePreserving_swap (μ := μa) (ν := μc)).prod (MeasurePreserving.id (μb.prod μd))
  have h := h6.comp (h5.comp (h4.comp (h3.comp (h2.comp h1))))
  convert h using 1
  funext p
  rfl

abbrev Lo (N : ℕ) : Type := {ab : Fin N × Fin N // ab.2 < ab.1}

abbrev Up (N : ℕ) : Type := {ab : Fin N × Fin N // ab.1 < ab.2}

variable {N : ℕ}

local instance volTri : (volume : Measure (TriCo N)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _

def idx (N : ℕ) : Fin N ⊕ (Lo N ⊕ Up N) ≃ Fin N × Fin N where
  toFun i := match i with
    | Sum.inl a => (a, a)
    | Sum.inr (Sum.inl ab) => ab.1
    | Sum.inr (Sum.inr ab) => ab.1
  invFun ab := if h : ab.1 = ab.2 then Sum.inl ab.1 else if h' : ab.2 < ab.1 then Sum.inr (Sum.inl ⟨ab, h'⟩)
    else Sum.inr (Sum.inr ⟨ab, lt_of_le_of_ne (not_lt.1 h') h⟩)
  left_inv := by
    rintro (a | ⟨ab, h⟩ | ⟨ab, h⟩)
    · simp
    · simp [h.ne', h]
    · simp [h.ne, not_lt.2 h.le]
  right_inv := by
    rintro ⟨a, b⟩
    dsimp only
    split_ifs with h h'
    · simp [h]
    · rfl
    · rfl

def rho (p : UCo N × TriCo N) : Fin N → Fin N → ℂ := fun a b =>
  if a = b then ((p.2.1 a : ℝ) : ℂ) + ((p.1.1 a : ℝ) : ℂ) * Complex.I
  else if h : b < a then p.1.2 ⟨(a, b), h⟩ else if h' : a < b then p.2.2 ⟨(a, b), h'⟩ else 0

def e2 (q : (Fin N → ℝ) × (Fin N → ℝ)) : Fin N → ℂ := fun a => ⟨q.1 a, q.2 a⟩

theorem measurePreserving_second_reorder : MeasurePreserving (e2 (N := N)) volume volume := by
  have h1 := (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin N)).symm _
  have h2 := volume_preserving_pi (fun _ : Fin N => (Complex.volume_preserving_equiv_real_prod).symm _)
  exact h2.comp h1

def rho0 (p : UCo N × TriCo N) : Fin N → Fin N → ℂ :=
  Function.curry (MeasurableEquiv.piCongrLeft (fun _ : Fin N × Fin N => ℂ) (idx N)
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin N ⊕ (Lo N ⊕ Up N) => ℂ)).symm
      (e2 (p.2.1, p.1.1), (MeasurableEquiv.sumPiEquivProdPi (fun _ : Lo N ⊕ Up N => ℂ)).symm (p.1.2, p.2.2))))

theorem measurePreserving_rho_reorder : MeasurePreserving (rho0 (N := N)) volume volume := by
  have h1 := mp_perm4 (volume : Measure (Fin N → ℝ)) (volume : Measure (Lo N → ℂ))
    (volume : Measure (Fin N → ℝ)) (volume : Measure (Up N → ℂ))
  have h2 := (measurePreserving_second_reorder (N := N)).prod (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Lo N ⊕ Up N => ℂ))
  have h3 := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin N ⊕ (Lo N ⊕ Up N) => ℂ)
  have h4 := volume_measurePreserving_piCongrLeft (fun _ : Fin N × Fin N => ℂ) (idx N)
  have h5 := mp_curry (Fin N) (Fin N)
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

theorem rho_reorder_eq_rho : rho0 (N := N) = rho := by
  funext p a b
  have key : ∀ i, rho0 p (idx N i).1 (idx N i).2 =
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin N ⊕ (Lo N ⊕ Up N) => ℂ)).symm
        (e2 (p.2.1, p.1.1), (MeasurableEquiv.sumPiEquivProdPi (fun _ : Lo N ⊕ Up N => ℂ)).symm (p.1.2, p.2.2)) i :=
    fun i => MeasurableEquiv.piCongrLeft_apply_apply (idx N) (β := fun _ => ℂ) _ i
  rcases lt_trichotomy a b with h | rfl | h
  · have k := key (Sum.inr (Sum.inr ⟨(a, b), h⟩))
    simp only [rho, h.ne, not_lt.2 h.le, h, if_false, dif_neg, dif_pos, not_false_eq_true]
    exact k
  · have k := key (Sum.inl a)
    simp only [rho, if_true]
    refine k.trans ?_
    apply Complex.ext <;> simp <;> rfl
  · have k := key (Sum.inr (Sum.inl ⟨(a, b), h⟩))
    simp only [rho, h.ne', h, if_false, dif_pos]
    exact k

theorem mp_rho : MeasurePreserving (rho (N := N)) volume volume := by
  rw [← rho_reorder_eq_rho]; exact measurePreserving_rho_reorder

def sh (p : UCo N × TriCo N) : UCo N × TriCo N :=
  (p.1, (p.2.1, fun ab => p.2.2 ab - star (p.1.2 ⟨(ab.1.2, ab.1.1), ab.2⟩)))

theorem mp_sh : MeasurePreserving (sh (N := N)) volume volume := by
  have hc : Continuous (fun q : UCo N × TriCo N =>
      ((0 : Fin N → ℝ), fun ab : Up N => -star (q.1.2 ⟨(ab.1.2, ab.1.1), ab.2⟩)) + q.2) := by
    refine (continuous_const.prodMk (continuous_pi fun ab => ?_)).add continuous_snd
    exact ((continuous_apply _).comp (continuous_snd.comp continuous_fst)).star.neg
  have h := (MeasurePreserving.id (volume : Measure (UCo N))).skew_product
    (g := fun x (t : TriCo N) => ((0 : Fin N → ℝ), fun ab : Up N => -star (x.2 ⟨(ab.1.2, ab.1.1), ab.2⟩)) + t)
    (μc := (volume : Measure (TriCo N))) (μd := (volume : Measure (TriCo N)))
    hc.measurable (Filter.Eventually.of_forall fun x => map_add_left_eq_self (volume : Measure (TriCo N)) _)
  have e : sh (N := N) = fun p => (id p.1,
      ((0 : Fin N → ℝ), fun ab : Up N => -star (p.1.2 ⟨(ab.1.2, ab.1.1), ab.2⟩)) + p.2) := by
    funext p
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · simp [sh]
    · funext ab
      simp [sh, sub_eq_add_neg, add_comm]
  rw [e]; exact h

def lam (p : UCo N × TriCo N) : Fin N → Fin N → ℂ := Matrix.of.symm (skMat p.1 + upMat p.2)

theorem lam_eq : lam (N := N) = rho ∘ sh := by
  funext p a b
  simp only [lam, Function.comp_apply, rho, sh, Matrix.of_symm_apply, Matrix.add_apply, skMat, upMat]
  rcases lt_trichotomy a b with h | rfl | h
  · simp [h.ne, not_lt.2 h.le, h]; ring
  · simp; ring
  · simp [h.ne', h, not_lt.2 h.le]

theorem mp_lam : MeasurePreserving (lam (N := N)) volume volume := by
  rw [lam_eq]; exact mp_rho.comp mp_sh

def lamInv (Z : Fin N → Fin N → ℂ) : UCo N × TriCo N :=
  ((fun a => (Z a a).im, fun ab => Z ab.1.1 ab.1.2),
   (fun a => (Z a a).re, fun ab => Z ab.1.1 ab.1.2 + star (Z ab.1.2 ab.1.1)))

theorem lamInv_lam (p : UCo N × TriCo N) : lamInv (lam p) = p := by
  obtain ⟨⟨x1, x2⟩, ⟨t1, t2⟩⟩ := p
  simp only [lamInv, lam, Matrix.of_symm_apply, Matrix.add_apply, skMat, upMat]
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
  · funext a; simp
  · funext ab; obtain ⟨⟨a, b⟩, h⟩ := ab; simp [h.ne', h, not_lt.2 h.le]
  · funext a; simp
  · funext ab; obtain ⟨⟨a, b⟩, h⟩ := ab; simp [h.ne, h.ne', h, not_lt.2 h.le]

theorem lam_lamInv (Z : Fin N → Fin N → ℂ) : lam (lamInv Z) = Z := by
  funext a b
  simp only [lamInv, lam, Matrix.of_symm_apply, Matrix.add_apply, skMat, upMat]
  rcases lt_trichotomy a b with h | rfl | h
  · simp [h.ne, not_lt.2 h.le, h]
  · apply Complex.ext <;> simp
  · simp [h.ne', h, not_lt.2 h.le]

def lamL : (UCo N × TriCo N) →ₗ[ℝ] (Fin N → Fin N → ℂ) where
  toFun := lam
  map_add' p q := by
    funext a b
    simp only [lam, Matrix.of_symm_apply, Matrix.add_apply, skMat, upMat, Prod.fst_add, Prod.snd_add,
      Pi.add_apply]
    split_ifs <;> (try simp [star_add]) <;> (try ring)
  map_smul' c p := by
    funext a b
    simp only [lam, Matrix.of_symm_apply, Matrix.add_apply, skMat, upMat, Prod.smul_fst, Prod.smul_snd,
      Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> (try simp [Complex.real_smul]) <;> (try ring)

def lamE : (UCo N × TriCo N) ≃L[ℝ] (Fin N → Fin N → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { lamL with invFun := lamInv, left_inv := lamInv_lam, right_inv := lam_lamInv }

theorem lamE_apply (p : UCo N × TriCo N) : lamE p = lam p := rfl

end ChartWRAux

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.DensOn
section
noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

abbrev KPair (ε : Fin n → Bool) : Type := {ab : Fin n × Fin n // ab.2 < ab.1 ∧ ε ab.1 = ε ab.2}

abbrev KCo (ε : Fin n → Bool) : Type := (Fin n → ℝ) × (KPair ε → ℂ)

def kMat {ε : Fin n → Bool} (w : KCo ε) : Matrix (Fin n) (Fin n) ℂ := fun a b =>
  if a = b then Complex.I * ((w.1 a : ℝ) : ℂ)
  else if h : b < a ∧ ε a = ε b then w.2 ⟨(a, b), h⟩
  else if h' : a < b ∧ ε b = ε a then -star (w.2 ⟨(b, a), h'⟩) else 0

abbrev GCo (ε : Fin n → Bool) : Type := KCo ε × (PCoord ε → ℂ)

def gMat {ε : Fin n → Bool} (s : GCo ε) : Matrix (Fin n) (Fin n) ℂ := kMat s.1 + pmat s.2

def expSet {ε : Fin n → Bool} (S : Set (GCo ε)) : Set (UJ ε) :=
  {g | ∃ s ∈ S, toM g = NormedSpace.exp (gMat s)}

def polSet {ε : Fin n → Bool} (S : Set (GCo ε)) : Set (UJ ε) :=
  {g | ∃ s ∈ S, toM g = NormedSpace.exp (kMat s.1) * NormedSpace.exp (pmat s.2)}

def DensOn {ε : Fin n → Bool} (ν : Set (GCo ε) → ENNReal) (d : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ δ > 0, ∀ S : Set (GCo ε), MeasurableSet S → (∀ s ∈ S, ‖s‖ < δ) →
    ν S ≤ ENNReal.ofReal ((1 + η) * d) * volume S ∧ ENNReal.ofReal ((1 - η) * d) * volume S ≤ ν S

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.DetNull
section
noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

theorem measurableSet_mem_span_range (n m : ℕ) :
    MeasurableSet {p : (Fin m → ℂ) × (Fin n → Fin m → ℂ) |
      p.1 ∈ Submodule.span ℂ (Set.range p.2)} := by
  have h : {p : (Fin m → ℂ) × (Fin n → Fin m → ℂ) | p.1 ∈ Submodule.span ℂ (Set.range p.2)} =
      Set.range (fun q : (Fin n → ℂ) × (Fin n → Fin m → ℂ) => (∑ j, q.1 j • q.2 j, q.2)) := by
    ext ⟨x, W⟩
    simp only [Set.mem_ofPred_eq, Set.mem_range, Prod.mk.injEq, Prod.exists]
    rw [Submodule.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, W, hc, rfl⟩
    · rintro ⟨c, W', hc, rfl⟩
      exact ⟨c, hc⟩
  rw [h]
  obtain ⟨K, hK, hKe⟩ := isSigmaCompact_range (X := (Fin n → ℂ) × (Fin n → Fin m → ℂ))
    (f := fun q => (∑ j, q.1 j • q.2 j, q.2)) (by fun_prop)
  rw [← hKe]
  exact MeasurableSet.iUnion fun k => (hK k).measurableSet

theorem volume_span_range_eq_zero (n : ℕ) (W : Fin n → Fin (n + 1) → ℂ) :
    volume ((Submodule.span ℂ (Set.range W) : Submodule ℂ (Fin (n + 1) → ℂ)) :
      Set (Fin (n + 1) → ℂ)) = 0 := by
  have h1 : Module.finrank ℂ (Submodule.span ℂ (Set.range W)) ≤ n := by
    first
    | simpa using finrank_span_range_le_card (R := ℂ) W
    | simpa using Submodule.finrank_span_range_le_card (R := ℂ) W
    | simpa using finrank_range_le_card (R := ℂ) W
    | (have h2 := finrank_range_le_card (R := ℂ) W
       unfold Set.finrank at h2
       simpa using h2)
    | (have h2 := finrank_range_le_card (K := ℂ) W
       unfold Set.finrank at h2
       simpa using h2)
    | (have h2 := rank_span_le_of_finite (R := ℂ) (Set.finite_range W)
       exact absurd h2 (by simp))
  have hne : (Submodule.span ℂ (Set.range W)) ≠ ⊤ := by
    intro htop
    rw [htop, finrank_top, Module.finrank_fin_fun] at h1
    omega
  have hne' : (Submodule.span ℂ (Set.range W)).restrictScalars ℝ ≠ ⊤ := by
    intro h
    apply hne
    first
    | exact (Submodule.restrictScalars_eq_top_iff ℝ ℂ _).mp h
    | exact Submodule.restrictScalars_injective ℝ ℂ (Fin (n + 1) → ℂ) (by rw [h]; rfl)
  exact MeasureTheory.Measure.addHaar_submodule volume _ hne'

theorem exists_row_mem_span_of_det_eq_zero {n : ℕ} (Z : Fin (n + 1) → Fin (n + 1) → ℂ)
    (hZ : (Matrix.of Z).det = 0) :
    ∃ i : Fin (n + 1), Z i ∈ Submodule.span ℂ (Set.range fun j : Fin n => Z (i.succAbove j)) := by
  have hli : ¬ LinearIndependent ℂ Z := by
    intro h
    have hu : IsUnit (Matrix.of Z) := Matrix.linearIndependent_rows_iff_isUnit.mp h
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero hZ
  have hex : ∃ i, Z i ∈ Submodule.span ℂ (Z '' (Set.univ \ {i})) := by
    by_contra hno
    push_neg at hno
    apply hli
    first
    | exact linearIndependent_iff_not_mem_span.mpr hno
    | exact linearIndependent_iff_notMem_span.mpr hno
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, ?_⟩
  have himg : Z '' (Set.univ \ {i}) = Set.range fun j : Fin n => Z (i.succAbove j) := by
    rw [show (fun j : Fin n => Z (i.succAbove j)) = Z ∘ i.succAbove from rfl, Set.range_comp,
      Fin.range_succAbove, Set.compl_eq_univ_diff]
  rw [himg] at hi
  exact hi

theorem volume_det_eq_zero :
    volume {Z : Fin N → Fin N → ℂ | (Matrix.of Z).det = 0} = 0 := by
  cases N with
  | zero =>
    have h : {Z : Fin 0 → Fin 0 → ℂ | (Matrix.of Z).det = 0} = ∅ := by
      ext Z
      simp [Matrix.det_isEmpty]
    rw [h, measure_empty]
  | succ n =>
    let T : Set ((Fin (n + 1) → ℂ) × (Fin n → Fin (n + 1) → ℂ)) :=
      {p | p.1 ∈ Submodule.span ℂ (Set.range p.2)}
    have hT : MeasurableSet T := measurableSet_mem_span_range n (n + 1)
    have hsub : {Z : Fin (n + 1) → Fin (n + 1) → ℂ | (Matrix.of Z).det = 0} ⊆
        ⋃ i : Fin (n + 1),
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Fin (n + 1) → ℂ) i) ⁻¹' T := by
      intro Z hZ
      obtain ⟨i, hi⟩ := exists_row_mem_span_of_det_eq_zero Z hZ
      exact Set.mem_iUnion.2 ⟨i, hi⟩
    refine measure_mono_null hsub (measure_iUnion_null fun i => ?_)
    have mp := measurePreserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => (volume : Measure (Fin (n + 1) → ℂ))) i
    have h1 := mp.measure_preimage hT.nullMeasurableSet
    change (Measure.pi fun _ : Fin (n + 1) => (volume : Measure (Fin (n + 1) → ℂ))) _ = 0
    rw [h1, Measure.prod_apply_symm hT]
    exact (lintegral_congr fun W => volume_span_range_eq_zero n W).trans lintegral_zero

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.GaussA
section
noncomputable section

section
open Finset MeasureTheory Set

namespace ReciprocityTheory.ChartRestriction.DS

theorem gaussA_lint_pi_ofReal {ι : Type*} [Fintype ι] {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : ∀ i, Measure (E i)} [∀ i, SigmaFinite (μ i)] (f : ∀ i, E i → ℝ)
    (hf : ∀ i, Integrable (f i) (μ i)) (h0 : ∀ i x, 0 ≤ f i x) :
    ∫⁻ x, ENNReal.ofReal (∏ i, f i (x i)) ∂(Measure.pi μ) = ∏ i, ENNReal.ofReal (∫ x, f i x ∂(μ i)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (Integrable.fintype_prod_dep hf)
    (ae_of_all _ fun x => Finset.prod_nonneg fun i _ => h0 i _), integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (h0 i))]

theorem gaussA_real_int : Integrable (fun x : ℝ => Real.exp (-x ^ 2)) := by
  simpa using integrable_exp_neg_mul_sq (b := 1) one_pos

theorem gaussA_cfun_eq : (fun z : ℂ => Real.exp (-‖z‖ ^ 2)) =
    (fun p : ℝ × ℝ => Real.exp (-p.1 ^ 2) * Real.exp (-p.2 ^ 2)) ∘ Complex.measurableEquivRealProd := by
  funext z
  simp only [Function.comp_apply, Complex.measurableEquivRealProd_apply, ← Real.exp_add]
  congr 1
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem gaussA_cint : Integrable (fun z : ℂ => Real.exp (-‖z‖ ^ 2)) := by
  rw [gaussA_cfun_eq, Complex.volume_preserving_equiv_real_prod.integrable_comp_emb
    Complex.measurableEquivRealProd.measurableEmbedding]
  exact Integrable.mul_prod gaussA_real_int gaussA_real_int

theorem gaussA_cintegral : ∫ z : ℂ, Real.exp (-‖z‖ ^ 2) = Real.pi := by
  have h := Complex.volume_preserving_equiv_real_prod.integral_comp
    Complex.measurableEquivRealProd.measurableEmbedding
    (fun p : ℝ × ℝ => Real.exp (-p.1 ^ 2) * Real.exp (-p.2 ^ 2))
  have h2 : ∫ p : ℝ × ℝ, Real.exp (-p.1 ^ 2) * Real.exp (-p.2 ^ 2) = Real.pi := by
    rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
      integral_prod_mul (fun x : ℝ => Real.exp (-x ^ 2)) (fun x : ℝ => Real.exp (-x ^ 2))]
    have hg : ∫ x : ℝ, Real.exp (-x ^ 2) = Real.sqrt Real.pi := by
      simpa using integral_gaussian 1
    rw [hg, Real.mul_self_sqrt Real.pi_pos.le]
  rw [gaussA_cfun_eq]
  simpa [Function.comp_def] using h.trans h2

theorem gaussA_rad (a : ℕ) :
    ∫ r in Ioi (0:ℝ), Real.exp (-r ^ 2) * |r| ^ (2 * a + 1) = (a.factorial : ℝ) / 2 := by
  have h := integral_rpow_mul_exp_neg_rpow (p := 2) (q := ((2 * a + 1 : ℕ) : ℝ)) two_pos (by have := (Nat.cast_nonneg (2*a+1) : (0:ℝ) ≤ _); linarith)
  have hc : ∫ r in Ioi (0:ℝ), Real.exp (-r ^ 2) * |r| ^ (2 * a + 1) =
      ∫ x in Ioi (0:ℝ), x ^ (((2 * a + 1 : ℕ) : ℝ)) * Real.exp (-x ^ (2:ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    simp only [Real.rpow_natCast, abs_of_pos (mem_Ioi.mp hx)]
    rw [show x ^ (2:ℝ) = x ^ (2:ℕ) by exact_mod_cast Real.rpow_natCast x 2, mul_comm]
  rw [hc, h]
  have : ((((2 * a + 1 : ℕ) : ℝ)) + 1) / 2 = (a : ℝ) + 1 := by push_cast; ring
  rw [this, Real.Gamma_nat_eq_factorial]
  ring

theorem gaussA_rad_int (a : ℕ) :
    IntegrableOn (fun r : ℝ => Real.exp (-r ^ 2) * |r| ^ (2 * a + 1)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := 1) one_pos (s := ((2 * a + 1 : ℕ) : ℝ)) (by have := (Nat.cast_nonneg (2*a+1) : (0:ℝ) ≤ _); linarith)
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast, abs_of_pos (mem_Ioi.mp hx)]
  ring_nf

end ReciprocityTheory.ChartRestriction.DS

end

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

theorem gaussB_hs_eq_re_trace (M : Matrix (Fin N) (Fin N) ℂ) : hs M = (trace (Mᴴ * M)).re := by
  simp only [hs, trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [Complex.star_def, Complex.conj_mul']
  norm_cast

theorem gaussB_hs_unitary_mul (k : UNgrp N) (M : Matrix (Fin N) (Fin N) ℂ) : hs (toM k * M) = hs M := by
  have hk : inUJ (fun _ : Fin N => true) (toM k) := k.2
  have hJ : Jm (fun _ : Fin N => true) = 1 := by
    unfold Jm; simp
  unfold inUJ at hk
  rw [hJ, Matrix.mul_one] at hk
  rw [gaussB_hs_eq_re_trace, gaussB_hs_eq_re_trace, conjTranspose_mul,
    show Mᴴ * (toM k)ᴴ * (toM k * M) = Mᴴ * ((toM k)ᴴ * toM k) * M by simp only [Matrix.mul_assoc],
    hk, Matrix.mul_one]

theorem gaussB_card_lt : Fintype.card {ab : Fin N × Fin N // ab.1 < ab.2} = N * (N - 1) / 2 := by
  rw [Fintype.card_subtype, Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product]
  have h1 : ∀ i : Fin N, (∑ j : Fin N, if i < j then 1 else 0) = N - 1 - i := by
    intro i
    rw [← Finset.card_filter, Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
  simp_rw [h1]
  have h2 : (∑ i : Fin N, (N - 1 - (i : ℕ))) = ∑ i : Fin N, (i : ℕ) := by
    refine Fintype.sum_equiv Fin.revPerm _ _ (fun i => ?_)
    simp only [Fin.revPerm_apply, Fin.val_rev]
    omega
  rw [h2, Fin.sum_univ_eq_sum_range (fun i => i) N, Finset.sum_range_id]

theorem gaussB_prod_fact :
    (∏ j : Fin N, (((N - 1 - (j : ℕ)).factorial : ℝ) / 2)) = (∏ i ∈ range N, (i.factorial : ℝ)) / 2 ^ N := by
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [← Fin.prod_univ_eq_prod_range (fun i => (i.factorial : ℝ)) N]
  refine Fintype.prod_equiv Fin.revPerm _ _ (fun i => ?_)
  simp only [Fin.revPerm_apply, Fin.val_rev]
  exact congrArg (fun m : ℕ => ((m.factorial : ℕ) : ℝ)) (by omega)

end ReciprocityTheory.ChartRestriction.DS
end
end

