module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerDilationWeightsDualIsotropicVector
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Counterexamples.TransversalityLocal.FramePairFixatorUnitaryAndFixesFrame

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFundConjAndMeasure
section
noncomputable section
open NumberField MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.DegVol.UnipConj
variable {k r : ℕ} {ι : Type}

theorem of_conjM (a : Mat k r) (x : Mt k r) : Matrix.of (conjM a x) = a * Matrix.of x * a⁻¹ := rfl

theorem conjM_lmulM {a : Mat k r} (ha : IsUnit a.det) (m x : Mt k r) :
    conjM a (lmulM (Matrix.of m) x) = lmulM (Matrix.of (conjM a m)) (conjM a x) := by
  apply Matrix.of.injective
  have hl : ∀ (b : Mat k r) (y : Mt k r), Matrix.of (lmulM b y) = b * Matrix.of y := fun _ _ => rfl
  rw [of_conjM, hl, hl, of_conjM, of_conjM]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc a⁻¹ a, Matrix.nonsing_inv_mul a ha, Matrix.one_mul]

theorem mulVec_conj_iff (a M : Mat k r) (ha : IsUnit a.det) (w w' : Fin (2 * r + k + 1) → ℂ) :
    M *ᵥ (a *ᵥ w) = a *ᵥ w' ↔ (a⁻¹ * M * a) *ᵥ w = w' := by
  constructor
  · intro h
    have h' := congrArg (fun u => a⁻¹ *ᵥ u) h
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul a ha, Matrix.one_mulVec] at h'
    rw [← h', Matrix.mul_assoc]
  · intro h
    rw [← h, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv a ha, Matrix.one_mul]

theorem mem_realPts_iff {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Φ : ι → V → Fin (2 * r + k + 1) → ℂ) (Γ : Set (V ≃ₗ[K] V)) (n : ι → Mat k r)
    (hn : ∀ v, IsUnit (n v).det) (m : ι → Mt k r) :
    m ∈ realPts (fun v y => n v *ᵥ Φ v y) Γ ↔ (fun v => conjM (n v)⁻¹ (m v)) ∈ realPts Φ Γ := by
  have key : ∀ v (w w' : Fin (2 * r + k + 1) → ℂ),
      (Matrix.of (m v) *ᵥ (n v *ᵥ w) = n v *ᵥ w') ↔ Matrix.of (conjM (n v)⁻¹ (m v)) *ᵥ w = w' := by
    intro v w w'
    rw [mulVec_conj_iff _ _ (hn v), of_conjM, Matrix.nonsing_inv_nonsing_inv _ (hn v)]
  simp only [realPts, Set.mem_ofPred_eq, key]

theorem mem_RP_iff (n₁ g n₂ : ι → Mat k r) (h₁ : ∀ v, n₁ v ∈ Nset k r) (h₂ : ∀ v, n₂ v ∈ Nset k r)
    (x : ι → Mt k r) :
    x ∈ RP k r g ↔ (fun v => conjM (n₂ v)⁻¹ (x v)) ∈ RP k r (fun v => n₁ v * g v * n₂ v) := by
  have hu : ∀ v, IsUnit (n₂ v).det := fun v => StabHaar.unit_of_GG (h₂ v).1
  simp only [RP, Set.mem_ofPred_eq]
  refine forall_congr' fun v => ?_
  rw [StabHaar.Rset_conj (g v) (h₁ v) (h₂ v), of_conjM, Matrix.nonsing_inv_nonsing_inv _ (hu v)]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hu v), Matrix.mul_one,
    Matrix.mul_nonsing_inv_cancel_left _ _ (hu v)]

private theorem conjM_conjM_inv {a : Mat k r} (ha : IsUnit a.det) (y : Mt k r) :
    conjM a (conjM a⁻¹ y) = y := by
  have h := congrFun (StabHaar.conj_conj a a⁻¹) y
  rw [Matrix.mul_nonsing_inv a ha, StabHaar.conj_one] at h
  exact h

private theorem conjM_inv_conjM' {a : Mat k r} (ha : IsUnit a.det) (y : Mt k r) :
    conjM a⁻¹ (conjM a y) = y := by
  have h := congrFun (StabHaar.conj_conj a⁻¹ a) y
  rw [Matrix.nonsing_inv_mul a ha, StabHaar.conj_one] at h
  exact h

theorem isFund_conj_and_measure : ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] (k r : ℕ) (ι : Type) [Fintype ι] (Φ : ι → V → Fin (2 * r + k + 1) → ℂ) (Γ : Set (V ≃ₗ[K] V)) (n₁ g n₂ : ι → Mat k r) (Ω : Set (ι → Mt k r)) (lam : Measure (Mt k r)), SigmaFinite lam → (∀ v, n₁ v ∈ Nset k r ∧ n₂ v ∈ Nset k r ∧ IsUnit (g v).det) → IsFund (realPts Φ Γ) (RP k r (fun v => n₁ v * g v * n₂ v)) Ω → IsFund (realPts (fun v y => n₂ v *ᵥ Φ v y) Γ) (RP k r g) ((fun (x : ι → Mt k r) v => conjM (n₂ v) (x v)) '' Ω) ∧ Measure.pi (fun v => lam.map (conjM (n₂ v)⁻¹)) Ω = Measure.pi (fun _ : ι => lam) ((fun (x : ι → Mt k r) v => conjM (n₂ v) (x v)) '' Ω) := by
  intro K V _ _ _ k r ι _ Φ Γ n₁ g n₂ Ω lam hlam hN hF
  have := hlam
  have hu : ∀ v, IsUnit (n₂ v).det := fun v => StabHaar.unit_of_GG (hN v).2.1.1
  have hui : ∀ v, IsUnit ((n₂ v)⁻¹).det := fun v => Matrix.isUnit_nonsing_inv_det _ (hu v)
  let e : ∀ _ : ι, Mt k r ≃ᵐ Mt k r := fun v => StabHaar.conjE (n₂ v)⁻¹ (hui v)
  let E : (ι → Mt k r) ≃ᵐ (ι → Mt k r) := MeasurableEquiv.piCongrRight e
  let Cf : (ι → Mt k r) → (ι → Mt k r) := fun x v => conjM (n₂ v) (x v)
  have hEC : ∀ y, E (Cf y) = y := fun y => funext fun v => conjM_inv_conjM' (hu v) (y v)
  have hCE : ∀ y, Cf (E y) = y := fun y => funext fun v => conjM_conjM_inv (hu v) (y v)
  have hC : Cf '' Ω = E ⁻¹' Ω := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show E (Cf x) ∈ Ω
      rw [hEC]
      exact hx
    · intro hy
      exact ⟨E y, hy, hCE y⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show MeasurableSet (Cf '' Ω)
    rw [hC]
    exact E.measurable hF.1
  · intro x hx
    have hx' : E x ∈ RP k r (fun v => n₁ v * g v * n₂ v) :=
      (mem_RP_iff n₁ g n₂ (fun v => (hN v).1) (fun v => (hN v).2.1) x).1 hx
    obtain ⟨m', ⟨hm'Γ, hm'Ω⟩, huniq⟩ := hF.2 (E x) hx'
    have hR : ∀ m, m ∈ realPts (fun v y => n₂ v *ᵥ Φ v y) Γ ↔ E m ∈ realPts Φ Γ :=
      fun m => mem_realPts_iff Φ Γ n₂ hu m
    have hM : ∀ m, E (mulP m x) = mulP (E m) (E x) := fun m =>
      funext fun v => conjM_lmulM (hui v) (m v) (x v)
    refine ⟨Cf m', ⟨(hR _).2 (by rw [hEC]; exact hm'Γ), ?_⟩, ?_⟩
    · show mulP (Cf m') x ∈ Cf '' Ω
      rw [hC]
      show E (mulP (Cf m') x) ∈ Ω
      rw [hM, hEC]
      exact hm'Ω
    · rintro m ⟨hmΓ, hmΩ⟩
      have hmΩ' : E (mulP m x) ∈ Ω := by
        have h0 : mulP m x ∈ Cf '' Ω := hmΩ
        rw [hC] at h0
        exact h0
      have h1 : E m = m' := huniq (E m) ⟨(hR m).1 hmΓ, by rw [← hM]; exact hmΩ'⟩
      rw [← h1, hCE]
  · have hmp : MeasurePreserving E (Measure.pi fun _ : ι => lam)
        (Measure.pi fun v => lam.map (e v)) :=
      haveI : ∀ v, SigmaFinite (lam.map (e v)) := fun v => (e v).sigmaFinite_map
      measurePreserving_pi _ _ (fun v => ⟨(e v).measurable, rfl⟩)
    show _ = Measure.pi (fun _ : ι => lam) (Cf '' Ω)
    rw [hC, hmp.measure_preimage_equiv]
    rfl
end GlobalTheory.DegVol.UnipConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsTermLocalTermMoveOfIsometry
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

namespace GlobalTheory.LocOver.MoveTerm

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem mem_img (g : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) (x : V) : x ∈ img g Λ ↔ g.symm x ∈ Λ := by
  unfold img
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨g.symm x, h, by simp⟩

theorem map_mem_span_range {R : Type} [Semiring R] [Module R V] (φ : V →ₗ[R] V) {ι : Type} (v : ι → V)
    {x : V} (hx : x ∈ Submodule.span R (Set.range v)) :
    φ x ∈ Submodule.span R (Set.range fun a => φ (v a)) := by
  have := Submodule.apply_mem_span_image_of_mem_span φ hx
  rwa [← Set.range_comp] at this

variable (H : HermSp M V)

theorem h_symm {g : V ≃ₗ[E] V} (hg : IsUnitary H g) (x y : V) : H.h (g.symm x) (g.symm y) = H.h x y := by
  rw [← hg]; simp

theorem isSelfDual_img {g : V ≃ₗ[E] V} (hg : IsUnitary H g) {Λ : Submodule M.L.O V}
    (h : H.IsSelfDual Λ) : H.IsSelfDual (img g Λ) := by
  obtain ⟨hfg, hspan, hdual⟩ := h
  refine ⟨hfg.map _, ?_, fun x => ?_⟩
  · rw [eq_top_iff]
    intro x _
    have h1 : g.symm x ∈ Submodule.span E (Λ : Set V) := by rw [hspan]; trivial
    have h2 := Submodule.apply_mem_span_image_of_mem_span (g : V →ₗ[E] V) h1
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨y, hy, rfl⟩
    exact (mem_img g Λ _).2 (by simpa using hy)
  · rw [mem_img, hdual (g.symm x)]
    constructor
    · intro h y hy
      have := h _ ((mem_img g Λ y).1 hy)
      rwa [h_symm H hg] at this
    · intro h y hy
      have := h (g y) ((mem_img g Λ _).2 (by simpa using hy))
      rw [← hg (g.symm x) y, LinearEquiv.apply_symm_apply]; exact this

theorem prim_img (g : V ≃ₗ[E] V) {Λ : Submodule M.L.O V} {ι : Type} {v : ι → V}
    (h : H.Prim Λ v) : H.Prim (img g Λ) (fun a => g (v a)) := by
  obtain ⟨hmem, hli, hsat⟩ := h
  refine ⟨fun a => (mem_img g Λ _).2 (by simpa using hmem a), ?_, fun x hx hxs => ?_⟩
  · exact hli.map' (g : V →ₗ[E] V) (LinearEquiv.ker g)
  · have h1 : g.symm x ∈ Submodule.span E (Set.range v) := by
      have := map_mem_span_range (g.symm : V →ₗ[E] V) _ hxs
      simpa using this
    have h2 := hsat _ ((mem_img g Λ x).1 hx) h1
    have h3 := map_mem_span_range ((g : V →ₗ[E] V).restrictScalars M.L.O) _ h2
    simpa using h3

theorem isFrame_img {g : V ≃ₗ[E] V} (hg : IsUnitary H g) {Λ : Submodule M.L.O V} {r : ℕ}
    {f : Fin (r + 1) → V} {T : F} (h : H.IsFrame Λ r f T) :
    H.IsFrame (img g Λ) r (fun a => g (f a)) T := by
  obtain ⟨hp, hiso, hz, hT, hT0⟩ := h
  refine ⟨prim_img H g hp, fun a b hab => ?_, ?_, hT, hT0⟩
  · rw [hg]; exact hiso a b hab
  · rw [hg]; exact hz

theorem smulLat_img (g : V ≃ₗ[E] V) (c : E) {Λ : Submodule M.L.O V} {y : V}
    (hy : y ∈ H.smulLat c Λ) : g y ∈ H.smulLat c (img g Λ) := by
  unfold HermSp.smulLat at hy ⊢
  have := Submodule.apply_mem_span_image_of_mem_span ((g : V →ₗ[E] V).restrictScalars M.L.O) hy
  refine Submodule.span_mono ?_ (by simpa using this)
  rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  exact ⟨g w, (mem_img g Λ _).2 (by simpa using hw), by simp⟩

theorem zhat_move {g : V ≃ₗ[E] V} (hg : IsUnitary H g) {r : ℕ} (f f' : Fin (r + 1) → V) :
    H.Zhat (fun a => g (f a)) (fun b => g (f' b)) = H.Zhat f f' := by
  ext a b
  exact hg _ _

theorem isTerm_move {r : ℕ} (g : V ≃ₗ[E] V) (t : Term V M r) (hg : IsUnitary H g) (ht : H.IsTerm t) :
    H.IsTerm (GlobalTheory.LocOver.move g t) := by
  obtain ⟨hSD, hF, hF', hU, hG, hsplit⟩ := ht
  have hD : ∀ l, H.Dl (GlobalTheory.LocOver.move g t).f (GlobalTheory.LocOver.move g t).f' l = H.Dl t.f t.f' l := by
    intro l
    unfold HermSp.Dl
    rw [show (GlobalTheory.LocOver.move g t).f = fun a => g (t.f a) from rfl,
      show (GlobalTheory.LocOver.move g t).f' = fun a => g (t.f' a) from rfl, zhat_move H hg]
  refine ⟨isSelfDual_img H hg hSD, isFrame_img H hg hF, isFrame_img H hg hF', ?_, ?_, fun gs hgs => ?_⟩
  · rw [hD]; exact hU
  · unfold HermSp.Gdet
    rw [hD, hD]
    exact hG
  · obtain ⟨h1, h2, h3⟩ := hsplit gs hgs
    refine ⟨h1, h2, fun b => ?_⟩
    show g (t.f' b) - g (t.f b) ∈ H.smulLat _ (img g t.abelian₂)
    rw [← map_sub]
    exact smulLat_img H g _ (h3 b)

end GlobalTheory.LocOver.MoveTerm

theorem GlobalTheory.LocOver.isTerm_move_of_unitary : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ} (g : V ≃ₗ[E] V) (t : Term V M r), IsUnitary H g → H.IsTerm t → H.IsTerm (GlobalTheory.LocOver.move g t) :=
  fun H _ g t hg ht => GlobalTheory.LocOver.MoveTerm.isTerm_move H g t hg ht
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalIndicesColumnRowLevelsExact
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

namespace GlobalTheory

theorem prod_pow_sub_pow_eq_mul_prod_Icc (g : ℝ) (k : ℕ) :
    ∏ j ∈ Finset.range k, (g ^ k - g ^ j) =
      g ^ (k * (k - 1) / 2) * ∏ j ∈ Finset.Icc 1 k, (g ^ j - 1) := by

  have hshift : ∀ n : ℕ, ∏ j ∈ Finset.range n, (g ^ (j + 1) - 1) = ∏ j ∈ Finset.Icc 1 n, (g ^ j - 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.prod_range_succ, ih, Finset.prod_Icc_succ_top (by omega)]
  have hterm : ∀ j ∈ Finset.range k, g ^ k - g ^ j = g ^ j * (g ^ (k - 1 - j + 1) - 1) := by
    intro j hj
    have hjk : j + (k - 1 - j + 1) = k := by
      have := Finset.mem_range.mp hj
      omega
    rw [mul_sub, mul_one, ← pow_add, hjk]
  have hrev := Finset.prod_range_reflect (fun j => g ^ (j + 1) - 1) k
  rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Finset.sum_range_id, hrev, hshift]

theorem natCard_GL_zmod_real (g n : ℕ) (hg : g.Prime) :
    (Nat.card (GL (Fin n) (ZMod g)) : ℝ) = ∏ j ∈ Finset.range n, ((g : ℝ) ^ n - (g : ℝ) ^ j) := by
  haveI : Fact g.Prime := ⟨hg⟩
  rw [Matrix.card_GL_field, ZMod.card, Nat.cast_prod, Finset.prod_range]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Nat.cast_sub (Nat.pow_le_pow_right hg.pos j.isLt.le), Nat.cast_pow, Nat.cast_pow]

private theorem card_pattern_GL_eq_card_pow {F : Type} [Field F] [Fintype F] {n : ℕ}
    (fr : Fin n → Fin n → Prop) [DecidableRel fr] (hfr : ∀ i j, fr i j → i < j)
    (P : Matrix (Fin n) (Fin n) F → Prop)
    (hP : ∀ M, P M ↔ (∀ i, M i i = 1) ∧ ∀ i j, i ≠ j → ¬ fr i j → M i j = 0) :
    Nat.card {A : GL (Fin n) F // P (A : Matrix (Fin n) (Fin n) F)} =
      Nat.card F ^ Nat.card {p : Fin n × Fin n // fr p.1 p.2} := by
  classical

  have hunit : ∀ M : Matrix (Fin n) (Fin n) F, P M → IsUnit M := by
    intro M hM
    have hup : M.IsUpperTriangular := by
      intro i j hji
      exact ((hP M).1 hM).2 i j (ne_of_gt hji) (fun h => lt_asymm hji (hfr i j h))
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_isUpperTriangular hup,
      Finset.prod_eq_one (fun i _ => ((hP M).1 hM).1 i)]
    exact isUnit_one

  have e1 : {A : GL (Fin n) F // P (A : Matrix (Fin n) (Fin n) F)} ≃
      {M : Matrix (Fin n) (Fin n) F // P M} :=
    { toFun := fun A => ⟨A.1, A.2⟩
      invFun := fun M => ⟨(hunit M.1 M.2).unit, by rw [IsUnit.unit_spec]; exact M.2⟩
      left_inv := fun A => Subtype.ext (Units.ext rfl)
      right_inv := fun M => Subtype.ext (IsUnit.unit_spec (hunit M.1 M.2)) }
  have e2 : {M : Matrix (Fin n) (Fin n) F // P M} ≃ ({p : Fin n × Fin n // fr p.1 p.2} → F) :=
    { toFun := fun M p => M.1 p.1.1 p.1.2
      invFun := fun f => ⟨Matrix.of fun i j => if i = j then 1 else if h : fr i j then f ⟨(i, j), h⟩ else 0, by
        rw [hP]
        refine ⟨fun i => by simp, fun i j hij hf => by simp [hij, hf]⟩⟩
      left_inv := fun M => by
        apply Subtype.ext
        funext i j
        by_cases hij : i = j
        · subst hij
          simp [((hP _).1 M.2).1 i]
        · by_cases hf : fr i j
          · simp [hij, hf]
          · simp [hij, hf, ((hP _).1 M.2).2 i j hij hf]
      right_inv := fun f => by
        funext p
        have hne : p.1.1 ≠ p.1.2 := ne_of_lt (hfr _ _ p.2)
        simp [hne, p.2] }
  rw [Nat.card_congr (e1.trans e2)]
  exact Nat.card_fun

private theorem card_lt_pairs_eq_choose_two (k : ℕ) :
    Nat.card {p : Fin k × Fin k // p.1 < p.2} = k * (k - 1) / 2 := by
  classical
  have h : ∀ j : Fin k, (∑ i : Fin k, if i < j then 1 else 0) = (j : ℕ) := by
    intro j
    rw [← Finset.card_filter, ← Fin.card_Iio j]
    congr 1
    ext i
    simp
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  simp only
  rw [Finset.sum_comm, Finset.sum_congr rfl (fun j _ => h j), Fin.sum_univ_eq_sum_range (fun i => i) k,
    Finset.sum_range_id]

private theorem blk_mono' (s k : ℕ) {a b : ℕ} (hab : a ≤ b) : StandardLattice.blk s k a ≤ StandardLattice.blk s k b := by
  unfold StandardLattice.blk
  split_ifs <;> omega

private theorem card_excluded_pairs_eq_k (s k : ℕ) :
    Nat.card {p : Fin (k + 2 * s + 1) × Fin (k + 2 * s + 1) //
      p.1 < p.2 ∧ (p.2.val = s + k ∧ StandardLattice.blk s k p.1.val = s)} = k := by
  have hb : ∀ a : ℕ, StandardLattice.blk s k a = s → s ≤ a ∧ a < s + k + 1 := by
    intro a ha
    unfold StandardLattice.blk at ha
    split_ifs at ha <;> omega
  have hb' : ∀ a : ℕ, s ≤ a → a < s + k + 1 → StandardLattice.blk s k a = s := by
    intro a h1 h2
    unfold StandardLattice.blk
    split_ifs <;> omega
  have e : {p : Fin (k + 2 * s + 1) × Fin (k + 2 * s + 1) //
      p.1 < p.2 ∧ (p.2.val = s + k ∧ StandardLattice.blk s k p.1.val = s)} ≃ Fin k :=
    { toFun := fun p => ⟨p.1.1.val - s, by
        have h1 := hb _ p.2.2.2
        have h2 : p.1.1.val < p.1.2.val := p.2.1
        have h3 := p.2.2.1
        omega⟩
      invFun := fun t => ⟨(⟨s + t.val, by omega⟩, ⟨s + k, by omega⟩), by
        refine ⟨?_, rfl, hb' (s + t.val) (Nat.le_add_right _ _) (by omega)⟩
        show s + t.val < s + k
        omega⟩
      left_inv := fun p => by
        have h1 := hb _ p.2.2.2
        have h3 := p.2.2.1
        apply Subtype.ext
        apply Prod.ext
        · apply Fin.ext
          simp only
          omega
        · apply Fin.ext
          simp only
          omega
      right_inv := fun t => by
        apply Fin.ext
        simp }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem card_not_excluded_pairs_eq (s k : ℕ) :
    Nat.card {p : Fin (k + 2 * s + 1) × Fin (k + 2 * s + 1) //
      p.1 < p.2 ∧ ¬ (p.2.val = s + k ∧ StandardLattice.blk s k p.1.val = s)} =
      s * (2 * k + 2 * s + 1) + k * (k - 1) / 2 := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun p : Fin (k + 2 * s + 1) × Fin (k + 2 * s + 1) => p.1 < p.2))
    (fun p => p.2.val = s + k ∧ StandardLattice.blk s k p.1.val = s)
  rw [Finset.filter_filter, Finset.filter_filter] at hsplit
  have hall := card_lt_pairs_eq_choose_two (k + 2 * s + 1)
  have hex := card_excluded_pairs_eq_k s k
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hall hex ⊢
  rw [hex, hall] at hsplit
  have e : (k + 2 * s + 1) * (k + 2 * s + 1 - 1) = k * (k - 1) + (k + s * (2 * k + 2 * s + 1)) * 2 := by
    rw [Nat.add_sub_cancel]
    rcases k with _ | k
    · simp
      ring
    · rw [Nat.add_sub_cancel]
      ring
  rw [e, Nat.add_mul_div_right _ _ two_pos] at hsplit
  omega

theorem idxColLoc_idxRowLoc_exact : ∀ (D : D7) (i : Fin 2), StandardLattice.idxColLoc (D.host.g i) D.R.k = ∏ j ∈ Finset.Icc 1 D.R.k, ((D.host.g i : ℝ) ^ j - 1) ∧ StandardLattice.idxRowLoc (D.host.g i) D.R.k D.R.m = (∏ j ∈ Finset.range D.R.r, ((D.host.g i : ℝ) ^ D.R.r - (D.host.g i : ℝ) ^ j)) / ((D.host.g i : ℝ) ^ (D.R.rS * (2 * D.R.k + 2 * D.R.rS + 1)) * (D.host.g i : ℝ) ^ (D.R.k * (D.R.k - 1) / 2)) := by
  intro D i
  have hg : (D.host.g i).Prime := D.host.g_prime i
  haveI : Fact (D.host.g i).Prime := ⟨hg⟩
  have hpos : (0 : ℝ) < (D.host.g i : ℝ) := by exact_mod_cast hg.pos
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hs : D.R.rS = D.R.m / 2 - 1 := rfl
  have hm : D.R.k + D.R.m - 1 = D.R.k + 2 * D.R.rS + 1 := by
    have h1 := D.R.m_even
    have h2 := D.R.two_le_m
    obtain ⟨t, ht⟩ := h1
    rw [hs]
    omega
  constructor
  ·
    have hcard := card_pattern_GL_eq_card_pow (F := ZMod (D.host.g i)) (n := D.R.k) (fun a b => a < b)
      (fun _ _ h => h) StandardLattice.IsUnitri (by
        intro M
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h2, fun a b hab hlt => h1 a b (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hab))⟩
        · rintro ⟨h1, h2⟩
          exact ⟨fun a b hba => h2 a b (ne_of_gt hba) (not_lt.mpr hba.le), h1⟩)
    rw [card_lt_pairs_eq_choose_two, Nat.card_zmod] at hcard
    unfold StandardLattice.idxColLoc StandardLattice.idxLoc
    rw [hcard, natCard_GL_zmod_real _ _ hg, prod_pow_sub_pow_eq_mul_prod_Icc, Nat.cast_pow,
      mul_div_cancel_left₀ _ (pow_ne_zero _ hpos.ne')]
  ·

    unfold StandardLattice.idxRowLoc StandardLattice.idxLoc
    rw [hr, natCard_GL_zmod_real _ _ hg, ← pow_add]
    congr 2
    have hcard := card_pattern_GL_eq_card_pow (F := ZMod (D.host.g i)) (n := D.R.k + D.R.m - 1)
      (fun a b => a < b ∧ ¬ (b.val = (D.R.m / 2 - 1) + D.R.k ∧ StandardLattice.blk (D.R.m / 2 - 1) D.R.k a.val = D.R.m / 2 - 1))
      (fun _ _ h => h.1) (StandardLattice.IsRowLev D.R.k (D.R.m / 2 - 1)) (by
        intro M
        constructor
        · rintro ⟨h1, h2, h3, h4⟩
          refine ⟨h2, fun a b hab hf => ?_⟩
          by_cases hlt : a < b
          · have hE : b.val = (D.R.m / 2 - 1) + D.R.k ∧ StandardLattice.blk (D.R.m / 2 - 1) D.R.k a.val = D.R.m / 2 - 1 := by
              by_contra hc
              exact hf ⟨hlt, hc⟩
            exact h4 a b hE.1 hab hE.2
          · have hba : b < a := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hab)
            have hmono := blk_mono' (D.R.m / 2 - 1) D.R.k (Fin.lt_def.mp hba).le
            rcases lt_or_eq_of_le hmono with hl | he
            · exact h1 a b hl
            · exact h3 a b he.symm hba
        · rintro ⟨h1, h2⟩
          refine ⟨fun a b hb => ?_, h1, fun a b he hba => ?_, fun a b hj hab hblk => ?_⟩
          · have hba : b < a := by
              by_contra hc
              have := blk_mono' (D.R.m / 2 - 1) D.R.k (Fin.le_def.mp (not_lt.mp hc))
              omega
            exact h2 a b (ne_of_gt hba) (fun h => lt_asymm hba h.1)
          · exact h2 a b (ne_of_gt hba) (fun h => lt_asymm hba h.1)
          · exact h2 a b hab (fun h => h.2 ⟨hj, hblk⟩))
    rw [hcard, Nat.card_zmod, Nat.cast_pow]
    congr 1
    rw [← hs]
    have hc := card_not_excluded_pairs_eq D.R.rS D.R.k
    rw [← hm] at hc
    rw [hs] at hc ⊢
    rw [hc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitRepsOver
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

namespace GlobalTheory.LocOver

theorem orbit_reps_over : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V]
    [Module E V] (H : HermSp M V) (r : ℕ), ∀ P : FPair H r, Equivalence (Datum.Rel (P := P)) ∧ Nonempty (Reps P) ∧
    ∀ (d d' : Datum P) (t : Term V M r), Datum.Rel d d' → Over P d t → Over P d' t := by
  intro F _ _ _ E _ _ _ _ M _ V _ _ H r P
  have he := GlobalTheory.NonGenericLocalCheck.rel_equiv P
  refine ⟨he, GlobalTheory.NonGenericLocalCheck.reps_nonempty P, ?_⟩
  rintro d d' t hdd' ⟨g, hg, d'', h1, h2⟩
  exact ⟨g, hg, d'', he.trans (he.symm hdd') h1, h2⟩

end GlobalTheory.LocOver
end

