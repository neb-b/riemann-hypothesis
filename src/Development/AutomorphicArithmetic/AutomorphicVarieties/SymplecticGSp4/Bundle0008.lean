module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SpanMono
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ExDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.SymplecticGSp4
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.LocUnr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PtLimit
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem mem_gradedSub {O S X : Type} [CommRing O] [CommRing S] [Algebra O S] [AddCommGroup X]
    (𝒜 : X → Submodule O S) [SetLike.GradedMonoid 𝒜] {j : X} {f : S} (hf : f ∈ 𝒜 j) : f ∈ gradedSub 𝒜 := by
  show f ∈ ⨆ i, 𝒜 i
  exact Submodule.mem_iSup_of_mem j hf

private theorem limit_graded {O S X K : Type} [CommRing O] [CommRing S] [Algebra O S] [AddCommGroup X]
    [CommRing K] [Algebra O K] (𝒜 : X → Submodule O S) [SetLike.GradedMonoid 𝒜] (hI : iSupIndep 𝒜)
    (ξ : gradedSub 𝒜 →ₐ[O] K) (p : X →+ ℤ)
    (h : ∀ j f (hf : f ∈ 𝒜 j), p j < 0 → ξ ⟨f, mem_gradedSub 𝒜 hf⟩ = 0) :
    ∃ ξ₀ : gradedSub 𝒜 →ₐ[O] K, ∀ j f (hf : f ∈ 𝒜 j),
      ξ₀ ⟨f, mem_gradedSub 𝒜 hf⟩ = if p j = 0 then ξ ⟨f, mem_gradedSub 𝒜 hf⟩ else 0 := by
  classical
  let B := gradedSub 𝒜
  let Z : Set X := {j | p j = 0}
  let P0 : Submodule O B := Submodule.comap B.val.toLinearMap (⨆ j ∈ Z, 𝒜 j)
  let P1 : Submodule O B := Submodule.comap B.val.toLinearMap (⨆ j ∈ Zᶜ, 𝒜 j)
  have hdisj := hI.disjoint_biSup_biSup (s := Z) (t := Zᶜ) disjoint_compl_right
  have hc : IsCompl P0 P1 := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x h0 h1
      exact Subtype.ext (Submodule.disjoint_def.mp hdisj _ h0 h1)
    · rw [codisjoint_iff, eq_top_iff]
      rintro ⟨x, hx⟩ -
      have hle : (⨆ j, 𝒜 j) ≤ (⨆ j ∈ Z, 𝒜 j) ⊔ (⨆ j ∈ Zᶜ, 𝒜 j) := by
        refine iSup_le fun j => ?_
        by_cases hj : j ∈ Z
        · exact le_sup_of_le_left (le_biSup 𝒜 hj)
        · exact le_sup_of_le_right (le_biSup 𝒜 hj)
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (hle hx)
      have hsub : ∀ s : Set X, (⨆ j ∈ s, 𝒜 j) ≤ ⨆ j, 𝒜 j := fun s => iSup₂_le fun j _ => le_iSup 𝒜 j
      have haB : a ∈ B := hsub Z ha
      have hbB : b ∈ B := hsub Zᶜ hb
      exact Submodule.mem_sup.mpr ⟨⟨a, haB⟩, ha, ⟨b, hbB⟩, hb, Subtype.ext hab⟩
  let L : B →ₗ[O] K := ξ.toLinearMap ∘ₗ Submodule.projection P0 P1 hc
  have hform : ∀ j f (hf : f ∈ 𝒜 j),
      L ⟨f, mem_gradedSub 𝒜 hf⟩ = if p j = 0 then ξ ⟨f, mem_gradedSub 𝒜 hf⟩ else 0 := by
    intro j f hf
    split_ifs with hj
    · have hm : (⟨f, mem_gradedSub 𝒜 hf⟩ : B) ∈ P0 := (le_biSup 𝒜 (show j ∈ Z from hj)) hf
      show ξ (Submodule.projection P0 P1 hc ⟨f, mem_gradedSub 𝒜 hf⟩) = _
      rw [Submodule.projection_apply_of_mem_left hc hm]
    · have hm : (⟨f, mem_gradedSub 𝒜 hf⟩ : B) ∈ P1 := (le_biSup 𝒜 (show j ∈ Zᶜ from hj)) hf
      show ξ (Submodule.projection P0 P1 hc ⟨f, mem_gradedSub 𝒜 hf⟩) = _
      have h0 := Submodule.projection_apply_right hc ⟨_, hm⟩
      rw [h0, map_zero]
  have hmul_h : ∀ j k f g (hf : f ∈ 𝒜 j) (hg : g ∈ 𝒜 k),
      L (⟨f, mem_gradedSub 𝒜 hf⟩ * ⟨g, mem_gradedSub 𝒜 hg⟩) =
        L ⟨f, mem_gradedSub 𝒜 hf⟩ * L ⟨g, mem_gradedSub 𝒜 hg⟩ := by
    intro j k f g hf hg
    have hfg : f * g ∈ 𝒜 (j + k) := SetLike.GradedMul.mul_mem hf hg
    have e : (⟨f, mem_gradedSub 𝒜 hf⟩ * ⟨g, mem_gradedSub 𝒜 hg⟩ : B) = ⟨f * g, mem_gradedSub 𝒜 hfg⟩ := rfl
    have hm : ξ ⟨f * g, mem_gradedSub 𝒜 hfg⟩ = ξ ⟨f, mem_gradedSub 𝒜 hf⟩ * ξ ⟨g, mem_gradedSub 𝒜 hg⟩ := by
      rw [← map_mul]
      rfl
    have h1 := h j f hf
    have h2 := h k g hg
    rw [e, hform _ _ hfg, hform _ _ hf, hform _ _ hg, map_add p]
    by_cases hj : p j = 0 <;> by_cases hk : p k = 0
    · simp [hj, hk, hm]
    · have : p j + p k ≠ 0 := by omega
      simp [hj, hk, this]
    · have : p j + p k ≠ 0 := by omega
      simp [hj, hk, this]
    · by_cases hs : p j + p k = 0
      · simp only [hs, hj, hk, if_true, if_false, mul_zero, hm]
        rcases lt_or_gt_of_ne hj with hj' | hj'
        · rw [h1 hj', zero_mul]
        · rw [h2 (by omega), mul_zero]
      · simp [hs, hj, hk]
  have hmul : ∀ (x : S) (hx : x ∈ ⨆ j, 𝒜 j) (y : S) (hy : y ∈ ⨆ j, 𝒜 j),
      L ((⟨x, hx⟩ : B) * ⟨y, hy⟩) = L ⟨x, hx⟩ * L ⟨y, hy⟩ := by
    intro x hx y hy
    induction hx using Submodule.iSup_induction' with
    | mem j f hf =>
      induction hy using Submodule.iSup_induction' with
      | mem k g hg => exact hmul_h j k f g hf hg
      | zero =>
        change L ((⟨f, _⟩ : B) * 0) = L ⟨f, _⟩ * L 0
        simp
      | add a b ha hb iha ihb =>
        change L ((⟨f, _⟩ : B) * (⟨a, ha⟩ + ⟨b, hb⟩)) = L ⟨f, _⟩ * L (⟨a, ha⟩ + ⟨b, hb⟩)
        rw [mul_add, map_add (f := _), map_add (f := _), mul_add, iha, ihb]
    | zero =>
      change L ((0 : B) * ⟨y, hy⟩) = L 0 * L ⟨y, hy⟩
      simp
    | add a b ha hb iha ihb =>
      change L (((⟨a, ha⟩ : B) + ⟨b, hb⟩) * ⟨y, hy⟩) = L (⟨a, ha⟩ + ⟨b, hb⟩) * L ⟨y, hy⟩
      rw [add_mul, map_add (f := _), map_add (f := _), add_mul, iha, ihb]
  have hone : L 1 = 1 := by
    have h1 : (1 : S) ∈ 𝒜 0 := SetLike.GradedOne.one_mem
    have e : (1 : B) = ⟨1, mem_gradedSub 𝒜 h1⟩ := rfl
    rw [e, hform _ _ h1, if_pos (map_zero p)]
    rw [← e, map_one]
  refine ⟨AlgHom.ofLinearMap L hone (fun x y => hmul x.1 x.2 y.1 y.2), ?_⟩
  intro j f hf
  exact hform j f hf

private theorem vanish_mono {O S K H : Type} [CommRing O] [CommRing S] [Algebra O S] [CommRing K] [Algebra O K]
    [Group H] (A : Subalgebra O S) (r : H →* M4 S) (hr : ∀ g i j, r g i j ∈ A) (ξ : A →ₐ[O] K)
    (p : ℤ × ℤ →+ ℤ) (h : ∀ g i j, p (wt i j) < 0 → ξ ⟨r g i j, hr g i j⟩ = 0) (w : ℤ × ℤ) (hw : p w < 0)
    (f : S) (hf : f ∈ Submodule.span O (mono r w)) (hA : f ∈ A) : ξ ⟨f, hA⟩ = 0 := by
  have hmemA : ∀ L : List (H × Fin 4 × Fin 4), (L.map (fun a => r a.1 a.2.1 a.2.2)).prod ∈ A := by
    intro L
    induction L with
    | nil => simpa using A.one_mem
    | cons a L ih => simpa using A.mul_mem (hr a.1 a.2.1 a.2.2) ih
  have hξL : ∀ L : List (H × Fin 4 × Fin 4), ξ ⟨_, hmemA L⟩ =
      (L.map (fun a => ξ ⟨r a.1 a.2.1 a.2.2, hr a.1 a.2.1 a.2.2⟩)).prod := by
    intro L
    induction L with
    | nil =>
      have e : (⟨_, hmemA []⟩ : A) = 1 := Subtype.ext (by simp)
      rw [e, map_one]
      simp
    | cons a L ih =>
      have e : ξ ⟨_, hmemA (a :: L)⟩ = ξ ⟨r a.1 a.2.1 a.2.2, hr a.1 a.2.1 a.2.2⟩ * ξ ⟨_, hmemA L⟩ := by
        rw [← map_mul]
        apply congrArg ξ
        apply Subtype.ext
        simp
      rw [e, ih]
      simp
  have hspan : Submodule.span O (mono r w) ≤ Subalgebra.toSubmodule A := by
    rw [Submodule.span_le]
    rintro x ⟨L, -, rfl⟩
    exact hmemA L
  revert hA
  induction hf using Submodule.span_induction with
  | mem x hx =>
    intro hA
    obtain ⟨L, hL, rfl⟩ := hx
    refine (hξL L).trans ?_
    apply List.prod_eq_zero
    by_contra hne
    have hall : ∀ a ∈ L, 0 ≤ p (wt a.2.1 a.2.2) := by
      intro a ha
      by_contra hlt
      push_neg at hlt
      exact hne (List.mem_map.mpr ⟨a, ha, h a.1 a.2.1 a.2.2 hlt⟩)
    have hnn : 0 ≤ p w := by
      rw [← hL, map_list_sum, List.map_map]
      apply List.sum_nonneg
      intro x hx
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
      exact hall a ha
    omega
  | zero =>
    intro hA
    have e : (⟨0, hA⟩ : A) = 0 := rfl
    rw [e, map_zero]
  | add x y hx hy ihx ihy =>
    intro hA
    have e : (⟨x + y, hA⟩ : A) = ⟨x, hspan hx⟩ + ⟨y, hspan hy⟩ := rfl
    rw [e, map_add (f := _), ihx, ihy, add_zero]
  | smul a x hx ih =>
    intro hA
    have e : (⟨a • x, hA⟩ : A) = a • (⟨x, hspan hx⟩ : A) := rfl
    rw [e, map_smul, ih, smul_zero]

theorem UpperTheory.V.GradeZeroInterpolatingElement.ptLimit :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, D.Fin0 → ∀ ξ : M.SS →ₐ[c.O] PadicAlgCl l, ((∀ i j, lamW i < lamW j → ¬ Ge (M.rep ξ) i j) ∨ ∀ i j, lamW j < lamW i → ¬ Ge (M.rep ξ) i j) → ∃ ξ₀ : M.SS →ₐ[c.O] PadicAlgCl l, ∀ g i j, M.rep ξ₀ g i j = if lamW i = lamW j then M.rep ξ g i j else 0 := by
  intro Ω _ _ _ l _ c D hD M hF ξ hcase
  have hrep : ∀ (ζ : M.SS →ₐ[c.O] PadicAlgCl l) g i j,
      M.rep ζ g i j = ζ ⟨M.ru.hom g i j, M.sPart_le (M.entry_mem g i j)⟩ := by
    intro ζ g i j
    rfl
  obtain ⟨p, hp, hp0⟩ : ∃ p : ℤ × ℤ →+ ℤ, (∀ g i j, p (wt i j) < 0 → M.rep ξ g i j = 0) ∧
      ∀ i j, (p (wt i j) = 0 ↔ lamW i = lamW j) := by
    rcases hcase with hc | hc
    · refine ⟨AddMonoidHom.fst ℤ ℤ, ?_, ?_⟩
      · intro g i j hlt
        have h1 : lamW i < lamW j := by
          simp only [wt, AddMonoidHom.coe_fst] at hlt
          omega
        have := hc i j h1
        simp only [Ge, not_exists, not_not] at this
        exact this g
      · intro i j
        simp only [wt, AddMonoidHom.coe_fst]
        constructor <;> intro h <;> omega
    · refine ⟨-AddMonoidHom.fst ℤ ℤ, ?_, ?_⟩
      · intro g i j hlt
        have h1 : lamW j < lamW i := by
          simp only [wt, AddMonoidHom.neg_apply, AddMonoidHom.coe_fst] at hlt
          omega
        have := hc i j h1
        simp only [Ge, not_exists, not_not] at this
        exact this g
      · intro i j
        simp only [wt, AddMonoidHom.neg_apply, AddMonoidHom.coe_fst]
        constructor <;> intro h <;> omega
  obtain ⟨hI, -, -⟩ := sInternal D hD M
  have hvan : ∀ j f (hf : f ∈ M.sPart j), p j < 0 → ξ ⟨f, mem_gradedSub M.sPart hf⟩ = 0 := by
    intro j f hf hj
    have hf' : f ∈ Submodule.span c.O (mono M.ru.hom j) := by
      rw [← spanMono D hD M hF j]
      exact hf
    exact vanish_mono M.SS M.ru.hom (fun g i j => M.sPart_le (M.entry_mem g i j)) ξ p
      (fun g i j hlt => (hrep ξ g i j).symm.trans (hp g i j hlt)) j hj f hf' _
  obtain ⟨ξ₀, hξ₀⟩ : ∃ ξ₀ : M.SS →ₐ[c.O] PadicAlgCl l, ∀ j f (hf : f ∈ M.sPart j),
      ξ₀ ⟨f, M.sPart_le hf⟩ = if p j = 0 then ξ ⟨f, M.sPart_le hf⟩ else 0 :=
    limit_graded M.sPart hI ξ p hvan
  refine ⟨ξ₀, fun g i j => ?_⟩
  rw [hrep, hrep, hξ₀ (wt i j) _ (M.entry_mem g i j)]
  by_cases hij : lamW i = lamW j
  · rw [if_pos ((hp0 i j).mpr hij), if_pos hij]
  · rw [if_neg (fun h => hij ((hp0 i j).mp h)), if_neg hij]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SmoothPtWeightedPresentationOfPointDerivations
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem origin_part {O X B : Type} [CommRing O] [AddCommGroup X] [CommRing B] [Algebra O B]
    (W : WPres O X B) (h : W.HasOrigin) {j : X} (hj : j ≠ 0) {x : B} (hx : x ∈ W.part j) :
    W.origin h x = 0 := by
  obtain ⟨F, hF, rfl⟩ := hx
  refine (W.origin_π h F).trans ?_
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact hF 0 (by rw [map_zero]; exact hj.symm)

private theorem sep_char {O : Type} [CommRing O] (u : Oˣ) (hu : ¬ IsOfFinOrder u) {i j : ℤ × ℤ} (h : i ≠ j) :
    ∃ t : Multiplicative (ℤ × ℤ) →* Oˣ, t (Multiplicative.ofAdd i) ≠ t (Multiplicative.ofAdd j) := by
  have hinj := injective_zpow_iff_not_isOfFinOrder.2 hu
  by_cases h1 : i.1 = j.1
  · refine ⟨(zpowersHom Oˣ u).comp (AddMonoidHom.toMultiplicative (AddMonoidHom.snd ℤ ℤ)), fun e => h ?_⟩
    exact Prod.ext h1 (hinj e)
  · exact ⟨(zpowersHom Oˣ u).comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst ℤ ℤ)), fun e => h1 (hinj e)⟩

private theorem core {O B ι : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [CommRing B] [Algebra O B] [IsCO O B]
    [IsCO O (DualNumber O)] (u : Oˣ) (hu : ¬ IsOfFinOrder u)
    (W : WPres O (ℤ × ℤ) B) (h : W.HasOrigin) (e : ι → B) (w : ι → ℤ × ℤ) (he : ∀ a, e a ∈ W.part (w a))
    (huniq : ∀ f f' : B →ₐ[O] DualNumber O, (∀ a, f (e a) = f' (e a)) → f = f')
    (y : B →ₐ[O] DualNumber O) (j : ℤ × ℤ)
    (h1 : ∀ a, (y (e a)).fst = W.origin h (e a)) (h2 : ∀ a, w a ≠ j → (y (e a)).snd = 0) :
    (∀ x, (y x).fst = W.origin h x) ∧ ∀ i, i ≠ j → ∀ x ∈ W.part i, (y x).snd = 0 := by
  classical
  have hz : ∀ s, W.z s ∈ maximalIdeal B := by
    intro s
    by_contra hs
    have hu' : IsUnit (W.z s) := by
      rw [mem_maximalIdeal, mem_nonunits_iff, not_not] at hs
      exact hs
    have h0 : W.origin h (W.z s) = 0 := by
      rw [WPres.z, WPres.origin_π, MvPowerSeries.constantCoeff_X]
    have h3 := hu'.map (W.origin h)
    rw [h0] at h3
    exact not_isUnit_zero h3
  have hmul : ∀ (c : O) (d : DualNumber O), (algebraMap O (DualNumber O) c * d).fst = c * d.fst ∧
      (algebraMap O (DualNumber O) c * d).snd = c * d.snd := by
    intro c d
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact ⟨rfl, rfl⟩
  have hfst : ∀ x, (y x).fst = W.origin h x := by
    have key := huniq ((Algebra.ofId O (DualNumber O)).comp ((TrivSqZeroExt.fstHom O O O).comp y))
      ((Algebra.ofId O (DualNumber O)).comp (W.origin h)) (by
        intro a
        simp only [AlgHom.comp_apply, TrivSqZeroExt.fstHom_apply, h1 a])
    intro x
    have h4 := congrArg TrivSqZeroExt.fst (AlgHom.congr_fun key x)
    simpa [Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl] using h4
  refine ⟨hfst, ?_⟩
  intro i hij x hx
  obtain ⟨s, hs⟩ := sep_char u hu hij
  obtain ⟨y1, hy1, -⟩ := tact O (ℤ × ℤ) B W hz (DualNumber O) y
    ((Units.map (algebraMap O (DualNumber O)).toMonoidHom).comp s)
  have hy1' : ∀ k, ∀ z ∈ W.part k, (y1 z).fst = ↑(s (Multiplicative.ofAdd k)) * (y z).fst ∧
      (y1 z).snd = ↑(s (Multiplicative.ofAdd k)) * (y z).snd := by
    intro k z hz'
    rw [hy1 k z hz']
    exact hmul _ _
  set c : O := ↑(s (Multiplicative.ofAdd j))⁻¹ with hc
  let φ : DualNumber O →ₐ[O] DualNumber O := TrivSqZeroExt.map (c • LinearMap.id)
  have hφ : ∀ d : DualNumber O, (φ d).fst = d.fst ∧ (φ d).snd = c * d.snd := by
    intro d
    exact ⟨TrivSqZeroExt.fst_map _ _, TrivSqZeroExt.snd_map _ _⟩
  have hcj : c * ↑(s (Multiplicative.ofAdd j)) = 1 := Units.inv_mul _
  have heq : φ.comp y1 = y := by
    apply huniq
    intro a
    obtain ⟨ha1, ha2⟩ := hy1' (w a) (e a) (he a)
    obtain ⟨hb1, hb2⟩ := hφ (y1 (e a))
    rw [AlgHom.comp_apply]
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [hb1, ha1, hfst]
      by_cases hw : w a = 0
      · rw [hw, ofAdd_zero, map_one, Units.val_one, one_mul]
      · rw [origin_part W h hw (he a), mul_zero]
    · rw [hb2, ha2]
      by_cases hw : w a = j
      · rw [hw, ← mul_assoc, hcj, one_mul]
      · rw [h2 a hw, mul_zero, mul_zero]
  have hx1 := congrArg TrivSqZeroExt.snd (AlgHom.congr_fun heq x)
  rw [AlgHom.comp_apply, (hφ _).2, (hy1' i x hx).2, ← mul_assoc] at hx1
  have hne : c * ↑(s (Multiplicative.ofAdd i)) - 1 ≠ 0 := by
    intro h0
    apply hs
    apply Units.ext
    have h5 : c * ↑(s (Multiplicative.ofAdd i)) = c * ↑(s (Multiplicative.ofAdd j)) := by
      rw [hcj]
      exact sub_eq_zero.mp h0
    exact (Units.isUnit _).mul_left_cancel h5
  have h6 : (c * ↑(s (Multiplicative.ofAdd i)) - 1) * (y x).snd = 0 := by
    rw [sub_mul, one_mul, hx1, sub_self]
  exact (mul_eq_zero.mp h6).resolve_left hne

private theorem ex_unit (l : ℕ) [hl : Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] : ∃ u : Oˣ, ¬ IsOfFinOrder u := by
  obtain ⟨hinj, -, -, -, -, -, -, -, hunit⟩ := dvrFacts l O
  have hnd : ¬ l ∣ (l + 1) := by
    intro h
    have h' := (Nat.dvd_add_right (dvd_refl l)).mp h
    exact hl.out.one_lt.ne' (Nat.dvd_one.mp h')
  obtain ⟨u, hu⟩ := hunit (l + 1) hnd
  refine ⟨u, ?_⟩
  intro hfin
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
  haveI : CharZero O := charZero_of_injective_algebraMap hinj
  have h1 : ((l + 1 : ℕ) : O) ^ n = 1 := by
    rw [← hu, ← Units.val_pow_eq_pow_val, hpow, Units.val_one]
  have h2 : (((l + 1) ^ n : ℕ) : O) = ((1 : ℕ) : O) := by
    push_cast at h1 ⊢
    exact h1
  rcases Nat.pow_eq_one.mp (Nat.cast_injective h2) with h3 | h3
  · exact hl.out.ne_zero (by omega)
  · exact hn.ne' h3

theorem UpperTheory.smoothPt_weightedPresentation_of_pointDerivations :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (L : LocBase D) (y : L.B →ₐ[c.O] DualNumber c.O) (j : ℤ × ℤ), (∀ (v : D.T) (g : D.Gp v) (a b : Fin 4), (y ((L.ρ v).hom g a b)).fst = D.r0 g a b ∧ (wt a b ≠ j → (y ((L.ρ v).hom g a b)).snd = 0)) → (∀ x, (y x).fst = L.W.origin L.org x) ∧ ∀ i, i ≠ j → ∀ x ∈ L.W.part i, (y x).snd = 0 := by
  intro Ω _ _ _ l _ c D _ L y j H
  haveI := c.dvr
  obtain ⟨u, hu⟩ := ex_unit l c.O
  refine core u hu L.W L.org (ι := (v : D.T) × D.Gp v × Fin 4 × Fin 4)
    (fun a => (L.ρ a.1).hom a.2.1 a.2.2.1 a.2.2.2) (fun a => wt a.2.2.1 a.2.2.2) (fun a => L.hom _ _ _ _) ?_ y j
    (fun a => (H _ _ _ _).1.trans (L.at0 _ _ _ _).symm) (fun a => (H _ _ _ _).2)
  intro f f' hff
  obtain ⟨f0, -, hf0⟩ := L.univ (DualNumber c.O) (fun v => (L.ρ v).map f) (L.eqs.map f)
  refine (hf0 f fun _ => rfl).trans (hf0 f' fun v => ?_).symm
  exact Lift.ext (MonoidHom.ext fun g => Matrix.ext fun a b => (hff ⟨v, g, a, b⟩).symm)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ValProd
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem val_dvd {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {m n : ℕ} (h : m ∣ n)
    (hA : A.valuation (m : Ω) < 1) : A.valuation (n : Ω) < 1 := by
  obtain ⟨k, rfl⟩ := h
  rw [Nat.cast_mul, map_mul]
  have hk : A.valuation (k : Ω) ≤ 1 := by
    simpa using A.valuation_le_one (k : A)
  calc A.valuation (m : Ω) * A.valuation (k : Ω) ≤ A.valuation (m : Ω) * 1 := mul_le_mul' le_rfl hk
    _ < 1 := by rwa [mul_one]

private theorem val_prod {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (S : Finset ℕ)
    (hA : A.valuation ((∏ p ∈ S, p : ℕ) : Ω) < 1) : ∃ p ∈ S, A.valuation (p : Ω) < 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp at hA
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Nat.cast_mul, map_mul] at hA
    by_cases hp : A.valuation (a : Ω) < 1
    · exact ⟨a, Finset.mem_insert_self a S, hp⟩
    · have h1 : A.valuation (a : Ω) = 1 :=
        le_antisymm (by simpa using A.valuation_le_one (a : A)) (not_lt.mp hp)
      rw [h1, one_mul] at hA
      obtain ⟨p, hpS, hp'⟩ := ih hA
      exact ⟨p, Finset.mem_insert_of_mem hpS, hp'⟩

private theorem vlen_le (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l)
    (N : ℕ) [NeZero N] (e : ℕ) (he : e ≠ 0) (ψ : DirichletCharacter c.O N) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Vlen Ω c e ψ ≤ Chr.VS l (∏ p ∈ S, p) e (Chr.dirG ℚ Ω ψ) := by
  classical
  haveI := c.dvr
  haveI := c.fin
  have hcls := Chr.clsFacts ℚ Ω N
  have hker : (Chr.cls ℚ Ω N).ker ≤ (Chr.dirG ℚ Ω ψ).ker := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    simp [Chr.dirG, hg]
  have hopen : IsOpen ((Chr.dirG ℚ Ω ψ).ker : Set (G ℚ Ω)) := Subgroup.isOpen_mono hker hcls.1
  have hpow : Chr.dirG ℚ Ω ψ ^ (Fintype.card (ZMod N)ˣ) = 1 := by
    refine MonoidHom.ext fun g => ?_
    rw [MonoidHom.pow_apply, MonoidHom.one_apply, Chr.dirG, MonoidHom.comp_apply, ← map_pow,
      pow_card_eq_one, map_one]
  have hint : ∀ (A : ValuationSubring Ω) (x : Ω) (z : ℤ), A.valuation x < 1 →
      A.valuation (x * (z : Ω)) < 1 := by
    intro A x z hx
    rw [map_mul]
    have hz : A.valuation (z : Ω) ≤ 1 := by simpa using A.valuation_le_one (z : A)
    calc A.valuation x * A.valuation (z : Ω) ≤ A.valuation x * 1 := mul_le_mul' le_rfl hz
      _ < 1 := by rwa [mul_one]
  show Chr.VS l (l * N) e (Chr.dirG ℚ Ω ψ) ≤ Chr.VS l (∏ p ∈ S, p) e (Chr.dirG ℚ Ω ψ)
  unfold Chr.VS
  set_option synthInstance.maxHeartbeats 200000 in
   refine Module.length_le_of_injective (Submodule.inclusion ?_) (Submodule.inclusion_injective _)
  intro x hx
  simp only [Base.ShaU, Base.mem_locSel] at hx ⊢
  intro D hD
  rcases hD with ⟨A, hAS, rfl⟩ | ⟨A, rfl⟩
  · obtain ⟨p, hpS, hp⟩ := val_prod A S hAS
    by_cases hdvd : p ∣ l * N
    · exact hx (Dec A) (Or.inl ⟨A, val_dvd A hdvd hp, rfl⟩)
    · have pp := hS p hpS
      have hpl : p ≠ l := by
        rintro rfl
        exact hdvd (dvd_mul_right p N)
      have hpN : ¬ p ∣ N := fun h' => hdvd (dvd_mul_of_dvd_right h' l)
      have hN : ¬ A.valuation (N : Ω) < 1 := by
        intro hN
        have hcop : Nat.gcd p N = 1 := ((Nat.Prime.coprime_iff_not_dvd pp).2 hpN)
        have hb := Nat.gcd_eq_gcd_ab p N
        rw [hcop] at hb
        have h1 : (1 : Ω) = (p : Ω) * (Nat.gcdA p N : Ω) + (N : Ω) * (Nat.gcdB p N : Ω) := by
          have := congrArg (fun z : ℤ => (z : Ω)) hb
          push_cast at this
          exact this
        have hsum := Valuation.map_add_lt A.valuation (hint A _ (Nat.gcdA p N) hp)
          (hint A _ (Nat.gcdB p N) hN)
        rw [← h1, map_one] at hsum
        exact lt_irrefl _ hsum
      have hIne : Ine A ≤ (Chr.dirG ℚ Ω ψ).ker := le_trans (hcls.2.2.2.2 A hN) hker
      have hU : (⊤ : Subgroup (G ℚ Ω)) ⊓ Ine A ≤ ⊤ ⊓ Dec A := inf_le_inf_left _ (Ine_le_Dec A)
      have hinj := (Chr.locUnr Ω l c.O e (Fintype.card (ZMod N)ˣ) (Chr.dirG ℚ Ω ψ) he
        Fintype.card_ne_zero hopen hpow p A pp hpl hp (⊤ ⊓ Ine A) (⊤ ⊓ Dec A) hU
        (top_inf_eq _) (top_inf_eq _)).2 (inf_le_right.trans hIne)
      have h0 := hx (Ine A) (Or.inr ⟨A, rfl⟩)
      have h2 : Base.resU (Chr.rho l e (Chr.dirG ℚ Ω ψ)) hU
          (Base.resU (Chr.rho l e (Chr.dirG ℚ Ω ψ)) (inf_le_left : ⊤ ⊓ Dec A ≤ ⊤) x) = 0 := by
        rw [Base.resU_resU]
        exact h0
      exact hinj (h2.trans (map_zero _).symm)
  · exact hx (Ine A) (Or.inr ⟨A, rfl⟩)

theorem UpperTheory.V.GradeZeroInterpolatingElement.shaEq :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (h : Host) (t : ℕ), h.Big t → ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (e : ℕ), l ≠ 2 → 0 < e → e < t → ∀ ψ ∈ h.X c e, ∀ D : Raw Ω c, D.Good → Aut.OfCase D h e ψ → Vlen Ω c e ψ ≤ D.sha := by
  intro Ω _ _ _ h t _ l _ c e _ he _ ψ _ D hD hA
  have key : ∀ {n' p₁ m₀ : ℕ}, Aut.OfChar D e ψ n' p₁ m₀ → Vlen Ω c e ψ ≤ D.sha := by
    intro n' p₁ m₀ hc
    unfold Raw.sha
    rw [hc.e_eq, hc.psi]
    exact vlen_le Ω l c h.N e he.ne' ψ D.S hD.S_prime
  rcases hA with ⟨_, hc⟩ | ⟨_, hc⟩
  · exact key hc
  · exact key hc
end

