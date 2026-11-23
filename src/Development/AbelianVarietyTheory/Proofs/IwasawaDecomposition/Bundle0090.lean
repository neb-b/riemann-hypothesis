module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0027
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0078

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueGeneratorExtendDenseProOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.GenExtendDense

open GlobalTheory.GenericExtend GlobalTheory.DvrModel

theorem gm_eq_of_corr {X Y U HU H Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {I : Type} [Fintype I]
    {φ : I → (H ⟶ X)} {ε : I → ℤ} {jH : HU ⟶ H} {e : Y ⟶ H} {j : U ⟶ Y} {eU : U ⟶ HU}
    (heU : eU ≫ jH = j ≫ e)
    {t : LB.Gen (LB.LinComb L (fun i => jH ≫ φ i) ε)}
    {ρ : LB.Gen (LB.LinComb L (fun i => e ≫ φ i) ε)} (ht : t.IsGen) (hρ : ρ.IsGen)
    (hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eU) (LB.pullGen L _ _ ρ j))
    (κ : Z ⟶ U) (z : Z) (a : I → L.ι) (ha : e (j (κ z)) ∈ LB.wchart L φ a) :
    gm (κ ≫ eU) z (LB.wchart L (fun i => jH ≫ φ i) a) (t.s a) =
      gm (κ ≫ j) z (LB.wchart L (fun i => e ≫ φ i) a) (ρ.s a) := by
  choose Jg hJg using fun ψ : Z ⟶ X => exists_chart hL (ψ z)
  have hG : Good L z Jg := hJg
  have hv := val_corr hG hc κ
  rw [val_pull hG, val_pull hG] at hv
  have hw : ∀ k, (κ ≫ eU) ≫ jH ≫ φ k = (κ ≫ j) ≫ e ≫ φ k := fun k => by
    simp only [Category.assoc, reassoc_of% heU]
  let a' : I → L.ι := fun k => Jg ((κ ≫ eU) ≫ jH ≫ φ k)
  have ha' : a' = fun k => Jg ((κ ≫ j) ≫ e ≫ φ k) := funext fun k => congrArg Jg (hw k)
  rw [val_of t (κ ≫ eU) z Jg a' (fun k => rfl),
    val_of ρ (κ ≫ j) z Jg a' (fun k => by rw [ha'])] at hv
  have hpt : jH ((κ ≫ eU) z) = e ((κ ≫ j) z) := by
    rw [← Scheme.Hom.comp_apply, Category.assoc, heU, ← Category.assoc, Scheme.Hom.comp_apply]
  have h1 : (κ ≫ eU) z ∈ LB.wchart L (fun i => jH ≫ φ i) a :=
    (wchart_comp L jH φ a).ge (show jH ((κ ≫ eU) z) ∈ LB.wchart L φ a by rw [hpt]; exact ha)
  have h2 : (κ ≫ j) z ∈ LB.wchart L (fun i => e ≫ φ i) a := (wchart_comp L e φ a).ge ha
  have h1' : (κ ≫ eU) z ∈ LB.wchart L (fun i => jH ≫ φ i) a' := hG.mem (fun i => jH ≫ φ i) (κ ≫ eU)
  have h2' : (κ ≫ j) z ∈ LB.wchart L (fun i => e ≫ φ i) a' := by
    rw [ha']; exact hG.mem (fun i => e ≫ φ i) (κ ≫ j)
  have htr : trF (L := L) (fun i => jH ≫ φ i) ε (κ ≫ eU) z a a' =
      trF (L := L) (fun i => e ≫ φ i) ε (κ ≫ j) z a a' := by
    unfold trF
    refine Finset.prod_congr rfl fun k _ => ?_
    dsimp only
    rw [hw k]
  rw [gen_trans ht (κ ≫ eU) z h1 h1', gen_trans hρ (κ ≫ j) z h2 h2', htr, hv]

theorem existsUnique_gen_extend : ∀ (Y U H HU X : Scheme.{0}) [IsLocallyNoetherian Y] (j : U ⟶ Y) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j], Geo.Tor.IsNormalScheme Y → ∀ (p : H ⟶ Y) (e : Y ⟶ H) (jH : HU ⟶ H) (pU : HU ⟶ U) (eU : U ⟶ HU), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → IsPullback jH pU p j → eU ≫ jH = j ≫ e → ∀ (L : LB X), L.IsLB → ∀ (I : Type) [Fintype I] (φ : I → (H ⟶ X)) (ε : I → ℤ) (t : LB.Gen (LB.LinComb L (fun i => jH ≫ φ i) ε)) (ρ : LB.Gen (LB.LinComb L (fun i => e ≫ φ i) ε)), t.IsGen → ρ.IsGen → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eU) (LB.pullGen L _ _ ρ j) → ∃! c : LB.Gen (LB.LinComb L φ ε), c.IsGen ∧ LB.pullGen L _ _ c jH = t := by
  intro Y U H HU X _ j _ _ _ _ hY p e jH pU eU hsm hgi he hP heU L hL I _ φ ε t ρ ht hρ hc
  haveI := hsm
  haveI := hgi
  have := IsNormalScheme.of_pred hY
  have := isNormalScheme_of_smooth p
  have := LocallyOfFiniteType.isLocallyNoetherian p
  have := IsSchemeTheoreticallyDominant.of_isDominant j
  have hJ := (pullback.fst p j).app_injective
  have hN : (LB.LinComb L φ ε).IsLB := LB.isLB_linComb hL φ ε
  let iso := hP.isoPullback
  have hiso : iso.inv ≫ jH = pullback.fst p j := hP.isoPullback_inv_fst
  have hiso' : iso.hom ≫ pullback.fst p j = jH := hP.isoPullback_hom_fst
  have hisoa : ∀ {W : Scheme.{0}} (g : H ⟶ W), iso.inv ≫ jH ≫ g = pullback.fst p j ≫ g := fun g => by
    rw [← Category.assoc, hiso]
  have hpt : ∀ q, jH (iso.inv q) = pullback.fst p j q := fun q => by
    rw [← Scheme.Hom.comp_apply, hiso]
  have hle : ∀ a, pullback.fst p j ⁻¹ᵁ (LB.LinComb L φ ε).U a ≤
      iso.inv ⁻¹ᵁ LB.wchart L (fun i => jH ≫ φ i) a := fun a q hq =>
    (wchart_comp L jH φ a).ge (show jH (iso.inv q) ∈ LB.wchart L φ a by rw [hpt]; exact hq)
  let τ : ∀ a, Γ(pullback p j, pullback.fst p j ⁻¹ᵁ (LB.LinComb L φ ε).U a)ˣ :=
    fun a => res (hle a) (pullU iso.inv _ (t.s a))
  have hτg : ∀ (Z : Scheme.{0}) (r : Z ⟶ pullback p j) (z : Z) (a),
      pullback.fst p j (r z) ∈ (LB.LinComb L φ ε).U a →
      gm r z _ (τ a) = gm (r ≫ iso.inv) z (LB.wchart L (fun i => jH ≫ φ i) a) (t.s a) :=
    fun Z r z a h => (gm_res r z (hle a) h _).trans (gm_pull r iso.inv z _ (hle a h) _)
  have hτ : Compat (LB.LinComb L φ ε) (pullback.fst p j) τ := fun Z r z a b ha hb => by
    have ha' : (r ≫ iso.inv) z ∈ LB.wchart L (fun i => jH ≫ φ i) a := hle a ha
    have hb' : (r ≫ iso.inv) z ∈ LB.wchart L (fun i => jH ≫ φ i) b := hle b hb
    rw [hτg Z r z a ha, hτg Z r z b hb, gen_trans ht (r ≫ iso.inv) z ha' hb']
    refine congrArg (· * _) (Eq.symm ((gm_linComb L φ ε (r ≫ pullback.fst p j) z a b ha hb).trans ?_))
    rw [trF]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [Category.assoc, hisoa]
  have hle' : ∀ a, e ⁻¹ᵁ (LB.LinComb L φ ε).U a ≤ LB.wchart L (fun i => e ≫ φ i) a :=
    fun a => (wchart_comp L e φ a).ge
  let ρ' : ∀ a, Γ(Y, e ⁻¹ᵁ (LB.LinComb L φ ε).U a)ˣ := fun a => res (hle' a) (ρ.s a)
  let eU' : U ⟶ pullback p j := pullback.lift (j ≫ e) (𝟙 U) (by simp [he])
  have w : eU' ≫ pullback.fst p j = j ≫ e := pullback.lift_fst _ _ _
  have hπ : eU' ≫ pullback.snd p j = 𝟙 U := pullback.lift_snd _ _ _
  have hsec : eU ≫ pU = 𝟙 U := by
    rw [← cancel_mono j, Category.id_comp, Category.assoc, ← hP.w, reassoc_of% heU, he,
      Category.comp_id]
  have heU' : eU' ≫ iso.inv = eU := by
    rw [← cancel_mono iso.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply pullback.hom_ext
    · rw [w, Category.assoc, hiso', heU]
    · rw [hπ, Category.assoc, hP.isoPullback_hom_snd, hsec]
  have hτρ : ∀ (Z : Scheme.{0}) (κ : Z ⟶ U) (z : Z) (a : I → L.ι),
      e (j (κ z)) ∈ (LB.LinComb L φ ε).U a →
      gm (κ ≫ eU') z (pullback.fst p j ⁻¹ᵁ (LB.LinComb L φ ε).U a) (τ a) =
        gm (κ ≫ j) z (e ⁻¹ᵁ (LB.LinComb L φ ε).U a) (ρ' a) := by
    intro Z κ z a ha
    have hm : pullback.fst p j ((κ ≫ eU') z) ∈ (LB.LinComb L φ ε).U a := by
      rw [← Scheme.Hom.comp_apply, Category.assoc, w]; exact ha
    have e₁ : gm ((κ ≫ eU') ≫ iso.inv) z (LB.wchart L (fun i => jH ≫ φ i) a) (t.s a) =
        gm (κ ≫ eU) z (LB.wchart L (fun i => jH ≫ φ i) a) (t.s a) := by
      rw [Category.assoc, heU']
    exact (hτg Z _ z a hm).trans (e₁.trans ((gm_eq_of_corr hL heU ht hρ hc κ z a ha).trans
      (gm_res (κ ≫ j) z (hle' a) ha _).symm))
  have key : ∀ a, ∀ y ∈ (LB.LinComb L φ ε).U a, Order.coheight y ≤ 1 →
      y ∉ Set.range (pullback.fst p j) →
      ExtAt (pullback.fst p j) ((LB.LinComb L φ ε).U a) (τ a).val y ∧
        ExtAt (pullback.fst p j) ((LB.LinComb L φ ε).U a) ((τ a)⁻¹).val y := fun a y ha h1 hy ↦ by
    refine extAt_of_coheight_eq_one j p he hN w hπ hτ hτρ y
      (le_antisymm (coheight_apply_le_one p h1) (ENat.one_le_iff_ne_zero.2 fun h0 ↦ hy ?_)) a ha
    rw [Scheme.Pullback.range_fst]
    obtain ⟨ξ, hξ, hξy⟩ := exists_specializes_mem_range j (p y)
    exact (Flat.generalizingMap j).stableUnderGeneralization_range
      (show p y ⤳ ξ from Order.coheight_eq_zero.1 h0 hξy) hξ
  choose s hs using fun a ↦ exists_app_eq _ hJ _ _ fun y ha h1 hy ↦ (key a y ha h1 hy).1
  choose s' hs' using fun a ↦ exists_app_eq _ hJ _ _ fun y ha h1 hy ↦ (key a y ha h1 hy).2
  have hm : ∀ a, s a * s' a = 1 := fun a ↦ hJ _ (by
    change ((pullback.fst p j).app _).hom _ = ((pullback.fst p j).app _).hom _
    rw [map_mul, map_one, hs, hs', Units.mul_inv])
  let σ : ∀ a, Γ(H, (LB.LinComb L φ ε).U a)ˣ := fun a ↦ ⟨s a, s' a, hm a, (mul_comm _ _).trans (hm a)⟩
  have hσ : ∀ a, pullU (pullback.fst p j) _ (σ a) = τ a := fun a ↦ Units.ext (hs a)
  have hgen : (⟨σ⟩ : LB.Gen (LB.LinComb L φ ε)).IsGen := fun a b ↦ Units.map_injective
      (f := ((pullback.fst p j).app ((LB.LinComb L φ ε).U a ⊓ (LB.LinComb L φ ε).U b)).hom.toMonoidHom)
      (hJ _) (by
    change pullU _ _ _ = pullU _ _ _
    refine unit_ext fun q hq ↦ ?_
    have := hτ _ (𝟙 _) q a b hq.1 hq.2
    rw [← hσ, ← hσ, gm_pull _ _ q _ hq.1, gm_pull _ _ q _ hq.2] at this
    rw [gm_pull _ _ q _ hq, gm_pull _ _ q _ hq, map_mul, gm_res _ q _ hq, gm_res _ q _ hq]
    exact this)
  have hτc : ∀ c : LB.Gen (LB.LinComb L φ ε), LB.pullGen L _ _ c jH = t → ∀ a,
      pullU (pullback.fst p j) _ (c.s a) = τ a := by
    rintro c rfl a
    refine unit_ext fun q hq ↦ ?_
    rw [gm_pull _ _ q _ hq, hτg _ (𝟙 _) q a hq]
    simp only [Category.id_comp]
    dsimp only [LB.pullGen]
    have h₁ : iso.inv q ∈ LB.wchart L (fun i => jH ≫ φ i) a := hle a hq
    have h₂ : jH (iso.inv q) ∈ LB.wchart L φ a := by rw [hpt]; exact hq
    exact ((gm_res iso.inv q _ h₁ _).trans ((gm_pull iso.inv jH q _ h₂ _).trans (congrArg (fun f => gm f q _ (c.s a)) hiso))).symm
  have hpg : LB.pullGen L _ _ (⟨σ⟩ : LB.Gen (LB.LinComb L φ ε)) jH = t := by
    refine congrArg LB.Gen.mk (funext fun a ↦ unit_ext fun y hy ↦ ?_)
    have hy' : jH y ∈ (LB.LinComb L φ ε).U a := (wchart_comp L jH φ a).le hy
    have h' : pullback.fst p j (iso.hom y) ∈ (LB.LinComb L φ ε).U a := by
      rw [← Scheme.Hom.comp_apply, hiso']; exact hy'
    have e₁ : gm jH y ((LB.LinComb L φ ε).U a) (σ a) =
        gm (𝟙 HU) y (LB.wchart L (fun i => jH ≫ φ i) a) (t.s a) := by
      refine (congrArg (fun f => gm f y ((LB.LinComb L φ ε).U a) (σ a)) hiso'.symm).trans
        ((gm_pull iso.hom _ y _ h' _).symm.trans ?_)
      rw [hσ]
      exact (hτg _ iso.hom y a h').trans (by rw [Iso.hom_inv_id])
    refine Eq.trans ?_ e₁
    dsimp only [LB.pullGen]
    rw [gm_res _ y _ hy, gm_pull _ _ y _ hy', Category.id_comp]
  refine ⟨⟨σ⟩, ⟨hgen, hpg⟩, ?_⟩
  rintro ⟨c⟩ ⟨-, hc'⟩
  refine congrArg LB.Gen.mk (funext fun a ↦ Units.map_injective
    (f := ((pullback.fst p j).app ((LB.LinComb L φ ε).U a)).hom.toMonoidHom) (hJ _) ?_)
  exact (hτc ⟨c⟩ hc' a).trans (hσ a).symm

end GlobalTheory.GenExtendDense
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulVecMemConjSmulOfAdjoint
section
open Formalism.MainNotions.S GlobalTheory.RowLev GlobalTheory.RowLev.Inhab NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Pointwise Classical

namespace GlobalTheory.Mem.RowsBundle

theorem exists_conj_involution (I : AutInst) :
    ∃ cj : HeightOneSpectrum (𝓞 I.E) → HeightOneSpectrum (𝓞 I.E), (∀ v, cj (cj v) = v) ∧
      (∀ v v', IsConj I v v' ↔ v' = cj v) ∧
      ∀ (m : ℕ) (v : HeightOneSpectrum (𝓞 I.E)), (m : 𝓞 I.E) ∈ v.asIdeal → (m : 𝓞 I.E) ∈ (cj v).asIdeal := by
  let st : 𝓞 I.E →+* 𝓞 I.E := RingOfIntegers.mapRingHom (starRingEnd I.E)
  have hst : ∀ a : 𝓞 I.E, (st a : I.E) = star (a : I.E) := fun a => rfl
  have hst2 : ∀ a, st (st a) = a := fun a => RingOfIntegers.ext (by rw [hst, hst, star_star])
  have hsurj : Function.Surjective st := fun a => ⟨st a, hst2 a⟩
  let cj : HeightOneSpectrum (𝓞 I.E) → HeightOneSpectrum (𝓞 I.E) := fun v => v.comap st hsurj
  have hcj : ∀ v a, a ∈ (cj v).asIdeal ↔ st a ∈ v.asIdeal := fun v a => Iff.rfl
  refine ⟨cj, fun v => HeightOneSpectrum.ext (Ideal.ext fun a => by rw [hcj, hcj, hst2]), fun v v' => ?_,
    fun m v hv => by rw [hcj, map_natCast]; exact hv⟩
  constructor
  · intro h
    refine HeightOneSpectrum.ext (Ideal.ext fun b => ?_)
    rw [hcj]
    exact (h (st b) b (by rw [hst, star_star])).symm
  · rintro rfl a b hab
    have : b = st a := RingOfIntegers.ext hab
    subst this
    rw [hcj, hst2]

theorem meets_iff_card {X P : Type} (cj : X → X) (hc : ∀ v, cj (cj v) = v) (S : Set X) (hS : ∀ v ∈ S, cj v ∈ S)
    {m : ℕ} (hm : 0 < m) (hcard : S.ncard = 2 * m) (w : P → X) (hw : ∀ v, w v ∈ S) (hinj : Function.Injective w)
    (hn : ∀ v v', w v' ≠ cj (w v)) : (∀ u ∈ S, ∃ v, u = w v ∨ u = cj (w v)) ↔ Nat.card P = m := by
  let f : P ⊕ P → S := Sum.elim (fun v => ⟨w v, hw v⟩) (fun v => ⟨cj (w v), hS _ (hw v)⟩)
  have hf : Function.Injective f := by
    rintro (a | a) (b | b) h
    · exact congrArg _ (hinj (congrArg Subtype.val h))
    · exact absurd (congrArg Subtype.val h) (hn _ _)
    · exact absurd (congrArg Subtype.val h).symm (hn _ _)
    · have h' : cj (w a) = cj (w b) := congrArg Subtype.val h
      exact congrArg _ (hinj (by rw [← hc (w a), h', hc]))
  have hS' : Nat.card S = 2 * m := hcard
  haveI : Finite S := Nat.finite_of_card_ne_zero (by omega)
  haveI : Finite P := Finite.of_injective _ (hf.comp Sum.inl_injective)
  have hP : Nat.card (P ⊕ P) = Nat.card P + Nat.card P := Nat.card_sum
  constructor
  · intro h
    have hs : Function.Surjective f := fun u => by
      obtain ⟨v, e | e⟩ := h u.1 u.2
      · exact ⟨Sum.inl v, Subtype.ext e.symm⟩
      · exact ⟨Sum.inr v, Subtype.ext e.symm⟩
    have := Nat.card_eq_of_bijective f ⟨hf, hs⟩
    omega
  · intro h u hu
    have hb := (Nat.bijective_iff_injective_and_card f).2 ⟨hf, by omega⟩
    obtain ⟨v | v, e⟩ := hb.2 ⟨u, hu⟩
    · exact ⟨v, Or.inl (congrArg Subtype.val e).symm⟩
    · exact ⟨v, Or.inr (congrArg Subtype.val e).symm⟩

theorem isChoice_of_card (I : AutInst) (g : Fin 2 → ℕ) (hg : ∀ k, (g k).Prime) (hne : g 0 ≠ g 1)
    (hsp : ∀ k (v : HeightOneSpectrum (𝓞 I.E)), ((g k : ℕ) : 𝓞 I.E) ∈ v.asIdeal →
      Ideal.absNorm v.asIdeal = g k ∧ ((g k : ℕ) : 𝓞 I.E) ∉ v.asIdeal ^ 2 ∧ ¬ IsConj I v v)
    {m : ℕ} (hm : 0 < m)
    (hcard : ∀ k, {v : HeightOneSpectrum (𝓞 I.E) | ((g k : ℕ) : 𝓞 I.E) ∈ v.asIdeal}.ncard = 2 * m) :
    (∃ w : ∀ _ : Fin 2, Fin m → HeightOneSpectrum (𝓞 I.E), IsChoice I g (fun _ => Fin m) w) ∧
      ∀ (Pl : Fin 2 → Type) [∀ k, Fintype (Pl k)] (w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)),
        (∀ k, Fintype.card (Pl k) = m) → (∀ k v, ((g k : ℕ) : 𝓞 I.E) ∈ (w k v).asIdeal) →
        (∀ k, Function.Injective (w k)) → (∀ k v v', ¬ IsConj I (w k v) (w k v')) → IsChoice I g Pl w := by
  obtain ⟨cj, hc, hconj, hmem⟩ := exists_conj_involution I
  obtain ⟨Pl₀, w₀, -, h₀⟩ := exists_choice I g hg hne hsp
  have key : ∀ (Pl : Fin 2 → Type) [∀ k, Fintype (Pl k)] (w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)),
      (∀ k, Fintype.card (Pl k) = m) → (∀ k v, ((g k : ℕ) : 𝓞 I.E) ∈ (w k v).asIdeal) →
      (∀ k, Function.Injective (w k)) → (∀ k v v', ¬ IsConj I (w k v) (w k v')) → IsChoice I g Pl w := by
    intro Pl _ w h1 h2 h3 h4
    refine ⟨hg, hne, h₀.2.2.1, fun k v => ⟨h2 k v, (hsp k _ (h2 k v)).1⟩, h3, h4, fun k u hu => ?_⟩
    simp only [hconj] at h4 ⊢
    exact (meets_iff_card cj hc _ (hmem (g k)) hm (hcard k) (w k) (h2 k) (h3 k) (h4 k)).2
      (by rw [Nat.card_eq_fintype_card, h1]) u hu
  refine ⟨?_, key⟩
  obtain ⟨-, -, -, h2, h3, h4, h5⟩ := h₀
  have hP : ∀ k, Nat.card (Pl₀ k) = m := fun k => by
    simp only [hconj] at h4 h5
    exact (meets_iff_card cj hc _ (hmem (g k)) hm (hcard k) (w₀ k) (fun v => (h2 k v).1) (h3 k) (h4 k)).1 (h5 k)
  have e : ∀ k, Fin m ≃ Pl₀ k := fun k =>
    haveI : Finite (Pl₀ k) := Nat.finite_of_card_ne_zero (by rw [hP]; omega)
    (Finite.equivFinOfCardEq (hP k)).symm
  exact ⟨fun k v => w₀ k (e k v), key _ _ (fun _ => Fintype.card_fin m) (fun k v => (h2 k _).1)
    (fun k => (h3 k).comp (e k).injective) fun k v v' => h4 k _ _⟩

section Unip

variable {I : AutInst}

theorem hAf_eq_dot (u v : Fin I.n → I.E ⊗[I.F] Af I.F) : hAf I u v =
    (fun i => sigR I.cm.sig (Af I.F) (u i)) ⬝ᵥ (I.J.map (inclE (F := I.F) (Af I.F)) *ᵥ v) := by
  simp only [hAf, hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hAf_inv_mulVec (x : I.Gf) (y z : Fin I.n → I.E ⊗[I.F] Af I.F) :
    hAf I (I.fmat x⁻¹ *ᵥ y) z = hAf I y (I.fmat x *ᵥ z) := by
  have hx : cT (sigR I.cm.sig (Af I.F)) (I.fmat x⁻¹) * I.J.map (inclE (F := I.F) (Af I.F)) * I.fmat x⁻¹ = _ := x⁻¹.2
  have hs : (fun i => sigR I.cm.sig (Af I.F) ((I.fmat x⁻¹ *ᵥ y) i)) =
      (fun i => sigR I.cm.sig (Af I.F) (y i)) ᵥ* cT (sigR I.cm.sig (Af I.F)) (I.fmat x⁻¹) := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, Matrix.vecMul, dotProduct, cT, map_sum, mul_comm]
  have h1 : I.fmat x⁻¹ * I.fmat x = 1 := by rw [← fmat_mul, inv_mul_cancel, fmat_one]
  rw [hAf_eq_dot, hAf_eq_dot, hs, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  conv_rhs => rw [← hx, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem hAf_pow_adjoint (x : I.Gf) (m : ℕ) (y z : Fin I.n → I.E ⊗[I.F] Af I.F) :
    hAf I ((I.fmat x⁻¹ - 1) ^ m *ᵥ y) z = hAf I y ((I.fmat x - 1) ^ m *ᵥ z) := by
  induction m generalizing z with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', pow_succ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← ih, Matrix.sub_mulVec,
      Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec]
    generalize (I.fmat x⁻¹ - 1) ^ m *ᵥ y = u
    have h := hAf_inv_mulVec x u z
    simp only [hAf, hform, Pi.sub_apply, map_sub, sub_mul, mul_sub, Finset.sum_sub_distrib] at h ⊢
    rw [h]

theorem sub_one_pow_mem {x : I.Gf} (hx : x ∈ I.Kset) (m : ℕ) {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ I.Lf) :
    (I.fmat x - 1) ^ m *ᵥ y ∈ I.Lf := by
  induction m with
  | zero => simpa using hy
  | succ m ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
    exact sub_mem (mulVec_mem hx ih) ih

end Unip

end GlobalTheory.Mem.RowsBundle
end

