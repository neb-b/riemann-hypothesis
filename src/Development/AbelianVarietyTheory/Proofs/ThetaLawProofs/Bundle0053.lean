module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
public import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAbelianSchemeThick
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0034

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsNumberFieldPointSiegelFamilyKnownValue
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam
open GlobalTheory.ZM.SiegPull

theorem polPB_of_keyPB_alg {R R' : Type} [CommRing R] [CommRing R'] {x' : KeyIn R'} {x : KeyIn R} {f : R →+* R'}
    (H : KeyPB x' x f) : ∃ φ, PolPB x'.P x.P (spMap f) φ := by
  obtain ⟨φ, -, w, hg, -, hp, hw, -⟩ := H
  exact ⟨φ, hp, hg, w, hw⟩

theorem Known.of_keyPB {K K' : Type} [Field K] [Field K'] {y' : KeyIn K'} {y : KeyIn K} {f : K →+* K'}
    (H : KeyPB y' y f) (h : Known K y) : Known K' y' := by
  obtain ⟨t, ht⟩ := h
  exact ⟨f t, fun e x hx => ht (e.comp f) x (keyPB_trans _ _ _ _ _ _ _ _ H hx)⟩

theorem exists_secHom_field (hL : Out.Laws) {K k : Type} [Field K] [Field k] {β : K →+* k} {Q : Out.PolAV (Sp K)}
    {Q' : Out.PolAV (Sp k)} {ψ : Q'.A.left ⟶ Q.A.left} (H : PolPB Q' Q (spMap β) ψ) :
    ∃ ρ : (𝟙_ (Over (Sp K)) ⟶ Q.A) →* (𝟙_ (Over (Sp k)) ⟶ Q'.A), Function.Injective ρ ∧
      (∀ x, (ρ x).left ≫ ψ = spMap β ≫ x.left) ∧
      ∀ (n : ℕ) x y (u : Kˣ), x ^ n = 1 → y ^ n = 1 →
        Out.WeilIs Q'.A Q'.L n (ρ x) (ρ y) (unitOn (Units.map β.toMonoidHom u)) →
        Out.WeilIs Q.A Q.L n x y (unitOn u) := by
  have := Q.isAb.comm
  obtain ⟨b, hb⟩ := UnifPoint.exists_pointEquiv H.1
  let e : Over.mk (spMap β) ⟶ 𝟙_ (Over (Sp K)) := Over.homMk (spMap β) (Category.comp_id _)
  let r : (𝟙_ (Over (Sp K)) ⟶ Q.A) →* (Over.mk (spMap β) ⟶ Q.A) :=
    MonoidHom.mk' (fun x => e ≫ x) fun x y => MonObj.comp_mul _ _ _
  have hρ : ∀ x, (b.symm (r x)).left ≫ ψ = spMap β ≫ x.left := fun x => by
    rw [← hb, b.apply_symm_apply]; rfl
  refine ⟨b.symm.toMonoidHom.comp r, b.symm.injective.comp fun x y hxy => ?_, hρ, fun n x y u hx hy hw => ?_⟩
  · have : Epi e.left := TorsionSeparable.epi_specMap β
    have : Epi e := Over.epi_of_epi_left _
    exact (cancel_epi e).1 hxy
  · obtain ⟨c, hc, -⟩ := (hL.weil _ Q n _).1 x y hx hy
    have h₁ := CommPairing.weilIs_pull hL.globalFns Q.isAb Q.isLB e hc
    have h₂ := (weilIs_grpPullback_of_comm _ _ Q.A Q'.A _ ψ Q.L Q'.L Q.isLB Q'.isLB H.1 H.2.2 _ n _ _
      (pushPt H.1.1.w _) (pushPt H.1.1.w _) _ rfl rfl).1 hw
    have h₃ : Out.WeilIs Q.A Q.L n (e ≫ x) (e ≫ y) (unitOn (Units.map β.toMonoidHom u)) :=
      UnifPoint.weilIs_congr (Category.id_comp _) (hρ x) (hρ y) h₂
    have h₄ := CommutatorPairing.weilIs_unique hL.globalFns Q.isAb Q.isLB h₁ h₃
    obtain ⟨v, rfl⟩ : ∃ v : Kˣ, unitOn v = c :=
      ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.toMonoidHom c,
        Units.ext (CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of K)) c.val)⟩
    have e' : Units.map e.left.appTop.hom.toMonoidHom (unitOn v) = unitOn (Units.map β.toMonoidHom v) :=
      Units.ext (congrArg (fun q => q.hom v.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm
    have h₅ := congrArg Units.val (TorsionGenerators.unitOn_injective (e'.symm.trans h₄))
    obtain rfl : v = u := Units.ext (β.injective h₅)
    exact hc

theorem sqOf_of_iso_of_siegPB {h k : ℕ} {o o' : Type} [CommRing o] [CommRing o'] {ζ : o} {ζ' : o'} {S S' : Scheme.{0}}
    {s : S ⟶ Sp o} {s' : S' ⟶ Sp o'} {c : SiegPre h k ζ s} {c' : SiegPre h k ζ' s'} {f : S' ⟶ S}
    (H : SiegPB c' c f) {P : Out.PolAV S'} (hg : P.g = h) (e : c'.A ≅ P.A) [IsMonHom e.hom]
    (hP : LBIso c'.P ((abelian₂ P.A P.L).pull (lift (fst c'.A c'.A ≫ e.hom) (snd c'.A c'.A ≫ e.hom)).left)) :
    ∃ φ, SqOf P c f φ ∧ ∀ a, (c'.lev a ≫ e.hom).left ≫ φ = f ≫ (c.lev a).left := by
  obtain ⟨φ, φ₂, gp, sq, iP, hlev⟩ := H
  have hinv : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  have hΛ : (abelian₂ P.A P.L).IsLB := DVR.linComb_isLB _ P.isLB _ _
  refine ⟨e.inv.left ≫ φ, ⟨((isGrpPullback_of_iso e.symm).comp gp).congr (Category.id_comp _) rfl, hg,
    (e.inv ⊗ₘ e.inv).left ≫ φ₂, isSquare_comp (isSquare_tensor e.inv) sq, ?_⟩, fun a => ?_⟩
  · have k₁ := GlobalTheory.ZM.SiegPull.lbIso_pull_comp hP (e.inv ⊗ₘ e.inv).left
    have k₂ := GlobalTheory.ZM.SiegPull.lbIso_pull_comp iP (e.inv ⊗ₘ e.inv).left
    have k₃ : (e.inv ⊗ₘ e.inv).left ≫ (lift (fst c'.A c'.A ≫ e.hom) (snd c'.A c'.A ≫ e.hom)).left = 𝟙 _ := by
      rw [← Over.comp_left, ← Over.id_left]
      congr 1
      ext1 <;> simp
    rw [k₃] at k₁
    exact LBIso.trans hΛ (pull_isLB c'.isLB _) (pull_isLB c.isLB _)
      (LBIso.trans (pull_isLB c'.isLB _) (pull_isLB hΛ _) hΛ k₁ (GlobalTheory.lbIso_pull_id hΛ)).symm k₂
  · rw [← hlev, ← Category.assoc, ← Over.comp_left, Category.assoc, e.hom_inv_id, Category.comp_id]

theorem PerLev.level {P : Out.PolAV (Sp ℂ)} {g k : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ}
    {lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)} (H : PerLev P τ k lev) (hk : 0 < k) :
    (∀ a b, lev (a + b) = lev a * lev b) ∧ (∀ a, lev a ^ k = 1) ∧
      ∀ z : ℂˣ, (z : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) / k) → ∀ a b,
        Out.WeilIs P.A P.L k (lev a) (lev b) (unitOn (z ^ omegaStd a b)) := by
  obtain ⟨-, -, -, u, hΛ, hw, hl⟩ := H
  have h0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  refine ⟨fun a b => by rw [hl, hl, hl, per_add, smul_add, u.ex_add], fun a => ?_, fun z hz a b => ?_⟩
  · have hp : ∀ (z) (m : ℕ), u.ex (m • z) = u.ex z ^ m := fun z m => by
      induction m with
      | zero => rw [zero_smul, pow_zero]; exact (u.ker 0).2 (zero_mem _)
      | succ m ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]
    rw [hl, ← hp, ← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ h0]
    exact (u.ker _).2 ((hΛ _).2 ⟨a, rfl⟩)
  · rw [hl, hl]
    refine hw k a b _ hk ?_
    rw [Units.val_zpow_eq_zpow_val, hz, ← Complex.exp_int_mul]
    congr 1
    ring

theorem exists_known_point : Out.Laws → ThetaUnifAV → ∀ (h k : ℕ) (K : Type) [Field K] (ζ : K) (σ : K →+* ℂ) (F : SFam h k ζ), 1 ≤ h → 3 ≤ k → Odd k → σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k) → NumberField K → ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (j : K →+* K₁) (σ₁ : K₁ →+* ℂ) (y : KeyIn K₁) (q : Sp K₁ ⟶ F.X) (φ : y.P.A.left ⟶ F.univ.A.left) (τ : Matrix (Fin h) (Fin h) ℂ), σ₁.comp j = σ ∧ q ≫ F.s = spMap j ∧ Known K₁ y ∧ SqOf y.P F.univ q φ ∧ PtAt F.univ (spMap σ₁ ≫ q) τ := by
  intro hL hT h k K _ ζ σ F hh hk _ hζ hK
  have hk0 : 0 < k := by omega
  obtain ⟨y₀, hg₀, hy₀⟩ := _root_.GlobalTheory.KeyFam.exists_known_rat hL hT h hh
  let k₀ : IntermediateField ℚ ℂ := σ.toRatAlgHom.fieldRange
  have : FiniteDimensional ℚ k₀ :=
    Module.Finite.of_surjective σ.toRatAlgHom.rangeRestrict.toLinearMap σ.toRatAlgHom.rangeRestrict_surjective
  obtain ⟨y₁, H₁⟩ := exists_keyPB_ring y₀ (algebraMap ℚ k₀)
  obtain ⟨k₁, fin₁, le₁, tors⟩ := exists_numberField_torsion_points hL k₀ y₁.P k hk0
  have : NumberField k₁ := ⟨⟩
  obtain ⟨y, H⟩ := exists_keyPB_ring y₁ (IntermediateField.inclusion le₁).toRingHom
  obtain ⟨x, Hx⟩ := exists_keyPB_ring y (algebraMap k₁ ℂ)
  obtain ⟨φ₀, p₀⟩ := polPB_of_keyPB_alg H₁
  obtain ⟨φ₁, p₁⟩ := polPB_of_keyPB_alg H
  obtain ⟨ψ, pψ⟩ := polPB_of_keyPB_alg Hx
  have hg : y.P.g = h := p₁.2.1.trans (p₀.2.1.trans hg₀)
  obtain ⟨τ, lev, hlev⟩ := exists_perLev hT x.P h k (pψ.2.1.trans hg)
  obtain ⟨ladd, ltors, lweil⟩ := hlev.level hk0
  obtain ⟨ρ, ρinj, hρ, ρw⟩ := exists_secHom_field hL pψ
  have es : spMap (algebraMap k₁ ℂ) ≫ spMap (IntermediateField.inclusion le₁).toRingHom = spMap (algebraMap k₀ ℂ) :=
    (spMap_comp _ _).symm
  obtain ⟨b, hb⟩ := UnifPoint.exists_pointEquiv ((pψ.1.comp p₁.1).congr es rfl)
  obtain ⟨b₁, hb₁⟩ := UnifPoint.exists_pointEquiv p₁.1
  have desc : ∀ a, ∃ t, ρ t = lev a := fun a => by
    obtain ⟨x₂, hx₂, -⟩ := tors k₁ le₁ le_rfl (b (lev a)) (by rw [← map_pow, ltors, map_one])
    refine ⟨b₁.symm x₂, b.injective (Over.OverMorphism.ext ?_)⟩
    rw [← hx₂, hb, ← Category.assoc, hρ, Category.assoc, ← hb₁, b₁.apply_symm_apply]
  choose t ht using desc
  let j : K →+* k₁ := σ.codRestrict k₁.toSubfield fun a => le₁ ⟨a, rfl⟩
  have hj : (algebraMap k₁ ℂ).comp j = σ := rfl
  have hprim : IsPrimitiveRoot (σ ζ) k := by
    rw [hζ, neg_div, Complex.exp_neg]
    exact (Complex.isPrimitiveRoot_exp k hk0.ne').inv
  have hprim₁ : IsPrimitiveRoot (j ζ) k :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap k₁ ℂ) hprim (algebraMap k₁ ℂ).injective
  let ze : k₁ˣ := Units.mk0 (j ζ) (hprim₁.ne_zero hk0.ne')
  have ttors : ∀ a, t a ^ k = 1 := fun a => ρinj (by rw [map_pow, ht, ltors, map_one])
  obtain ⟨c, e, he, pr, iP, hc⟩ := exists_siegPre_of_polAV hL Moduli.cube_of_isLB K k₁ j h k ζ ze y.P t hg
    (Nat.cast_ne_zero.2 hk0.ne') rfl (IsPrimitiveRoot.coe_units_iff.1 hprim₁)
    (fun a a' => ρinj (by rw [map_mul, ht, ht, ht, ladd])) ttors fun a a' =>
      ρw k _ _ _ (ttors a) (ttors a') (by
        rw [ht, ht, map_zpow]
        exact lweil _ hζ a a')
  obtain ⟨q, hq, pb⟩ := F.rep _ _ c inferInstance (fun z => subset_closure (by
    show ((spMap j) z).asIdeal = ⊥
    exact congrArg PrimeSpectrum.asIdeal (Subsingleton.elim (α := PrimeSpectrum K) _ ⊥))) pr
  obtain ⟨φ, sq, hφ⟩ := sqOf_of_iso_of_siegPB pb hg e iP
  refine ⟨k₁, inferInstance, inferInstance, j, algebraMap k₁ ℂ, y, q, φ, τ, hj, hq,
    (hy₀.of_keyPB H₁).of_keyPB H, sq, x.P, lev, ψ ≫ φ, hlev,
    (sqOf_calculus h k K ζ _ _ _ _ F.univ q).1 _ _ _ _ _ sq pψ, fun a => ?_⟩
  rw [← ht, ← Category.assoc, hρ, Category.assoc, Category.assoc, ← hφ, hc]

end GlobalTheory.KeyFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPointOfPerLev
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.KeyFam

theorem sqOf_of_siegPB {h k : ℕ} {o o' : Type} [CommRing o] [CommRing o'] {ζ : o} {ζ' : o'} {S S' : Scheme.{0}}
    {s : S ⟶ Sp o} {s' : S' ⟶ Sp o'} (P : Out.PolAV S') (c : SiegPre h k ζ s) (c' : SiegPre h k ζ' s') (f : S' ⟶ S)
    (e : c'.A ≅ P.A) [IsMonHom e.hom] (hg : P.g = h)
    (hw : LBIso c'.P ((abelian₂ P.A P.L).pull (lift (fst c'.A c'.A ≫ e.hom) (snd c'.A c'.A ≫ e.hom)).left))
    (m : SiegPB c' c f) :
    ∃ φ : P.A.left ⟶ c.A.left, SqOf P c f φ ∧ ∀ a, (c'.lev a ≫ e.hom).left ≫ φ = f ≫ (c.lev a).left := by
  obtain ⟨ψ, ψ₂, hψ, hs, hv, hl⟩ := m
  have lam : (abelian₂ P.A P.L).IsLB := LB.isLB_linComb P.isLB _ _
  haveI : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  let j : P.A ⊗ P.A ⟶ c'.A ⊗ c'.A := lift (fst P.A P.A ≫ e.inv) (snd P.A P.A ≫ e.inv)
  let i : c'.A ⊗ c'.A ⟶ P.A ⊗ P.A := lift (fst c'.A c'.A ≫ e.hom) (snd c'.A c'.A ≫ e.hom)
  have hji : j.left ≫ i.left = 𝟙 _ := by
    have : j ≫ i = 𝟙 _ := by
      apply CartesianMonoidalCategory.hom_ext <;> simp [i, j]
    exact congrArg (fun q => q.left) this
  have h₁ : j.left ≫ (fst c'.A c'.A).left = (fst P.A P.A).left ≫ e.inv.left :=
    congrArg (fun q => q.left) (lift_fst (fst P.A P.A ≫ e.inv) (snd P.A P.A ≫ e.inv))
  have h₂ : j.left ≫ (snd c'.A c'.A).left = (snd P.A P.A).left ≫ e.inv.left :=
    congrArg (fun q => q.left) (lift_snd (fst P.A P.A ≫ e.inv) (snd P.A P.A ≫ e.inv))
  refine ⟨e.inv.left ≫ ψ, ⟨((isGrpPullback_of_iso e.symm).comp hψ).congr (Category.id_comp _) rfl, hg,
    j.left ≫ ψ₂, ⟨?_, ?_⟩, ?_⟩, fun a => ?_⟩
  · rw [Category.assoc, hs.1, ← Category.assoc, h₁, Category.assoc]
  · rw [Category.assoc, hs.2, ← Category.assoc, h₂, Category.assoc]
  · have a₁ : LBIso (abelian₂ P.A P.L) ((abelian₂ P.A P.L).pull (j.left ≫ i.left)) := by
      rw [hji]; exact SiegelPullComp.iso_pull_id lam
    have a₂ := a₁.trans lam (pull_isLB lam _) (pull_isLB (pull_isLB lam _) _)
      (SiegelPullComp.iso_pull_pull lam i.left j.left).symm
    have a₃ := a₂.trans lam (pull_isLB (pull_isLB lam _) _) (pull_isLB c'.isLB _)
      (SiegelPullComp.iso_pull j.left hw).symm
    have a₄ := a₃.trans lam (pull_isLB c'.isLB _) (pull_isLB (pull_isLB c.isLB _) _)
      (SiegelPullComp.iso_pull j.left hv)
    exact a₄.trans lam (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _)
      (SiegelPullComp.iso_pull_pull c.isLB ψ₂ j.left)
  · rw [← Category.assoc, ← Over.comp_left, Category.assoc, e.hom_inv_id, Category.comp_id]
    exact hl a

theorem exists_point_of_perLev : Out.Laws → ∀ (h k : ℕ) (K : Type) [Field K] (ζ : K) (σ : K →+* ℂ) (F : SFam h k ζ), 1 ≤ h → 3 ≤ k → Odd k → σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k) → ∀ (P : Out.PolAV (Sp ℂ)) (τ : Matrix (Fin h) (Fin h) ℂ) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), PerLev P τ k lev → ∃ (p : Sp ℂ ⟶ F.X) (φ : P.A.left ⟶ F.univ.A.left), p ≫ F.s = spMap σ ∧ SqOf P F.univ p φ ∧ ∀ a, (lev a).left ≫ φ = p ≫ (F.univ.lev a).left := by
  intro hL h k K _ ζ σ F _ hk _ hζ P τ lev hP
  obtain ⟨hg, -, -, u, hΛ, hW, hlev⟩ := hP
  have hk₀ : k ≠ 0 := by omega
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk₀
  let ze : ℂˣ := Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) / k)) (Complex.exp_ne_zero _)
  have hprim : IsPrimitiveRoot ze k := by
    rw [← IsPrimitiveRoot.coe_units_iff]
    have := (Complex.isPrimitiveRoot_exp k hk₀).inv
    rw [← Complex.exp_neg, ← neg_div] at this
    exact this
  have add : ∀ x y, lev (x + y) = lev x * lev y := fun x y => by
    rw [hlev, hlev, hlev, per_add, smul_add, u.ex_add]
  have ex0 : u.ex 0 = 1 := (u.ker 0).2 u.Λ.zero_mem
  have pw : ∀ (z : Fin h → ℂ) (n : ℕ), u.ex ((n : ℂ) • z) = u.ex z ^ n := fun z n => by
    induction n with
    | zero => rw [Nat.cast_zero, zero_smul, pow_zero, ex0]
    | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, u.ex_add, ih, pow_succ]
  have tors : ∀ x, lev x ^ k = 1 := fun x => by
    rw [hlev, ← pw, smul_smul, mul_inv_cancel₀ hk', one_smul]
    exact (u.ker _).2 ((hΛ _).2 ⟨x, rfl⟩)
  have weil : ∀ x y, Out.WeilIs P.A P.L k (lev x) (lev y) (unitOn (ze ^ omegaStd x y)) := fun x y => by
    rw [hlev, hlev]
    refine hW k x y _ (Nat.pos_of_ne_zero hk₀) ?_
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, ← Complex.exp_int_mul]
    congr 1
    ring
  obtain ⟨c, e, he, hc, hw, hl⟩ := GlobalTheory.exists_siegPre_of_polAV hL GlobalTheory.Moduli.cube_of_isLB K ℂ σ h k ζ ze P lev hg hk'
    hζ.symm hprim add tors weil
  have hd : Dense {x : Sp ℂ | (spMap σ x).asIdeal = ⊥} := by
    have : {x : Sp ℂ | (spMap σ x).asIdeal = ⊥} = Set.univ :=
      Set.eq_univ_of_forall fun x => Ideal.eq_bot_of_prime _ (h := (spMap σ x).isPrime)
    rw [this]
    exact dense_univ
  obtain ⟨p, hp, m⟩ := F.rep _ _ c inferInstance hd hc
  obtain ⟨φ, hφ, hl'⟩ := sqOf_of_siegPB P F.univ c p e hg hw m
  exact ⟨p, φ, hp, hφ, fun a => by rw [← hl a]; exact hl' a⟩

end GlobalTheory.KeyFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRigidTranslatePrincipalPolarisationOrderTw
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.RigidTranslate

open GlobalTheory.CoordToExt GlobalTheory.PolTranslate

section Calculus

variable {X Y Z : Scheme.{0}}

theorem lbIso_of_refines {L : LB X} (hL : L.IsLB) {K K' K'' : Type} [Fintype K] [Fintype K']
    [Fintype K''] {M M' : LB Y} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (h : Refines M L φ ε) (h' : Refines M' L φ' ε') {ψ : K'' → (Y ⟶ X)} {δ : K'' → ℤ}
    (t : LB.Gen (LB.LinComb L ψ δ)) (ht : t.IsGen)
    (hF : ∀ (U : Type) [CommGroup U] (f : (Y ⟶ X) → U),
      (∏ k, f (ψ k) ^ δ k) * ∏ k, f (φ k) ^ ε k = ∏ k, f (φ' k) ^ ε' k) : LBIso M M' := by
  refine (h'.div h).exists_gen hL (fun U _ f => ?_) t ht
  refine Eq.symm ((Fintype.prod_sum_type _).trans ?_)
  simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  rw [← hF U f, mul_inv_cancel_right]

theorem gen_of_lbIso {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) (h : LBIso A B) (t : LB.Gen A) (ht : t.IsGen) :
    ∃ s : LB.Gen B, s.IsGen := by
  obtain ⟨w, hw⟩ := h.chartPull (chartPullId A) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull B (𝟙 X) (𝟙 X) rfl)
  obtain ⟨c, hc⟩ := gen_chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A (𝟙 X) (𝟙 X) rfl) t ht
  obtain ⟨c', hc', -⟩ := exists_up ((isGen_iff w).1 hw) hB hA c hc
  exact gen_chartPull (chartPullUnpull B _ (Category.id_comp _)) c' hc'

abbrev diff (L : LB X) (u v : Y ⟶ X) : LB Y := LB.LinComb L (K := Fin 2) ![u, v] ![1, -1]

theorem lbIso_diff_diff {L : LB X} (hL : L.IsLB) (u v : Y ⟶ X) (a b : Z ⟶ Y) (e : a ≫ v = b ≫ v) :
    LBIso (diff (diff L u v) a b) (diff (L.pull u) a b) := by
  refine lbIso_of_refines hL ((refines_self _ _).linComb _ _) ((refines_self _ _).linComb _ _) _ isGen_one
    fun U _ f => ?_
  simp [Fintype.prod_prod_type, Fin.prod_univ_two, e, mul_comm (f (b ≫ u))⁻¹, mul_assoc]

theorem lbIso_diff_pull {L : LB X} (hL : L.IsLB) (u v : Y ⟶ X) (a : Z ⟶ Y) (i : L.ι) (h : ∀ z, (a ≫ v) z ∈ L.U i) :
    LBIso ((diff L u v).pull a) (L.pull (a ≫ u)) := by
  obtain ⟨c, hc⟩ := IsoExtend.exists_gen_of_chart hL (a ≫ v) i h
  refine lbIso_of_refines hL ((refines_self _ _).linComb _ _) (refines_self _ _) c hc fun U _ f => ?_
  simp [Fintype.prod_prod_type, Fin.prod_univ_two, mul_left_comm]

end Calculus

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

abbrev rigTransl (L : LB A.left) (t : 𝟙_ (Over S) ⟶ A) : LB A.left := diff L (transl t).left (toUnit A ≫ t).left

theorem comp_const {T : Over S} (y : T ⟶ A) (t : 𝟙_ (Over S) ⟶ A) :
    y.left ≫ (toUnit A ≫ t).left = (toUnit T ≫ t).left := by
  rw [← Over.comp_left, ← Category.assoc, comp_toUnit]

theorem comp_transl_left {T : Over S} (y : T ⟶ A) (t : 𝟙_ (Over S) ⟶ A) :
    y.left ≫ (transl t).left = (y * (toUnit T ≫ t)).left := by
  rw [← Over.comp_left, comp_transl]

variable {L : LB A.left} {t : 𝟙_ (Over S) ⟶ A}

theorem rigidified_rigTransl (hL : L.IsLB) : Out.Rigidified A (rigTransl L t) := by
  refine ((refines_self _ _).linComb _ _).exists_gen hL (fun U _ f => ?_) _ isGen_one
  have e : eSec A ≫ (transl t).left = eSec A ≫ (toUnit A ≫ t).left := by
    rw [eSec, comp_const, comp_transl_left]
    have : (η[A] : 𝟙_ (Over S) ⟶ A) = 1 := by rw [Hom.one_def, toUnit_unit, Category.id_comp]
    rw [this, _root_.one_mul]
  simp only [Fintype.prod_prod_type, Fin.prod_univ_two, Fintype.prod_unique, Fintype.prod_empty,
    Matrix.cons_val_zero, Matrix.cons_val_one, e, _root_.mul_one, zpow_neg, mul_inv_cancel]

theorem sym_rigTransl [IsCommMonObj A] (ht : t * t = 1) (hL : L.IsLB) (h : Out.Sym A L) :
    Out.Sym A (rigTransl L t) := by
  intro s
  obtain ⟨U, hU, c, hc⟩ := sym_transl ht h s
  refine ⟨U, hU, gen_of_lbIso (DVR.linComb_isLB _ (pull_isLB hL _) _ _)
    (DVR.linComb_isLB _ (DVR.linComb_isLB _ hL _ _) _ _) (lbIso_diff_diff hL _ _ _ _ ?_).symm c hc⟩
  rw [Category.assoc, comp_const]

theorem kTriv_rigTransl (ht : t * t = 1) (hL : L.IsLB) (h : Out.KTriv A L) : Out.KTriv A (rigTransl L t) := by
  intro R _ s y hy
  refine kTriv_transl ht hL h R s y fun p => ?_
  obtain ⟨V, hV, c, hc⟩ := hy p
  refine ⟨V, hV, gen_of_lbIso (pull_isLB (DVR.linComb_isLB _ (DVR.linComb_isLB _ hL _ _) _ _) _)
    (pull_isLB (DVR.linComb_isLB _ (pull_isLB hL _) _ _) _)
    (LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl) (lbIso_diff_diff hL _ _ _ _ ?_)) c hc⟩
  rw [comp_const, comp_const]

theorem relAmple_rigTransl [IsAffine S] [IsProper A.hom] (ht : t * t = 1) (hL : L.IsLB) (h : Out.RelAmple A L) :
    Out.RelAmple A (rigTransl L t) := by
  have hL' : (rigTransl L t).IsLB := DVR.linComb_isLB _ hL _ _
  refine AmpleLocal.relAmple_of_locally S A _ hL' inferInstance inferInstance fun s => ?_
  let t₀ : S ⟶ A.left := t.left
  obtain ⟨i, hi⟩ := exists_chart hL (t₀ s)
  let U : S.Opens := t₀ ⁻¹ᵁ L.U i
  refine ⟨U, hi, ?_⟩
  have e : (transl t).left ≫ (transl t).left = 𝟙 _ := congrArg (fun q => q.left) (transl_transl ht)
  have : IsIso (transl t).left := ⟨⟨(transl t).left, e, e⟩⟩
  have hp : IsPullback (transl t).left A.hom A.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨(Over.w _).trans (Category.comp_id _).symm⟩
  have H := (isPullback_morphismRestrict A.hom U).flip.paste_horiz hp
  have k : (toUnit A ≫ t).left = A.hom ≫ t₀ := rfl
  obtain ⟨w, hw⟩ := lbIso_diff_pull hL (transl t).left (toUnit A ≫ t).left (A.hom ⁻¹ᵁ U).ι i fun z => by
    rw [k]; exact z.2
  exact relAmple_pull (A' := Over.mk (A.hom ∣_ U)) H hL (pull_isLB hL' _) ((isGen_iff w).1 hw) ⊤
    (isAffineOpen_top _) (fun _ => trivial) h

theorem lam_rigTransl [IsCommMonObj A] (hL : L.IsLB) (c : LB.Gen (Theta A L)) (hc : c.IsGen) :
    LBIso (abelian₂ A (rigTransl L t)) ((abelian₂ A L).pull (𝟙 _)) := by
  refine LBIso.symm (LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl) (chartPullId _) ?_)
  refine lbIso_of_refines hL (refines_self _ _) ((refines_self _ _).linComb _ _) _
    (DVR.pullGen_isGen _ _ _ _ hc (lift (x2 A 0) (lift (x2 A 1) (toUnit _ ≫ t))).left) fun U _ f => ?_
  rw [Fintype.prod_prod_type]
  simp only [zpow_mul, Finset.prod_zpow, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    comp_const, comp_transl_left]
  refine (congrArg₂ (· * ·) (prod_cub (x2 A 0) (x2 A 1) (toUnit _ ≫ t) f)
    (prod_square (x2 A) fun x => f x.left)).trans (Eq.symm ((prod_square (x2 A) fun x =>
      f (x * (toUnit _ ≫ t)).left ^ (1 : ℤ) * f (toUnit (G2 A) ≫ t).left ^ (-1 : ℤ)).trans ?_))
  simp only [zpow_neg, zpow_one, _root_.one_mul, _root_.mul_assoc]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_rigid_translate : Out.Laws → ∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (t : 𝟙_ (Over (Sp R)) ⟶ P.A), t ^ 2 = 1 → ∃ (P' : Out.PolAV (Sp R)) (e : P'.A ≅ P.A), IsMonHom e.hom ∧ P'.g = P.g ∧ LamIs P'.A P'.L P.A (abelian₂ P.A P.L) e.hom.left ∧ LBIso P'.L (LB.LinComb P.L (K := Fin 2) ![(e.hom ≫ ((toUnit P.A ≫ t) * 𝟙 P.A)).left, (toUnit P'.A ≫ t).left] ![1, -1]) := by
  intro _ R _ P t ht
  rw [sq] at ht
  have := P.isAb.comm
  have := P.isAb.proper
  obtain ⟨c, hc⟩ := Moduli.cube_of_isLB _ P P.L P.isLB
  refine ⟨{ A := P.A, isAb := P.isAb, g := P.g, smoothDim := P.smoothDim, L := rigTransl P.L t
            isLB := DVR.linComb_isLB _ P.isLB _ _
            rigid := rigidified_rigTransl P.isLB
            sym := sym_rigTransl ht P.isLB P.sym
            ample := relAmple_rigTransl ht P.isLB P.ample
            ktriv := kTriv_rigTransl ht P.isLB P.ktriv },
    Iso.refl _, inferInstanceAs (IsMonHom (𝟙 _)), rfl,
    ⟨𝟙 _, ⟨(Category.id_comp _).trans (Category.comp_id _).symm, (Category.id_comp _).trans (Category.comp_id _).symm⟩,
      lam_rigTransl P.isLB c hc⟩, exists_iso P.isLB ?_ _⟩
  have e : transl t = 𝟙 P.A ≫ ((toUnit P.A ≫ t) * 𝟙 P.A) := by
    rw [Category.id_comp, transl, _root_.mul_comm]
  exact congrArg (fun q : P.A ⟶ P.A => ![q.left, (toUnit P.A ≫ t).left]) e

end GlobalTheory.RigidTranslate
end
end

