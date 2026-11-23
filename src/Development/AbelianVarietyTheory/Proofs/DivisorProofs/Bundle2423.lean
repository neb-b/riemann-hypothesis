module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2326
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2176
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2205
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisExtendsNormalAffineC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2387
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupExtendsNormalAffineChartAfterRescaling
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitIntCastStalkIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2247
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2354
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2339
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveActionThickeningEndosCompletePoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.ThickEndo

variable {S S' : Scheme.{0}}

theorem homEquiv_mul' (φ : S' ⟶ S) (X : Over S') (A : Over S) [GrpObj A]
    (a b : (Over.map φ).obj X ⟶ A) :
    (Over.mapPullbackAdj φ).homEquiv X A (a * b) =
      (Over.mapPullbackAdj φ).homEquiv X A a * (Over.mapPullbackAdj φ).homEquiv X A b := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Hom.mul_def,
    Hom.mul_def, Functor.obj.μ_def, ← comp_lift_assoc, ← Category.assoc (lift _ _),
    Functor.Monoidal.lift_μ, CategoryTheory.Functor.map_comp]

theorem homEquiv_symm_mul' (φ : S' ⟶ S) (X : Over S') (A : Over S) [GrpObj A]
    (a b : X ⟶ (Over.pullback φ).obj A) :
    ((Over.mapPullbackAdj φ).homEquiv X A).symm (a * b) =
      ((Over.mapPullbackAdj φ).homEquiv X A).symm a * ((Over.mapPullbackAdj φ).homEquiv X A).symm b := by
  apply ((Over.mapPullbackAdj φ).homEquiv X A).injective
  rw [homEquiv_mul', Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem homEquiv_left' (t : S' ⟶ S) {Y : Over S'} {A : Over S} (k : (Over.map t).obj Y ⟶ A) :
    ((Over.mapPullbackAdj t).homEquiv Y A k).left ≫ pullback.fst A.hom t = k.left := by
  rw [Over.mapPullbackAdj, Adjunction.mkOfHomEquiv_homEquiv]
  exact pullback.lift_fst _ _ _

theorem homEquiv_symm_left' (t : S' ⟶ S) {Y : Over S'} {A : Over S} (q : Y ⟶ (Over.pullback t).obj A) :
    (((Over.mapPullbackAdj t).homEquiv Y A).symm q).left = q.left ≫ pullback.fst A.hom t := by
  have := homEquiv_left' t (((Over.mapPullbackAdj t).homEquiv Y A).symm q)
  rw [Equiv.apply_symm_apply] at this
  exact this.symm

end GlobalTheory.ThickEndo

namespace GlobalTheory.ThickEndo

variable {R : Type} [CommRing R] (I : Ideal R) {B : Type} [CommRing B] [IsLocalRing B]

theorem le_comap_of_mem_range {φ : CommRingCat.of R ⟶ CommRingCat.of B}
    (h : Spec.map φ (closedPoint B) ∈ Set.range (thick R I 0)) :
    I ≤ (maximalIdeal B).comap φ.hom := by
  obtain ⟨y, hy⟩ := h
  intro a ha
  have h1 : a ∈ ((thick R I 0) y).asIdeal := by
    show Ideal.Quotient.mk (I ^ (0 + 1)) a ∈ y.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using ha)]
    exact zero_mem _
  rw [hy] at h1
  exact h1

def lev (φ : CommRingCat.of R ⟶ CommRingCat.of B) (hI : I ≤ (maximalIdeal B).comap φ.hom) (e : ℕ) :
    Sp (B ⧸ maximalIdeal B ^ (e + 1)) ⟶ Sp (R ⧸ I ^ (e + 1)) :=
  Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ φ.hom
    ((Ideal.pow_right_mono hI (e + 1)).trans (Ideal.le_comap_pow _ _))))

variable {I}

theorem lev_thick (φ : CommRingCat.of R ⟶ CommRingCat.of B) (hI : I ≤ (maximalIdeal B).comap φ.hom) (e : ℕ) :
    lev I φ hI e ≫ thick R I e = thick B (maximalIdeal B) e ≫ Spec.map φ := by
  rw [lev, ← Spec.map_comp, ← Spec.map_comp]
  congr 1

theorem adicLevelMap_lev (φ : CommRingCat.of R ⟶ CommRingCat.of B) (hI : I ≤ (maximalIdeal B).comap φ.hom)
    (e : ℕ) : adicLevelMap (maximalIdeal B) (Nat.le_succ (e + 1)) ≫ lev I φ hI (e + 1) =
      lev I φ hI e ≫ thickTrans R I e := by
  rw [lev, lev, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext1
  exact Ideal.Quotient.ringHom_ext rfl

end GlobalTheory.ThickEndo

namespace GlobalTheory.ThickEndo

section Main

variable {R : Type} [CommRing R] {I : Ideal R} {G : Over (Sp R)} [GrpObj G] {B : Type} [CommRing B]
  [IsLocalRing B] {φ : CommRingCat.of R ⟶ CommRingCat.of B} (hI : I ≤ (maximalIdeal B).comap φ.hom)

abbrev lvl (e : ℕ) : Over (Sp (R ⧸ I ^ (e + 1))) := Over.mk (lev I φ hI e)

def incl (e : ℕ) : (Over.map (thick R I e)).obj (lvl hI e) ⟶ Over.mk (Spec.map φ) :=
  Over.homMk (thick B (maximalIdeal B) e) (lev_thick φ hI e).symm

def red (e : ℕ) (x : Over.mk (Spec.map φ) ⟶ G) : lvl hI e ⟶ thickObj R I e G :=
  (Over.mapPullbackAdj (thick R I e)).homEquiv (lvl hI e) G (incl hI e ≫ x)

theorem red_fst (e : ℕ) (x : Over.mk (Spec.map φ) ⟶ G) :
    (red hI e x).left ≫ pullback.fst G.hom (thick R I e) = thick B (maximalIdeal B) e ≫ x.left :=
  homEquiv_left' _ _

theorem red_snd (e : ℕ) (x : Over.mk (Spec.map φ) ⟶ G) :
    (red hI e x).left ≫ pullback.snd G.hom (thick R I e) = lev I φ hI e :=
  Over.w (red hI e x)

omit [GrpObj G] in
theorem thickMap_fst (e : ℕ) :
    thickMap R I e G ≫ pullback.fst G.hom (thick R I (e + 1)) = pullback.fst G.hom (thick R I e) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

omit [GrpObj G] in
theorem thickMap_snd (e : ℕ) :
    thickMap R I e G ≫ pullback.snd G.hom (thick R I (e + 1)) =
      pullback.snd G.hom (thick R I e) ≫ thickTrans R I e :=
  pullback.lift_snd _ _ _

theorem red_succ (e : ℕ) (x : Over.mk (Spec.map φ) ⟶ G) :
    adicLevelMap (maximalIdeal B) (Nat.le_succ (e + 1)) ≫ (red hI (e + 1) x).left =
      (red hI e x).left ≫ thickMap R I e G := by
  apply pullback.hom_ext
  · rw [Category.assoc, red_fst, Category.assoc, thickMap_fst, red_fst]
    exact adicLevelMap_ι_assoc (maximalIdeal B) (Nat.le_succ (e + 1)) x.left
  · rw [Category.assoc, red_snd, Category.assoc, thickMap_snd, ← Category.assoc, red_snd, adicLevelMap_lev]

variable (b : ∀ e : ℕ, thickObj R I e G ⟶ thickObj R I e G)

def fam (x : Over.mk (Spec.map φ) ⟶ G) (e : ℕ) : Sp (B ⧸ maximalIdeal B ^ (e + 1)) ⟶ G.left :=
  (red hI e x ≫ b e).left ≫ pullback.fst G.hom (thick R I e)

variable {b}

theorem fam_adic (hb : ∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G)
    (x : Over.mk (Spec.map φ) ⟶ G) : IsAdicFamily (maximalIdeal B) (fam hI b x) := fun e => by
  simp only [fam, Over.comp_left, Category.assoc]
  rw [← Category.assoc (adicLevelMap _ _), red_succ, Category.assoc, ← Category.assoc (thickMap R I e G),
    hb, Category.assoc, thickMap_fst]

variable (b) in
theorem fam_over (x : Over.mk (Spec.map φ) ⟶ G) (e : ℕ) :
    fam hI b x e ≫ G.hom = adicLevelι (maximalIdeal B) (e + 1) ≫ Spec.map φ := by
  have hw : (b e).left ≫ pullback.snd G.hom (thick R I e) = pullback.snd G.hom (thick R I e) := Over.w (b e)
  simp only [fam, Over.comp_left, Category.assoc]
  rw [pullback.condition, ← Category.assoc ((b e).left), hw, ← Category.assoc, red_snd, lev_thick]

variable [IsAdicComplete (maximalIdeal B) B]

theorem exists_lim (hb : ∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G)
    (x : Over.mk (Spec.map φ) ⟶ G) : ∃ g : Sp B ⟶ G.left, g ≫ G.hom = Spec.map φ ∧
      ∀ e, adicLevelι (maximalIdeal B) (e + 1) ≫ g = fam hI b x e :=
  (existsUnique_over_of_isAdicFamily (Spec.map φ) G.hom (fam_adic hI hb x) (fam_over hI b x)).exists

def lim (hb : ∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G)
    (x : Over.mk (Spec.map φ) ⟶ G) : Over.mk (Spec.map φ) ⟶ G :=
  Over.homMk (exists_lim hI hb x).choose (exists_lim hI hb x).choose_spec.1

theorem lim_level (hb : ∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G)
    (x : Over.mk (Spec.map φ) ⟶ G) (e : ℕ) :
    thick B (maximalIdeal B) e ≫ (lim hI hb x).left = fam hI b x e :=
  (exists_lim hI hb x).choose_spec.2 e

theorem incl_lim (hb : ∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G)
    (x : Over.mk (Spec.map φ) ⟶ G) (e : ℕ) :
    incl hI e ≫ lim hI hb x = ((Over.mapPullbackAdj (thick R I e)).homEquiv _ G).symm (red hI e x ≫ b e) := by
  apply Over.OverMorphism.ext
  rw [homEquiv_symm_left', Over.comp_left]
  exact lim_level hI hb x e

theorem lim_mul (hmon : ∀ e, IsMonHom (b e))
    (hb : ∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G)
    (x y : Over.mk (Spec.map φ) ⟶ G) : lim hI hb (x * y) = lim hI hb x * lim hI hb y := by
  have he : ∀ e, incl hI e ≫ lim hI hb (x * y) = incl hI e ≫ (lim hI hb x * lim hI hb y) := by
    intro e
    have := hmon e
    rw [comp_mul, incl_lim, incl_lim, incl_lim, red, comp_mul, homEquiv_mul', mul_comp, homEquiv_symm_mul']
    rfl
  exact Over.OverMorphism.ext (hom_ext_of_isHausdorff (maximalIdeal B) fun e => congrArg (·.left) (he e))

end Main

end GlobalTheory.ThickEndo


open GlobalTheory.ThickEndo in
theorem GlobalTheory.exists_mul_map_points_of_thickEndo : ∀ (R : Type) [CommRing R] (I : Ideal R) (G : Over (Sp R)) [GrpObj G] (b : ∀ e : ℕ, thickObj R I e G ⟶ thickObj R I e G), (∀ e, IsMonHom (b e)) → (∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G) → ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsAdicComplete (maximalIdeal B) B] (s : Sp B ⟶ Sp R), s (closedPoint B) ∈ Set.range (thick R I 0) → ∃ Φ : (Over.mk s ⟶ G) → (Over.mk s ⟶ G), (∀ x y, Φ (x * y) = Φ x * Φ y) ∧ ∀ (x : Over.mk s ⟶ G) (e : ℕ), ∃ r : Sp (B ⧸ maximalIdeal B ^ (e + 1)) ⟶ (thickObj R I e G).left, r ≫ pullback.fst G.hom (thick R I e) = thick B (maximalIdeal B) e ≫ x.left ∧ r ≫ (b e).left ≫ pullback.fst G.hom (thick R I e) = thick B (maximalIdeal B) e ≫ (Φ x).left := by
  intro R _ I G _ b hmon hb B _ _ _ s hs
  obtain ⟨φ, rfl⟩ := Spec.map_surjective s
  have hI := le_comap_of_mem_range I hs
  refine ⟨lim hI hb, fun x y => lim_mul hI hmon hb x y, fun x e => ⟨(red hI e x).left, red_fst hI e x, ?_⟩⟩
  rw [lim_level hI hb x e]
  simp only [fam, Over.comp_left, Category.assoc]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineChartThetaSystemUnitaryModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UPoinc.exists_tie_of_uOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (wi : UWit X) (R : Subalgebra X.o₁ X.Ω₁) (P' : PolAV (Sp R)) (u' : Sp (ratHull R) ⟶ Xo.XF cf), spMap (ratHull R).val.toRingHom ≫ u' = X.uΩ → UOver Xo cf P' (toRat R) u' → ∃ (G : Over (Sp (ratHull R))) (_ : GrpObj G) (α : G.left ⟶ P'.A.left) (β : G.left ⟶ Xo.univ.t.G.left) (m : wi.G.left ⟶ G.left) (P₀ : PolAV (Sp X.Ω₁)) (e : P₀.A.left ⟶ wi.G.left), IsGrpPullback G P'.A (spMap (toRat R)) α ∧ IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β ∧ LBIso (P'.L.pull α) (Xo.univ.t.PP.L.pull β) ∧ IsGrpPullback wi.G G (spMap (ratHull R).val.toRingHom) m ∧ m ≫ β = wi.β ∧ IsGrpPullback P₀.A X.ρ.P.A (spMap X.S.R.val.toRingHom) (e ≫ wi.α) ∧ IsGrpPullback P₀.A P'.A (spMap R.val.toRingHom) (e ≫ m ≫ α) ∧ LBIso P₀.L (X.ρ.P.L.pull (e ≫ wi.α)) ∧ LBIso P₀.L (P'.L.pull (e ≫ m ≫ α)) := by
  intro E _ _ _ H Dw l Xo cf C X wi R P' u' hc h
  obtain ⟨G, _, α, β, hα, hβ, hL⟩ := h
  have hb : IsGrpPullback wi.G Xo.univ.t.G (spMap (ratHull R).val.toRingHom ≫ u' ≫ pullback.fst _ _) wi.β :=
    wi.hβ.congr (by rw [← hc, Category.assoc]) rfl
  have w₁ : wi.β ≫ Xo.univ.t.G.hom = (wi.G.hom ≫ spMap (ratHull R).val.toRingHom) ≫ u' ≫ pullback.fst _ _ := by
    rw [Category.assoc]; exact hb.1.w
  have em := hβ.1.lift_fst _ _ w₁
  have hm := hβ.cancel (hb.congr rfl em.symm) (hβ.1.lift_snd _ _ w₁)
  generalize hβ.1.lift _ _ w₁ = m at em hm
  obtain ⟨P₀, φ, hφ, hφL⟩ := exists_pol_baseChange X.ρ.P (spMap X.S.R.val.toRingHom)
  have w₂ : φ ≫ X.ρ.P.A.hom = (P₀.A.hom ≫ 𝟙 _) ≫ spMap X.S.R.val.toRingHom := by
    rw [Category.comp_id]; exact hφ.1.w
  have ee := wi.hα.1.lift_fst _ _ w₂
  have he := wi.hα.cancel (hφ.congr (Category.id_comp _).symm ee.symm) (wi.hα.1.lift_snd _ _ w₂)
  generalize wi.hα.1.lift _ _ w₂ = e at ee he
  subst ee
  have hU := Xo.univ.t.PP.isLB
  refine ⟨G, _, α, β, m, P₀, e, hα, hβ, hL, hm, em, hφ,
    (he.comp (hm.comp hα)).congr ((Category.id_comp _).trans (spMap_val_toRat R)) rfl, hφL, ?_⟩
  have l₁ : LBIso (X.ρ.P.L.pull (e ≫ wi.α)) (Xo.univ.t.PP.L.pull (e ≫ wi.β)) :=
    GenSpread.lbIso_pull_comp _ rfl rfl wi.hL
  have l₂ : LBIso (P'.L.pull (m ≫ α)) (Xo.univ.t.PP.L.pull (m ≫ β)) := GenSpread.lbIso_pull_comp _ rfl rfl hL
  rw [em] at l₂
  have l₃ : LBIso (P'.L.pull (e ≫ m ≫ α)) (Xo.univ.t.PP.L.pull (e ≫ wi.β)) := GenSpread.lbIso_pull_comp _ rfl rfl l₂
  exact LBIso.trans P₀.isLB (pull_isLB X.ρ.P.isLB _) (pull_isLB P'.isLB _) hφL
    (LBIso.trans (pull_isLB X.ρ.P.isLB _) (pull_isLB hU _) (pull_isLB P'.isLB _) l₁ l₃.symm)


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.UPoinc.exists_urechart_affine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (wi : UWit X) (w : X.M.Z), X.π w ∈ Set.range C.i → ∃ (U : X.M.Z.Opens) (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (fg : (X.M.ringOn U).FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ X.M.ringOn U, ∃ b ∈ X.M.ringOn U, x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ X.M.ringOn U) (hev : ∀ x k, c₀ * X.S.ev x k ∈ X.M.ringOn U) (ρ' : (X.S.rechart c₀ hc (X.M.ringOn U) fg frac hth hev).Real) (u' : Sp (ratHull (X.M.ringOn U)) ⟶ Xo.XF cf), IsAffineOpen U ∧ w ∈ U ∧ USame X.ρ ρ' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X.ρ.i₀ ∧ (∃ (G : Over (Sp (ratHull (X.M.ringOn U)))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ'.P.A (spMap (toRat (X.M.ringOn U))) α ∧ IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β ∧ LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) ∧ (∃ m : wi.G.left ⟶ G.left, IsGrpPullback wi.G G (spMap (ratHull (X.M.ringOn U)).val.toRingHom) m ∧ m ≫ β = wi.β ∧ ∀ x, ∃ w : Sp X.Ω₁ ⟶ wi.G.left, w ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧ w ≫ m ≫ α = spMap (Subalgebra.val (X.M.ringOn U)).toRingHom ≫ (ρ'.pt x).left)) ∧ spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ u' = X.uΩ := by
  intro E _ _ _ H Dw _hpq l Xo cf C X wi w hw
  obtain ⟨U₀, u₀, hU₀a, hwU₀, hu₀⟩ := GlobalTheory.UPoinc.ChartAt.exists_affine_chart_ratLift E H Dw l Xo cf C X w hw
  obtain ⟨U₁, h₁, P₁, _hU₁₀, hU₁a, hwU₁, hP₁⟩ := GlobalTheory.UPoinc.LocSpread.exists_uOver_ringOn E H Dw l Xo cf C X U₀ u₀ w hU₀a hwU₀ hw
  have hN : 1 ≤ X.S.N := by have := X.S.N_ge; omega
  obtain ⟨U, h, P', φ, _hUU₁, hUa, hwU, hφ, hφL, _hgφ, ⟨th, hth⟩, b, hb⟩ :=
    GlobalTheory.Poinc.exists_univBasis_affineChart X.o₁ X.Ω₁ X.M U₁ w hU₁a hwU₁ P₁ X.S.N hN
  have hne : ((U : X.M.Z.Opens) : Set X.M.Z).Nonempty := ⟨w, hwU⟩
  let u' : Sp (ratHull (X.M.ringOn U)) ⟶ Xo.XF cf :=
    spMap (Subalgebra.inclusion (ratHull_mono (h₁.trans h))).toRingHom ≫ u₀
  have hP' : UOver Xo cf P' (toRat (X.M.ringOn U)) u' := by
    refine (uOver_baseChange_iff hφ hφL (toRat _)).2 ?_
    have := hP₁.comp (Subalgebra.inclusion (ratHull_mono h)).toRingHom
    have e : spMap (Subalgebra.inclusion (ratHull_mono h)).toRingHom ≫
        spMap (Subalgebra.inclusion (ratHull_mono h₁)).toRingHom ≫ u₀ = u' := by
      rw [← Category.assoc, ← Spec.map_comp]; rfl
    rw [e] at this
    exact this
  have hcomp : spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ u' = X.uΩ := by
    rw [← hu₀, ← Category.assoc, ← Spec.map_comp]; rfl
  obtain ⟨G, _, α, β, m, P₀, e, hα, hβ, hαβ, hm, hmβ, ha, ha', hL, hL'⟩ :=
    GlobalTheory.UPoinc.exists_tie_of_uOver E H Dw l Xo cf C X wi (X.M.ringOn U) P' u' hcomp hP'
  have hg' : P'.g = X.S.g :=
    (GlobalTheory.polAV_g_eq_of_isGrpPullback X.Ω₁ _ P' P₀ _ _ ha').symm.trans
      ((GlobalTheory.polAV_g_eq_of_isGrpPullback X.Ω₁ _ X.ρ.P P₀ _ _ ha).trans X.ρ.g_eq)
  have hyp : HypS P'.A P'.L :=
    GlobalTheory.Poinc.hypS_of_generic_ringOn X.o₁ X.Ω₁ X.M U hUa hne X.normal X.S.R X.ρ.P P' P₀ _ _ _ ha ha' hL hL' X.ρ.hypS

  obtain ⟨⟨hLw, -⟩, -⟩ := GlobalTheory.lawsAndExpansions
  haveI := RatModel.isFractionRing_ringOn hUa hne
  haveI := TorsExtend.isIntegrallyClosed_ringOn X.M ((isNormalScheme_iff_pred _).1 X.normal) hUa hne
  haveI := ArithBase.ded (o := X.o₁) (Ω := X.Ω₁)
  have fg : (X.M.ringOn U).FG := GlobalTheory.Poinc.fg_ringOn_of_isAffineOpen _ _ X.M U hUa hne
  haveI : IsNoetherianRing (X.M.ringOn U) := isNoetherianRing_of_fg fg
  have hn : 1 ≤ X.S.r * X.S.N := Nat.mul_pos X.S.r_pos (le_trans one_le_two X.S.N_ge)
  have hu : IsUnit ((X.S.r * X.S.N : ℕ) : X.M.ringOn U) := by
    have := X.S.unit.map (algebraMap X.o₁ (X.M.ringOn U))
    rwa [map_natCast] at this
  obtain ⟨pt', hadd, hbij, h₃, hw0⟩ := TorsExtend.exists_labelled hLw X.S.R.val.toRingHom X.ρ.P P' P₀ _ _ ha ha' hL hL'
    hn hu (M := X.S.Gam) (fun x => by ext k; simp [nsmul_eq_mul, -Nat.cast_mul]) X.ρ.pt X.ρ.pt_add X.ρ.pt_bij
  have hweil : ∀ x y (c : (X.M.ringOn U)ˣ), (c : (X.M.ringOn U)) = algebraMap X.o₁ (X.M.ringOn U)
      (X.S.ζ ^ (X.S.r * X.S.N * (eStd X.S.g _ x y).val)) →
      WeilIs P'.A P'.L (X.S.r * X.S.N : ℕ) (pt' x) (pt' y) (unitOn c) := fun x y c hc => by
    obtain ⟨c₀, hc₀⟩ := ((X.S.prim.isUnit (by positivity)).pow (X.S.r * X.S.N * (eStd X.S.g _ x y).val)).map
      (algebraMap X.o₁ X.S.R)
    refine h₃ x y c₀ c ?_ (X.ρ.weil x y c₀ hc₀)
    rw [hc₀, hc]
    rfl
  have frac : ∀ x : X.Ω₁, ∃ a ∈ X.M.ringOn U, ∃ b ∈ X.M.ringOn U, x = a / b := fun x => by
    obtain ⟨p, q, -, e⟩ := RatModel.exists_eq_div hUa hne x
    exact ⟨_, (RatModel.mem_ringOn_iff_exists hne).2 ⟨p, rfl⟩, _, (RatModel.mem_ringOn_iff_exists hne).2 ⟨q, rfl⟩, e⟩
  have hQ : (∃ (G : Over (Sp (ratHull (X.M.ringOn U)))) (_ : GrpObj G) (α : G.left ⟶ P'.A.left)
      (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G P'.A (spMap (toRat (X.M.ringOn U))) α ∧
        IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β ∧ LBIso (P'.L.pull α) (Xo.univ.t.PP.L.pull β) ∧
        (∃ m : wi.G.left ⟶ G.left, IsGrpPullback wi.G G (spMap (ratHull (X.M.ringOn U)).val.toRingHom) m ∧
          m ≫ β = wi.β ∧ ∀ x, ∃ w : Sp X.Ω₁ ⟶ wi.G.left,
            w ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧
            w ≫ m ≫ α = spMap (Subalgebra.val (X.M.ringOn U)).toRingHom ≫ (pt' x).left)) ∧
      ∃ a'' : P₀.A.left ⟶ P'.A.left, IsGrpPullback P₀.A P'.A (spMap (X.M.ringOn U).val.toRingHom) a'' ∧
        LBIso P₀.L (P'.L.pull a'') ∧
        ∀ x, ∃ w0 : Sp X.Ω₁ ⟶ P₀.A.left, w0 ≫ e ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧
          w0 ≫ a'' = spMap (X.M.ringOn U).val.toRingHom ≫ (pt' x).left := by
    refine ⟨⟨G, inferInstance, α, β, hα, hβ, hαβ, m, hm, hmβ, fun x => ?_⟩, _, ha', hL', hw0⟩
    obtain ⟨w0, h₁, h₂⟩ := hw0 x
    exact ⟨w0 ≫ e, by rw [Category.assoc]; exact h₁, by rw [Category.assoc]; exact h₂⟩
  obtain ⟨c₀, hc, hthm, hevm, ρ', ⟨hU', a'', q₂, q₃, q₅⟩, hi₀⟩ := GlobalTheory.ThetaExtend.exists_real_rechart
    GlobalTheory.abelianSchemeLaws_all.1 X.S X.ρ (X.M.ringOn U) fg frac P' P₀ _ _ pt' th b ha ha' hL hL' hg' hyp hadd hbij hweil
    hw0 hth hb
    (fun P pt => (∃ (G : Over (Sp (ratHull (X.M.ringOn U)))) (_ : GrpObj G) (α : G.left ⟶ P.A.left)
      (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G P.A (spMap (toRat (X.M.ringOn U))) α ∧
        IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β ∧ LBIso (P.L.pull α) (Xo.univ.t.PP.L.pull β) ∧
        (∃ m : wi.G.left ⟶ G.left, IsGrpPullback wi.G G (spMap (ratHull (X.M.ringOn U)).val.toRingHom) m ∧
          m ≫ β = wi.β ∧ ∀ x, ∃ w : Sp X.Ω₁ ⟶ wi.G.left,
            w ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧
            w ≫ m ≫ α = spMap (Subalgebra.val (X.M.ringOn U)).toRingHom ≫ (pt x).left)) ∧
      ∃ a'' : P₀.A.left ⟶ P.A.left, IsGrpPullback P₀.A P.A (spMap (X.M.ringOn U).val.toRingHom) a'' ∧
        LBIso P₀.L (P.L.pull a'') ∧
        ∀ x, ∃ w0 : Sp X.Ω₁ ⟶ P₀.A.left, w0 ≫ e ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧
          w0 ≫ a'' = spMap (X.M.ringOn U).val.toRingHom ≫ (pt x).left) hQ
  exact ⟨U, c₀, hc, fg, frac, hthm, hevm, ρ', u', hUa, hwU, ⟨P₀, e ≫ wi.α, a'', ha, q₂, hL, q₃, q₅⟩, hi₀, hU', hcomp⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenDescendingFiniteFreeBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_isAffineOpen_of_preimage_le_affine : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] [Algebra R R₁]
    [Module.Finite R R₁] [Module.Free R R₁] [Nontrivial R₁] [IsLocalRing R] (X X₁ : Scheme.{0})
    (p : X ⟶ Sp R) (p₁ : X₁ ⟶ Sp R₁) (b : X₁ ⟶ X), IsPullback b p₁ p (spMap (algebraMap R R₁)) →
    IsSeparated p → QuasiCompact p → ∀ (W : X₁.Opens), IsAffineOpen W → ∀ s : Finset X,
    (∀ z : X₁, b z ∈ s → z ∈ W) → ∃ O : X.Opens, IsAffineOpen O ∧ ∀ x ∈ s, x ∈ O := by
  intro R R₁ _ _ _ _ _ _ _ X X₁ p p₁ b H _ _ W hW s hs
  classical

  have hg : IsFinite (spMap (algebraMap R R₁)) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 inferInstance
  have hff : Flat (spMap (algebraMap R R₁)) ∧ Surjective (spMap (algebraMap R R₁)) := by
    rw [flat_and_surjective_SpecMap_iff]
    exact RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance
  have : Flat (spMap (algebraMap R R₁)) := hff.1
  have : Surjective (spMap (algebraMap R R₁)) := hff.2
  have : IsFinite b := MorphismProperty.of_isPullback H.flip hg
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated p

  let O' : X.Opens := ⟨(b '' (W : Set X₁)ᶜ)ᶜ, (b.isClosedMap _ W.isOpen.isClosed_compl).isOpen_compl⟩
  have hsO' : ∀ x ∈ s, x ∈ O' := by
    rintro x hx ⟨z, hz, rfl⟩
    exact hz (hs z hx)
  have key : ∀ x ∈ s, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ U ≤ O' := by
    intro x hx
    obtain ⟨U, hU, hxU, hUO⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) (hsO' x hx)
    exact ⟨U, hU, hxU, hUO⟩
  choose U hU hxU hUO using key
  let V : X.Opens := ⨆ x : s, U x.1 x.2
  have hVO : V ≤ O' := iSup_le fun x => hUO x.1 x.2
  have hsV : ∀ x ∈ s, x ∈ V := fun x hx => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxU x hx⟩
  have hVc : IsCompact (V : Set X) := by
    rw [TopologicalSpace.Opens.coe_iSup]
    exact isCompact_iUnion fun x => (hU x.1 x.2).isCompact
  have hVq : IsQuasiSeparated (V : Set X) := IsQuasiSeparated.of_quasiSeparatedSpace _
  have hVW : b ⁻¹ᵁ V ≤ W := by
    intro z hz
    by_contra h
    exact hVO hz ⟨z, h, rfl⟩

  have hfin : (b ⁻¹' (s : Set X)).Finite :=
    s.finite_toSet.preimage' fun x _ => b.finite_preimage_singleton x
  obtain ⟨f, hfV, hft⟩ := _root_.GlobalTheory.Mum.exists_basicOpen_between_finset_and_open X₁ W hW (b ⁻¹ᵁ V) hVW hfin.toFinset
    (fun z hz => hsV _ ((hfin.mem_toFinset).1 hz))
  let f' : Γ(X₁, b ⁻¹ᵁ V) := X₁.presheaf.map (homOfLE hVW).op f
  have hf' : X₁.basicOpen f' = X₁.basicOpen f := by
    rw [Scheme.basicOpen_res]
    exact inf_eq_right.2 hfV
  obtain ⟨n, hn⟩ := _root_.GlobalTheory.Mum.NormBC.exists_norm_basicOpen R R₁ X X₁ p p₁ b H V hVc hVq f'
  refine ⟨X.basicOpen n, ?_, fun x hx => (hn x).2 ⟨hsV x hx, fun z hz => ?_⟩⟩
  swap
  · rw [hf']
    exact hft z ((hfin.mem_toFinset).2 (by simpa [hz] using hx))

  have hle : b ⁻¹ᵁ X.basicOpen n ≤ X₁.basicOpen f := by
    intro z hz
    rw [← hf']
    exact ((hn (b z)).1 hz).2 z rfl
  have hA : IsAffineOpen (b ⁻¹ᵁ X.basicOpen n) := by
    let g : Γ(X₁, X₁.basicOpen f) := X₁.presheaf.map (homOfLE hfV).op (b.app V n)
    have e : X₁.basicOpen g = b ⁻¹ᵁ X.basicOpen n := by
      rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]
      exact inf_eq_right.2 hle
    rw [← e]
    exact (hW.basicOpen f).basicOpen g
  have : IsAffine (b ⁻¹ᵁ X.basicOpen n).toScheme := hA
  exact isAffine_of_isPullback_of_flat_surjective
    ((isPullback_morphismRestrict b (X.basicOpen n)).paste_vert H)

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertFrameOfComplexExponential
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory.ExpUnifAH

theorem exists_unif_isFactorAH_of_isExp : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (M : LB A.left), M.IsLB → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)), IsExp (𝟙 (Sp ℂ)) e → ∃ (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), (∀ z, u.ex z = e z) ∧ GlobalTheory.TorusRM.IsFactorAH u Hm χ := by
  intro A _ _ g hA hg M hM e he
  exact GlobalTheory.ExpFrame.exists_isFactorAH_frame_of_isExp A g hA hg e he M hM

end GlobalTheory.ExpUnifAH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAwaySpreadPointLocalizationAtPrime
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SpreadPoint

set_option backward.isDefEq.respectTransparency false

theorem isStalkMap_atPrime (R : Type) [CommRing R] (𝔭 : Ideal R) [𝔭.IsPrime] :
    GlobalTheory.UPoinc.LocSpread.IsStalkMap (algebraMap R (Localization.AtPrime 𝔭)) := by
  let x : PrimeSpectrum R := ⟨𝔭, inferInstance⟩
  let T := (Spec.structureSheaf R).presheaf.stalk x
  haveI : IsLocalization x.asIdeal.primeCompl T := StructureSheaf.IsLocalization.to_stalk R x
  let e : T ≃ₐ[R] Localization.AtPrime 𝔭 := IsLocalization.algEquiv x.asIdeal.primeCompl T _
  refine ⟨x, asIso (Spec.map (e.toRingEquiv.toCommRingCatIso).hom), ?_, fun a ha =>
    IsLocalization.map_units (Localization.AtPrime 𝔭) (⟨a, ha⟩ : 𝔭.primeCompl)⟩
  rw [Spec.fromSpecStalk_eq', asIso_hom, ← Spec.map_comp]
  congr 1
  ext a
  exact e.commutes a

end GlobalTheory.SpreadPoint

theorem GlobalTheory.SpreadPoint.exists_away : ∀ (B : Type) [CommRing B] (X : Scheme.{0}) (q : X ⟶ Sp B) [LocallyOfFinitePresentation q] (R : Type) [CommRing R] (β : B →+* R) (𝔭 : Ideal R) [𝔭.IsPrime] (f₀ : Sp (Localization.AtPrime 𝔭) ⟶ X), f₀ ≫ q = spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β) → ∃ r ∉ 𝔭, ∃ (j : Localization.Away r →+* Localization.AtPrime 𝔭) (f : Sp (Localization.Away r) ⟶ X), j.comp (algebraMap R (Localization.Away r)) = algebraMap R (Localization.AtPrime 𝔭) ∧ f ≫ q = spMap ((algebraMap R (Localization.Away r)).comp β) ∧ spMap j ≫ f = f₀ := by
  intro B _ X q _ R _ β 𝔭 _ f₀ hf₀
  set σ := algebraMap R (Localization.AtPrime 𝔭)
  have hσ := GlobalTheory.SpreadPoint.isStalkMap_atPrime R 𝔭
  let q' : pullback q (spMap β) ⟶ Sp R := pullback.snd q (spMap β)
  have hP : IsPullback (spMap σ) (𝟙 _) (𝟙 (Sp R)) (spMap σ) :=
    IsPullback.of_vert_isIso ⟨by simp⟩
  have hcomp : ∀ {A C D : Type} [CommRing A] [CommRing C] [CommRing D] (f : A →+* C) (g : C →+* D),
      spMap g ≫ spMap f = spMap (g.comp f) := fun f g => (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm
  let u₀ : Sp (Localization.AtPrime 𝔭) ⟶ pullback q (spMap β) :=
    pullback.lift f₀ (spMap σ) (by rw [hf₀, hcomp])
  obtain ⟨a, ha, H⟩ := GlobalTheory.UPoinc.LocSpread.exists_hom hσ (𝟙 (Sp R)) q' hP u₀ (by simp [u₀, q'])
  have ha' : a ∉ 𝔭 := by
    intro h
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime 𝔭) 𝔭 a).1 ha h
  let g := algebraMap R (Localization.Away a)
  obtain ⟨u, hu, hu₀⟩ := H (Localization.Away a) g (IsLocalization.Away.algebraMap_isUnit a) (Sp (Localization.Away a))
    (spMap g) (𝟙 _) (by simp)
  let j : Localization.Away a →+* Localization.AtPrime 𝔭 := IsLocalization.Away.lift a ha
  have hj : j.comp g = σ := IsLocalization.Away.lift_comp _ _
  refine ⟨a, ha', j, u ≫ pullback.fst q (spMap β), hj, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (u ≫ q') ≫ _ = _
    rw [hu, Category.comp_id, hcomp]
  · rw [← Category.assoc, hu₀ (spMap j) (by rw [hcomp, hj])]
    exact pullback.lift_fst _ _ _
end
end

