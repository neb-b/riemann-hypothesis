module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2046
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0485
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0539
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationDifferenceTrivialBaseChangeIffOverA
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TwistFlat

theorem pull_restrict_eq_zero_iff {X₁ X₂ Z : Scheme.{0}} (f₁ : X₁ ⟶ Z) (f₂ : X₂ ⟶ Z) (h : X₁ ⟶ X₂) (k : X₂ ⟶ X₁)
    (hk : k ≫ h = 𝟙 X₂) (hf : h ≫ f₂ = f₁) (hf' : k ≫ f₁ = f₂) (U : Z.Opens) (c : Pic X₂) :
    CechPic.pull (f₁ ⁻¹ᵁ U).ι (CechPic.pull h c) = 0 ↔ CechPic.pull (f₂ ⁻¹ᵁ U).ι c = 0 := by
  constructor
  · intro e
    have e' := pull_eq_zero_of_mem (f₁ ⁻¹ᵁ U) ((f₂ ⁻¹ᵁ U).ι ≫ k) (fun z ↦ by
      show f₁ (k ((f₂ ⁻¹ᵁ U).ι z)) ∈ U
      rw [← Scheme.Hom.comp_apply, hf']
      exact z.2) (c := CechPic.pull h c) e
    rwa [← pull_comp, Category.assoc, hk, Category.comp_id] at e'
  · intro e
    rw [← pull_comp]
    exact pull_eq_zero_of_mem (f₂ ⁻¹ᵁ U) ((f₁ ⁻¹ᵁ U).ι ≫ h) (fun z ↦ by
      show f₂ (h ((f₁ ⁻¹ᵁ U).ι z)) ∈ U
      rw [← Scheme.Hom.comp_apply, hf]
      exact z.2) e

section Iso
variable {R : Type} [CommRing R] (A : Over (Sp R)) {T : Over (Sp R)} {V : Type} [CommRing V] (φ : Sp V ⟶ T.left)
  (Y : Over (Sp V))

def cmpHom : pullback Y.hom (pullback.snd A.hom (φ ≫ T.hom)) ⟶ pullback (Y.hom ≫ φ ≫ T.hom) A.hom :=
  pullback.lift (pullback.fst Y.hom _) (pullback.snd Y.hom _ ≫ pullback.fst A.hom (φ ≫ T.hom)) (by
    rw [← Category.assoc, pullback.condition, Category.assoc, Category.assoc, pullback.condition])

def cmpInv : pullback (Y.hom ≫ φ ≫ T.hom) A.hom ⟶ pullback Y.hom (pullback.snd A.hom (φ ≫ T.hom)) :=
  pullback.lift (pullback.fst _ A.hom)
    (pullback.lift (pullback.snd _ A.hom) (pullback.fst _ A.hom ≫ Y.hom) (by
      rw [Category.assoc]; exact pullback.condition.symm)) (pullback.lift_snd _ _ _).symm

theorem cmpInv_hom : cmpInv A φ Y ≫ cmpHom A φ Y = 𝟙 _ := by
  apply pullback.hom_ext <;>
    simp only [cmpHom, cmpInv, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc, Category.id_comp]

theorem cmpHom_fst : cmpHom A φ Y ≫ pullback.fst _ A.hom = pullback.fst Y.hom (pullback.snd A.hom (φ ≫ T.hom)) :=
  pullback.lift_fst _ _ _

theorem cmpInv_fst : cmpInv A φ Y ≫ pullback.fst Y.hom (pullback.snd A.hom (φ ≫ T.hom)) = pullback.fst _ A.hom :=
  pullback.lift_fst _ _ _

theorem cmpHom_snd : cmpHom A φ Y ≫ pullback.snd (Y.hom ≫ φ ≫ T.hom) A.hom =
    pullback.snd Y.hom (pullback.snd A.hom (φ ≫ T.hom)) ≫ pullback.fst A.hom (φ ≫ T.hom) :=
  pullback.lift_snd _ _ _

end Iso

section Main
variable {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {T : Over (Sp R)} {V : Type} [CommRing V]
  (φ : Sp V ⟶ T.left)

def cmpOver (Y : Over (Sp V)) : Over.mk ((Y ⊗ bc A φ).hom ≫ φ ≫ T.hom) ⟶ up φ Y ⊗ A :=
  Over.homMk (cmpHom A φ Y) (by
    show cmpHom A φ Y ≫ (up φ Y ⊗ A).hom = (Y ⊗ bc A φ).hom ≫ φ ≫ T.hom
    rw [← Over.w (fst (up φ Y) A), ← Over.w (fst Y (bc A φ))]
    show cmpHom A φ Y ≫ pullback.fst _ A.hom ≫ (Y.hom ≫ φ ≫ T.hom) =
      (pullback.fst Y.hom (pullback.snd A.hom (φ ≫ T.hom)) ≫ Y.hom) ≫ φ ≫ T.hom
    rw [← Category.assoc, cmpHom_fst, Category.assoc])

theorem mul_left_fst {Y : Over (Sp V)} (x : Y ⟶ bc A φ) :
    ((fst Y (bc A φ) ≫ x) * snd Y (bc A φ)).left ≫ pullback.fst A.hom (φ ≫ T.hom) =
      cmpHom A φ Y ≫ ((fst (up φ Y) A ≫ upa φ x) * snd (up φ Y) A).left := by
  have hG := (ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback A (φ ≫ T.hom)).2 (Y ⊗ bc A φ)
    (fst Y (bc A φ) ≫ x) (snd Y (bc A φ)) (cmpOver A φ Y ≫ fst (up φ Y) A ≫ upa φ x)
    (cmpOver A φ Y ≫ snd (up φ Y) A) (by
      show cmpHom A φ Y ≫ pullback.fst _ A.hom ≫ x.left ≫ pullback.fst A.hom (φ ≫ T.hom) =
        (pullback.fst Y.hom (pullback.snd A.hom (φ ≫ T.hom)) ≫ x.left) ≫ pullback.fst A.hom (φ ≫ T.hom)
      rw [← Category.assoc, cmpHom_fst, Category.assoc]) (cmpHom_snd A φ Y)
  rw [← MonObj.comp_mul] at hG
  exact hG.symm

theorem snd_lift_pa_pt (Y : Over (Sp V)) :
    (snd Y (bc A φ)).left ≫ (lift (pa A φ) (pt A φ)).left =
      cmpHom A φ Y ≫ (lift (snd (up φ Y) A) (fst (up φ Y) A ≫ upt φ Y)).left := by
  apply pullback.hom_ext
  · show (snd Y (bc A φ)).left ≫ (lift (pa A φ) (pt A φ) ≫ fst A T).left =
      cmpHom A φ Y ≫ (lift (snd (up φ Y) A) (fst (up φ Y) A ≫ upt φ Y) ≫ fst A T).left
    rw [lift_fst, lift_fst]
    exact (cmpHom_snd A φ Y).symm
  · show (snd Y (bc A φ)).left ≫ (lift (pa A φ) (pt A φ) ≫ snd A T).left =
      cmpHom A φ Y ≫ (lift (snd (up φ Y) A) (fst (up φ Y) A ≫ upt φ Y) ≫ snd A T).left
    rw [lift_snd, lift_snd]
    show pullback.snd Y.hom (pullback.snd A.hom (φ ≫ T.hom)) ≫ pullback.snd A.hom (φ ≫ T.hom) ≫ φ =
      cmpHom A φ Y ≫ pullback.fst _ A.hom ≫ Y.hom ≫ φ
    rw [← Category.assoc (cmpHom A φ Y), cmpHom_fst, ← Category.assoc, ← pullback.condition, Category.assoc]

theorem triv_pull_iff {X : Scheme.{0}} {D : LB X} (hD : D.IsLB) (W : X.Opens) :
    Triv (D.pull W.ι) ↔ CechPic.pull W.ι (cls D hD) = 0 := by
  unfold Triv
  rw [← cls_eq_zero_iff (pull_isLB hD _), cls_pull hD]

theorem triv_twist_iff (L : LB A.left) (hL : L.IsLB) (N : LB (A ⊗ T).left) (hN : N.IsLB) (Y : Over (Sp V))
    (x : Y ⟶ bc A φ) (U : Y.left.Opens) :
    Triv ((LB.div (translDiff (bc A φ) (L.pull (pullback.fst A.hom (φ ≫ T.hom))) x)
        ((twist A φ N).pull (snd Y (bc A φ)).left)).pull ((fst Y (bc A φ)).left ⁻¹ᵁ U).ι) ↔
      Triv ((LB.div (translDiff A L (upa φ x)) (ev N (snd (up φ Y) A) (fst (up φ Y) A ≫ upt φ Y))).pull
        ((fst (up φ Y) A).left ⁻¹ᵁ U).ι) := by
  have hL' : (L.pull (pullback.fst A.hom (φ ≫ T.hom))).IsLB := pull_isLB hL _
  have h₁ : (translDiff (bc A φ) (L.pull (pullback.fst A.hom (φ ≫ T.hom))) x).IsLB := LB.isLB_linComb hL' _ _
  have hO : (twist A φ N).IsLB := pull_isLB hN _
  have h₂ : ((twist A φ N).pull (snd Y (bc A φ)).left).IsLB := pull_isLB hO _
  have h₃ : (translDiff A L (upa φ x)).IsLB := LB.isLB_linComb hL _ _
  have h₄ : (ev N (snd (up φ Y) A) (fst (up φ Y) A ≫ upt φ Y)).IsLB := pull_isLB hN _
  have hc : cls _ (LB.isLB_div h₁ h₂) = CechPic.pull (cmpHom A φ Y) (cls _ (LB.isLB_div h₃ h₄)) := by
    rw [cls_div h₁ h₂, cls_div h₃ h₄, map_sub]
    have e₁ := pull_translDiff hL' x h₁ (fst Y (bc A φ)) (snd Y (bc A φ))
    rw [lift_fst_snd, Over.id_left, pull_id] at e₁
    have e₂ := pull_translDiff hL (upa φ x) h₃ (fst (up φ Y) A) (snd (up φ Y) A)
    rw [lift_fst_snd, Over.id_left, pull_id] at e₂
    rw [e₁, e₂, map_sub, cls_pull hL, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp, mul_left_fst]
    have e₅ : (snd Y (bc A φ)).left ≫ pullback.fst A.hom (φ ≫ T.hom) = cmpHom A φ Y ≫ (snd (up φ Y) A).left :=
      (cmpHom_snd A φ Y).symm
    rw [e₅, cls_pull hO _ h₂,
      show cls (twist A φ N) hO = CechPic.pull (lift (pa A φ) (pt A φ)).left (cls N hN) from cls_pull hN _ hO,
      cls_pull hN, ← pull_comp, ← pull_comp, snd_lift_pa_pt]
  rw [triv_pull_iff (LB.isLB_div h₁ h₂), triv_pull_iff (LB.isLB_div h₃ h₄), hc]
  exact pull_restrict_eq_zero_iff _ _ (cmpHom A φ Y) (cmpInv A φ Y) (cmpInv_hom A φ Y) (cmpHom_fst A φ Y)
    (cmpInv_fst A φ Y) U _

end Main

end GlobalTheory.TwistFlat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TsumNatCastEq
section
set_option autoImplicit false

noncomputable section

open NumberField
open scoped nonZeroDivisors
open GlobalTheory.LatVal GlobalTheory.LatJet

namespace GlobalTheory.PairFourier

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

theorem tsum_natCast_eq {ι : Type} (n : ι → ℕ) (h : Summable (fun i ↦ (n i : ℂ))) :
    ∃ m : ℕ, ∑' i, (n i : ℂ) = m := by
  have hfin : (Function.support n).Finite := by
    have ht := h.tendsto_cofinite_zero
    have hev : ∀ᶠ i in Filter.cofinite, ‖(n i : ℂ)‖ < 1 := by
      have := ht.norm
      simp only [norm_zero] at this
      exact this.eventually (gt_mem_nhds (by norm_num))
    refine (Filter.eventually_cofinite.1 hev).subset ?_
    intro i hi
    simp only [Function.mem_support] at hi
    simp only [Set.mem_setOf_eq, not_lt]
    have : (1 : ℝ) ≤ n i := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hi
    simpa [Complex.norm_natCast] using this
  refine ⟨∑ i ∈ hfin.toFinset, n i, ?_⟩
  rw [tsum_eq_sum (s := hfin.toFinset)]
  · push_cast; rfl
  · intro i hi
    simp only [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hi
    simp [hi]

variable {F : Type} [Field F] [NumberField F]

theorem norm_div_eq_nat (𝔞 : Frac F) {ν : F} (hν : ν ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F)) :
    ∃ m : ℕ, |((Algebra.norm ℚ ν : ℚ) : ℝ)| / nrm 𝔞 = m := by
  set J : FractionalIdeal (𝓞 F)⁰ F :=
    FractionalIdeal.spanSingleton (𝓞 F)⁰ ν * ((𝔞⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) with hJdef
  have hle : J ≤ 1 := by
    have h1 : FractionalIdeal.spanSingleton (𝓞 F)⁰ ν ≤ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) :=
      FractionalIdeal.spanSingleton_le_iff_mem.2 hν
    calc J ≤ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) * ((𝔞⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) :=
          mul_le_mul_left h1 _
      _ = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hle
  have hJa : J * (𝔞 : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.spanSingleton (𝓞 F)⁰ ν := by
    rw [hJdef, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  have hn := congrArg FractionalIdeal.absNorm hJa
  rw [map_mul, FractionalIdeal.absNorm_span_singleton, ← hI, FractionalIdeal.coeIdeal_absNorm] at hn
  have h0 : (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) : ℚ) ≠ 0 := by
    rw [Ne, FractionalIdeal.absNorm_eq_zero_iff]
    exact Units.ne_zero 𝔞
  refine ⟨Ideal.absNorm I, ?_⟩
  unfold nrm
  rw [div_eq_iff (by exact_mod_cast h0)]
  have := congrArg (fun q : ℚ ↦ (q : ℝ)) hn
  simp only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_abs] at this
  rw [← this]

variable [IsTotallyReal F]

def pairPt (𝔞 𝔟 : Frac F) (c : Quotient (qRel 𝔞 𝔟)) : GlobalTheory.RealMult.FracId.elt (𝔞 * 𝔟) :=
  ⟨c.out.1.1 * c.out.1.2, by
    show _ ∈ ((𝔞 * 𝔟 : Frac F) : FractionalIdeal (𝓞 F)⁰ F)
    rw [Units.val_mul]
    exact FractionalIdeal.mul_mem_mul c.out.2.1 c.out.2.2.1⟩

def pairCoef (𝔞 𝔟 : Frac F) (k : ℕ) (c : Quotient (qRel 𝔞 𝔟)) : ℕ :=
  (norm_div_eq_nat 𝔞 c.out.2.1).choose ^ (k - 1)

theorem qClass_eq (𝔞 𝔟 : Frac F) (k : ℕ) (z : Emb F → ℂ) (c : Quotient (qRel 𝔞 𝔟)) :
    qClass 𝔞 𝔟 k z c = (pairCoef 𝔞 𝔟 k c : ℂ) * GlobalTheory.RealMult.qPower ((pairPt 𝔞 𝔟 c : F)) z := by
  unfold qClass qTerm pairCoef pairPt
  have hs := (norm_div_eq_nat 𝔞 c.out.2.1).choose_spec
  generalize (norm_div_eq_nat 𝔞 c.out.2.1).choose = m at hs ⊢
  rw [hs]
  push_cast
  rfl

theorem pairPt_ne_zero (𝔞 𝔟 : Frac F) (c : Quotient (qRel 𝔞 𝔟)) : pairPt 𝔞 𝔟 c ≠ 0 := by
  intro h
  have h' : c.out.1.1 * c.out.1.2 = 0 := congrArg Subtype.val h
  obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
  have hr : NumberField.ComplexEmbedding.IsReal φ := IsTotallyReal.complexEmbedding_isReal φ
  have := c.out.2.2.2 hr.embedding
  rw [h', map_zero] at this
  exact lt_irrefl _ this

end GlobalTheory.PairFourier
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistFibreIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep.Twist

theorem spMap_comp_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (b : R →+* R') (a : R' →+* R'') :
    spMap a ≫ spMap b = spMap (a.comp b) := by
  rw [← Spec.map_comp]; rfl

theorem twist_fibre_iso : ∀ (V₁ : Type) [CommRing V₁] (X : Over (Sp V₁)) [GrpObj X] (L : LB X.left), L.IsLB →
  ∀ (K : Type) [Field K]
  (ev : V₁ →+* K) (σ : K ≃+* K) (K₀ : Type) [Field K₀] (e : K₀ →+* K), σ.toRingHom.comp e = e →
  ∀ (Z : Over (Sp K)) [GrpObj Z] (LZ : LB Z.left), LZ.IsLB → ∀ (ψ : ((Over.pullback (spMap ev)).obj X).left ⟶ Z.left),
  IsGrpPullback ((Over.pullback (spMap ev)).obj X) Z (𝟙 _) ψ →
  LBIso (L.pull (pullback.fst X.hom (spMap ev))) (LZ.pull ψ) →
  ∀ (Y : Over (Sp K₀)) [GrpObj Y] (L₀ : LB Y.left), L₀.IsLB → ∀ (φ : Z.left ⟶ Y.left), IsGrpPullback Z Y (spMap e) φ →
  LBIso LZ (L₀.pull φ) →
  ∃ f : ((Over.pullback (spMap ev)).obj X).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj X).left,
    IsGrpPullback ((Over.pullback (spMap ev)).obj X) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj X) (𝟙 _) f ∧
    LBIso (L.pull (pullback.fst X.hom (spMap ev))) (L.pull (f ≫ pullback.fst X.hom (spMap (σ.toRingHom.comp ev)))) ∧
    ∀ (q : Sp K ⟶ ((Over.pullback (spMap ev)).obj X).left) (y₀ : Sp K₀ ⟶ Y.left), q ≫ ψ ≫ φ = spMap e ≫ y₀ →
      q ≫ pullback.snd X.hom (spMap ev) = 𝟙 _ →
      q ≫ f ≫ pullback.fst X.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ q ≫ pullback.fst X.hom (spMap ev) := by
  intro V₁ _ X _ L hL K _ ev σ K₀ _ e hσe Z _ LZ hLZ ψ hψ H1 Y _ L₀ hL₀ φ hφ H2
  have hs : spMap σ.toRingHom ≫ spMap e = spMap e := by rw [spMap_comp_spMap, hσe]
  have hev : spMap σ.toRingHom ≫ spMap ev = spMap (σ.toRingHom.comp ev) := spMap_comp_spMap _ _
  have hX := isGrpPullback_pullback X (spMap ev)
  have hXσ := isGrpPullback_pullback X (spMap (σ.toRingHom.comp ev))
  have hχ := hψ.comp hφ
  obtain ⟨ρ, hρ1, hρ2⟩ : ∃ ρ : pullback X.hom (spMap (σ.toRingHom.comp ev)) ⟶ pullback X.hom (spMap ev),
      ρ ≫ pullback.fst X.hom (spMap ev) = pullback.fst X.hom (spMap (σ.toRingHom.comp ev)) ∧
      ρ ≫ pullback.snd X.hom (spMap ev) = pullback.snd X.hom (spMap (σ.toRingHom.comp ev)) ≫ spMap σ.toRingHom :=
    ⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap σ.toRingHom)
      (by rw [pullback.condition, Category.assoc, hev]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hρ : IsGrpPullback ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj X) ((Over.pullback (spMap ev)).obj X)
      (spMap σ.toRingHom) ρ := hX.cancel (hXσ.congr hev.symm hρ1.symm) hρ2
  have hσχ := hρ.comp hχ
  obtain ⟨f, hf1, hf2⟩ : ∃ f : pullback X.hom (spMap ev) ⟶ pullback X.hom (spMap (σ.toRingHom.comp ev)),
      f ≫ ρ ≫ ψ ≫ φ = ψ ≫ φ ∧
      f ≫ pullback.snd X.hom (spMap (σ.toRingHom.comp ev)) = pullback.snd X.hom (spMap ev) :=
    ⟨hσχ.1.lift (ψ ≫ φ) (pullback.snd X.hom (spMap ev))
      (by rw [hχ.1.w]; simp only [Category.id_comp, hs]; try rfl), hσχ.1.lift_fst _ _ _, hσχ.1.lift_snd _ _ _⟩
  have hfg : IsGrpPullback ((Over.pullback (spMap ev)).obj X) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj X)
      (𝟙 _) f :=
    hσχ.cancel (hχ.congr (by simp only [Category.id_comp, hs]) hf1.symm)
      (by rw [Category.comp_id]; exact hf2)
  have hτ1 : f ≫ pullback.fst X.hom (spMap (σ.toRingHom.comp ev)) = (f ≫ ρ) ≫ pullback.fst X.hom (spMap ev) := by
    rw [Category.assoc, hρ1]
  have hτχ : (f ≫ ρ) ≫ ψ ≫ φ = ψ ≫ φ := by rw [Category.assoc, hf1]
  have hτ2 : (f ≫ ρ) ≫ pullback.snd X.hom (spMap ev) = pullback.snd X.hom (spMap ev) ≫ spMap σ.toRingHom := by
    rw [Category.assoc, hρ2, ← Category.assoc, hf2]
  refine ⟨f, hfg, ?_, ?_⟩
  · have K1 : LBIso (LZ.pull ψ) (L₀.pull (ψ ≫ φ)) :=
      LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull LZ ψ ψ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullSame L₀ _ (fun _ => φ) _ ψ fun _ => rfl) H2
    have hA := pull_isLB hL (pullback.fst X.hom (spMap ev))
    have hC := pull_isLB hL₀ (ψ ≫ φ)
    have AC := LBIso.trans hA (pull_isLB hLZ ψ) hC H1 K1
    have D : LBIso (L.pull (f ≫ pullback.fst X.hom (spMap (σ.toRingHom.comp ev)))) (L₀.pull (ψ ≫ φ)) :=
      LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullSame L _ (fun _ => pullback.fst X.hom (spMap ev)) _ (f ≫ ρ) fun _ => hτ1)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullSame L₀ _ (fun _ => ψ ≫ φ) _ (f ≫ ρ) fun _ => hτχ.symm) AC
    exact LBIso.trans hA hC (pull_isLB hL _) AC D.symm
  · intro q y₀ hq hq'
    have hqτ : q ≫ f ≫ ρ = spMap σ.toRingHom ≫ q := by
      apply hχ.1.hom_ext
      · rw [Category.assoc, hτχ, hq, Category.assoc, hq, ← Category.assoc, hs]
      · show (q ≫ f ≫ ρ) ≫ pullback.snd X.hom (spMap ev) = (spMap σ.toRingHom ≫ q) ≫ pullback.snd X.hom (spMap ev)
        rw [Category.assoc, hτ2, ← Category.assoc, hq', Category.assoc, hq', Category.id_comp, Category.comp_id]
    rw [hτ1, ← Category.assoc, hqτ, Category.assoc]

end GlobalTheory.Poinc.Sep.Twist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHilbertLatticeContainsAndCoordinateSize
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HilbFam.TwistSize

theorem intVec_mem_std {F : Type} [Field F] [NumberField F] (z : Fin 2 → ℤ) :
    (fun j ↦ ((z j : ℤ) : F)) ∈ stdLat F := by
  rw [stdLat, Submodule.mem_pi]
  intro j _
  exact Submodule.mem_one.2 ⟨(z j : 𝓞 F), by simp⟩

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N n : ℕ) (L : Lat F) (α : GL (Fin 2) (ZMod N)) (ρ₀ : ℝ), L ≤ stdLat F → (∀ x ∈ stdLat F, (n : 𝓞 F) • x ∈ L) → (∀ v ∈ L, ∀ (j : Fin 2) (i : Emb F), Sz l lam ρ₀ ((i (v j) : ℝ) : ℂ)) → Sz l lam ρ₀ (N : ℂ) → ![0, (n : F)] ∈ twist N L (α : Matrix (Fin 2) (Fin 2) (ZMod N)) ∧ ∀ v ∈ twist N L (α : Matrix (Fin 2) (Fin 2) (ZMod N)), ∀ i : Emb F, Sz l lam ρ₀ ((i (v 0) : ℝ) : ℂ) := by
  intro l _ lam F _ _ _ N n L α ρ₀ hLs hnL hL hN
  have hR := _root_.GlobalTheory.QFam.SzSum.sz_ring l lam
  have hZ := _root_.GlobalTheory.SzRules.main l lam
  let A : Matrix (Fin 2) (Fin 2) ℤ := (α : Matrix (Fin 2) (Fin 2) (ZMod N)).map (ZMod.cast : ZMod N → ℤ)
  have hAα : A.map (Int.cast : ℤ → ZMod N) = (α : Matrix (Fin 2) (Fin 2) (ZMod N)) := by
    ext i j; simp [A, ZMod.intCast_cast, ZMod.cast_id']
  have hI := (GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N L A · hLs)
  rw [← hAα]
  refine ⟨?_, ?_⟩
  · let B : Matrix (Fin 2) (Fin 2) ℤ :=
      ((α⁻¹ : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)).map (ZMod.cast : ZMod N → ℤ)
    have h1 : ((α⁻¹ : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) * (α : Matrix (Fin 2) (Fin 2) (ZMod N)) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hmod : ∀ i j, (((B * A) i j - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod N) = 0 := by
      intro i j
      have h2 := congrFun (congrFun h1 i) j
      rw [Matrix.mul_apply] at h2
      rw [Int.cast_sub, Matrix.mul_apply, Int.cast_sum, Matrix.one_apply]
      rw [Matrix.one_apply] at h2
      simp only [Int.cast_mul, B, A, Matrix.map_apply, ZMod.intCast_cast, ZMod.cast_id', id_eq]
      rw [h2]; split_ifs <;> simp
    have hdv : ∀ i j, (N : ℤ) ∣ (B * A) i j - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j :=
      fun i j ↦ (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 (hmod i j)
    choose D hD using hdv
    have hy : (fun j ↦ (n : F) * (B 1 j : F)) ∈ L := by
      have := hnL _ (intVec_mem_std (fun j ↦ B 1 j))
      convert this using 1
      ext j
      simp [Nat.cast_smul_eq_nsmul]
    have hw : (fun j ↦ -((n : F) * (D 1 j : F))) ∈ stdLat F := by
      have := Submodule.smul_mem (stdLat F) (-(n : 𝓞 F)) (intVec_mem_std (fun j ↦ D 1 j))
      convert this using 1
      ext j
      simp [Nat.cast_smul_eq_nsmul]
    refine (hI _).2 ⟨_, hy, _, hw, ?_⟩
    have hBA : ∀ j, (B 1 0 : F) * (A 0 j : F) + (B 1 1 : F) * (A 1 j : F) = (if (1 : Fin 2) = j then 1 else 0) + (N : F) * (D 1 j : F) := by
      intro j
      have := congrArg (Int.cast : ℤ → F) (hD 1 j)
      rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] at this
      split_ifs at this ⊢ <;> push_cast at this ⊢ <;> linear_combination this
    ext j
    fin_cases j
    · have := hBA 0
      simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two] at this ⊢
      linear_combination -(n : F) * this
    · have := hBA 1
      simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two] at this ⊢
      linear_combination -(n : F) * this
  · intro v hv i
    obtain ⟨y, hy, w, hw, rfl⟩ := (hI v).1 hv
    have hw0 : w 0 ∈ (1 : Submodule (𝓞 F) F) := by
      rw [stdLat, Submodule.mem_pi] at hw; exact hw 0 (Set.mem_univ _)
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 hw0
    have hint : Sz l lam 0 ((i (w 0) : ℝ) : ℂ) := by
      refine hZ.1 1 _ (Nat.Prime.not_dvd_one (Fact.out)) ?_
      rw [Nat.cast_one, one_mul, ← hr]
      exact map_isIntegral_int ((Complex.ofRealHom.comp i).comp (algebraMap (𝓞 F) F)) (RingOfIntegers.isIntegral r)
    have heq : ((i ((Matrix.vecMul y (A.map (Int.cast : ℤ → F)) + (N : F) • w) 0) : ℝ) : ℂ) =
        ((i (y 0) : ℝ) : ℂ) * ((A 0 0 : ℤ) : ℂ) + ((i (y 1) : ℝ) : ℂ) * ((A 1 0 : ℤ) : ℂ) + (N : ℂ) * ((i (w 0) : ℝ) : ℂ) := by
      simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    rw [heq]
    have p1 := hR.2.2.1 ρ₀ 0 _ _ (hL y hy 0 i) (hR.2.2.2.2.1 (A 0 0))
    have p2 := hR.2.2.1 ρ₀ 0 _ _ (hL y hy 1 i) (hR.2.2.2.2.1 (A 1 0))
    have p3 := hR.2.2.1 ρ₀ 0 _ _ hN hint
    rw [add_zero] at p1 p2 p3
    exact (hR.2.1 _ _ _ (hR.2.1 _ _ _ p1 p2).1 p3).1

end GlobalTheory.HilbFam.TwistSize
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedPointOverLabelPowRNEqOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LabelTorsion

theorem pt_nsmul {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real) (b : S.Gam)
    (n : ℕ) : ρ.pt (n • b) = ρ.pt b ^ n := by
  have h0 : ρ.pt 0 = 1 := by
    have h := ρ.pt_add 0 0
    rw [add_zero] at h
    exact left_eq_mul.mp h
  induction n with
  | zero => rw [zero_smul, pow_zero, h0]
  | succ n ih => rw [succ_nsmul, ρ.pt_add, ih, pow_succ]

theorem pt_pow_eq_one {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real) (b : S.Gam) :
    ρ.pt b ^ (S.r * S.N) = 1 := by
  have h : (S.r * S.N) • b = 0 • b := by
    funext i
    rw [Pi.smul_apply, Pi.smul_apply, zero_smul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  rw [← pt_nsmul, h, pt_nsmul, pow_zero]

theorem pow_eq_one_of_over_label : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (b : S.Gam) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt b).left → x ^ (S.r * S.N) = 1 := by
  intro o Ω _ _ _ S ρ p _ y₀ u b x hx
  exact GlobalTheory.FrameMove.pow_eq_one_of (T := baseOver (Sp S.R)) (x := ρ.pt b) u.cart hx (pt_pow_eq_one ρ b)

end GlobalTheory.LabelTorsion
end

