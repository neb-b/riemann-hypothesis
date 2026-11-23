module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2721
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2590
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0043
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.FiniteLocalLifts.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1072
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2727
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1906
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2720
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2232
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2147
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2307
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2657
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2724
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2713
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2669
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2699

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationFiniteExtensionSiegelFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.PoincUnif

theorem exists_unif_finExt : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V₁ : Type) [CommRing V₁] [IsDomain V₁]
    [IsLocalRing V₁], GlobalTheory.LN.CDvr V₁ → ∀ (y₁ : Sp (FractionRing V₁) ⟶ F.X) (A : PolAV (Sp (FractionRing V₁)))
    (α : A.A.left ⟶ F.univ.A.left) (α₂ : (G2 A.A).left ⟶ (G2 F.univ.A).left),
    IsGrpPullback A.A F.univ.A y₁ α → IsSquare α α₂ → LBIso (abelian₂ A.A A.L) (F.univ.P.pull α₂) →
    ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G] (gen : (Over.pullback (jK V₁)).obj G ≅ A.A),
    IsSemiAbelian G → IsMonHom gen.hom →
      ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (f : V₁ →+* W)
        (fK : FractionRing V₁ →+* FractionRing W), GlobalTheory.LN.CDvr W ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
        (∀ a, fK (algebraMap V₁ _ a) = algebraMap W _ (f a)) ∧
        ∃ (G' : Over (Sp W)) (_ : GrpObj G') (_ : IsCommMonObj G') (D : DegData W (maximalIdeal W))
          (A' : PolAV (Sp (FractionRing W))) (_ : Unif (maximalIdeal W) D A' G') (α' : A'.A.left ⟶ F.univ.A.left)
          (α₂' : (G2 A'.A).left ⟶ (G2 F.univ.A).left),
          IsSemiAbelian G' ∧ IsGrpPullback A'.A F.univ.A (spMap fK ≫ y₁) α' ∧ IsSquare α' α₂' ∧
          LBIso (abelian₂ A'.A A'.L) (F.univ.P.pull α₂') := by
  intro g n o _ ζ F V₁ _ _ _ hV y₁ A α α₂ hα hsq hL G _ _ gen hG hgen
  haveI : IsMonHom gen.hom := hgen
  have hdvr : IsDiscreteValuationRing V₁ := hV.1
  have hLgen : (A.L.pull gen.hom.left).IsLB := pull_isLB A.isLB _
  obtain ⟨PP, hPP⟩ := GlobalTheory.MumExt.exists_extLam V₁ G hG _ hLgen
  obtain ⟨R', _, _, _, ρ, D₁, G₁, _, _, β, β₂, A₁, U₁, hR', hρ, hβ, hβ₂, hPβ⟩ :=
    _root_.GlobalTheory.Mum.exists_unif_finExt_lam V₁ hV G hG A gen hgen PP hPP
  obtain ⟨-, hinj, hfin⟩ := hρ
  have hloc : IsLocalHom ρ := by
    letI := ρ.toAlgebra
    haveI : Module.Finite V₁ R' := hfin
    exact ReciprocityTheory.ChartRestriction.G.Pdiv.FiniteLocalHoms.isLocalHom_algebraMap
  have hinj' : Function.Injective ((algebraMap R' (FractionRing R')).comp ρ) :=
    (IsFractionRing.injective R' (FractionRing R')).comp hinj
  let fK : FractionRing V₁ →+* FractionRing R' := IsFractionRing.lift (K := FractionRing V₁) hinj'
  have hfK : ∀ a, fK (algebraMap V₁ _ a) = algebraMap R' _ (ρ a) := fun a =>
    IsFractionRing.lift_algebraMap _ _
  have hbase : jK R' ≫ spMap ρ = spMap fK ≫ jK V₁ := by
    have e : fK.comp (algebraMap V₁ (FractionRing V₁)) = (algebraMap R' (FractionRing R')).comp ρ :=
      RingHom.ext hfK
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact congrArg CommRingCat.ofHom e.symm

  let g₁ : A₁.A.left ⟶ G₁.left := U₁.gen.inv.left ≫ pullback.fst G₁.hom (jK R')
  have hg₁ : IsGrpPullback A₁.A G₁ (jK R') g₁ := GlobalTheory.ThetaBaseChange.grp_generic U₁.toUnifPre
  have hgβ := hg₁.comp hβ
  have hfst : IsGrpPullback ((Over.pullback (jK V₁)).obj G) G (jK V₁) (pullback.fst G.hom (jK V₁)) :=
    isGrpPullback_pullback G (jK V₁)
  have hw : (g₁ ≫ β) ≫ G.hom = (A₁.A.hom ≫ spMap fK) ≫ jK V₁ := by
    have := hgβ.1.w
    simp only [Category.assoc] at this ⊢
    rw [← hbase]; exact this
  let ι' : A₁.A.left ⟶ ((Over.pullback (jK V₁)).obj G).left := hfst.1.lift (g₁ ≫ β) (A₁.A.hom ≫ spMap fK) hw
  have hι'f : ι' ≫ pullback.fst G.hom (jK V₁) = g₁ ≫ β := hfst.1.lift_fst _ _ _
  have hι's : ι' ≫ ((Over.pullback (jK V₁)).obj G).hom = A₁.A.hom ≫ spMap fK := hfst.1.lift_snd _ _ _
  have hι' : IsGrpPullback A₁.A ((Over.pullback (jK V₁)).obj G) (spMap fK) ι' :=
    IsGrpPullback.cancel hfst (hgβ.congr hbase hι'f.symm) hι's
  let ι : A₁.A.left ⟶ A.A.left := ι' ≫ gen.hom.left
  have hι : IsGrpPullback A₁.A A.A (spMap fK) ι :=
    (hι'.comp (isGrpPullback_of_iso gen)).congr (Category.comp_id _) rfl
  have hα' : IsGrpPullback A₁.A F.univ.A (spMap fK ≫ y₁) (ι ≫ α) := hι.comp hα

  obtain ⟨ι₂, hι₂⟩ : ∃ m, IsSquare ι m := ⟨_, GlobalTheory.LamPull.exists_isSquare hι.1.w⟩
  obtain ⟨ι'₂, hι'₂⟩ : ∃ m, IsSquare ι' m := ⟨_, GlobalTheory.LamPull.exists_isSquare hι'.1.w⟩
  obtain ⟨g₁₂, hg₁₂⟩ : ∃ m, IsSquare g₁ m := ⟨_, GlobalTheory.LamPull.exists_isSquare hg₁.1.w⟩
  obtain ⟨κ₂, hκ₂⟩ : ∃ m, IsSquare (G' := (Over.pullback (jK V₁)).obj G) (G := G) (pullback.fst G.hom (jK V₁)) m :=
    ⟨_, GlobalTheory.LamPull.exists_isSquare hfst.1.w⟩
  have sqc : ∀ {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} {φ : G'.left ⟶ G.left}
      {ψ : G''.left ⟶ G'.left} {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} {ψ₂ : (G'' ⊗ G'').left ⟶ (G' ⊗ G').left},
      IsSquare ψ ψ₂ → IsSquare φ φ₂ → IsSquare (ψ ≫ φ) (ψ₂ ≫ φ₂) := fun h' h =>
    ⟨by rw [Category.assoc, h.1, ← Category.assoc, h'.1, Category.assoc],
      by rw [Category.assoc, h.2, ← Category.assoc, h'.2, Category.assoc]⟩
  have hsq' := sqc hι₂ hsq
  have e₂ := GlobalTheory.LamPull.isSquare_unique (sqc hg₁₂ hβ₂) (hι'f ▸ sqc hι'₂ hκ₂)

  have hPPlb : PP.IsLB := hPP.1
  have hA₁L : LBIso A₁.L (U₁.LG.L.pull g₁) := by
    have hgi : U₁.gen.inv.left ≫ U₁.gen.hom.left = 𝟙 _ := by
      rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
    exact LBIso.chartPull (h := U₁.gen.inv.left) (chartPullSec A₁.L _ _ hgi)
      (chartPullSame U₁.LG.L _ (fun _ => pullback.fst G₁.hom (jK R')) _ _ fun _ => rfl) U₁.ext
  have lamLB : ∀ {S : Scheme.{0}} (X : Over S) [GrpObj X] [IsCommMonObj X] {M : LB X.left}, M.IsLB →
      (abelian₂ X M).IsLB := fun X _ _ M hM => DVR.linComb_isLB M hM _ _
  have s1 := GlobalTheory.LamPull.lbIso_lam_pull hg₁ U₁.LG.isLB A₁.isLB hA₁L hg₁₂
  have s2 := GlobalTheory.ZM.SiegClause.lbIso_pull_pull hPβ g₁₂
  rw [e₂] at s2
  have s3 := (GlobalTheory.ZM.SiegClause.lbIso_pull_pull (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hPPlb κ₂)) ι'₂).symm
  have s4 := hPP.2 κ₂ hκ₂
  have s5 := (GlobalTheory.RigidBundleGlue.LBIso.pull s4 ι'₂).symm
  have hιL : LBIso (A.L.pull ι) ((A.L.pull gen.hom.left).pull ι') :=
    (GlobalTheory.ZM.SiegClause.lbIso_pull_pull (GlobalTheory.PolBaseChange.lbIso_refl hLgen) ι').symm
  have s6 := (GlobalTheory.LamPull.lbIso_lam_pull hι' hLgen (pull_isLB A.isLB ι) hιL hι'₂).symm
  have s7 := GlobalTheory.LamPull.lbIso_lam_pull hι A.isLB (pull_isLB A.isLB ι)
    (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB A.isLB ι)) hι₂
  have s8 := GlobalTheory.ZM.SiegClause.lbIso_pull_pull hL ι₂
  have t1 := LBIso.trans (lamLB _ A₁.isLB) (pull_isLB (lamLB _ U₁.LG.isLB) _) (pull_isLB hPPlb _) s1 s2
  have t2 := LBIso.trans (lamLB _ A₁.isLB) (pull_isLB hPPlb _) (pull_isLB (pull_isLB hPPlb _) _) t1 s3
  have t3 := LBIso.trans (lamLB _ A₁.isLB) (pull_isLB (pull_isLB hPPlb _) _) (pull_isLB (lamLB _ hLgen) _) t2 s5
  have t4 := LBIso.trans (lamLB _ A₁.isLB) (pull_isLB (lamLB _ hLgen) _) (lamLB _ (pull_isLB A.isLB ι)) t3 s6
  have t5 := LBIso.trans (lamLB _ A₁.isLB) (lamLB _ (pull_isLB A.isLB ι)) (pull_isLB (lamLB _ A.isLB) _) t4 s7
  have t6 := LBIso.trans (lamLB _ A₁.isLB) (pull_isLB (lamLB _ A.isLB) _) (pull_isLB F.univ.isLB _) t5 s8
  have hG₁ : IsSemiAbelian G₁ := by
    obtain ⟨bc, mbc, -⟩ := grpPullback_iso hβ (isGrpPullback_pullback G (spMap ρ))
    haveI := mbc
    exact GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback (spMap ρ) G hG)
  exact ⟨R', inferInstance, inferInstance, inferInstance, ρ, fK, hR', hinj, hloc, hfin, hfK, G₁, inferInstance,
    inferInstance, D₁, A₁, U₁, ι ≫ α, _, hG₁, hα', hsq', t6⟩

end GlobalTheory.PoincUnif
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleCosetRationalProductOfLocalLevels
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.ClassFinLev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def finPart : UA E n →* finU (E := E) (n := n) where
  toFun u := ⟨⟨finGL E n (GeneralLinearGroup.map (pFin E) u.1), GlobalTheory.DefU.ClassFin.finGL_mem_UA _ (GlobalTheory.DefU.ClassFin.cT_pFin u)⟩,
    pInf_finGL _⟩
  map_one' := Subtype.ext (Subtype.ext (by simp))
  map_mul' a b := Subtype.ext (Subtype.ext (by simp))

theorem finPart_fin (k : finU (E := E) (n := n)) : finPart (k : UA E n) = k :=
  Subtype.ext (Subtype.ext (GlobalTheory.DefU.ClassFin.finGL_pFin k))

theorem finPart_inf {x : UA E n} (hx : x ∈ infU E n) : finPart x = 1 := by
  have h : GeneralLinearGroup.map (pFin E) x.1 = 1 := hx
  refine Subtype.ext (Subtype.ext ?_)
  change finGL E n (GeneralLinearGroup.map (pFin E) x.1) = 1
  rw [h, map_one]

theorem finPart_rat {γ : UA E n} (hγ : γ ∈ ratU E n) : finPart γ ∈ ratFinU E n := by
  obtain ⟨γ₀, hγ₀'⟩ := hγ
  have hγ₀ : ratGL E n γ₀ = γ.1 := hγ₀'
  have hg : cT (conjAd E) γ.1.val * 1 * γ.1.val = 1 := γ.2
  rw [← hγ₀, mul_one] at hg
  have hv : (ratGL E n γ₀).val = γ₀.val.map (algebraMap E (Ad E)) := rfl
  rw [hv, GlobalTheory.DefU.ClassFin.cT_map (algebraMap E (Ad E)) (IsCMField.complexConj E).toRingEquiv.toRingHom (conjAd E)
    (fun y => (conjAd_algebraMap y).symm), ← Matrix.map_mul] at hg
  have hU : γ₀ ∈ UE E n := by
    change cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * 1 * γ₀.val = 1
    rw [mul_one]
    ext i j
    have := congrFun₂ hg i j
    rw [Matrix.map_apply, Matrix.one_apply] at this
    rw [Matrix.one_apply]
    haveI hnt : Nontrivial (Ad E) := show Nontrivial (InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E) from inferInstance
    apply (algebraMap E (Ad E)).injective
    rw [this]
    split_ifs <;> simp
  refine ⟨γ₀, hU, ?_⟩
  change finGL E n (ratF E n γ₀) = finGL E n (GeneralLinearGroup.map (pFin E) γ.1)
  rw [← hγ₀]
  rfl

theorem finite_doubleCoset_of_isOpen (K : Subgroup (finU (E := E) (n := n))) (hK : IsOpen (K : Set (finU (E := E) (n := n)))) :
    Finite (DoubleCoset.Quotient (ratFinU E n : Set (finU (E := E) (n := n))) (K : Set (finU (E := E) (n := n)))) := by
  obtain ⟨T, hT⟩ := GlobalTheory.DefU.ClassFin.classSet_finite E n K hK
  let φ : T → DoubleCoset.Quotient (ratFinU E n : Set (finU (E := E) (n := n))) (K : Set (finU (E := E) (n := n))) :=
    fun s => DoubleCoset.mk _ _ (finPart (s : UA E n))
  refine Finite.of_surjective φ fun q => ?_
  obtain ⟨g, rfl⟩ : ∃ g, DoubleCoset.mk _ _ g = q := ⟨q.out, DoubleCoset.out_eq' q⟩
  obtain ⟨γ, hγ, s, hs, x, hx, k, hk, e⟩ := hT (g : UA E n)
  refine ⟨⟨s, hs⟩, ?_⟩
  have hg : g = finPart γ * finPart s * k := by
    have := congrArg finPart e
    rw [finPart_fin, map_mul, map_mul, map_mul, finPart_inf hx, mul_one, finPart_fin] at this
    exact this
  show DoubleCoset.mk _ _ (finPart (s : UA E n)) = DoubleCoset.mk _ _ g
  rw [hg]
  exact (@DoubleCoset.eq _ _ _ _ _ _).2 ⟨finPart γ, finPart_rat hγ, k, hk, rfl⟩

end GlobalTheory.BCT.ClassFinLev


open GlobalTheory.BCT.ClassFinLev in
theorem GlobalTheory.BCT.finite_doubleCoset_globLev : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → Finite (DoubleCoset.Quotient (ratFinU E n : Set (finU (E := E) (n := n))) (globLev S K' : Set (finU (E := E) (n := n)))) := by
  intro E _ _ _ hE n _ S _ K' hK
  exact finite_doubleCoset_of_isOpen _ (GlobalTheory.T.isOpen_productOfLocalLevelsUnitary E hE n S K' hK)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTestDivisorsKltLcPencilBoundaries
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.Discrepancy GlobalTheory.EtaleKlt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairStep

theorem finite_test_divisors : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (G D₀ : CartierDiv X), η ≠ 0 → 0 < m → ∃ S : Set (DivOver p), S.Finite ∧ ∀ (x : X) (g f : X.functionFieldˣ) (c : ℚ), G.IsEqn x g → D₀.IsEqn x f → ((∀ E ∈ S, E.Through x → -1 < discrep E η m g - c * E.ord f) → ∀ E : DivOver p, E.Through x → -1 < discrep E η m g - c * E.ord f) ∧ ((∀ E ∈ S, E.Through x → -1 ≤ discrep E η m g - c * E.ord f) → ∀ E : DivOver p, E.Through x → -1 ≤ discrep E η m g - c * E.ord f) := by
  intro hP X _ _ p n hproj hn η m G D₀ hη hm
  haveI : LocallyOfFiniteType p := by
    obtain ⟨h1, -⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hproj
    infer_instance
  obtain ⟨Y, hYi, hYn, s, hsd, B, hsm, hprop, hbij, hfin, hη', hchart, hG, hD, hK⟩ :=
    _root_.GlobalTheory.ResPairSupp.exists_resolution_supp hP X p n hproj hn η G D₀ hη
  haveI := SmoothOfRelativeDimension.smooth n (s ≫ p)
  haveI : GlobalTheory.IsNormalScheme Y := isNormalScheme_of_smooth (s ≫ p)
  have hnY : topologicalKrullDim Y = n := GlobalTheory.NadelApp.topologicalKrullDim_eq_of_smooth Y (s ≫ p) n
  set S : Set (DivOver p) := ⋃ v ∈ {v : Y | v ∈ B ∧ Order.coheight v = 1},
    {E : DivOver p | ∀ f, f ∈ E.ring ↔ RegAt v (functionFieldMap s f)} with hSdef
  refine ⟨S, hfin.biUnion fun v _ => Set.Subsingleton.finite fun E hE E₂ hE₂ => ?_, ?_⟩
  · have hr : E.ring = E₂.ring := SetLike.ext fun f => (hE f).trans (hE₂ f).symm
    cases E; cases E₂
    cases hr
    rfl
  intro x g f c hg hf
  have hmq : (0 : ℚ) < m := by exact_mod_cast hm

  have core : ∀ E : DivOver p, E.Through x → ∃ (ι : Type) (_ : Fintype ι) (Es : ι → DivOver p) (t : ι → ℤ),
      (∀ j, Es j ∈ S ∧ (Es j).Through x ∧ 0 ≤ t j) ∧
      ((∀ j, t j = 0) → (1 : ℚ) ≤ 1 + (discrep E η m g - c * E.ord f)) ∧
      ((∃ j, t j ≠ 0) → ∑ j, (1 + (discrep (Es j) η m g - c * (Es j).ord f)) * (t j : ℚ) ≤
        1 + (discrep E η m g - c * E.ord f)) := by
    intro E hE
    obtain ⟨E', hE'⟩ := _root_.GlobalTheory.Discrepancy.DivOver.exists_over_complex p s hbij E
    obtain ⟨y, hyx, hy⟩ := _root_.GlobalTheory.ProperCentre.exists_regAt_centre s E'.ring x fun a ha => (hE' a).1 (hE a ha)
    obtain ⟨U, hyU, z, J, w, u, hc⟩ := hchart y
    have hgen := isFreeGen_formOf (gen_mem hyU) hc.frame
    set ω0 := formOf U (gen_mem hyU) (dOn (s ≫ p) z) with hω0
    have h0 : ω0 ≠ 0 := fun h =>
      one_ne_zero (hgen.1 (a₁ := 1) (a₂ := 0) (by simp [h]))
    obtain ⟨h, hh⟩ := hgen.2 (ratPull p s n η)
    have hh0 : h ≠ 0 := fun e => hη' (by simp [← hh, e])
    set H : Y.functionFieldˣ := Units.mk0 h hh0 with hH
    have hHη : ratPull p s n η = (H : Y.functionField) • ω0 := hh.symm

    have hgy : G.IsEqn (s y) g := by
      obtain ⟨V, hV, hgV⟩ := hg.exists_nhds
      exact hgV _ (hyx.mem_open V.isOpen hV)
    have hfy : D₀.IsEqn (s y) f := by
      obtain ⟨V, hV, hfV⟩ := hf.exists_nhds
      exact hfV _ (hyx.mem_open V.isOpen hV)

    have hoff : ∀ v, v ⤳ y → Order.coheight v = 1 → (∀ j : J, v ≠ w j) → v ∉ B := by
      intro v hv h1 hne hvB
      obtain ⟨j, hj, rfl⟩ := (hc.mem v hv h1).1 hvB
      exact hne ⟨j, hj⟩ rfl
    have hHv : ∀ v, v ⤳ y → Order.coheight v = 1 → (∀ j : J, v ≠ w j) →
        Scheme.ord (H : Y.functionField) v = 0 := by
      intro v hv h1 hne
      obtain ⟨F, hF⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := s ≫ p) h1
      have e1 := hK v F h1 (hoff v hv h1 hne) hF
      change F.formOrd (ratPull p s n η) = 0 at e1
      rw [hHη, F.formOrd_smul hnY h0, DivOver.formOrd_formOf_eq_zero (hv.mem_open U.isOpen hyU) hF hc.frame,
        add_zero, hF.ord_eq] at e1
      exact e1
    have hM := fun φ hφ => _root_.GlobalTheory.Discrepancy.MonoOrd.ord_eq_sum_of_monomial E' y hy (ι := J) (fun j => w j) (fun j => u j)
      (fun a b e => Subtype.ext (hc.inj a.2 b.2 e)) (fun j => hc.spec j j.2) (fun j => hc.coheight j j.2)
      (fun j => hc.ord_self j j.2) (fun j v hv _ hne => hc.ord_other j j.2 v hv hne) φ hφ
    have hMH := hM H hHv
    have hMg := hM (fnPull s g) fun v hv h1 hne => hG y v g hv h1 (hoff v hv h1 hne) hgy
    have hMf := hM (fnPull s f) fun v hv h1 hne => hD y v f hv h1 (hoff v hv h1 hne) hfy

    have hFj : ∀ j : J, ∃ F : DivOver (s ≫ p), F.IsAt (w j) := fun j =>
      DivOver.exists_isAt_of_coheight_eq_one (hc.coheight j j.2)
    choose F hF using hFj
    have hEj : ∀ j : J, ∃ Ej : DivOver p, DivOver.Over s (F j) Ej := fun j => _root_.GlobalTheory.Discrepancy.DivOver.exists_over_of_bijective_complex p s hbij (F j)
    choose Es hEs using hEj
    have hA := _root_.GlobalTheory.BirOrd.ord_and_formOrd_of_over p n hn s hbij E E' hE'
    have hAj := fun j => _root_.GlobalTheory.BirOrd.ord_and_formOrd_of_over p n hn s hbij (Es j) (F j) (hEs j)

    set t : J → ℤ := fun j => E'.ord (u j) with ht
    have htn : ∀ j, 0 ≤ t j := fun j => by
      refine (E'.ord_nonneg_iff _).2 (hy _ ?_)
      rw [hc.val j j.2]
      exact regAt_fnOf hyU _ _
    set Fo := E'.formOrd ω0 with hFo
    have hlog : ∑ j : J, t j - 1 ≤ Fo :=
      _root_.GlobalTheory.Discrepancy.DivOver.sum_ord_sub_one_le_formOrd_dOn hnY E' hyU hy z h0 (J := J) Subtype.val Subtype.val_injective (fun j => u j)
        fun j => hc.val j j.2
    have hnn : 0 ≤ Fo := DivOver.formOrd_formOf_nonneg hnY hyU hy (dOn (s ≫ p) z) h0
    have eFE : E.formOrd η = ∑ j : J, Scheme.ord (H : Y.functionField) (w j) * t j + Fo := by
      have hAform : E'.formOrd (ratPull p s n η) = E.formOrd η := hA.2 η hη
      rw [← hAform, hHη, E'.formOrd_smul hnY h0, hMH]
    have egE : E.ord g = ∑ j : J, Scheme.ord (fnPull s g : Y.functionField) (w j) * t j := by
      rw [← hA.1 g, hMg]
    have efE : E.ord f = ∑ j : J, Scheme.ord (fnPull s f : Y.functionField) (w j) * t j := by
      rw [← hA.1 f, hMf]
    have eFj : ∀ j, (Es j).formOrd η = Scheme.ord (H : Y.functionField) (w j) := fun j => by
      have hAform : (F j).formOrd (ratPull p s n η) = (Es j).formOrd η := (hAj j).2 η hη
      rw [← hAform, hHη, (F j).formOrd_smul hnY h0,
        DivOver.formOrd_formOf_eq_zero ((hc.spec j j.2).mem_open U.isOpen hyU) (hF j) hc.frame, add_zero,
        (hF j).ord_eq]
    have egj : ∀ j, (Es j).ord g = Scheme.ord (fnPull s g : Y.functionField) (w j) := fun j => by
      rw [← (hAj j).1 g, (hF j).ord_eq]
    have efj : ∀ j, (Es j).ord f = Scheme.ord (fnPull s f : Y.functionField) (w j) := fun j => by
      rw [← (hAj j).1 f, (hF j).ord_eq]
    have key : ∑ j : J, (1 + (discrep (Es j) η m g - c * (Es j).ord f)) * (t j : ℚ) =
        1 + (discrep E η m g - c * E.ord f) - (1 + Fo - ∑ j : J, (t j : ℚ)) := by
      simp only [discrep, eFE, egE, efE, eFj, egj, efj]
      push_cast
      rw [Finset.sum_div, Finset.mul_sum]
      have : ∀ j : J, (1 + ((Scheme.ord (H : Y.functionField) (w j) : ℚ) -
          (Scheme.ord (fnPull s g : Y.functionField) (w j) : ℚ) / m -
          c * (Scheme.ord (fnPull s f : Y.functionField) (w j) : ℚ))) * (t j : ℚ) =
          (t j : ℚ) + (Scheme.ord (H : Y.functionField) (w j) : ℚ) * t j -
          (Scheme.ord (fnPull s g : Y.functionField) (w j) : ℚ) * t j / m -
          c * ((Scheme.ord (fnPull s f : Y.functionField) (w j) : ℚ) * t j) := fun j => by ring
      rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        Finset.sum_add_distrib]
      ring
    refine ⟨J, inferInstance, Es, t, fun j => ⟨?_, ?_, htn j⟩, fun h0' => ?_, fun ⟨j0, hj0⟩ => ?_⟩
    · refine Set.mem_biUnion (x := w j) ⟨(hc.mem _ (hc.spec j j.2) (hc.coheight j j.2)).2 ⟨j, j.2, rfl⟩,
        hc.coheight j j.2⟩ fun a => (hEs j a).trans (hF j _)
    · intro a ha
      refine (hEs j a).2 ((hF j _).2 (regAt_of_specializes (hc.spec j j.2) ?_))
      exact GlobalTheory.Cartier.PullDominant.regAt_map s (regAt_of_specializes hyx ha)
    · have hs0 : ∑ j : J, (1 + (discrep (Es j) η m g - c * (Es j).ord f)) * (t j : ℚ) = 0 :=
        Finset.sum_eq_zero fun j _ => by rw [h0' j]; simp
      have ht0 : ∑ j : J, (t j : ℚ) = 0 := Finset.sum_eq_zero fun j _ => by rw [h0' j]; simp
      have : (0 : ℚ) ≤ Fo := by exact_mod_cast hnn
      linarith
    · have h1 : 1 ≤ ∑ j : J, t j := by
        have := Finset.single_le_sum (f := t) (fun j _ => htn j) (Finset.mem_univ j0)
        have : 1 ≤ t j0 := by have := htn j0; omega
        omega
      have h1q : (1 : ℚ) ≤ ∑ j : J, (t j : ℚ) := by exact_mod_cast h1
      have hlq : (∑ j : J, (t j : ℚ)) - 1 ≤ Fo := by exact_mod_cast hlog
      rw [key]
      linarith
  refine ⟨fun hS E hE => ?_, fun hS E hE => ?_⟩
  · obtain ⟨ι, _, Es, t, hEs, h0, h1⟩ := core E hE
    by_cases hall : ∀ j, t j = 0
    · have := h0 hall
      linarith
    · push_neg at hall
      have hpos : 0 < ∑ j, (1 + (discrep (Es j) η m g - c * (Es j).ord f)) * (t j : ℚ) := by
        obtain ⟨j0, hj0⟩ := hall
        refine Finset.sum_pos' (fun j _ => mul_nonneg ?_ ?_) ⟨j0, Finset.mem_univ _, mul_pos ?_ ?_⟩
        · have := hS (Es j) (hEs j).1 (hEs j).2.1; linarith
        · exact_mod_cast (hEs j).2.2
        · have := hS (Es j0) (hEs j0).1 (hEs j0).2.1; linarith
        · have : 0 < t j0 := lt_of_le_of_ne (hEs j0).2.2 (Ne.symm hj0)
          exact_mod_cast this
      have := h1 hall
      linarith
  · obtain ⟨ι, _, Es, t, hEs, h0, h1⟩ := core E hE
    by_cases hall : ∀ j, t j = 0
    · have := h0 hall
      linarith
    · push_neg at hall
      have hnn : 0 ≤ ∑ j, (1 + (discrep (Es j) η m g - c * (Es j).ord f)) * (t j : ℚ) := by
        refine Finset.sum_nonneg fun j _ => mul_nonneg ?_ ?_
        · have := hS (Es j) (hEs j).1 (hEs j).2.1; linarith
        · exact_mod_cast (hEs j).2.2
      have := h1 hall
      linarith

end GlobalTheory.PairStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramPosDefL2LeSupOfLinIndep
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
open scoped ComplexOrder
namespace GlobalTheory.HSAmp

theorem gram_posDef_and_l2_le_sup_bound : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p) (ω : ∀ σ, VolDens p σ D) (a b : ℤ) (ι : Type) [Fintype ι] [DecidableEq ι] (f : ι → X.functionField), (∀ i, f i ∈ P.H a b) → LinearIndependent ℤ f → IsFam (fun σ => (ω σ).meas) (vals P a b f) ∧ (gram (fun σ => (ω σ).meas) (vals P a b f)).PosDef ∧ ∀ (c : ι → ℂ) (M : ℝ), (∀ σ y, cmb (vals P a b f) c σ y ≤ M) → l2 (fun σ => (ω σ).meas) (vals P a b f) c ≤ (∑ᶠ σ, ((ω σ).meas Set.univ).toReal) * M := by
  intro k _ X _ p D hX hG P ω a b ι _ _ f hf hli
  haveI : Finite (k →+* ℂ) := hX.finite_emb
  have hfin := fun σ => _root_.GlobalTheory.HSAmp.volDens_meas_finite_openPos k X p D hX hG σ (ω σ)
  obtain ⟨hprod, hnu⟩ := _root_.GlobalTheory.HSAmp.continuous_val_and_bounded k X p D hX P a b
  have hfam : IsFam (fun σ => (ω σ).meas) (vals P a b f) := by
    refine ⟨inferInstance, fun σ i j => ?_⟩
    haveI := (hfin σ).1
    obtain ⟨C₁, hC₁⟩ := (hnu (f i) (hf i)).2
    obtain ⟨C₂, hC₂⟩ := (hnu (f j) (hf j)).2
    refine Integrable.of_bound (hprod σ _ (hf i) _ (hf j)).aestronglyMeasurable (C₁ * C₂)
      (Filter.Eventually.of_forall fun y => ?_)
    have h0 : 0 ≤ P.nu a b σ y (f j) := (norm_val P a b σ y (f j)) ▸ norm_nonneg _
    simp only [vals, norm_mul, Complex.norm_conj, norm_val]
    exact mul_le_mul (hC₁ σ y) (hC₂ σ y) h0 (le_trans ((norm_val P a b σ y (f i)) ▸ norm_nonneg _) (hC₁ σ y))
  have hl2 := gram_isHermitian_and_l2_eq_quadratic_form (S := k →+* ℂ) (Y := fun σ => CxPts p σ) (ι := ι) (fun σ => (ω σ).meas) (vals P a b f) hfam
  have hcont : ∀ (c : ι → ℂ) σ, Continuous (cmb (vals P a b f) c σ) := by
    intro c σ
    have e : cmb (vals P a b f) c σ = fun y => (∑ i, ∑ j, (c i * (starRingEnd ℂ) (c j)) *
        (vals P a b f σ y i * (starRingEnd ℂ) (vals P a b f σ y j))).re := by
      funext y
      have h1 := Complex.mul_conj' (∑ i, c i * vals P a b f σ y i)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_mul_sum] at h1
      simp only [cmb]
      rw [← Complex.ofReal_re (‖_‖ ^ 2), Complex.ofReal_pow, ← h1]
      congr 1
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [map_mul]; ring
    rw [e]
    exact Complex.continuous_re.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      continuous_const.mul (hprod σ _ (hf i) _ (hf j)))
  haveI : Fintype (k →+* ℂ) := Fintype.ofFinite _
  refine ⟨hfam, _root_.GlobalTheory.HSAmp.gram_posDef (k →+* ℂ) (fun σ => CxPts p σ) ι (fun σ => (ω σ).meas) (vals P a b f) hfam
    fun c hc => ?_, fun c M hM => ?_⟩
  · rw [l2, finsum_eq_sum_of_fintype] at hc
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun σ _ =>
      integral_nonneg fun y => sq_nonneg ‖∑ i, c i * vals P a b f σ y i‖).1 hc
    refine _root_.GlobalTheory.HSAmp.linearIndependent_vals k X p D hX P a b ι f hf hli c fun σ y => ?_
    haveI := (hfin σ).2
    have hae := (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg ‖∑ i, c i * vals P a b f σ y i‖)
      ((hl2.2 c).1 σ)).1 (hz σ (Finset.mem_univ _))
    have hall := (Continuous.ae_eq_iff_eq _ (hcont c σ) continuous_const).1 hae
    have hy : ‖∑ i, c i * vals P a b f σ y i‖ ^ 2 = 0 := congrFun hall y
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hy)
  · rw [l2, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.sum_mul]
    refine Finset.sum_le_sum fun σ _ => ?_
    haveI := (hfin σ).1
    calc ∫ y, cmb (vals P a b f) c σ y ∂(ω σ).meas ≤ ∫ _y, M ∂(ω σ).meas :=
          integral_mono ((hl2.2 c).1 σ) (integrable_const M) fun y => hM σ y
      _ = ((ω σ).meas Set.univ).toReal * M := by
          rw [integral_const, smul_eq_mul, measureReal_def]

end GlobalTheory.HSAmp
end

