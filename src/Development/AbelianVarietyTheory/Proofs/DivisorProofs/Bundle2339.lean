module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2237
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2146
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2164
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1962
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulIncl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBigCellSectionOverBasicOpenInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2231
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2278
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2286

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertFrameOfExponential
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.ExpFrame

theorem exists_isFactorAH_frame_of_isExp : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)), IsExp (𝟙 (Sp ℂ)) e → ∀ (M : LB A.left), M.IsLB → ∃ (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), (∀ z, u.ex z = e z) ∧ GlobalTheory.TorusRM.IsFactorAH u Hm χ := by
  intro A _ _ g hA hg e he M hM
  obtain ⟨Λ, hd, hf, hk⟩ := GlobalTheory.ExpKernel.kernel_isFullLattice (Sp ℂ) A g hA hg (𝟙 (Sp ℂ)) e he
  obtain ⟨L₀, u₀, hu₀⟩ := GlobalTheory.exists_holUnif_of_isExp A g e Λ he hd hf hk
  obtain ⟨u, Hm, χ, hu, hAH⟩ := GlobalTheory.exists_isFactorAH_frame_of_unif A hA L₀ g u₀ M hM
  exact ⟨u, Hm, χ, fun z => by rw [hu, hu₀], hAH⟩

end GlobalTheory.ExpFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeSemiAbelianCubicalPolarisedData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_baseChange_semiAbelian_data : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (P : GlobalTheory.UU.CP G) (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), GlobalTheory.LN.CDvr R' → FinExt ρ → ∃ (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (P₁ : GlobalTheory.UU.CP G₁) (A₁ : PolAV (Sp (FractionRing R'))) (gen₁ : (Over.pullback (jK R')).obj G₁ ≅ A₁.A), IsSemiAbelian G₁ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ IsMonHom gen₁.hom ∧ LBIso (A₁.L.pull gen₁.hom.left) (P₁.L.L.pull (pullback.fst G₁.hom (jK R'))) ∧ LBIso (abelian₂ G₁ P₁.L.L) ((abelian₂ G P.L.L).pull β₂) := by
  intro R _ _ _ _ G _ _ hG P A gen hmon hext R' _ _ _ ρ _ hfin
  have hinj : Function.Injective ρ := hfin.2.1

  have gpG₁ : IsGrpPullback ((Over.pullback (spMap ρ)).obj G) G (spMap ρ) (pullback.fst G.hom (spMap ρ)) :=
    isGrpPullback_pullback G (spMap ρ)
  obtain ⟨β₂, hsq, hlam⟩ := lbIso_lam_pull_of_isGrpPullback _ _ (spMap ρ) G ((Over.pullback (spMap ρ)).obj G) _ gpG₁

  obtain ⟨rig, hr, c, s, h₁, h₂, h₃, -⟩ := GlobalTheory.UU.exists_isCPMap (hw := pullback.condition) P
    (GlobalTheory.UU.toBase_mul_pullback G (spMap ρ)) _ (pull_isLB P.L.isLB _) _ (GlobalTheory.UU.pullIso_isGen P.L.isLB _)
  let P₁ : GlobalTheory.UU.CP ((Over.pullback (spMap ρ)).obj G) :=
    ⟨⟨P.L.L.pull (pullback.fst G.hom (spMap ρ)), rig, pull_isLB P.L.isLB _, hr⟩, c, s, h₁, h₂, h₃⟩

  obtain ⟨A', gA, pA, dA, mA, tA⟩ := GlobalTheory.firstFiveLaws.1.polBaseChange _ _ (spMap (GlobalTheory.ArcPull.fracMap hinj)) A
  have gpA : IsGrpPullback A'.A A.A (spMap (GlobalTheory.ArcPull.fracMap hinj)) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  haveI := hmon
  haveI : IsMonHom gen.symm.hom := by show IsMonHom gen.inv; infer_instance
  have gpGen : IsGrpPullback A.A G (jK R) (gen.inv.left ≫ pullback.fst G.hom (jK R)) :=
    ((isGrpPullback_of_iso gen.symm).comp (isGrpPullback_pullback G (jK R))).congr (Category.id_comp _) rfl
  have sq : spMap (GlobalTheory.ArcPull.fracMap hinj) ≫ jK R = jK R' ≫ spMap ρ :=
    (GlobalTheory.ArcPull.fracMap_sq hinj).symm.trans (Category.id_comp _)
  have gp' : IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)) G
      (spMap (GlobalTheory.ArcPull.fracMap hinj) ≫ jK R)
      (pullback.fst ((Over.pullback (spMap ρ)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap ρ)) :=
    ((isGrpPullback_pullback ((Over.pullback (spMap ρ)).obj G) (jK R')).comp gpG₁).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpGen)
  refine ⟨(Over.pullback (spMap ρ)).obj G, inferInstance, inferInstance, pullback.fst G.hom (spMap ρ), β₂, P₁, A', eA,
    IsSemiAbelian.pullback _ G hG, gpG₁, hsq, mE, ?_, ?_⟩
  · refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB (pull_isLB P.L.isLB _) _)
      ((LBIso.symm tA).chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A'.L _ _ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    have hgi : gen.inv.left ≫ gen.hom.left = 𝟙 _ := by
      rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ gen.inv.left)
      (chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => gen.hom.left) _ _ fun _ => ?_)
      (chartPullLinComb P.L.L (pullback.fst G.hom (spMap ρ))
        (fun _ => pullback.fst ((Over.pullback (spMap ρ)).obj G).hom (jK R'))
        (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) hext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [← heA]; simp only [Category.assoc]
  · have hL := P.L.isLB
    have h := hlam P.L.L (P.L.L.pull (pullback.fst G.hom (spMap ρ))) _ (abelian₂ G P.L.L) (𝟙 _) hL (pull_isLB hL _)
      (LB.isLB_linComb hL _ _) (lbIso_refl (pull_isLB hL _)) (LBIso.symm (lbIso_pull_id (LB.isLB_linComb hL _ _)))
    rwa [Category.comp_id] at h

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseGlobalUnitAbelianSchemeBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TwoTors

set_option autoImplicit false

namespace GlobalTheory.CharKer

theorem exists_pullTop_of_isPullback : ∀ {S X : Scheme.{0}} (A Z : Over S) [GrpObj A], IsAbelianScheme A → ∀ (p : X ⟶ A.left) (q : X ⟶ Z.left), IsPullback p q A.hom Z.hom → ∀ D : Γ(X, ⊤)ˣ, ∃ c : Γ(Z.left, ⊤)ˣ, GlobalTheory.CharKer.pullTop q c = D := by
  intro S X A Z _ hA p q h D
  obtain ⟨c, hc⟩ := exists_pullTop_snd A Z hA (pullTop h.isoPullback.inv D)
  refine ⟨c, ?_⟩
  have h₁ : h.isoPullback.hom ≫ (snd A Z).left = q := h.isoPullback_hom_snd
  have h₂ := congrArg (pullTop h.isoPullback.hom) hc
  rw [← h₁]
  refine (pullTop_pullTop_comp _ _ c).symm.trans (h₂.trans ?_)
  rw [pullTop_pullTop_comp, Iso.hom_inv_id]
  rfl

end GlobalTheory.CharKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBigCellSectionOverBasicOpenInteriorStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bigCellSection_over_basicOpen_interior : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)), IsCell TF Z U e v W k L N → ∀ (a : Γ(TF.Y.X, U.1)), TF.Y.X.basicOpen a ≤ LogKS.interior TF.Y ⊓ barComp TF.Y Z ⊓ (TF.X.F.M k).U → (∃ w : Y₀ TF.X Z, w ∈ W ∧ w ∈ U₀ TF.X Z ∧ toBase TF Z w ∈ TF.Y.X.basicOpen a) → ∃ z₁ : Sp (Localization.Away (MvPolynomial.C a : MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1))) ⟶ Y₀ TF.X Z, ⊤ ≤ z₁ ⁻¹ᵁ U₀ TF.X Z ∧ (∃ hU : ⊤ ≤ (z₁ ≫ toBase TF Z) ⁻¹ᵁ U.1, ∀ r, ev (z₁ ≫ toBase TF Z) U.1 hU r = algebraMap (MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) (Localization.Away (MvPolynomial.C a : MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1))) (MvPolynomial.C r)) ∧ ((z₁ ⁻¹ᵁ W : TopologicalSpace.Opens _) : Set (Sp (Localization.Away (MvPolynomial.C a : MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1))))).Nonempty ∧ ∀ (S : Type) [CommRing S] (ψ : Localization.Away (MvPolynomial.C a : MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) →+* S) (hW : ⊤ ≤ (spMap ψ ≫ z₁) ⁻¹ᵁ W) (σ : E →+* ℂ), ∃ b : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, (∀ i j, i < j → b i j = 0) ∧ ∀ i j, ψ (algebraMap (MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) _ (if h : i < j then MvPolynomial.X ⟨σ, ⟨(i, j), h⟩⟩ else if i = j then 1 else 0)) = ∑ m, b i m * ev (spMap ψ ≫ z₁) W hW ((L σ * N σ) m j) := by
  first | exact @GlobalTheory.LogPole.exists_cell_section_away | exact GlobalTheory.LogPole.exists_cell_section_away | (intros; apply GlobalTheory.LogPole.exists_cell_section_away <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBundleExtensionTranslateOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum
open GlobalTheory.CechPic

theorem exists_ext_translate : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (L : LB ((Over.pullback (jK R)).obj G).left) (PP : LB (G2 G).left), L.IsLB → ExtLam G L PP →
    ∀ (O : G.left.Opens) (N : LB O.toScheme), N.IsLB →
    LBIso (N.pull (pullback.fst O.ι (pullback.fst G.hom (jK R)))) (L.pull (pullback.snd O.ι (pullback.fst G.hom (jK R)))) →
    ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, ∃ N' : LB ((𝟙 G * (toUnit G ≫ a)).left ⁻¹ᵁ O).toScheme, N'.IsLB ∧
      LBIso (N'.pull (pullback.fst ((𝟙 G * (toUnit G ≫ a)).left ⁻¹ᵁ O).ι (pullback.fst G.hom (jK R))))
        (L.pull (pullback.snd ((𝟙 G * (toUnit G ≫ a)).left ⁻¹ᵁ O).ι (pullback.fst G.hom (jK R)))) := by
  intro R _ _ G _ _ L PP hL hExt O N hN hNL a
  have hPP : PP.IsLB := hExt.1
  let GK := (Over.pullback (jK R)).obj G
  let J := pullback.fst G.hom (jK R)
  let T := (𝟙 G * (toUnit G ≫ a)).left
  let V := T ⁻¹ᵁ O
  let σ := (lift (𝟙 G) (toUnit G ≫ a)).left
  obtain ⟨N', hN', hc⟩ := cls_surj (pull (T ∣_ O) (cls N hN) - pull (V.ι ≫ σ) (cls PP hPP))
  refine ⟨N', hN', ?_⟩
  let p₁ := pullback.fst V.ι J
  let p₂ := pullback.snd V.ι J
  rw [← cls_eq_iff (pull_isLB hN' _) (pull_isLB hL _), cls_pull hN', cls_pull hL, hc]

  have hNL' : pull (pullback.fst O.ι J) (cls N hN) = pull (pullback.snd O.ι J) (cls L hL) := by
    rw [← cls_pull hN, ← cls_pull hL]
    exact (cls_eq_iff (pull_isLB hN _) (pull_isLB hL _)).2 hNL

  obtain ⟨κ₂, hκ, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ (jK R) G GK J (isGrpPullback_pullback G (jK R))
  have hLamc : lam (cls L hL) (fst GK GK) (snd GK GK) = pull κ₂ (cls PP hPP) := by
    rw [← cls_cube_two hL (fst GK GK) (snd GK GK) (LB.isLB_linComb hL _ _), ← cls_pull hPP κ₂ (pull_isLB hPP _)]
    exact (cls_eq_iff (LB.isLB_linComb hL _ _) (pull_isLB hPP _)).2 (hExt.2 κ₂ hκ)

  have hw : p₁ ≫ V.ι ≫ G.hom = p₂ ≫ GK.hom ≫ jK R := by
    rw [← Category.assoc, pullback.condition, Category.assoc]
    exact congrArg (p₂ ≫ ·) pullback.condition
  let Ty : Over (Sp (FractionRing R)) := Over.mk (p₂ ≫ GK.hom)
  let y : Ty ⟶ GK := Over.homMk p₂ rfl
  have haw : a.left ≫ G.hom = 𝟙 _ := by simpa using Over.w a
  let aK : 𝟙_ (Over (Sp (FractionRing R))) ⟶ GK :=
    Over.homMk (pullback.lift (jK R ≫ a.left) (𝟙 _) (by rw [Category.assoc, haw]; simp)) (pullback.lift_snd _ _ _)
  let aY : Ty ⟶ GK := toUnit Ty ≫ aK
  have hzero : ∀ (z : 𝟙_ (Over (Sp (FractionRing R))) ⟶ GK) (c : Pic GK.left), pull (toUnit Ty ≫ z).left c = 0 := by
    intro z c
    rw [Over.comp_left, pull_comp, GlobalTheory.DualOpen.pic_sp_local_eq_zero (FractionRing R) (pull z.left c), map_zero]
  have haY : aY.left ≫ J = p₁ ≫ V.ι ≫ G.hom ≫ a.left := by
    have : aY.left = (p₂ ≫ GK.hom) ≫ aK.left := rfl
    rw [this, Category.assoc, show aK.left ≫ J = jK R ≫ a.left from pullback.lift_fst _ _ _, ← Category.assoc,
      ← Category.assoc, ← Category.assoc]
    simp only [Category.assoc]
    rw [← Category.assoc p₁, ← Category.assoc (p₁ ≫ V.ι), Category.assoc p₁, hw]
    simp only [Category.assoc]

  have hsq : (lift y aY).left ≫ κ₂ = p₁ ≫ V.ι ≫ σ := by
    apply pullback.hom_ext
    · show ((lift y aY).left ≫ κ₂) ≫ (fst G G).left = (p₁ ≫ V.ι ≫ σ) ≫ (fst G G).left
      rw [Category.assoc, hκ.1, ← Category.assoc, ← Over.comp_left, lift_fst]
      simp only [Category.assoc, σ, ← Over.comp_left, lift_fst, Over.id_left, Category.comp_id]
      exact pullback.condition.symm
    · show ((lift y aY).left ≫ κ₂) ≫ (snd G G).left = (p₁ ≫ V.ι ≫ σ) ≫ (snd G G).left
      rw [Category.assoc, hκ.2, ← Category.assoc, ← Over.comp_left, lift_snd, haY]
      show p₁ ≫ V.ι ≫ G.hom ≫ a.left = (p₁ ≫ V.ι ≫ (lift (𝟙 G) (toUnit G ≫ a)).left) ≫ (snd G G).left
      rw [Category.assoc, Category.assoc, ← Over.comp_left, lift_snd, Over.comp_left, Over.toUnit_left]
  have hlam : pull (p₁ ≫ V.ι ≫ σ) (cls PP hPP) = @id (Pic (pullback V.ι J)) (pull (y * aY).left (cls L hL)) - pull p₂ (cls L hL) := by
    have h := congrArg (pull (lift y aY).left) hLamc
    rw [pull_lam, lift_fst, lift_snd, ← pull_comp, hsq] at h
    rw [← h, lam, hzero, show (1 : Ty ⟶ GK) = toUnit Ty ≫ 1 from (MonObj.comp_one _).symm, hzero]
    simp only [sub_zero, add_zero]
    rfl

  let u : Over.mk (Ty.hom ≫ jK R) ⟶ G := Over.homMk (p₁ ≫ V.ι) (by simpa [Ty] using hw)
  have hmul : (y * aY).left ≫ J = p₁ ≫ V.ι ≫ T := by
    have e := (isGrpPullback_pullback G (jK R)).2 Ty y aY u (u ≫ toUnit G ≫ a) (pullback.condition (f := V.ι) (g := J))
      (by rw [haY, Over.comp_left, Over.comp_left, Over.toUnit_left]; show (p₁ ≫ V.ι) ≫ _ = _; simp only [Category.assoc])
    have e' : u * (u ≫ toUnit G ≫ a) = u ≫ (𝟙 G * (toUnit G ≫ a)) := by rw [MonObj.comp_mul, Category.comp_id]
    rw [← e, e', Over.comp_left]
    exact Category.assoc _ _ _
  have hq : (p₁ ≫ (T ∣_ O)) ≫ O.ι = (y * aY).left ≫ J := by
    rw [Category.assoc, morphismRestrict_ι, hmul]
  have hN2 := congrArg (pull (pullback.lift _ _ hq)) hNL'
  rw [← pull_comp, ← pull_comp, pullback.lift_fst, pullback.lift_snd] at hN2
  rw [map_sub, ← pull_comp, ← pull_comp, hN2, hlam]
  exact sub_sub_cancel _ _

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCarriesTransportUniformisingIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.SecTransport

open TopologicalSpace Opposite

variable {X Y : Scheme.{0}} {L : LB X} {M : LB Y} {β : Y ⟶ X}

lemma le_pull (j : Fin 1 → L.ι) (i : M.ι) :
    LB.wchart L (fun _ : Fin 1 => β) j ⊓ M.U i ≤ (L.pull β).U (fun _ => j 0) ⊓ M.U i :=
  fun _ hy => ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy.1 0, hy.2⟩

lemma le_one (j : Fin 1 → L.ι) (i : M.ι) :
    LB.wchart L (fun _ : Fin 1 => β) j ⊓ M.U i ≤ LB.wchart M (fun _ : Fin 1 => 𝟙 Y) (fun _ => i) :=
  fun _ hy => Set.mem_iInter.2 fun _ => hy.2

def piece (ℓ : LB.Iso M (L.pull β)) (c : Γ(Y, ⊤)) (k : ℕ) (σ' : H0 M k) (j : Fin 1 → L.ι) (i : M.ι) :
    Γ(Y, LB.wchart L (fun _ : Fin 1 => β) j ⊓ M.U i) :=
  (Y.presheaf.map (homOfLE le_top).op).hom c * ((res (le_pull j i) (ℓ.s (fun _ => j 0, i))) ^ k).val *
    (Y.presheaf.map (homOfLE (le_one j i)).op).hom (σ'.f (fun _ => i))

theorem gs_piece (ℓ : LB.Iso M (L.pull β)) (c : Γ(Y, ⊤)) (k : ℕ) (σ' : H0 M k) (j : Fin 1 → L.ι) (i : M.ι)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (hz : r z ∈ LB.wchart L (fun _ : Fin 1 => β) j ⊓ M.U i) :
    gs r z _ (piece ℓ c k σ' j i) = gs r z ⊤ c * (gw ℓ r z (j 0) i ^ k).val *
      gs r z (LB.wchart M (fun _ : Fin 1 => 𝟙 Y) (fun _ => i)) (σ'.f (fun _ => i)) := by
  exact (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·)
    (gs_res r z le_top hz c) ((gs_unit r z _ hz _).trans (congrArg Units.val ((map_pow _ _ _).trans
      (congrArg (· ^ k) (gm_res r z (le_pull j i) hz _)))))))
    (gs_res r z (le_one j i) hz _))

theorem indep (hL : L.IsLB) (ℓ : LB.Iso M (L.pull β)) (hℓ : PGen ℓ) (k : ℕ) (σ' : H0 M k) {Z : Scheme.{0}}
    (r : Z ⟶ Y) (z : Z) (j₀ : L.ι) (i i' : M.ι) (hj : β (r z) ∈ L.U j₀) (hi : r z ∈ M.U i) (hi' : r z ∈ M.U i') :
    (gw ℓ r z j₀ i ^ k).val * gs r z (LB.wchart M (fun _ : Fin 1 => 𝟙 Y) (fun _ => i)) (σ'.f (fun _ => i)) =
      (gw ℓ r z j₀ i' ^ k).val * gs r z (LB.wchart M (fun _ : Fin 1 => 𝟙 Y) (fun _ => i')) (σ'.f (fun _ => i')) := by
  have e1 := hℓ Z r z j₀ j₀ i i' hj hj hi hi'
  rw [gm_self hL (r ≫ β) z hj, _root_.one_mul] at e1
  have hm : r z ∈ LB.wchart M (fun _ : Fin 1 => 𝟙 Y) (fun _ => i) := Set.mem_iInter.2 fun _ => hi
  have hm' : r z ∈ LB.wchart M (fun _ : Fin 1 => 𝟙 Y) (fun _ => i') := Set.mem_iInter.2 fun _ => hi'
  have e2 := sec_trans σ' r z hm hm'
  have e3 : trF (L := M) (fun _ : Fin 1 => 𝟙 Y) (fun _ => (k : ℤ)) r z (fun _ => i) (fun _ => i') =
      gm r z _ (M.g i i') ^ k := by
    simp only [trF, Fin.prod_univ_one, Category.comp_id, zpow_natCast]
  rw [e2, e3, ← _root_.mul_assoc, ← Units.val_mul, e1, mul_pow, inv_pow,
    _root_.mul_comm ((gm r z _ (M.g i i') ^ k)⁻¹), _root_.mul_assoc, _root_.inv_mul_cancel, _root_.mul_one]

theorem exists_transport (hL : L.IsLB) (hM : M.IsLB) (ℓ : LB.Iso M (L.pull β)) (hℓ : ℓ.IsGen) (c : Γ(Y, ⊤))
    (k : ℕ) (σ' : H0 M k) : ∃ σ : SecK L β k, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J J', Good L z J → Good M z J' →
      sval σ r z J = gs r z ⊤ c * (gw ℓ r z (J (r ≫ β)) (J' r) ^ k).val * sval σ' r z J' := by
  have hP := (isGen_iff ℓ).1 hℓ
  have glue : ∀ j : Fin 1 → L.ι, ∃ a : Γ(Y, LB.wchart L (fun _ : Fin 1 => β) j), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z)
      (i : M.ι), r z ∈ LB.wchart L (fun _ : Fin 1 => β) j → r z ∈ M.U i →
      gs r z _ a = gs r z ⊤ c * (gw ℓ r z (j 0) i ^ k).val *
        gs r z (LB.wchart M (fun _ : Fin 1 => 𝟙 Y) (fun _ => i)) (σ'.f (fun _ => i)) := by
    intro j
    obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' (fun i : M.ι => LB.wchart L (fun _ : Fin 1 => β) j ⊓ M.U i)
      (LB.wchart L (fun _ : Fin 1 => β) j) (fun i => homOfLE inf_le_left)
      (fun y hy => Opens.mem_iSup.2 ⟨(exists_chart hM y).choose, hy, (exists_chart hM y).choose_spec⟩)
      (fun i => piece ℓ c k σ' j i) (fun i i' => fn_ext fun y hy => by
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        rw [gs_piece ℓ c k σ' j i (𝟙 Y) y hy.1, gs_piece ℓ c k σ' j i' (𝟙 Y) y hy.2, _root_.mul_assoc, _root_.mul_assoc]
        exact congrArg _ (indep hL ℓ hP k σ' (𝟙 Y) y (j 0) i i' (Set.mem_iInter.1 hy.1.1 0) hy.1.2 hy.2.2))
    refine ⟨a, fun Z r z i h₁ h₂ => ?_⟩
    have hz : r z ∈ LB.wchart L (fun _ : Fin 1 => β) j ⊓ M.U i := ⟨h₁, h₂⟩
    exact (gs_res r z inf_le_left hz a).symm.trans ((congrArg (gs r z _) (ha i)).trans (gs_piece ℓ c k σ' j i r z hz))
  choose a ha using glue
  refine ⟨⟨a, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z J J' hJ hJ' => ?_⟩
  · obtain ⟨i, hi⟩ := exists_chart hM y
    refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2)))
      (gs_res (𝟙 Y) y _ hy _))).symm)
    change gs (𝟙 Y) y (LB.wchart L (fun _ : Fin 1 => β) j) (a j) =
      _ * gs (𝟙 Y) y (LB.wchart L (fun _ : Fin 1 => β) j') (a j')
    rw [ha j _ (𝟙 Y) y i hy.1 hi, ha j' _ (𝟙 Y) y i hy.2 hi]
    have e1 := hP Y (𝟙 Y) y (j 0) (j' 0) i i (Set.mem_iInter.1 hy.1 0) (Set.mem_iInter.1 hy.2 0) hi hi
    rw [gm_self hM (𝟙 Y) y hi, inv_one, _root_.mul_one] at e1
    rw [e1]
    simp only [Fin.prod_univ_one, zpow_natCast, mul_pow, Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  · rw [sval_of σ' r z J' (fun _ => J' r) (fun _ => by rw [Category.comp_id])]
    exact ha _ Z r z (J' r) (hJ.mem (fun _ : Fin 1 => β) r) (hJ' r)

end GlobalTheory.Mum.SecTransport

namespace GlobalTheory.Mum

theorem Trait.exists_carries : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R))
    (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (u : W)
    (σ' : H0 T.U.LG.L k), ∃ σ'' : SecK C.P.L.L T.β k, T.Carries u σ' σ'' := by
  intro R _ _ _ D C W _ _ _ T k u σ'
  exact SecTransport.exists_transport C.P.L.isLB T.U.LG.isLB T.ℓ T.ℓ_gen (scal T.G.hom u) k σ'

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorDetLieEigenpartsToroidal
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EigDiv

theorem exists_eigFrame_stalk : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (R : Type) [CommRing R] [IsLocalRing R] (p : Sp R ⟶ X₀ TF.Y Z), ∃ (φ : c.F →+* R) (_ : GlobalTheory.ShFam.EigFrame TF.Y φ (p ≫ (barComp TF.Y Z).ι)), p ≫ s₀ TF.Y Z = spMap φ := by
  intro E _ _ _ H Dw l Xo c TF Z R _ _ p
  have hid : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
  haveI : IsIso (spMap (RingHom.id c.F)) := by rw [hid]; infer_instance
  haveI : IsIso (GlobalTheory.Toroidal.genι TF.Y) := inferInstanceAs (IsIso (pullback.fst TF.Y.s (spMap (RingHom.id c.F))))
  have hs : inv (GlobalTheory.Toroidal.genι TF.Y) ≫ GlobalTheory.Toroidal.genStr TF.Y = TF.Y.s := by
    rw [IsIso.inv_comp_eq]
    calc GlobalTheory.Toroidal.genStr TF.Y = GlobalTheory.Toroidal.genStr TF.Y ≫ spMap (RingHom.id c.F) := by rw [hid, Category.comp_id]
      _ = GlobalTheory.Toroidal.genι TF.Y ≫ TF.Y.s := pullback.condition.symm
  let x : Sp R ⟶ GlobalTheory.Toroidal.gen TF.Y := (p ≫ (barComp TF.Y Z).ι) ≫ inv (GlobalTheory.Toroidal.genι TF.Y)
  let φ : c.F →+* R := (Spec.preimage (p ≫ s₀ TF.Y Z)).hom
  have hφ : spMap φ = p ≫ s₀ TF.Y Z := Spec.map_preimage _
  have hx : x ≫ GlobalTheory.Toroidal.genStr TF.Y = spMap φ := by
    rw [hφ, Category.assoc, hs, Category.assoc]
  obtain ⟨f⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c c.F (RingHom.id c.F) TF.Y R φ x hx
  have e : x ≫ GlobalTheory.Toroidal.genι TF.Y = p ≫ (barComp TF.Y Z).ι := by
    simp only [x, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact ⟨φ, e ▸ f, hφ.symm⟩

theorem ratio_mem {K : Type} [Field K] (S : Subgroup Kˣ) {ι : Type} [Fintype ι] (u v w : ι → Kˣ)
    (h : ∀ τ, (v τ : K) = w τ * u τ) (hw : ∀ τ, w τ ∈ S) (a : ι → ℤ) :
    (∏ τ, u τ ^ (-a τ)) / (∏ τ, v τ ^ (-a τ)) ∈ S := by
  have hv : ∀ τ, v τ = w τ * u τ := fun τ => Units.ext (by rw [Units.val_mul]; exact h τ)
  rw [← Finset.prod_div_distrib]
  refine S.prod_mem fun τ _ => ?_
  have e : u τ / v τ = (w τ)⁻¹ := by rw [hv, div_mul_eq_div_div_swap, div_self', one_div]
  rw [← div_zpow, e]
  exact S.zpow_mem (S.inv_mem (hw τ)) _

theorem exists_div {X : Scheme.{0}} [IsIntegral X] (g : X → X.functionFieldˣ)
    (h : ∀ x, ∃ U : X.Opens, x ∈ U ∧ ∀ y ∈ U, UnitAt y ((g x : X.functionField) / g y)) :
    ∃ D : CartierDiv X, ∀ x, D.IsEqn x (g x) :=
  ⟨show cartierGroup X from ⟨fun x => germOf x (g x), fun x => by
    obtain ⟨U, hx, hU⟩ := h x
    exact ⟨U, hx, g x, fun y hy => germOf_eq_iff.2 (hU y hy)⟩⟩, fun _ => rfl⟩

theorem exists_detDiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)], ∃ (φ₀ : c.F →+* (X₀ TF.Y Z).functionField) (f₀ : GlobalTheory.ShFam.EigFrame TF.Y φ₀ ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι)), (show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ s₀ TF.Y Z = spMap φ₀ ∧ ∀ a : (E →+* ℂ) → ℤ, ∃ D : CartierDiv (X₀ TF.Y Z), CechPic.pull (π₀ TF.X Z) (cls (toLB D) (isLB_toLB D)) = cls (LL₀ TF.X Z fun ix => ix.elim 0 fun x => a x.1) (LB.isLB_pull (TF.X.F.isLB_LL _) _) ∧ ∀ x : X₀ TF.Y Z, ∃ (φ : c.F →+* (X₀ TF.Y Z).presheaf.stalk x) (f : GlobalTheory.ShFam.EigFrame TF.Y φ ((show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ (barComp TF.Y Z).ι)) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (X₀ TF.Y Z).functionField) (d : (E →+* ℂ) → (X₀ TF.Y Z).functionFieldˣ), (show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ s₀ TF.Y Z = spMap φ ∧ (∀ τ, (d τ : (X₀ TF.Y Z).functionField) = (A τ).det) ∧ (∀ τ i, IsCombAtG TF.Y.t ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι) (fun k => spMap (dualMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField)) ≫ f.v τ k) (A τ i) (f₀.v τ i)) ∧ D.IsEqn x (∏ τ, d τ ^ (-a τ)) := by
  intro E _ _ _ H Dw l Xo c TF Z _
  have hloc : ∀ x : X₀ TF.Y Z, IsLocalRing ((X₀ TF.Y Z).presheaf.stalk x) := fun x => inferInstance
  obtain ⟨φ₀, f₀, h₀⟩ := @exists_eigFrame_stalk E _ _ _ H Dw l Xo c TF Z ((X₀ TF.Y Z).presheaf.stalk (genericPoint (X₀ TF.Y Z))) _ (hloc _) ((X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)))
  refine ⟨φ₀, f₀, h₀, fun a => ?_⟩
  choose φx fx hx using fun x : X₀ TF.Y Z => @exists_eigFrame_stalk E _ _ _ H Dw l Xo c TF Z ((X₀ TF.Y Z).presheaf.stalk x) _ (hloc x) ((X₀ TF.Y Z).fromSpecStalk x)
  have hpt : ∀ x : X₀ TF.Y Z, spMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField) ≫
      (X₀ TF.Y Z).fromSpecStalk x = (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) := fun x =>
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes x)
  have hφ : ∀ x, φ₀ = (algebraMap _ (X₀ TF.Y Z).functionField).comp (φx x) := fun x =>
    GlobalTheory.ShFam.EigLoc.spMap_inj (by rw [← h₀, ← hpt x, Category.assoc, hx x]; exact (Spec.map_comp _ _).symm)
  have hFK : ∀ x : X₀ TF.Y Z, ∃ fK : GlobalTheory.ShFam.EigFrame TF.Y φ₀
      ((X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ (barComp TF.Y Z).ι),
      (fx x).IsMap (algebraMap _ (X₀ TF.Y Z).functionField) fK := fun x =>
    (fx x).exists_isMap (algebraMap _ (X₀ TF.Y Z).functionField) (hφ x)
      (by rw [← hpt x]; exact Category.assoc _ _ _)
  let fK := fun x => Classical.choose (hFK x)
  have hfK := fun x => Classical.choose_spec (hFK x)
  let g : ∀ fK : GlobalTheory.ShFam.EigFrame TF.Y φ₀ ((X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ (barComp TF.Y Z).ι),
    (X₀ TF.Y Z).functionFieldˣ := fun fK => ∏ τ, (fK.isUnit_det_co f₀ τ).unit ^ (-a τ)
  have key : ∀ (y : X₀ TF.Y Z) (fK fK' : GlobalTheory.ShFam.EigFrame TF.Y φ₀
      ((X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ (barComp TF.Y Z).ι)),
      (∀ τ, UnitAt y (fK'.co fK τ).det) → UnitAt y ((g fK : (X₀ TF.Y Z).functionField) / g fK') := by
    intro y fK fK' hu
    have := ratio_mem (unitsAt y) (fun τ => (fK.isUnit_det_co f₀ τ).unit) (fun τ => (fK'.isUnit_det_co f₀ τ).unit)
      (fun τ => (fK'.isUnit_det_co fK τ).unit) (fun τ => by
        simp only [IsUnit.unit_spec]
        rw [← Matrix.det_mul, GlobalTheory.ShFam.EigFrame.co_mul]) (fun τ => hu τ) a
    rw [← Units.val_div_eq_div_val (g fK) (g fK')]
    exact this
  obtain ⟨D, hD⟩ := exists_div (fun x => g (fK x)) fun x => by
    obtain ⟨U, hxU, hU⟩ := _root_.GlobalTheory.FrameSpread.unitAt_det_co E H Dw l Xo c TF Z x (φx x) (fx x) (hx x)
    exact ⟨U, hxU, fun y hy => key y _ _ (hU y hy (φx y) (fx y) φ₀ (fK x) (fK y) (hx y) h₀ (hfK x) (hfK y))⟩
  refine ⟨D, ?_, fun x => ⟨φx x, fx x, fun τ => (fK x |>.co f₀ τ).transpose,
    fun τ => (fK x |>.isUnit_det_co f₀ τ).unit, hx x, fun τ => (IsUnit.unit_spec _).trans (Matrix.det_transpose _).symm, fun τ i => ?_, hD x⟩⟩
  · refine GlobalTheory.T.flagSpacePullback_eigenDeterminantDivisor_eq_gradedLines E H Dw l Xo c TF Z φ₀ f₀ a D h₀ fun x φ f fK' hs hm => ?_
    obtain ⟨U, hxU, hU⟩ := _root_.GlobalTheory.FrameSpread.unitAt_det_co E H Dw l Xo c TF Z x φ f hs
    exact (hD x).iff_unitAt.2 (key x _ _ (hU x hxU (φx x) (fx x) φ₀ fK' (fK x) (hx x) h₀ hm (hfK x)))
  · have e : (fK x).v τ = fun k => spMap (dualMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x)
        (X₀ TF.Y Z).functionField)) ≫ (fx x).v τ k := funext (hfK x τ)
    rw [← e]
    exact (fK x).co_spec f₀ τ i

end GlobalTheory.EigDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalStabiliserMulMemBigCellInert
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.DblVac

theorem exists_diag_mul_bigCell : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
      ∃ p ∈ GlobalTheory.DblVac.KD σ W v, p ∈ GlobalTheory.DblVac.PDiag σ W ∧ p * g ∈ GlobalTheory.DblVac.KD σ W v ∧ GlobalTheory.DblVac.BigCell W v (p * g) :=
  GlobalTheory.T.inertPlace_bigCell_stabiliser_of_localRingBigCell_lemma _root_.GlobalTheory.LocalLift.exists_admissible_isUnit_det

end GlobalTheory.DblVac
end

