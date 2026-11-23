module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0073
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveLatticeTwistGenerated
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestFieldFiniteOverPadic

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericSectionsFromIntegralModel
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight

noncomputable section
namespace GlobalTheory.ZH.IntegralCarry
open GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH.ParTranslate GlobalTheory.ThetaSpecialise

section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)

theorem expandsG_extend
    (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (hE : ∀ e, U.ExpandsAt e k σ f) (s : Fam D.toPre F k)
    (hs : FamOf D.toPre F f s) : U.ExpandsG F k (extendSec U F k (genericSec U k σ)) s := by
  have one : ∀ {Y : Scheme.{0}} (π : Y ⟶ Spec (CommRingCat.of F)) (y : Y), gs (𝟙 Y) y ⊤ (scal π (1 : F)) = 1 :=
    fun π y => by simp only [gs_eq _ y ⊤ trivial, scal, map_one]
  refine ⟨1, fun _ => 1, fun _ => σ, fun _ => f, fun _ => hE,
    (secLin_iff_val U.LG.isLB _ _ _ _).2 fun y J hJ => ?_,
    fun α => (secLin_iff_val D.toPre.P.isLB _ _ _ _).2 fun y J hJ => ?_⟩
  · rw [Fin.sum_univ_one, one, _root_.one_mul]
    exact (sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans
      (congrArg (fun q => sval σ q y J) (Category.assoc _ _ _)))
  · rw [Fin.sum_univ_one, one, _root_.one_mul]
    exact (SectionScalarValuation.secScal_sval (hs α) _ y hJ).symm

theorem famOf_zero (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (s : Fam D.toPre F k)
    (hs : FamOf D.toPre F f s) (α : D.toPre.X) (h : ∀ j, (f α).f j = 0) (j) : (s.s α).f j = 0 := by
  refine sec_ext_val (s' := (0 : Fam D.toPre F k).s α) D.toPre.P.isLB (fun y J hJ => ?_) j
  refine (SectionScalarValuation.secScal_sval (hs α) _ y hJ).symm.trans (Eq.trans ?_ (sval_zero' (π := famBase D.toPre F) hJ _).symm)
  exact (gs_eq _ _ _ (hJ.mem _ _) _).trans ((congrArg _ ((congrArg _ (h _)).trans (map_zero _))).trans (map_zero _))

theorem crd_carries (w : W0 U) {J : Type}
    (σ : J → LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (t : J → SecA A F k) (ht : ∀ i, Carries U F k w (t i) (extendSec U F k (genericSec U k (σ i))))
    (a : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj G) (v : J → F)
    (h : Crd _ σ (show Sp F ⟶ G.left from a.left ≫ pullback.fst G.hom (jK R)) v) :
    Crd (LPow A.A A.L (k : ℤ) (TFK (R := R) F)) t (show Sp F ⟶ _ from (ptSecT A.A (a ≫ U.gen.hom)).left) v := by
  obtain ⟨l', c, hl', hv⟩ := h
  obtain ⟨l, rfl⟩ : ∃ l : U.LG.L.ι, l' = fun _ : Fin 1 => l := ⟨l' 0, funext fun i => congrArg l' (Subsingleton.elim _ _)⟩
  let y : Sp F := IsLocalRing.closedPoint F
  let x : Sp F ⟶ G.left := a.left ≫ pullback.fst G.hom (jK R)
  have m : x y ∈ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => l) := (top_le_iff_mem _ _ y).1 hl'
  have m₀ : x y ∈ U.LG.L.U l := mem_wchart.1 m 0
  obtain ⟨J₀, hJ⟩ := GlobalTheory.UT.CoefBasic.exists_good' A.isLB y
  obtain ⟨d, hd⟩ := exists_unit_carries U F k w a l ((top_le_iff_mem x _ y).2 m₀) y J₀ hJ
  obtain ⟨d₀, hd₀⟩ := toStk_onto y d.val
  have hd₁ : d₀ ≠ 0 := fun h0 => by
    have : Nontrivial ((Sp F).presheaf.stalk y) := inferInstance
    rw [h0, map_zero] at hd₀
    exact Units.ne_zero _ hd₀.symm
  let r : Sp F ⟶ (UnifPre.GF (G := G) F).left := (lift (𝟙 (TFK (R := R) F)) a).left
  let r' : Sp F ⟶ (TFK (R := R) F ⊗ A.A).left := (ptSecT A.A (a ≫ U.gen.hom)).left
  have e₀ : r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = a.left :=
    congrArg (fun q => q.left) (lift_snd (𝟙 (TFK (R := R) F)) a)
  have e₁ : (r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) ≫ pullback.fst G.hom (jK R) = x := by
    rw [e₀]
  have m₂ : ((r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) ≫ pullback.fst G.hom (jK R)) y ∈
      U.LG.L.U l := e₁ ▸ m₀
  have m' := hJ.mem (fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) r'
  refine ⟨fun _ : Fin 1 => J₀ (r' ≫ (snd (TFK (R := R) F) A.A).left), c * Units.mk0 d₀ hd₁,
    (top_le_iff_mem r' _ y).2 m', fun i => ?_⟩
  rw [hv i, Units.val_mul, _root_.mul_assoc, Units.val_mk0]
  refine congrArg _ ((toStk y).injective ?_)
  rw [map_mul, hd₀]
  refine (toStk_valF_gs x _ y m _).trans (Eq.trans ?_ ((hd _ _ (ht i)).trans
    (congrArg _ (toStk_valF_gs r' _ y m' _).symm)))
  refine Eq.symm ((toStk_valF_gs r _ y (mem_wchart.2 fun _ => m₂) _).trans ?_)
  rw [← e₁]
  exact (gs_pullOver (isPullback_groupBase F).w (fun _ => rfl) (genericSec U k (σ i)) r y (fun _ => l)
      (fun _ => m₂)).trans (gs_pullOver (p := pullback.fst G.hom (jK R)) pullback.condition
        (fun _ => (Category.comp_id _).symm) (σ i) _ y (fun _ => l) (fun _ => m₂))

end

theorem exists_carry : LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (k : ℕ) (J : Type) (σ : J → (u.H k).Sec) (f : J → ∀ α, u.D.toPre.SecB k α), (∀ i e, u.U.toUnifPre.ExpandsAt e k (σ i) (f i)) → (∀ i, ∃ s : Fam u.D.toPre (FractionRing u.V) k, FamOf u.D.toPre _ (f i) s) → ∀ w₀ : W0 u.U.toUnifPre, w₀.IsGen → ∃ (t : J → SecA u.A (PadicAlgCl p) k) (s : J → Fam u.D.toPre (PadicAlgCl p) k), (∀ i, u.U.toUnifPre.ExpandsF (PadicAlgCl p) k w₀ (t i) (s i)) ∧ (∀ i α, (∀ j, (f i α).f j = 0) → ∀ j, ((s i).s α).f j = 0) ∧ ∀ (a : u.PtC) (v : J → PadicAlgCl p), Crd (u.H k) σ (u.toG a) v → Crd (LPow u.A.A u.A.L (k : ℤ) (TFK (R := u.V) (PadicAlgCl p))) t (show Sp (PadicAlgCl p) ⟶ _ from (ptSecT u.A.A (a ≫ u.U.gen.hom)).left) v := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u k J σ f hE hf w₀ hw₀
  have hs : ∀ i, ∃ s : Fam u.D.toPre (PadicAlgCl p) k, FamOf u.D.toPre _ (f i) s := fun i => by
    obtain ⟨s, hs⟩ := hf i
    exact GlobalTheory.FamBaseChange.main hL.1.globalFns u.V _ u.D k s (f i) hs (PadicAlgCl p)
  choose s hs using hs
  choose t ht using fun i => exists_carries u.U.toUnifPre (PadicAlgCl p) k w₀ hw₀
    (extendSec u.U.toUnifPre (PadicAlgCl p) k (genericSec u.U.toUnifPre k (σ i)))
  exact ⟨t, s, fun i => ⟨_, ht i, expandsG_extend _ _ k (σ i) (f i) (hE i) (s i) (hs i)⟩,
    fun i α h j => famOf_zero _ k (f i) (s i) (hs i) α h j,
    fun a v h => crd_carries u.U.toUnifPre _ k w₀ σ t ht a v h⟩

end GlobalTheory.ZH.IntegralCarry
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGlueSectionsSameThetaMultiple
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.GlueTheta

theorem res_res {X : Scheme.{0}} {U V T : X.Opens} (h : V ≤ U) (h' : T ≤ V) (f : Γ(X, U)) :
    resG X h' (resG X h f) = resG X (h'.trans h) f := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem glue_secOn {X : Scheme.{0}} (L : LB X) {I : Type} (V : I → X.Opens) (W : X.Opens) (hle : ∀ i, V i ≤ W)
    (hcov : ∀ x ∈ W, ∃ i, x ∈ V i) (σ : ∀ i j, Γ(X, V i ⊓ L.U j)) (hσ : ∀ i, σ i ∈ secOn L (V i))
    (hc : ∀ i i' j (O : X.Opens) (h : O ≤ V i ⊓ L.U j) (h' : O ≤ V i' ⊓ L.U j),
      resG X h (σ i j) = resG X h' (σ i' j)) :
    ∃ s ∈ secOn L W, ∀ i j, resG X (inf_le_inf_right _ (hle i)) (s j) = σ i j := by
  have key : ∀ j, ∃ s : Γ(X, W ⊓ L.U j), ∀ i, resG X (inf_le_inf_right _ (hle i)) s = σ i j := by
    intro j
    obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (fun i => V i ⊓ L.U j) (W ⊓ L.U j)
      (fun i => homOfLE (inf_le_inf_right _ (hle i)))
      (fun x hx => by
        obtain ⟨i, hi⟩ := hcov x hx.1
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi, hx.2⟩)
      (fun i => σ i j) (fun i i' => hc i i' j _ inf_le_left inf_le_right)
    exact ⟨s, hs⟩
  choose s hs using key
  refine ⟨s, fun j k => ?_, fun i j => hs j i⟩
  refine X.sheaf.eq_of_locally_eq' (fun i => V i ⊓ L.U j ⊓ L.U k) (W ⊓ L.U j ⊓ L.U k)
    (fun i => homOfLE (inf_le_inf_right _ (inf_le_inf_right _ (hle i))))
    (fun x hx => by
      obtain ⟨i, hi⟩ := hcov x hx.1.1
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, ⟨hi, hx.1.2⟩, hx.2⟩) _ _ fun i => ?_
  have h := hσ i j k
  rw [← hs j i, ← hs k i, res_res, res_res] at h
  change resG X _ _ = resG X _ _
  rw [map_mul, res_res, res_res, res_res]
  exact h

theorem exists_glue : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (c : Ω), (∀ (N N' : M.Z.Opens) (σ : Q.SecFam N) (σ' : Q.SecFam N'), Q.ThMul c N σ → Q.ThMul c N' σ' → ∀ (j : Q.LOne.ι) (O : Q.G.left.Opens) (h : O ≤ Q.G.hom ⁻¹ᵁ N ⊓ Q.LOne.U j) (h' : O ≤ Q.G.hom ⁻¹ᵁ N' ⊓ Q.LOne.U j), resG _ h (σ j) = resG _ h' (σ' j)) → ∀ W : M.Z.Opens, (∀ z ∈ W, ∃ (N : M.Z.Opens) (σ : Q.SecFam N), z ∈ N ∧ N ≤ W ∧ σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) ∧ Q.ThMul c N σ ∧ Q.FibNe N σ) → ∃ σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ W), Q.ThMul c W σ ∧ Q.FibNe W σ := by
  intro o Ω _ _ _ _ S ρ M U₀ Q c huniq W hloc
  choose N σ hz hNW hsec hth hne using fun z : W => hloc z.1 z.2
  obtain ⟨s, hs, hres⟩ := glue_secOn Q.LOne (fun z : W => Q.G.hom ⁻¹ᵁ N z) (Q.G.hom ⁻¹ᵁ W)
    (fun z x hx => hNW z hx) (fun x hx => ⟨⟨Q.G.hom x, hx⟩, hz _⟩) σ hsec
    (fun z z' => huniq _ _ _ _ (hth z) (hth z'))
  have hval : ∀ (K : Type) [Field K] (g : Sp K ⟶ Q.G.left) (z : W) (j : Q.LOne.ι),
      ⊤ ≤ g ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N z ⊓ Q.LOne.U j) → valF g _ (σ z j) = valF g _ (s j) := by
    intro K _ g z j h
    rw [← hres z j]
    exact GlobalTheory.Points.valR_res g _ h _
  refine ⟨s, hs, ?_, ?_⟩
  · intro K _ β g r jP jL h1 h2 h3 h4 h5
    let z : W := ⟨Q.G.hom ((g ≫ Q.φ) (IsLocalRing.closedPoint K)), h5 ⟨_, rfl⟩⟩
    have hN : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N z) := (GlobalTheory.Points.le_preimage_iff _ _).2 (hz z)
    have hU : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N z ⊓ Q.LOne.U fun _ => jL) := fun t ht =>
      ⟨hN ht, Set.mem_iInter.2 fun _ => h4 ⟨t, rfl⟩⟩
    rw [← hval K _ z _ hU]
    exact hth z K β g r jP jL h1 h2 h3 h4 (by rintro _ ⟨t, rfl⟩; exact hN (x := t) trivial)
  · intro K _ _ x hx
    let z : W := ⟨x (IsLocalRing.closedPoint K), hx ⟨_, rfl⟩⟩
    have hN : ⊤ ≤ x ⁻¹ᵁ N z := (GlobalTheory.Points.le_preimage_iff _ _).2 (hz z)
    obtain ⟨g, j, hg, hv⟩ := hne z K x (by rintro _ ⟨t, rfl⟩; exact hN (x := t) trivial)
    refine ⟨g, j, hg, ?_⟩
    have hU : ⊤ ≤ g ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N z ⊓ Q.LOne.U j) := by
      by_contra hU
      exact hv (dif_neg hU)
    rwa [← hval K g z j hU]

end GlobalTheory.ZH.GlueTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsHomSpecOfLeRingOn
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

theorem comp_opens_toSpecΓ_eq_valMap {C : Type} [CommRing C] {X : Scheme.{0}} (U : X.Opens)
    (eta : Sp C ⟶ U.toScheme) (h : ⊤ ≤ (eta ≫ U.ι) ⁻¹ᵁ U) :
    eta ≫ U.toSpecΓ = Spec.map (valMap (eta ≫ U.ι) U h) := by
  have e : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U := fun z _ => z.2
  rw [← appLE_valMap eta U.ι e (le_preimage_top eta) h, Scheme.Opens.toSpecΓ, ← Category.assoc,
    Scheme.toSpecΓ_naturality, Spec.map_comp, valMap, Spec.map_comp]
  have h1 : (Sp C).toSpecΓ = Spec.map (Scheme.ΓSpecIso (CommRingCat.of C)).hom := by
    rw [← Scheme.isoSpec_Spec_hom]; rfl
  have h2 : U.topIso.inv = U.ι.appLE U ⊤ e := by
    rw [Scheme.Opens.ι_appLE]; rfl
  rw [h1, h2]
  rfl

theorem exists_hom_spec_of_le_ringOn :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U₀ : M.Z.Opens) (R : Subalgebra o Ω), (U₀ : Set M.Z).Nonempty → R ≤ M.ringOn U₀ → ∃ u₀ : U₀.toScheme ⟶ Sp R, ∀ eta : Sp Ω ⟶ U₀.toScheme, eta ≫ U₀.ι = M.pt → eta ≫ u₀ = spMap R.val.toRingHom := by
  intro o Ω _ _ _ M U R hU hR
  let ψ : R →+* Γ(M.Z, U) :=
    (M.sectionsEquiv U hU).symm.toRingHom.comp (Subalgebra.inclusion hR).toRingHom
  refine ⟨U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ), fun eta he => ?_⟩
  have h : ⊤ ≤ (eta ≫ U.ι) ⁻¹ᵁ U := he ▸ M.top_le_preimage_pt hU
  rw [← Category.assoc, comp_opens_toSpecΓ_eq_valMap U eta h, ← Spec.map_comp]
  congr 1
  ext a
  have e : (M.sectionsEquiv U hU (ψ a) : Ω) = a :=
    congrArg Subtype.val ((M.sectionsEquiv U hU).apply_symm_apply _)
  rw [coe_sectionsEquiv, ← he, valF_eq_valR, valR_eq _ U h] at e
  exact e

end GlobalTheory.ZH.RatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsImage
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.AbelianImage

theorem exists_lift {S : Scheme.{0}} {T N G : Over S} [IsReduced T.left] (ν : N ⟶ G)
    [IsClosedImmersion ν.left] (g : T ⟶ G) (h : Set.range g.left ⊆ Set.range ν.left) :
    ∃ l : T ⟶ N, l ≫ ν = g := by
  let Z : TopologicalSpace.Closeds G.left :=
    ⟨Set.range ν.left, ν.left.isClosedEmbedding.isClosed_range⟩
  have h2 : ν.left.ker ≤ g.left.ker :=
    (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.1
      (show Z ≤ ν.left.ker.support from ν.left.range_subset_ker_support)).trans
      (ReducedSubgroup.vanishingIdeal_le_ker g.left Z h)
  have h3 := IsClosedImmersion.lift_fac ν.left g.left h2
  refine ⟨Over.homMk (IsClosedImmersion.lift ν.left g.left h2) ?_, ?_⟩
  · rw [← Over.w ν, ← Category.assoc, h3, Over.w]
  · ext1
    exact h3

theorem geometricallyConnected_of_surjective {X Y Z : Scheme.{0}} (p : X ⟶ Y) (f : Y ⟶ Z)
    [Surjective p] [GeometricallyConnected (p ≫ f)] : GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  have : ConnectedSpace ↥(pullback (p ≫ f) x) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)
  let q := (pullbackRightPullbackFstIso f x p).inv ≫ pullback.snd p (pullback.fst f x)
  have : Surjective q := inferInstance
  exact q.surjective.connectedSpace q.continuous

theorem relDim_le_of_isDominant {k : Type} [Field k] {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] (p : X ⟶ Y) [IsDominant p] (f : Y ⟶ Spec (.of k)) {a b : ℕ}
    (ha : SmoothOfRelativeDimension a (p ≫ f)) (hb : SmoothOfRelativeDimension b f) : b ≤ a := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨A', j', hj', ⟨y, hy⟩, -⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (x := p x) (U := ⊤) trivial
  obtain ⟨A, j, hj, ⟨z, hz⟩, hr⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (x := x) (U := p ⁻¹ᵁ j'.opensRange) ⟨y, hy⟩
  have hrange : Set.range (j ≫ p) ⊆ Set.range j' := by
    rintro _ ⟨t, rfl⟩
    exact hr ⟨t, rfl⟩
  have hl := IsOpenImmersion.lift_fac j' (j ≫ p) hrange
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift j' (j ≫ p) hrange)
  obtain ⟨α, hα⟩ := Spec.map_surjective (j' ≫ f)
  rw [← hφ] at hl
  have : Nonempty (Spec A) := ⟨z⟩
  have : Nonempty (Spec A') := ⟨y⟩
  have : IsIntegral (Spec A) := isIntegral_of_isOpenImmersion j
  have : IsIntegral (Spec A') := isIntegral_of_isOpenImmersion j'
  have : IsDomain A := (affine_isIntegral_iff A).1 inferInstance
  have : IsDomain A' := (affine_isIntegral_iff A').1 inferInstance
  have : IsDominant j := ⟨j.isOpenEmbedding.isOpen_range.dense ⟨_, z, rfl⟩⟩
  have : IsDominant (Spec.map φ ≫ j') := by rw [hl]; infer_instance
  have hd : IsDominant (Spec.map φ) := IsDominant.of_comp_of_isOpenImmersion _ j'
  have hinj : Function.Injective φ.hom := by
    have h1 := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ.hom).1 hd.1
    rw [nilradical_eq_zero] at h1
    exact (RingHom.injective_iff_ker_eq_bot _).2 (le_bot_iff.1 h1)
  letI : Algebra k A' := α.hom.toAlgebra
  letI : Algebra k A := (α ≫ φ).hom.toAlgebra
  have h1 := trdeg_eq_of_smoothOfRelativeDimension k Y f b hb A' j' hj' hα.symm
  have h2 := trdeg_eq_of_smoothOfRelativeDimension k X (p ≫ f) a ha A j hj (by
    rw [← Category.assoc, ← hl, Category.assoc, ← hα, ← Spec.map_comp]; rfl)
  have h3 := trdeg_le_of_injective (R := k) (A := A') (A' := A) ⟨φ.hom, fun _ => rfl⟩ hinj
  rw [h1, h2] at h3
  exact_mod_cast h3

section Cat

variable {𝒞 : Type*} [Category 𝒞] [CartesianMonoidalCategory 𝒞] [BraidedCategory 𝒞]

theorem isCommMonObj_of_mono {N G : 𝒞} [MonObj N] [MonObj G] [IsCommMonObj G] (ν : N ⟶ G)
    [Mono ν] [IsMonHom ν] : IsCommMonObj N := by
  refine ⟨?_⟩
  rw [← cancel_mono ν, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
    IsCommMonObj.mul_comm]


omit [BraidedCategory 𝒞] in
theorem isMonHom_of_comp_mono {M N G : 𝒞} [MonObj M] [MonObj N] [MonObj G] (l : M ⟶ N) (ν : N ⟶ G)
    [Mono ν] [IsMonHom ν] [IsMonHom (l ≫ ν)] : IsMonHom l := by
  refine ⟨?_, ?_⟩
  · rw [← cancel_mono ν, Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  · rw [← cancel_mono ν, Category.assoc, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom,
      tensorHom_comp_tensorHom_assoc]

end Cat


open RationalPoint in
theorem exists_image : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ ψ : B ⟶ G, IsMonHom ψ → ∃ (B' : Over (Sp k)) (_ : GrpObj B') (ν : B' ⟶ G) (π : B ⟶ B'), IsAbelianScheme B' ∧ IsMonHom ν ∧ IsClosedImmersion ν.left ∧ π ≫ ν = ψ ∧ (∀ F : G ⟶ G, IsMonHom F → (∀ x : (𝟙_ (Over (Sp k)) ⟶ B), ∃ y : (𝟙_ (Over (Sp k)) ⟶ B), x ≫ ψ ≫ F = y ≫ ψ) → ∃ F' : B' ⟶ B', IsMonHom F' ∧ F' ≫ ν = ν ≫ F) ∧ ∀ a, SmoothOfRelativeDimension a B.hom → ∃ a', a' ≤ a ∧ SmoothOfRelativeDimension a' B'.hom := by
  intro k _ _ G _ hG B _ hB ψ hψ
  obtain ⟨hc, hs, hsep, -, -⟩ := hG
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  have : IsProper (ψ.left ≫ G.hom) := by rw [Over.w ψ]; infer_instance
  have : IsProper ψ.left := IsProper.of_comp ψ.left G.hom
  have hZ : IsClosed (Set.range ψ.left) := ψ.left.isClosedMap.isClosed_range
  let φ : (𝟙_ (Over (Sp k)) ⟶ B) →* (𝟙_ (Over (Sp k)) ⟶ G) :=
    MonoidHom.mk' (fun x => x ≫ ψ) fun x y => MonObj.mul_comp x y ψ
  have hC : ∀ x, x ∈ φ.range ↔ Set.range x.left ⊆ Set.range ψ.left := fun x => by
    rw [range_left_subset_iff, ← Set.image_univ, pt_mem_image_iff ψ isClosed_univ]
    simp only [Set.mem_univ, true_and]
    rfl
  obtain ⟨N, _, ν, hν, hcl, hsm, hr⟩ := ReducedSubgroup.exists_smooth_closed_subgroup k G
    inferInstance φ.range _ hZ hC
  have : ConnectedSpace B.left := GeometricallyConnected.connectedSpace_of_subsingleton B.hom
  have : IsIntegral B.left := isIntegral_of_smooth_field_of_connectedSpace B.hom
  obtain ⟨π, hπ⟩ := exists_lift ν ψ hr.ge
  have : Surjective π.left := ⟨fun y => by
    obtain ⟨x, hx⟩ := hr.le ⟨y, rfl⟩
    refine ⟨x, ν.left.isClosedEmbedding.injective ?_⟩
    rw [← hx, ← hπ]
    rfl⟩
  have : Mono ν := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono ν.left))
  have : ConnectedSpace N.left := π.left.surjective.connectedSpace π.left.continuous
  have : IsIntegral N.left := isIntegral_of_smooth_field_of_connectedSpace N.hom
  have hw : π.left ≫ N.hom = B.hom := Over.w π
  have : IsSeparated N.hom := by rw [← Over.w ν]; infer_instance
  have : UniversallyClosed (π.left ≫ N.hom) := by rw [hw]; infer_instance
  have : UniversallyClosed N.hom := UniversallyClosed.of_comp_surjective π.left N.hom
  have : GeometricallyConnected (π.left ≫ N.hom) := by rw [hw]; infer_instance
  have hN : IsAbelianScheme N := ⟨isCommMonObj_of_mono ν, hsm, ⟨⟩,
    geometricallyConnected_of_surjective π.left N.hom⟩
  refine ⟨N, inferInstance, ν, π, hN, hν, hcl, hπ, fun F hF h => ?_, fun a ha => ?_⟩
  · have h1 : Set.range (ψ ≫ F).left ⊆ Set.range ψ.left :=
      ReducedSubgroup.range_subset_of_points (ψ ≫ F) hZ fun x => by
        obtain ⟨y, hy⟩ := h x
        exact (hC _).1 ⟨y, hy.symm⟩
    obtain ⟨F', hF'⟩ := exists_lift ν (ν ≫ F) (by
      rintro _ ⟨t, rfl⟩
      obtain ⟨x, hx⟩ := hr.le ⟨t, rfl⟩
      refine hr.ge (h1 ⟨x, ?_⟩)
      change F.left (ψ.left x) = F.left (ν.left t)
      rw [hx])
    have : IsMonHom (F' ≫ ν) := by rw [hF']; infer_instance
    exact ⟨F', isMonHom_of_comp_mono F' ν, hF'⟩
  · obtain ⟨b, hb⟩ := AbelianDim.exists_relDim k N hN
    exact ⟨b, relDim_le_of_isDominant π.left N.hom (hw ▸ ha) hb, hb⟩

end GlobalTheory.AbelianImage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsLBGenTrivOfRatios
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)

theorem eq_of_res_eq_of_nonempty {U : M.Z.Opens} {f g : Γ(M.Z, U)}
    (h : ∀ hU : (U : Set M.Z).Nonempty, M.res U hU f = M.res U hU g) : f = g := by
  by_cases hU : (U : Set M.Z).Nonempty
  · exact M.res_injective U hU (h hU)
  · obtain rfl : U = ⊥ := SetLike.coe_injective (Set.not_nonempty_iff_eq_empty.1 hU)
    exact Subsingleton.elim _ _

theorem exists_unit_res_eq {U : M.Z.Opens} {x : Ω} (hx : x ≠ 0) (h : ∀ z ∈ U, x ∈ M.O z)
    (h' : ∀ z ∈ U, x⁻¹ ∈ M.O z) :
    ∃ g : Γ(M.Z, U)ˣ, ∀ hU : (U : Set M.Z).Nonempty, M.res U hU (g : Γ(M.Z, U)) = x := by
  by_cases hU : (U : Set M.Z).Nonempty
  · obtain ⟨a, ha⟩ := (mem_ringOn_iff_exists hU).1 (mem_ringOn.2 h)
    obtain ⟨b, hb⟩ := (mem_ringOn_iff_exists hU).1 (mem_ringOn.2 h')
    have hab : a * b = 1 := M.res_injective U hU (by
      rw [map_mul, map_one, res_apply, res_apply, ha, hb, mul_inv_cancel₀ hx])
    exact ⟨⟨a, b, hab, (mul_comm _ _).trans hab⟩, fun _ => (M.res_apply U hU a).trans ha⟩
  · exact ⟨1, fun h => (hU h).elim⟩

theorem exists_isLB_genTriv_of_ratios : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (ι : Type) (U : ι → M.Z.Opens) (d : ι → Ω), ⨆ k, U k = ⊤ → (∀ k, d k ≠ 0) → (∀ k k', ∀ z ∈ U k ⊓ U k', d k' / d k ∈ M.O z) → ∃ g : ∀ k k', Γ(M.Z, U k ⊓ U k')ˣ, (⟨ι, U, g⟩ : LB M.Z).IsLB ∧ M.GenTriv ⟨ι, U, g⟩ d := by
  intro o Ω _ _ _ M ι U d hU hd hr
  have key : ∀ k k', ∃ g : Γ(M.Z, U k ⊓ U k')ˣ, ∀ h : ((U k ⊓ U k' : M.Z.Opens) : Set M.Z).Nonempty,
      M.res _ h (g : Γ(M.Z, U k ⊓ U k')) = d k' / d k := fun k k' =>
    M.exists_unit_res_eq (div_ne_zero (hd k') (hd k)) (hr k k') fun z hz => by
      rw [inv_div]
      exact hr k' k z ⟨hz.2, hz.1⟩
  choose g hg using key
  have hres : ∀ k k' {V : M.Z.Opens} (h : V ≤ U k ⊓ U k') (hV : (V : Set M.Z).Nonempty),
      M.res V hV ((Semi.res h (g k k') : Γ(M.Z, V)ˣ) : Γ(M.Z, V)) = d k' / d k := fun k k' V h hV =>
    (M.res_resG h hV _).trans (hg k k' _)
  refine ⟨g, ⟨hU, fun i => Units.ext (M.eq_of_res_eq_of_nonempty fun hV => ?_),
    fun i j k => Units.ext (M.eq_of_res_eq_of_nonempty fun hV => ?_)⟩,
    ⟨hd, fun k k' h => (M.res_apply _ h _).symm.trans (hg k k' h)⟩⟩
  · refine (hres i i _ hV).trans ?_
    rw [div_self (hd i), Units.val_one, map_one]
  · rw [Units.val_mul, map_mul]
    refine (congrArg₂ (· * ·) (hres i j _ hV) (hres j k _ hV)).trans (Eq.trans ?_ (hres i k _ hV).symm)
    have := hd i
    have := hd j
    field_simp

end GlobalTheory.ZH.RatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveLatticeTwistGeneratedStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_projective_lattice_twist_generated : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [IsNoetherianRing o] (M : RatModel o Ω), IsProjOver M.s → ∀ (J : Type) [Fintype J] (EE : M.Lat J), ∃ (n : ℕ) (t : Fin (n + 1) → Ω) (e m : ℕ) (v : Fin m → J → Ω), M.IsCl t ∧ ∀ z i, M.Div t i z → EE.E z = Submodule.span (M.O z) (Set.range fun k j => v k j / t i ^ e) := by
  first | exact @GlobalTheory.ZH.RatModel.exists_isCl_lat_eq_span | exact GlobalTheory.ZH.RatModel.exists_isCl_lat_eq_span | (intros; apply GlobalTheory.ZH.RatModel.exists_isCl_lat_eq_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestFieldFiniteOverPadicStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.testField_finite_over_padic : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), CharZero u.V ∧ IsLocalHom u.j ∧ Function.Injective u.j ∧ ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧ (K : Set (PadicAlgCl p)) = Set.range (algebraMap (FractionRing u.V) (PadicAlgCl p)) := by
  first | exact @GlobalTheory.ZH.FieldOfTest.fractionRing_finite_over_padic | exact GlobalTheory.ZH.FieldOfTest.fractionRing_finite_over_padic | (intros; apply GlobalTheory.ZH.FieldOfTest.fractionRing_finite_over_padic <;> assumption)
end

