module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAbelianSchemeThick
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0070
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0073
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0024

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPrincipalPolarisationAbelianFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib
open GlobalTheory.CoordToExt

theorem lbIso_of_refines {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' K'' : Type} [Fintype K] [Fintype K']
    [Fintype K''] {M M' : LB Y} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (h : Refines M L φ ε) (h' : Refines M' L φ' ε') {ψ : K'' → (Y ⟶ X)} {δ : K'' → ℤ}
    (t : LB.Gen (LB.LinComb L ψ δ)) (ht : t.IsGen)
    (hF : ∀ (U : Type) [CommGroup U] (f : (Y ⟶ X) → U),
      (∏ k, f (ψ k) ^ δ k) * ∏ k, f (φ k) ^ ε k = ∏ k, f (φ' k) ^ ε' k) : LBIso M M' := by
  refine (h'.div h).exists_gen hL (fun U _ f => ?_) t ht
  refine Eq.symm ((Fintype.prod_sum_type _).trans ?_)
  simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  rw [← hF U f, mul_inv_cancel_right]

theorem refines_npw {X : Scheme.{0}} (L : LB X) (N : ℕ) :
    Refines (npw L N) L (K := PUnit) (fun _ => 𝟙 X) (fun _ => (N : ℤ)) := by
  refine ⟨fun i _ => i, fun i y hy => Set.mem_iInter.2 fun _ => hy, fun Z r z i j _ _ => ?_⟩
  refine (map_pow _ _ _).trans (Eq.symm ((Fintype.prod_unique _).trans ((zpow_natCast _ _).trans ?_)))
  rw [Category.comp_id]
  rfl

theorem npw_iso {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (N : ℕ) :
    LBIso (npw L N) (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) (fun _ => (N : ℤ))) :=
  lbIso_of_refines hL (refines_npw L N) (refines_self _ _) _ isGen_one fun U _ f => by
    rw [Fintype.prod_empty, _root_.one_mul]

theorem lbIso_drop {k : Type} [Field k] {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (p : Y ⟶ Sp k) (a b : Sp k ⟶ X)
    (u v : Y ⟶ X) (φ : Fin 4 → (Y ⟶ X)) (h₀ : φ 0 = u) (h₁ : φ 1 = p ≫ a) (h₂ : φ 2 = v) (h₃ : φ 3 = p ≫ b) :
    LBIso (LB.LinComb L φ Oε) (LB.LinComb L (K := Fin 2) ![u, v] ![1, -1]) := by
  obtain ⟨e, he⟩ := DVR.exists_gen_of_local (V := k) L hL (K := Fin 2) ![a, b] ![1, -1]
  refine lbIso_of_refines hL (refines_self _ _) (refines_self _ _) _ (DVR.pullGen_isGen _ _ _ e he p) fun U _ f => ?_
  rw [Fin.prod_univ_four, Fin.prod_univ_two, Fin.prod_univ_two, h₀, h₁, h₂, h₃]
  change f (p ≫ a) ^ (1 : ℤ) * f (p ≫ b) ^ (-1 : ℤ) *
    (f u ^ (1 : ℤ) * f (p ≫ a) ^ (-1 : ℤ) * f v ^ (-1 : ℤ) * f (p ≫ b) ^ (1 : ℤ)) = f u ^ (1 : ℤ) * f v ^ (-1 : ℤ)
  simp only [zpow_neg, zpow_one]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_pol : PolBaseChangeSt → ∀ (k : Type) [Field k] (Φ : FibPre k) (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (s : Sp k ⟶ Sp R) (π : Φ.E.B.left ⟶ D.P.A.left), IsGrpPullback Φ.E.B D.P.A s π → ∀ (xe : Φ.E.X → D.X), (∀ χ, LBIso (Φ.E.O χ).L (LB.LinComb D.P.L (fun a => π ≫ D.Oφ (𝟙 D.P.A) (xe χ) a) Oε)) → ∀ (N : ℕ), Nonempty (ChartPull Φ.N₀ (npw D.P.L N) π) → ∃ pol : Φ.Pol N, pol.PB.g = D.P.g := by
  rintro hB k _ Φ R _ _ D s π hπ xe hO N ⟨cp⟩
  obtain ⟨P', g, hg, hdim, hm, t, ht⟩ := hB _ _ s D.P
  have gp : IsGrpPullback P'.A D.P.A s g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    rw [(Over.OverMorphism.ext hx : x₀ = toBase hg.w x), (Over.OverMorphism.ext hy : y₀ = toBase hg.w y), ← hm]
    rfl⟩
  obtain ⟨β, hβ, hβπ⟩ := grpPullback_iso hπ gp
  obtain ⟨w, hw⟩ := LBIso.symm ⟨t, ht⟩
  have hL := D.P.isLB
  have hL' := P'.isLB
  have key : ∀ {K : Type} [Fintype K] (φ' : K → (Φ.E.B.left ⟶ P'.A.left)) (φ : K → (Φ.E.B.left ⟶ D.P.A.left))
      (ε : K → ℤ), (∀ a, φ a = φ' a ≫ g) → LBIso (LB.LinComb D.P.L φ ε) (LB.LinComb P'.L φ' ε) := by
    intro K _ φ' φ ε h
    obtain rfl : φ = fun a => φ' a ≫ g := funext h
    exact (iso_linComb ((isGen_iff w).1 hw) φ' ε).symm
  have hc : ∀ x : 𝟙_ (Over (Sp R)) ⟶ D.P.A, (s ≫ x.left) ≫ D.P.A.hom = 𝟙 _ ≫ s := fun x => by
    rw [Category.assoc, Over.w x, Category.id_comp]
    exact Category.comp_id _
  let c : Φ.E.X → (baseOver (Sp k) ⟶ P'.A) := fun χ =>
    Over.homMk (hg.lift (s ≫ (D.c (xe χ)).left) (𝟙 _) (hc _)) (hg.lift_snd _ _ _)
  have hcg : ∀ χ, (c χ).left ≫ g = s ≫ (D.c (xe χ)).left := fun χ => hg.lift_fst _ _ _
  have hu : ∀ x : 𝟙_ (Over (Sp R)) ⟶ D.P.A, π ≫ (toUnit D.P.A ≫ x).left = Φ.E.B.hom ≫ s ≫ x.left := fun x => by
    rw [← Category.assoc, ← hπ.1.w, Category.assoc]
    rfl
  refine ⟨⟨P', β, hβ, c, ?_, fun χ => ?_⟩, hdim⟩
  · have h₁ : LBIso Φ.N₀ (LB.LinComb D.P.L (K := PUnit) (fun _ => π) (fun _ => (N : ℤ))) :=
      LBIso.chartPull cp (chartPullSame _ _ _ _ π fun _ => (Category.comp_id _).symm) (npw_iso hL N)
    have h₂ := key (K := PUnit) (fun _ => β.hom.left) (fun _ => π) (fun _ => (N : ℤ)) fun _ => hβπ.symm
    have h₃ : LBIso (LB.LinComb P'.L (K := PUnit) (fun _ => β.hom.left) (fun _ => (N : ℤ)))
        ((lbPow P'.L N).pull β.hom.left) :=
      LBIso.chartPull (chartPullId _) (chartPullOut P'.L _ _ β.hom.left _ fun _ => (Category.comp_id _).symm)
        (exists_iso hL' rfl _)
    exact LBIso.trans Φ.isLB (DVR.linComb_isLB _ hL _ _) (pull_isLB (DVR.linComb_isLB _ hL' _ _) _) h₁
      (LBIso.trans (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL' _ _)
        (pull_isLB (DVR.linComb_isLB _ hL' _ _) _) h₂ h₃)
  · let q : Φ.E.B ⟶ baseOver (Sp k) := Over.homMk Φ.E.B.hom (Category.comp_id _)
    have e₀ : π ≫ D.Oφ (𝟙 D.P.A) (xe χ) 0 = (β.hom * (q ≫ c χ)).left ≫ g := by
      let ρ : Over.mk (Φ.E.B.hom ≫ s) ⟶ D.P.A := Over.homMk π hπ.1.w
      refine Eq.trans ?_ (gp.2 Φ.E.B β.hom (q ≫ c χ) (ρ ≫ 𝟙 _) (ρ ≫ toUnit _ ≫ D.c (xe χ))
        ((Category.comp_id _).trans hβπ.symm) ?_)
      · exact congrArg (fun f => f.left) (MonObj.comp_mul ρ (𝟙 _) (toUnit _ ≫ D.c (xe χ)))
      · refine (hu _).trans ?_
        rw [← hcg]
        exact (Category.assoc _ _ _).symm
    have h₁ := lbIso_drop hL Φ.E.B.hom (s ≫ (D.c (xe χ)).left) (s ≫ (η[D.P.A]).left) _ π
      (fun a => π ≫ D.Oφ (𝟙 D.P.A) (xe χ) a) e₀ (hu _) (Category.comp_id _) (hu _)
    have h₂ := key (K := Fin 2) ![(β.hom * (q ≫ c χ)).left, β.hom.left] ![(β.hom * (q ≫ c χ)).left ≫ g, π] ![1, -1]
      (fun a => by
        fin_cases a
        · rfl
        · exact hβπ.symm)
    exact LBIso.trans (Φ.E.O χ).isLB (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL' _ _) (hO χ)
      (LBIso.trans (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL' _ _) h₁ h₂)

end GlobalTheory.ZH.UFib
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullDegCancelTowerOfFields
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

noncomputable section
namespace GlobalTheory.FieldPull
open GlobalTheory.ArcPull GlobalTheory.PsiEvenPull

theorem exists_cancel_of_eq {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X}
    {F' : X'' ⟶ X'} {F'' : X'' ⟶ X} (e : F' ≫ F = F'') (hL : L.IsLB) (hL' : L'.IsLB) (hL'' : L''.IsLB)
    (w : LB.Iso L' (L.pull F)) (w'' : LB.Iso L'' (L.pull F'')) (hw : PGen w) (hw'' : PGen w'')
    {Y Y' Y'' : Scheme.{0}} {φ : Y ⟶ X} {φ' : Y' ⟶ X'} {φ'' : Y'' ⟶ X''}
    {t : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => φ) (fun _ => 1))}
    {t' : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => φ') (fun _ => 1))}
    {t'' : LB.Gen (LB.LinComb L'' (K := PUnit) (fun _ => φ'') (fun _ => 1))}
    {h : Y' ⟶ Y} {h' : Y'' ⟶ Y'} {h'' : Y'' ⟶ Y} (eh : h' ≫ h = h'') (hc : φ'' ≫ F' = h' ≫ φ')
    (H : PMaps w _ _ _ t' t h) (H'' : PMaps w'' _ _ _ t'' t h'') :
    ∃ w' : LB.Iso L'' (L'.pull F'), PGen w' ∧ PMaps w' _ _ _ t'' t' h' ∧
      ∀ (Z : Scheme.{0}) (z : Z) J J' J'', Good L z J → Good L' z J' → Good L'' z J'' → ∀ x : Z ⟶ X'',
        om w'' z J J'' x = om w z J J' (x ≫ F') * om w' z J' J'' x := by
  subst e eh
  obtain ⟨w', T⟩ := exists_cancel hL w w'' hw hw'' hL' hL''
  refine ⟨w', T.pgen_cancel hL hw hw'', T.pmaps_cancel hL (fun _ => hc) H H'', fun Z z J J' J'' hJ hJ' hJ'' x => ?_⟩
  rw [om, om, om, Category.assoc]
  exact T Z x z _ _ _ (hJ (x ≫ F' ≫ F)) (hJ' (x ≫ F')) (hJ'' x)

theorem exists_isPullDeg_cancel : ∀ (K₀ K₁ K : Type) [Field K₀] [Field K₁] [Field K] (α : K₀ →+* K₁) (β : K₁ →+* K) (D₀ : DegPre K₀) (D₁ : DegPre K₁) (D : DegPre K) (h₁ : IsPullDeg α D₀ D₁) (h : IsPullDeg (β.comp α) D₀ D), ∃ hD : IsPullDeg β D₁ D, PsiEvenPull.proj hD ≫ PsiEvenPull.proj h₁ = PsiEvenPull.proj h := by
  intro K₀ K₁ K _ _ _ α β D₀ D₁ D h₁ h
  have p₁ : IsGrpPullback D₁.P.A D₀.P.A (spMap α) (proj h₁) := pull_grp h₁
  have sc : spMap β ≫ spMap α = spMap (β.comp α) := (spMap_comp α β).symm
  have p : IsGrpPullback D.P.A D₀.P.A (spMap β ≫ spMap α) (proj h) := (pull_grp h).congr sc.symm rfl
  obtain ⟨Φ, e₁, e₂⟩ : ∃ Φ : D.P.A.left ⟶ D₁.P.A.left, Φ ≫ proj h₁ = proj h ∧ Φ ≫ D₁.P.A.hom = D.P.A.hom ≫ spMap β :=
    ⟨p₁.1.lift (proj h) (D.P.A.hom ≫ spMap β) (p.1.w.trans (Category.assoc _ _ _).symm), p₁.1.lift_fst _ _ _,
      p₁.1.lift_snd _ _ _⟩
  have gp : IsGrpPullback D.P.A D₁.P.A (spMap β) Φ := IsGrpPullback.cancel p₁ (p.congr rfl e₁.symm) e₂
  obtain ⟨w, hw, hr, T⟩ := exists_cancel_of_eq e₁ D₀.P.isLB D₁.P.isLB D.P.isLB h₁.w h.w ((isGen_iff _).1 h₁.w_gen)
    ((isGen_iff _).1 h.w_gen) sc (cubeMapOf gp).e_comm (pmaps_rig h₁) (pmaps_rig h)
  let xe : D.X ≃+ D₁.X := h.xe.trans h₁.xe.symm
  have hxe : ∀ x, h₁.xe (xe x) = h.xe x := fun x => h₁.xe.apply_symm_apply _
  have hc : ∀ x, (D.c x).left ≫ Φ = spMap β ≫ (D₁.c (xe x)).left := fun x => by
    apply p₁.1.hom_ext
    · rw [Category.assoc, e₁, Category.assoc, h₁.c_pr, hxe]
      exact (h.c_pr x).trans ((congrArg (· ≫ _) sc.symm).trans (Category.assoc _ _ _))
    · rw [Category.assoc, e₂, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨hD, hΦ, -, -⟩ := exists_isPullDeg_of_val β D₁ D gp w hw hr xe hc (fun x z J₁ J hJ₁ hJ => by
    obtain ⟨J₀, hJ₀⟩ := DegPull.exists_good' D₀.P.isLB z
    have sβ : jK K ≫ spMap β = genMap β.injective ≫ jK K₁ :=
      (Category.id_comp _).symm.trans (fracMap_sq β.injective)
    have sα : jK K₁ ≫ spMap α = genMap α.injective ≫ jK K₀ :=
      (Category.id_comp _).symm.trans (fracMap_sq α.injective)
    have q₁ : genMap β.injective ≫ jK K₁ ≫ spMap α = (genMap β.injective ≫ genMap α.injective) ≫ jK K₀ :=
      (congrArg (_ ≫ ·) sα).trans (Category.assoc _ _ _).symm
    have q : 𝟙 (TK K).left ≫ jK K ≫ spMap (β.comp α) = (genMap β.injective ≫ genMap α.injective) ≫ jK K₀ :=
      (Category.id_comp _).trans ((congrArg (_ ≫ ·) sc.symm).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) sβ).trans ((Category.assoc _ _ _).trans q₁))))
    have v := psi_val h _ _ q hJ₀ hJ x
    have v₁ := psi_val h₁ _ _ q₁ hJ₀ hJ₁ (xe x)
    have hx : D.xK x ≫ Φ = genMap β.injective ≫ D₁.xK (xe x) := by
      show (jK K ≫ (D.c x).left) ≫ Φ = genMap β.injective ≫ jK K₁ ≫ (D₁.c (xe x)).left
      rw [Category.assoc, hc, ← Category.assoc, sβ, Category.assoc]
    rw [hxe, v, Category.id_comp, T _ z J₀ J₁ J hJ₀ hJ₁ hJ, hx, mul_inv, _root_.mul_assoc] at v₁
    exact (mul_left_cancel v₁).symm)
  exact ⟨hD, hΦ ▸ e₁⟩

end GlobalTheory.FieldPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPureWeightSectionReduction
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib

theorem gm_charUnit_zero_eq_one {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Z : Over S} (τ : Z ⟶ splitTorus S X)
    (z : Z.left) : gm τ.left z ⊤ (charUnit S X 0) = 1 := by
  have a : splitTorusPointsEquiv S X Z τ (Multiplicative.ofAdd 0) = pullU τ.left ⊤ (charUnit S X 0) :=
    Units.ext (splitTorusPointsEquiv_val _ _ _ τ 0)
  have b : pullU τ.left ⊤ (charUnit S X 0) = 1 := a.symm.trans (map_one _)
  have c := gm_pull (𝟙 Z.left) τ.left z ⊤ trivial (charUnit S X 0)
  rw [b, map_one, Category.id_comp] at c
  exact c.symm

def chartPullH {k : Type} [Field k] (Φ : FibPre k) {Y : Scheme.{0}} {L : LB Y} {π : Φ.E.B.left ⟶ Y} {N : ℕ}
    (c : ChartPull Φ.N₀ (npw L N) π) :
    ChartPull (Φ.H 1) (LB.LinComb L (fun _ : Fin 1 => Φ.D.q.left ≫ π) (fun _ => (N : ℤ))) (𝟙 _) :=
  have le : ∀ l : Φ.N₀.ι, Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l ≤
      LB.wchart L (fun _ : Fin 1 => Φ.D.q.left ≫ π) (fun _ => c.idx l) :=
    fun l _ hy => Set.mem_iInter.2 fun _ => c.le l hy
  { idx := fun l _ => c.idx l
    le := le
    g := fun y l l' hl hl' => by
      refine Eq.trans ?_ (gm_linComb L (fun _ : Fin 1 => Φ.D.q.left ≫ π) (fun _ => (N : ℤ)) (𝟙 _) y _ _
        (le l hl) (le l' hl')).symm
      have e₁ := gm_chartPull_g c (𝟙 _ ≫ Φ.D.q.left) y l l' hl hl'
      have e₂ := gm_pull (𝟙 _) Φ.D.q.left y (Φ.N₀.U l ⊓ Φ.N₀.U l') ⟨hl, hl'⟩ (Φ.N₀.g l l')
      refine (((congrArg (gm (𝟙 _) y _) (pow_one _)).trans e₂).trans e₁).trans (Eq.symm ?_)
      refine Eq.trans ?_ (map_pow _ _ _).symm
      refine (Fintype.prod_unique _).trans ((zpow_natCast _ _).trans ?_)
      rw [Category.assoc]
      rfl }

theorem trF_comp {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] (q : Y' ⟶ Y) (ψ : K → (Y ⟶ X))
    (ε : K → ℤ) (r : Z ⟶ Y') (z : Z) (j j' : K → L.ι) :
    trF (fun a => q ≫ ψ a) ε r z j j' = trF ψ ε (r ≫ q) z j j' := by
  simp only [trF, Category.assoc]

theorem exists_red_of_pure : ∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (π : Φ.E.B.left ⟶ Y) (N : ℕ) (c : ChartPull Φ.N₀ (npw L N) π) (K K' : Type) [Fintype K] [Fintype K'] (ψ : K → (Φ.E.B.left ⟶ Y)) (ε : K → ℤ) (φt : K' → (Φ.G.left ⟶ Y)) (εt : K' → ℤ) (t : LB.Gen (LB.LinComb L φt εt)), t.IsGen → FormEq (Sum.elim (fun a => Φ.D.q.left ≫ ψ a) φt) (Sum.elim ε εt) (fun _ : Fin 1 => Φ.D.q.left ≫ π) (fun _ => (N : ℤ)) → ∀ α : Φ.E.X, UFib.GenWt Φ.D.i t α → ∀ φ : (Φ.H 1).Sec, Φ.Pure α φ → ∃ b : LB.Sec (LB.LinComb L ψ ε), UFib.Red Φ c t b φ := by
  intro k _ _ Φ Y L hL π N c K K' _ _ ψ ε φt εt t ht hF α hw φ hp
  have := Φ.D.q_hom
  have := Φ.D.q_flat
  have := Φ.D.q_surjective
  obtain ⟨s, hs⟩ := exists_sec_of_refine _ _ _ (Φ.H_isLB 1) (DVR.linComb_isLB L hL _ _) (chartPullH Φ c) φ
  have hF' : FormEq (Sum.elim (fun _ : Fin 1 => 𝟙 _ ≫ Φ.D.q.left ≫ π) φt)
      (Sum.elim (fun _ => (N : ℤ)) (fun a => - εt a)) (fun a => Φ.D.q.left ≫ ψ a) ε := by
    intro U _ h
    have e := hF U h
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Category.id_comp, zpow_neg,
      Finset.prod_inv_distrib] at e ⊢
    rw [← e, mul_inv_cancel_right]
  obtain ⟨σ, hσ⟩ := exists_sec hL hF' (pullMulSec s (𝟙 _) (LB.invGen L _ _ t) (DVR.invGen_isGen _ _ _ _ ht))
  have vσ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Φ.G.left) (z : Z) (J : (Z ⟶ Y) → L.ι), Good L z J → ∀ l : Φ.N₀.ι,
      r z ∈ Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l → J (r ≫ Φ.D.q.left ≫ π) = c.idx l →
      gs r z (Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l) (φ.f l) = sval σ r z J * (val t r z J).val := by
    intro Z r z J hJ l hl e
    rw [hσ Z r z J hJ, sval_pullMulSec _ _ _ _ r z hJ, val_inv, Category.comp_id, Units.inv_mul_cancel_right,
      sval_of s r z J (fun _ => c.idx l) (fun _ => e)]
    exact hs l Z r z hl
  have le : ∀ j : K → L.ι, Φ.D.q.left ⁻¹ᵁ LB.wchart L ψ j ≤ LB.wchart L (fun a => Φ.D.q.left ≫ ψ a) j :=
    fun j y hy => Set.mem_iInter.2 fun a => Set.mem_iInter.1 hy a
  have desc : ∀ j : K → L.ι, ∃ a : Γ(Φ.E.B.left, LB.wchart L ψ j),
      (Φ.D.q.left.app _).hom a = (Φ.G.left.presheaf.map (homOfLE (le j)).op).hom (σ.f j) := by
    intro j
    refine exists_app_eq_of_hasWt_zero k Φ.E Φ.G Φ.D _ _ fun Z τ g z hz => ?_
    have hq : ((τ ≫ Φ.D.i) * g).left ≫ Φ.D.q.left = g.left ≫ Φ.D.q.left :=
      congrArg (fun x => x.left) (GtBaseChange.translate_comp Φ.D.q Φ.D.i Φ.D.isKernel τ g)
    have hz' := GtBaseChange.translate_mem Φ.D.q Φ.D.i Φ.D.isKernel τ g _ z hz
    obtain ⟨l, hl⟩ := exists_chart Φ.isLB (Φ.D.q.left (g.left z))
    have hl' := GtBaseChange.translate_mem Φ.D.q Φ.D.i Φ.D.isKernel τ g _ z hl
    obtain ⟨J, hJ, e⟩ := exists_good L hL z (K := Unit) (fun _ => g.left ≫ Φ.D.q.left ≫ π) (fun _ => c.idx l)
      (fun _ _ _ => rfl) (fun _ => c.le l hl)
    have hwt : HasWt Φ.D.i _ (φ.f l) α :=
      (PureWt.hasWt_iff_weight k Φ.E Φ.G Φ.D (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l) (φ.f l) α).2 fun χ hne => by
        by_contra h
        exact hne (hp ⟨l, h⟩)
    have h₀ := hwt Z τ g z hl
    have h₁ := vσ _ g.left z J hJ l hl (e ())
    have h₂ := vσ _ ((τ ≫ Φ.D.i) * g).left z J hJ l hl' (by rw [← Category.assoc, hq, Category.assoc]; exact e ())
    have h₃ : sval σ ((τ ≫ Φ.D.i) * g).left z J = sval σ g.left z J := by
      have h₄ := h₂.symm.trans (h₀.trans (congrArg _ h₁))
      rw [hw Z τ g z J hJ, mul_left_comm, ← Units.val_mul] at h₄
      exact (Units.mul_left_inj _).1 h₄
    rw [gm_charUnit_zero_eq_one, Units.val_one, _root_.one_mul]
    refine (gs_res _ z (le j) hz' _).trans (Eq.trans ?_ (gs_res _ z (le j) hz _).symm)
    refine (sec_trans σ _ z (le j hz') (hJ.mem _ _)).trans (Eq.trans ?_ (sec_trans σ _ z (le j hz) (hJ.mem _ _)).symm)
    refine congrArg₂ (· * ·) (congrArg Units.val ?_) h₃
    simp only [trF_comp, ← Category.assoc, hq]
  choose a ha using desc
  have hv : ∀ j (Z : Scheme.{0}) (r : Z ⟶ Φ.G.left) (z : Z), Φ.D.q.left (r z) ∈ LB.wchart L ψ j →
      gs (r ≫ Φ.D.q.left) z (LB.wchart L ψ j) (a j) =
        gs r z (LB.wchart L (fun a => Φ.D.q.left ≫ ψ a) j) (σ.f j) := fun j Z r z hz =>
    (gs_pull r _ z _ hz _).symm.trans ((congrArg (gs r z _) (ha j)).trans (gs_res r z (le j) hz _))
  refine ⟨⟨a, fun j j' => FunDescent.app_injective Φ.D.q.left (LB.wchart L ψ j ⊓ LB.wchart L ψ j')
    (fn_ext fun y hy => ?_)⟩, fun Z r z J hJ l hl e => ?_⟩
  · have hy' : Φ.D.q.left y ∈ LB.wchart L ψ j ⊓ LB.wchart L ψ j' := hy
    refine (gs_pull (𝟙 _) Φ.D.q.left y _ hy' _).trans (Eq.trans ?_ (gs_pull (𝟙 _) Φ.D.q.left y _ hy' _).symm)
    refine ((gs_res (𝟙 _ ≫ Φ.D.q.left) y _ hy' _).trans ((hv j _ _ y hy'.1).trans
      (sec_trans σ (𝟙 _) y (le j hy'.1) (le j' hy'.2)))).trans (Eq.symm ?_)
    refine (gs_mul (𝟙 _ ≫ Φ.D.q.left) y _ hy' _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 _ ≫ Φ.D.q.left) y _ hy' _).trans (congrArg Units.val
        ((gm_linComb L ψ ε (𝟙 _ ≫ Φ.D.q.left) y j j' hy'.1 hy'.2).trans (trF_comp _ _ _ _ _ _ _).symm)))
      ((gs_res (𝟙 _ ≫ Φ.D.q.left) y _ hy' _).trans (hv j' _ _ y hy'.2)))
  · refine (vσ Z r z J hJ l hl e).trans (congrArg₂ (· * ·) (Eq.symm ?_) rfl)
    rw [sval_of _ (r ≫ Φ.D.q.left) z J (fun a => J (r ≫ Φ.D.q.left ≫ ψ a)) (fun a => by rw [Category.assoc])]
    exact hv _ Z r z (Set.mem_iInter.2 fun a => hJ (r ≫ Φ.D.q.left ≫ ψ a))

end GlobalTheory.ZH.UFib
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRatioDescendsDegenerationPsiFamily
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

noncomputable section
namespace GlobalTheory.FieldPull
open GlobalTheory.ArcPull GlobalTheory.PsiEvenPull

theorem exists_psi_ratio {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (ψ : TauTwist.PsiFam D)
    (hψ : ∀ χ, (ψ χ).IsGen) (χ : D.X) : ∃ u : (FractionRing R)ˣ, ∀ (z : (TK R).left) J, Good D.P.L z J →
      val (D.psi χ) (𝟙 _) z J = TauTwist.unitAt (A := FractionRing R) (Z := (TK R).left) (𝟙 _) z u * val (ψ χ) (𝟙 _) z J :=
  TauTwist.exists_ratio (F := FractionRing R) D.P.isLB (fun _ _ _ => rfl) (D.psi_gen χ) (hψ χ)

theorem unitAt_genMap {K₁ K : Type} [Field K₁] [Field K] (β : K₁ →+* K) (z : (TK K).left) (v : (FractionRing K₁)ˣ) :
    TauTwist.unitAt (A := FractionRing K₁) (genMap β.injective) z v =
      TauTwist.unitAt (A := FractionRing K) (Z := (TK K).left) (𝟙 _) z (Units.map (fracMap β.injective).toMonoidHom v) :=
  (congrArg (fun r => TauTwist.unitAt (A := FractionRing K₁) r z v) (Category.id_comp _).symm).trans
    (TauTwist.unitAt_spMap (𝟙 _) (fracMap β.injective) z v)

theorem exists_isPullDeg_rescale {K₁ K : Type} [Field K₁] [Field K] (β : K₁ →+* K) (D₁ : DegPre K₁) (D : DegPre K)
    (ψ : TauTwist.PsiFam D) (hψ : ∀ χ, (ψ χ).IsGen) (h : IsPullDeg β D₁ (TauTwist.withPsi D ψ hψ))
    (q : D₁.X → (FractionRing K₁)ˣ)
    (hq : ∀ χ (z : (TK K).left) J, Good D.P.L z J → val (D.psi χ) (𝟙 _) z J =
      TauTwist.unitAt (A := FractionRing K) (Z := (TK K).left) (𝟙 _) z (Units.map (fracMap β.injective).toMonoidHom (q (h.xe χ))) *
        val (ψ χ) (𝟙 _) z J) :
    ∃ hD : IsPullDeg β (TauTwist.rescale D₁ q) D, proj hD = proj h := by
  have key : ∀ (x : D.X) (z : (TK K).left) J J', Good D₁.P.L z J → Good D.P.L z J' →
      val ((TauTwist.rescale D₁ q).psi (h.xe x)) (genMap β.injective) z J =
        (om h.w z J J' (D.xK x))⁻¹ * val (D.psi x) (𝟙 _) z J' := fun x z J J' hJ hJ' => by
    have e := psi_val (D := D₁) (D' := TauTwist.withPsi D ψ hψ) h (genMap β.injective) (𝟙 _) (fracMap_sq β.injective) hJ hJ' x
    rw [Category.id_comp] at e
    refine (TauTwist.val_psi_rescale q (h.xe x) _ hJ).trans ((congrArg₂ (· * ·) (unitAt_genMap β z _) e).trans ?_)
    exact (mul_left_comm _ _ _).trans (congrArg₂ (· * ·) rfl (hq x z J' hJ')).symm
  obtain ⟨hD, hp, -, -⟩ := exists_isPullDeg_of_val β (TauTwist.rescale D₁ q) D (Φ := proj (D := D₁) (D' := TauTwist.withPsi D ψ hψ) h)
    (pull_grp (D := D₁) (D' := TauTwist.withPsi D ψ hψ) h) h.w
    ((isGen_iff h.w).1 h.w_gen) (pmaps_rig (D := D₁) (D' := TauTwist.withPsi D ψ hψ) h) h.xe h.c_pr key
  exact ⟨hD, hp⟩

theorem exists_ratio_descends (K : Type) [Field K] (D : DegPre K) (ψ : TauTwist.PsiFam D) (hψ : ∀ χ, (ψ χ).IsGen) :
    ∃ a : D.X → K, ∀ (K₁ : Type) [Field K₁] (β : K₁ →+* K) (D₁ : DegPre K₁)
      (h : IsPullDeg β D₁ (TauTwist.withPsi D ψ hψ)), (∀ χ, a χ ∈ Set.range β) →
      ∃ (ψ₁ : TauTwist.PsiFam D₁) (hψ₁ : ∀ χ, (ψ₁ χ).IsGen) (hD : IsPullDeg β (TauTwist.withPsi D₁ ψ₁ hψ₁) D),
        PsiEvenPull.proj hD = PsiEvenPull.proj h := by
  choose u hu using exists_psi_ratio D ψ hψ
  refine ⟨fun χ => FractionRing.algEquiv K K (u χ).val, fun K₁ _ β D₁ h ha => ?_⟩
  choose a₁ ha₁ using ha
  have key : ∀ χ, fracMap β.injective (algebraMap K₁ (FractionRing K₁) (a₁ χ)) = (u χ).val := fun χ => by
    rw [fracMap_algebraMap, ha₁]
    exact (FractionRing.algEquiv K K).injective ((FractionRing.algEquiv K K).commutes _)
  have hne : ∀ χ, algebraMap K₁ (FractionRing K₁) (a₁ χ) ≠ 0 := fun χ e => (u χ).ne_zero (by
    rw [← key, e, map_zero])
  obtain ⟨q, hq⟩ : ∃ q : D₁.X → (FractionRing K₁)ˣ,
      ∀ χ, Units.map (fracMap β.injective).toMonoidHom (q (h.xe χ)) = u χ :=
    ⟨fun y => Units.mk0 _ (hne (h.xe.symm y)), fun χ => Units.ext (by
      show fracMap β.injective (algebraMap K₁ (FractionRing K₁) (a₁ (h.xe.symm (h.xe χ)))) = _
      rw [AddEquiv.symm_apply_apply, key])⟩
  obtain ⟨hD, hp⟩ := exists_isPullDeg_rescale β D₁ D ψ hψ h q fun χ z J hJ => by
    rw [hq]; exact hu χ z J hJ
  exact ⟨_, _, hD, hp⟩

end GlobalTheory.FieldPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTwistedSectionThetaTranslateCoefStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twistedSection_thetaTranslate_coef : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (th : SecBT D (𝟙_ _) 1 0), (∀ g : SecBT D (𝟙_ _) 1 0, ∃ b : R, Mult D th g b) → ∀ (χ : D.X) (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))), u.IsGen → ∀ g : SecBT D (𝟙_ _) 1 χ, ∃ b : R, Coef D χ u th g b := by
  first | exact @GlobalTheory.PsiCoef.exists_coef | exact GlobalTheory.PsiCoef.exists_coef | (intros; apply GlobalTheory.PsiCoef.exists_coef <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExpansionCoefMemAdicPowStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expansionCoef_mem_adic_pow : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), I ≠ ⊤ → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (σ : U.SecGT (𝟙_ _) 1) (f : ∀ α, SecBT D (𝟙_ _) 1 α) (th : SecBT D (𝟙_ _) 1 0), U.ExpT (𝟙_ _) 1 σ f → FibNZ (𝟙_ _ ⊗ D.P.A).hom th → ∀ e : ℕ, ∃ s : Finset D.X, ∀ χ ∉ s, ∀ (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (b : R), Coef D χ u th (f χ) b → b ∈ I ^ (e + 1) := by
  first | exact @GlobalTheory.PsiRing.coef_mem_pow | exact GlobalTheory.PsiRing.coef_mem_pow | (intros; apply GlobalTheory.PsiRing.coef_mem_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfSection
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.NeutralPart


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.SS.NeutralPart.geometricallyConnected_of_section {X S : Scheme.{0}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [QuasiCompact f] (e : S ⟶ X) (he : e ≫ f = 𝟙 S)
    (h : ∀ s : S, _root_.IsConnected (f ⁻¹' {s})) : GeometricallyConnected f := by
  rw [GeometricallyConnected.iff_geometricallyConnected_fiber]
  intro s
  haveI : ConnectedSpace (f ⁻¹' {s}) := isConnected_iff_connectedSpace.mp (h s)
  haveI : ConnectedSpace (f.fiber s) :=
    (f.fiberHomeo s).symm.surjective.connectedSpace (f.fiberHomeo s).symm.continuous
  haveI : LocallyOfFiniteType (f.fiberToSpecResidueField s) :=
    instLocallyOfFiniteTypeSndScheme f (S.fromSpecResidueField s)
  exact _root_.GlobalTheory.RatPointConn.of_section (k := S.residueField s)
    (f.fiberToSpecResidueField s)
    (pullback.lift (S.fromSpecResidueField s ≫ e) (𝟙 _) (by simp [he]))
    (pullback.lift_snd _ _ _)

end GlobalTheory.SS.NeutralPart
end

