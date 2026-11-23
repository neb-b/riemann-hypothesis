module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0073
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSectionRestrictionUnitTwist
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH
open GlobalTheory.Points

theorem resG_trans_apply {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(X, U)) :
    resG X h₂ (resG X h₁ a) = resG X (h₂.trans h₁) a := by
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

theorem scale_mem_secOn {X : Scheme.{0}} (L : LB X) {V V' : X.Opens} (h : V' ≤ V) (a : Γ(X, V'))
    {σ : ∀ j, Γ(X, V ⊓ L.U j)} (hσ : σ ∈ secOn L V) :
    (fun j => resG X inf_le_left a * resG X (inf_le_inf_right _ h) (σ j)) ∈ secOn L V' := by
  intro i j
  have e := congrArg (resG X (inf_le_inf_right _ (inf_le_inf_right _ h) :
    V' ⊓ L.U i ⊓ L.U j ≤ V ⊓ L.U i ⊓ L.U j)) (hσ i j)
  simp only [map_mul, resG_trans_apply] at e ⊢
  rw [e, mul_left_comm]

theorem valF_scale {X Z : Scheme.{0}} (p : X ⟶ Z) {N N' : Z.Opens} (h : p ⁻¹ᵁ N' ≤ p ⁻¹ᵁ N) (F : Γ(Z, N'))
    (U : X.Opens) (s : Γ(X, p ⁻¹ᵁ N ⊓ U)) {K : Type} [Field K] (g : Sp K ⟶ X)
    (hg : ⊤ ≤ g ⁻¹ᵁ (p ⁻¹ᵁ N' ⊓ U)) :
    valF g (p ⁻¹ᵁ N' ⊓ U) (resG X inf_le_left ((p.app N').hom F) * resG X (inf_le_inf_right _ h) s) =
      valF (g ≫ p) N' F * valF g _ s := by
  rw [valF_eq_valR, valR_mul g _ hg, valR_res g _ hg, valR_res g _ hg, ← valR_comp]
  rfl

theorem RatModel.exists_unit_fn {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    (N' : M.Z.Opens) (f : Ω) (hf : ∀ z ∈ N', f ≠ 0 ∧ f ∈ M.O z ∧ f⁻¹ ∈ M.O z) :
    ∃ F : Γ(M.Z, N'), (∀ z ∈ N', z ∈ M.Z.basicOpen F) ∧ ((N' : Set M.Z).Nonempty → valF M.pt N' F = f) := by
  by_cases hN : (N' : Set M.Z).Nonempty
  · obtain ⟨F, hF⟩ := (RatModel.mem_ringOn_iff_exists hN).1 (RatModel.mem_ringOn.2 fun z hz => (hf z hz).2.1)
    subst hF
    exact ⟨F, fun z hz => (RatModel.isUnit_valF_iff hz F).1
      ((RatModel.isUnit_O_iff _).2 ⟨(hf z hz).1, (hf z hz).2.2⟩), fun _ => rfl⟩
  · exact ⟨1, fun z hz => (hN ⟨z, hz⟩).elim, fun h => (hN h).elim⟩

theorem ZHPre.exists_scale_section : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (N N' : M.Z.Opens) (σ : Q.SecFam N) (c f : Ω), N' ≤ N → (∀ z ∈ N', f ≠ 0 ∧ f ∈ M.O z ∧ f⁻¹ ∈ M.O z) → σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) → Q.ThMul c N σ → Q.FibNe N σ → ∃ σ' : Q.SecFam N', σ' ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N') ∧ Q.ThMul (f * c) N' σ' ∧ Q.FibNe N' σ' := by
  intro o Ω _ _ _ _ S ρ M U₀ Q N N' σ c f hN hf hσ hT hF
  obtain ⟨F, hFu, hFv⟩ := M.exists_unit_fn N' f hf
  have h : Q.G.hom ⁻¹ᵁ N' ≤ Q.G.hom ⁻¹ᵁ N := fun _ hz => hN hz
  refine ⟨_, scale_mem_secOn Q.LOne h ((Q.G.hom.app N').hom F) hσ, ?_, ?_⟩
  · intro K _ β g r jP jL h1 h2 h3 h4 h5
    have e := hT K β g r jP jL h1 h2 h3 h4 (h5.trans h)
    have hg : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N' ⊓ Q.LOne.U (fun _ => jL)) := fun w _ =>
      ⟨h5 ⟨w, rfl⟩, Set.mem_iInter.2 fun _ => h4 ⟨w, rfl⟩⟩
    have hp : (g ≫ Q.φ) ≫ Q.G.hom = spMap β ≫ M.pt := by
      rw [Category.assoc, Q.cart.1.w, ← h1]
      rfl
    have hne : (N' : Set M.Z).Nonempty := ⟨_, h5 ⟨IsLocalRing.closedPoint K, rfl⟩⟩
    have hv := valF_scale Q.G.hom h F _ (σ fun _ => jL) _ hg
    rw [hp, valF_eq_valR (spMap β ≫ M.pt), valR_spMap_comp β M.pt N' (M.top_le_preimage_pt hne),
      ← valF_eq_valR, hFv hne] at hv
    refine Eq.trans ?_ (congrArg (_ * ·) hv.symm)
    refine Eq.trans ?_ ((congrArg (β f * ·) e).trans (mul_left_comm _ _ _))
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by rw [map_mul, _root_.mul_assoc]
  · intro K _ _ x hx
    obtain ⟨g, j, hg, hne⟩ := hF K x (hx.trans hN)
    have h1 : ⊤ ≤ g ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N ⊓ Q.LOne.U j) := by
      by_contra hc
      exact hne (dif_neg hc)
    have hx' : ⊤ ≤ x ⁻¹ᵁ N' := (top_le_preimage_iff x N').2 hx
    have h2 : ⊤ ≤ g ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N' ⊓ Q.LOne.U j) := fun w hw =>
      ⟨(show ⊤ ≤ (g ≫ Q.G.hom) ⁻¹ᵁ N' from hg ▸ hx') hw, (h1 hw).2⟩
    refine ⟨g, j, hg, ?_⟩
    rw [valF_scale Q.G.hom h F _ (σ j) g h2, hg]
    exact mul_ne_zero ((le_preimage_basicOpen_iff x hx' F).1 fun w hw => hFu _ (hx' hw)).ne_zero hne

end GlobalTheory.ZH
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionSectionEqIntegralPointAtTest
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH

theorem extPt_comp_eq_integral_point : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (jV : u.V →+* OO p) (yV : Sp u.V ⟶ M.Z) (yK : Sp (FractionRing u.V) ⟶ U₀.toScheme), Q.TestFac y u jV yV yK → ∀ (F : u.G.left ⟶ Q.G.left) (ψ : pullback u.G.hom (jK u.V) ⟶ pullback ρ.P.A.hom Q.u₀), Q.TestMap u yV yK F ψ → ∀ (a : S.Gam) (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.left), Q.ExtPt a W h → ∀ (hV : Sp u.V ⟶ u.G.left) (x : Sp (FractionRing u.V) ⟶ pullback u.G.hom (jK u.V)), (hV ≫ u.G.hom = 𝟙 _ ∧ x ≫ pullback.fst _ _ = jK u.V ≫ hV ∧ x ≫ pullback.snd _ _ = 𝟙 _ ∧ x ≫ u.U.gen.hom.left ≫ u.φ = spMap u.yK ≫ (ρ.pt a).left) → ∀ yW : Sp u.V ⟶ W.toScheme, yW ≫ W.ι = yV → yW ≫ h = hV ≫ F := by
  intro o Ω _ _ _ _ S ρ M U₀ Q p _ y y₀ u jV yV yK hT F ψ hM a W h hE hV x hx yW hyW
  obtain ⟨-, -, hK, hK0⟩ := hT
  obtain ⟨hF, hψ1, hψ2, hψ3⟩ := hM
  obtain ⟨hh, hE⟩ := hE
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  have hsep : IsSeparated Q.G.hom := Q.semi.separated
  have hpa : (ρ.pt a).left ≫ ρ.P.A.hom = 𝟙 _ := Over.w (ρ.pt a)
  have hφ : Q.φ ≫ Q.G.hom = pullback.snd ρ.P.A.hom Q.u₀ ≫ U₀.ι := Q.cart.1.w
  have hFw : F ≫ Q.G.hom = u.G.hom ≫ yV := hF.1.w
  let sec : U₀.toScheme ⟶ pullback ρ.P.A.hom Q.u₀ :=
    pullback.lift (Q.u₀ ≫ (ρ.pt a).left) (𝟙 _) (by
      rw [Category.assoc, hpa]; exact (Category.comp_id _).trans (Category.id_comp _).symm)
  have hs1 : sec ≫ pullback.fst _ _ = Q.u₀ ≫ (ρ.pt a).left := pullback.lift_fst _ _ _
  have hs2 : sec ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
  have hs3 : sec ≫ Q.φ ≫ Q.G.hom = U₀.ι := by
    rw [hφ, ← Category.assoc, hs2, Category.id_comp]
  let N : M.Z.Opens := W ⊓ U₀
  let iW : N.toScheme ⟶ W.toScheme := M.Z.homOfLE inf_le_left
  let iU : N.toScheme ⟶ U₀.toScheme := M.Z.homOfLE inf_le_right
  have hiW : iW ≫ W.ι = N.ι := M.Z.homOfLE_ι _
  have hiU : iU ≫ U₀.ι = N.ι := M.Z.homOfLE_ι _
  have hr : Set.range (jK u.V ≫ yV) ⊆ Set.range N.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine ⟨?_, ?_⟩
    · rw [← hyW]
      exact (yW (jK u.V w)).2
    · rw [← hK]
      exact (yK w).2
  let k : Sp (FractionRing u.V) ⟶ N.toScheme := IsOpenImmersion.lift N.ι (jK u.V ≫ yV) hr
  have hk : k ≫ N.ι = jK u.V ≫ yV := IsOpenImmersion.lift_fac _ _ _
  have hkW : k ≫ iW = jK u.V ≫ yW := by
    rw [← cancel_mono W.ι, Category.assoc, hiW, hk, Category.assoc, hyW]
  have hkU : k ≫ iU = yK := by
    rw [← cancel_mono U₀.ι, Category.assoc, hiU, hk, hK]
  have hne : (N : Set M.Z).Nonempty :=
    ⟨_, (k (IsLocalRing.closedPoint (FractionRing u.V))).2⟩
  have hg : Set.range M.pt ⊆ Set.range N.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact M.top_le_preimage_pt hne (x := w) trivial
  let g : Sp Ω ⟶ N.toScheme := IsOpenImmersion.lift N.ι M.pt hg
  have hgN : g ≫ N.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  have : IsDominant (g ≫ N.ι) := by rw [hgN]; infer_instance
  have : IsDominant g := IsDominant.of_comp_of_isOpenImmersion g N.ι
  have key : iW ≫ h = iU ≫ sec ≫ Q.φ := by
    refine ext_of_isDominant_of_isSeparated Q.G.hom ?_ g ?_
    · simp only [Category.assoc]
      rw [hh, hs3, hiW, hiU]
    · have h1 : (g ≫ iU) ≫ U₀.ι = M.pt := by rw [Category.assoc, hiU, hgN]
      have := hE (g ≫ iW) (g ≫ iU ≫ sec) (by rw [Category.assoc, hiW, hgN])
        (by simp only [Category.assoc]; rw [hs3, hiU, hgN])
        (by
          simp only [Category.assoc]
          rw [hs1, ← Q.u₀_gen _ h1]
          simp only [Category.assoc])
      simpa only [Category.assoc] using this
  have hxψ : yK ≫ sec = x ≫ ψ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hs1, Category.assoc, hψ1, ← Category.assoc, hK0]
      exact hx4.symm
    · rw [Category.assoc, hs2, Category.assoc, hψ2, ← Category.assoc, hx3, Category.comp_id, Category.id_comp]
  have : IsDominant (jK u.V) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap u.V (FractionRing u.V))).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective u.V (FractionRing u.V))]
      exact bot_le)⟩
  refine ext_of_isDominant_of_isSeparated Q.G.hom ?_ (jK u.V) ?_
  · simp only [Category.assoc]
    rw [hh, hyW, hFw, ← Category.assoc, hx1, Category.id_comp]
  · rw [← Category.assoc, ← hkW, Category.assoc, key, ← Category.assoc, hkU, ← Category.assoc, hxψ,
      Category.assoc, hψ3, ← Category.assoc, hx2, Category.assoc]

end GlobalTheory.ZH
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelEqPullbackGroupScheme
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH

theorem exists_iso_of_existsUnique_ext {B B' : Scheme.{0}} (j : B' ⟶ B) (G G' : Over B) [GrpObj G] [GrpObj G']
    (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (hext : ∀ (G G' : Over B) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' →
      ∀ f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G', IsMonHom f →
        ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback j).map F = f)
    (e : (Over.pullback j).obj G ≅ (Over.pullback j).obj G') (he : IsMonHom e.hom) :
    ∃ E : G ≅ G', IsMonHom E.hom ∧ (Over.pullback j).map E.hom = e.hom := by
  obtain ⟨a, ⟨ha, ha'⟩, -⟩ := hext G G' hG hG' e.hom he
  obtain ⟨b, ⟨hb, hb'⟩, -⟩ := hext G' G hG' hG e.inv inferInstance
  refine ⟨⟨a, b, ?_, ?_⟩, ha, ha'⟩
  · exact (hext G G hG hG (𝟙 _) inferInstance).unique
      ⟨inferInstance, by rw [Functor.map_comp, ha', hb', e.hom_inv_id]⟩ ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩
  · exact (hext G' G' hG' hG' (𝟙 _) inferInstance).unique
      ⟨inferInstance, by rw [Functor.map_comp, ha', hb', e.inv_hom_id]⟩ ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩

theorem ZHPre.exists_testMap : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (jV : u.V →+* OO p) (yV : Sp u.V ⟶ M.Z) (yK : Sp (FractionRing u.V) ⟶ U₀.toScheme), Q.TestFac y u jV yV yK → ∃ F ψ, Q.TestMap u yV yK F ψ := by
  intro hext o Ω _ _ _ _ S ρ M U₀ Q p _ y y₀ u jV yV yK hT
  obtain ⟨-, -, h₁, h₂⟩ := hT
  have := u.U.gen_hom
  have gp₁ : IsGrpPullback ((Over.pullback (jK u.V)).obj u.G) ρ.P.A (spMap u.yK) (u.U.gen.hom.left ≫ u.φ) :=
    ((isGrpPullback_of_iso u.U.gen).comp u.cart).congr (Category.id_comp _) rfl
  have gp₂ := ((isGrpPullback_pullback ((Over.pullback Q.u₀).obj ρ.P.A) yK).comp
    (isGrpPullback_pullback ρ.P.A Q.u₀)).congr h₂ rfl
  obtain ⟨e₁, m₁, he₁⟩ := grpPullback_iso gp₁ gp₂
  have gp₃ := ((((isGrpPullback_of_iso e₁).comp
    (isGrpPullback_pullback ((Over.pullback Q.u₀).obj ρ.P.A) yK)).congr (Category.id_comp _) rfl).comp Q.cart).congr h₁ rfl
  have gp₄ := (isGrpPullback_pullback ((Over.pullback yV).obj Q.G) (jK u.V)).comp (isGrpPullback_pullback Q.G yV)
  obtain ⟨e₂, m₂, he₂⟩ := grpPullback_iso gp₃ gp₄
  obtain ⟨E, mE, hE⟩ := exists_iso_of_existsUnique_ext (jK u.V) u.G ((Over.pullback yV).obj Q.G) u.semi
    (IsSemiAbelian.pullback _ Q.G Q.semi) (fun G G' _ _ => hext u.V (FractionRing u.V) G G') e₂ m₂
  refine ⟨E.hom.left ≫ pullback.fst Q.G.hom yV,
    e₁.hom.left ≫ pullback.fst ((Over.pullback Q.u₀).obj ρ.P.A).hom yK,
    ((isGrpPullback_of_iso E).comp (isGrpPullback_pullback Q.G yV)).congr (Category.id_comp _) rfl, ?_, ?_, ?_⟩
  · exact (Category.assoc _ _ _).trans he₁
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (e₁.hom.left ≫ ·) (pullback.condition (f := ((Over.pullback Q.u₀).obj ρ.P.A).hom) (g := yK))).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ yK) (Over.w e₁.hom))
  · refine he₂.symm.trans ?_
    have a : ((Over.pullback (jK u.V)).map E.hom).left ≫ pullback.fst ((Over.pullback yV).obj Q.G).hom (jK u.V) =
        pullback.fst u.G.hom (jK u.V) ≫ E.hom.left := pullback.lift_fst _ _ _
    rw [← hE]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst Q.G.hom yV) a).trans (Category.assoc _ _ _))

end GlobalTheory.ZH
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeilPairingLabelledTorsionUniformTestStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_labelledTorsion_uniformTest : Laws → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), (∀ a, (x a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left) → ∀ a b (c : (PadicAlgCl p)ˣ), (c : PadicAlgCl p) = y₀ (algebraMap o S.R (S.ζ ^ (S.r * S.N * (eStd S.g _ a b).val))) → WeilIs u.A.A u.A.L (S.r * S.N : ℕ) (x a) (x b) (unitOn c) := by
  first | exact @GlobalTheory.ZH.weilIs_uTest | exact GlobalTheory.ZH.weilIs_uTest | (intros; apply GlobalTheory.ZH.weilIs_uTest <;> assumption)
end

