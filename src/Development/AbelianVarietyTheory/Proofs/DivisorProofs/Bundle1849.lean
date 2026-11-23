module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusOrbitOfUnramifiedPrime
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIntegralChartIntegralFramedPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1834
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1407

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportedRuleOfFlagComponentSection
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}

theorem exists_j_of_mem_flagOpen (X : FlagCover Y) {y : X.YY} (hy : y ∈ flagOpen X) :
    ∃ x : Xo.XF c, X.π y = Y.j x := by
  obtain ⟨w, rfl⟩ := (opensRange_inc X).ge hy
  refine ⟨(pullback.snd X.π Y.j) w, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]

theorem j_mem_closure_iff {s : Set (Xo.XF c)} (hs : IsClosed s) (x : Xo.XF c) :
    Y.j x ∈ closure (Y.j '' s) ↔ x ∈ s :=
  Set.ext_iff.1 (Y.j.isOpenEmbedding.isOpenMap.preimage_closure_image Y.j.isOpenEmbedding.injective Y.j.continuous _ hs) x

section Ext

variable (X : FlagCover Y) (Z : Comp Xo c)

def openOn : X.YY.Opens := flagOpen X ⊓ X.π ⁻¹ᵁ barComp Y Z

def openOff : X.YY.Opens :=
  flagOpen X ⊓ X.π ⁻¹ᵁ ⟨(closure (Y.j '' (Z : Set (Xo.XF c))))ᶜ, isClosed_closure.isOpen_compl⟩

theorem flagOpen_le_sup : flagOpen X ≤ openOn X Z ⊔ openOff X Z := fun y hy => by
  obtain ⟨x, hx⟩ := exists_j_of_mem_flagOpen X hy
  by_cases hZ : x ∈ (Z : Set (Xo.XF c))
  · refine Or.inl ⟨hy, ?_⟩
    show X.π y ∈ barComp Y Z
    rw [hx]; exact (j_mem_barComp Z x).2 hZ
  · refine Or.inr ⟨hy, ?_⟩
    show X.π y ∉ closure (Y.j '' (Z : Set (Xo.XF c)))
    rw [hx, j_mem_closure_iff (isClosed_of_mem_irreducibleComponents _ Z.2)]
    exact hZ

theorem not_mem_openOn_openOff {y : X.YY} (h₁ : y ∈ openOn X Z) (h₂ : y ∈ openOff X Z) : False := by
  obtain ⟨x, hx⟩ := exists_j_of_mem_flagOpen X h₁.1
  have a : X.π y ∈ barComp Y Z := h₁.2
  have b : X.π y ∉ closure (Y.j '' (Z : Set (Xo.XF c))) := h₂.2
  rw [hx] at a b
  exact b (subset_closure ⟨x, (j_mem_barComp Z x).1 a, rfl⟩)

end Ext

section Glue

variable {X : FlagCover Y} {Z : Comp Xo c} {e : Ix Dw → ℤ}

theorem exists_extZero (m : H0 (str₀ X Z) (LL₀ X Z e) (U₀ X Z)) :
    ∃ m' : H0 (flagStr X) (X.LL e) (flagOpen X),
      H0.pull (inc₀ X Z) le_rfl m' = m ∧ ∀ (S : Type) [CommRing S] (x : Sp S ⟶ X.YY) (k : X.F.J)
        (hO : ⊤ ≤ x ⁻¹ᵁ flagOpen X) (hk : ⊤ ≤ x ⁻¹ᵁ X.F.U k), ⊤ ≤ x ⁻¹ᵁ openOff X Z →
        H0.val (B := X.LL e) x k hO hk m' = 0 := by
  have hiso : IsoOver (inc₀ X Z) (openOn X Z) := isoOver_of_isOpenImmersion _ (by
    rw [Scheme.Opens.opensRange_ι]; exact inf_le_right)
  have e₁ : U₀ X Z ≤ inc₀ X Z ⁻¹ᵁ openOn X Z := fun z hz => ⟨hz, z.2⟩
  have e₂ : inc₀ X Z ⁻¹ᵁ openOn X Z ≤ U₀ X Z := fun z hz => hz.1
  obtain ⟨m₁, hm₁⟩ := (hiso.bijective_pull (p := flagStr X) (X.F.isLB_LL e) e₁ e₂).2 m
  let W : Bool → X.YY.Opens := fun b => Bool.rec (openOff X Z) (openOn X Z) b
  have hW : ∀ b, W b ≤ flagOpen X := fun b => by cases b <;> exact inf_le_left
  have hc : flagOpen X ≤ iSup W := fun y hy => by
    rcases flagOpen_le_sup X Z hy with h | h
    · exact Opens.mem_iSup.2 ⟨true, h⟩
    · exact Opens.mem_iSup.2 ⟨false, h⟩
  let s : ∀ b, H0 (flagStr X) (X.LL e) (W b) := fun b => Bool.rec (motive := fun b => H0 (flagStr X) (X.LL e) (W b)) 0 m₁ b
  obtain ⟨m', hm'⟩ := GlobalTheory.LB.exists_mod_of_cover (F := GlobalTheory.LB.toMod (X.LL e)) W hW hc s (by
    rintro (_ | _) (_ | _)
    · rfl
    · exact H0.ext_germ (p := flagStr X) fun y hy => (not_mem_openOn_openOff X Z hy.2 hy.1).elim
    · exact H0.ext_germ (p := flagStr X) fun y hy => (not_mem_openOn_openOff X Z hy.1 hy.2).elim
    · rfl)
  have r₁ : H0.restr (p := flagStr X) (hW true) m' = m₁ := hm' true
  have r₂ : H0.restr (p := flagStr X) (hW false) m' = 0 := hm' false
  refine ⟨m', ?_, fun S _ x k hO hk hx => ?_⟩
  · have h₃ : H0.pull (p := flagStr X) (inc₀ X Z) e₁ (H0.restr (p := flagStr X) (hW true) m') =
        H0.pull (p := flagStr X) (inc₀ X Z) le_rfl m' := H0.pull_restr _ _ _ _
    rw [r₁] at h₃
    exact h₃.symm.trans hm₁
  · have a := GlobalTheory.TangentOrigin.evalPt_res x (inf_le_inf_right _ (hW false)) (GlobalTheory.FlagMod.le_preimage_inf hO hk)
      (GlobalTheory.FlagMod.le_preimage_inf hx hk) (H0.loc (p := flagStr X) m' k)
    refine a.symm.trans ?_
    change H0.val (B := X.LL e) x k hx hk (H0.restr (p := flagStr X) (hW false) m') = 0
    rw [r₂, map_zero]

end Glue

theorem exists_suppOn_sec₀_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : FlagCover Y) (Z : Comp Xo c) (e : Ix Dw → ℤ) (m : H0 (str₀ X Z) (LL₀ X Z e) (U₀ X Z)), ∃ f : GlobalTheory.AllWt.secZ Xo c e, (f : Rul Xo c) ∈ GlobalTheory.AllWt.suppOn Z ∧ sec₀ X Z e f = m := by
  intro E _ _ _ H Dw l Xo c Y X Z e m
  obtain ⟨m', h₁, h₂⟩ := exists_extZero m
  refine ⟨(secOf X e).symm m', ?_, ?_⟩
  · intro S _ _ y hy
    have hv : FlagCover.val (toSecO m') y = 0 := by
      refine (FlagCover.IsVal.eq_val fun S' _ _ ψ P' hP k hz Q t hQ ht => ?_).symm
      have hO := FlagMod.le_preimage_map (z := X.pt P') X.inc (top_le_inc X) le_top
      rw [map_zero, coef_toSecO _ _ _ _ hO, h₂ _ _ _ _ _ ?_, mul_zero]
      intro s _
      refine ⟨hO (Set.mem_univ s), ?_⟩
      show X.π ((X.pt P' ≫ X.inc) s) ∉ closure (Y.j '' (Z : Set (Xo.XF c)))
      rw [FlagCover.pt_inc, ← Scheme.Hom.comp_apply, (X.lies_ptY P').1, Scheme.Hom.comp_apply,
        j_mem_closure_iff (isClosed_of_mem_irreducibleComponents _ Z.2), ← FlagMod.frX_frMap hP,
        Scheme.Hom.comp_apply]
      exact hy _
    change evR Xo c (FlagCover.toRule (toSecO m')) y = 0
    by_cases hT : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y
    · rw [FlagCover.evR_toRule _ y hT, hv]
    · unfold evR evalAt
      rw [dite_eq_right hT]
  · show H0.pull (inc₀ X Z) le_rfl ((secOf X e) ((secOf X e).symm m')) = m
    rw [LinearEquiv.apply_symm_apply]
    exact h₁

end GlobalTheory.CompHS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorSectionNonvanishingOfBaseChange
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

noncomputable section

namespace GlobalTheory.FieldDescent

open scoped TensorProduct


open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC in
theorem exists_sec_of_pull {F E : Type} [Field F] [Field E] [Algebra F E] {Y X : Scheme.{0}}
    {p : Y ⟶ Sp F} {q : X ⟶ Sp E} {π : X ⟶ Y} (H : IsPullback π q p (spMap (algebraMap F E)))
    [CompactSpace Y] [Y.IsSeparated] {N : LB Y} (hN : N.IsLB) (σ : (N.pull π).Sec) (x : X)
    (hx : x ∈ nonzeroLocus σ) : ∃ θ : N.Sec, π x ∈ nonzeroLocus θ := by
  classical
  obtain ⟨n, V, c, hVa, hVc, hcov⟩ := exists_affine_chart_cover N hN
  letI instV : ∀ a, Algebra F Γ(Y, V a) := fun a => (algX p (V a)).toAlgebra
  letI instW : ∀ ab : Fin n × Fin n, Algebra F Γ(Y, V ab.1 ⊓ V ab.2) := fun ab => (algX p _).toAlgebra
  let δ : (∀ a, Γ(Y, V a)) →ₗ[F] (∀ ab : Fin n × Fin n, Γ(Y, V ab.1 ⊓ V ab.2)) :=
    { toFun := fun f ab => dfun N V c hVc f ab.1 ab.2
      map_add' := fun f g => by
        funext ab
        simp only [dfun, Pi.add_apply, map_add (f := _), mul_add]
        abel
      map_smul' := fun r f => by
        funext ab
        simp only [dfun, RingHom.id_apply, Pi.smul_apply, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
        rw [ReciprocityTheory.ChartRestriction.G.DVR.rs_mul, ReciprocityTheory.ChartRestriction.G.DVR.rs_mul, rs_algX, rs_algX]
        ring }
  have hδ : ∀ m, δ m = 0 ↔ dfun N V c hVc m = 0 := fun m => by
    constructor
    · intro h; funext a b; exact congrFun h (a, b)
    · intro h; funext ab; exact congrFun (congrFun h ab.1) ab.2
  have hV'c : ∀ a, π ⁻¹ᵁ V a ⊓ q ⁻¹ᵁ ⊤ ≤ (N.pull π).U (fun _ => c a) := fun a y hy =>
    Set.mem_iInter.2 fun _ => hVc a hy.1
  let m' : ∀ a, Γ(X, π ⁻¹ᵁ V a ⊓ q ⁻¹ᵁ ⊤) := fun a => ReciprocityTheory.ChartRestriction.G.DVR.rs (hV'c a) (σ.f (fun _ => c a))
  let t : (∀ a, Γ(Y, V a)) ⊗[F] E := (TensorProduct.piLeft (R := F) (N := E) (M := fun a => Γ(Y, V a))).symm
    (fun a => (eTens p q π H (V a) (hVa a)).symm (m' a))
  have hpt : ∀ a, (TensorProduct.piLeft (R := F) (N := E) (M := fun a => Γ(Y, V a))) t a =
      (eTens p q π H (V a) (hVa a)).symm (m' a) := fun a => by
    simp only [t, LinearEquiv.apply_symm_apply]
  have ht : δ.rTensor E t = 0 := by
    apply (TensorProduct.piLeft (R := F) (N := E) (M := fun ab : Fin n × Fin n => Γ(Y, V ab.1 ⊓ V ab.2))).injective
    rw [map_zero]
    funext ab
    obtain ⟨a, b⟩ := ab
    rw [piLeft_apply_eq, ← LinearMap.rTensor_comp_apply]
    have hdec : (LinearMap.proj (a, b) : (∀ ab : Fin n × Fin n, Γ(Y, V ab.1 ⊓ V ab.2)) →ₗ[F] _).comp δ =
        (rsL p (V a) (V a ⊓ V b) inf_le_left).comp (LinearMap.proj a) -
          (mulL p (V a ⊓ V b) (ReciprocityTheory.ChartRestriction.G.Semi.res (pair_le N V c hVc a b) (N.g (c a) (c b))).val).comp
            ((rsL p (V b) (V a ⊓ V b) inf_le_right).comp (LinearMap.proj b)) := by
      ext f; rfl
    rw [hdec, LinearMap.rTensor_sub, LinearMap.sub_apply, LinearMap.rTensor_comp_apply, LinearMap.rTensor_comp_apply,
      LinearMap.rTensor_comp_apply, ← piLeft_apply_eq, ← piLeft_apply_eq, hpt, hpt]
    apply (eTens p q π H (V a ⊓ V b) ((hVa a).inf (hVa b))).injective
    rw [map_sub, eTens_rs p q π H (V a) (V a ⊓ V b) (hVa a) _ inf_le_left, eTens_mul,
      eTens_rs p q π H (V b) (V a ⊓ V b) (hVa b) _ inf_le_right, RingEquiv.apply_symm_apply,
      RingEquiv.apply_symm_apply, Pi.zero_apply, map_zero, sub_eq_zero]
    refine ReciprocityTheory.ChartRestriction.G.Geo.Tor.fn_ext fun y hy => ?_
    have hyk : y ∈ (N.pull π).U (fun _ => c a) := Set.mem_iInter.2 fun _ => hVc a hy.1.1
    have hyl : y ∈ (N.pull π).U (fun _ => c b) := Set.mem_iInter.2 fun _ => hVc b hy.1.2
    have hyk' : y ∈ π ⁻¹ᵁ V a ⊓ q ⁻¹ᵁ ⊤ := ⟨hy.1.1, hy.2⟩
    have hyl' : y ∈ π ⁻¹ᵁ V b ⊓ q ⁻¹ᵁ ⊤ := ⟨hy.1.2, hy.2⟩
    have hφy : π y ∈ V a ⊓ V b := hy.1
    simp only [m']
    rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_mul _ y _ hy, ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_res _ y _ hy,
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_res _ y _ hyk', ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_res _ y _ hy,
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_res _ y _ hyl', ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_appLE π _ _ _ (𝟙 _) y hy]
    erw [Category.id_comp, ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_unit _ y _ hφy, ReciprocityTheory.ChartRestriction.G.Geo.Tor.gm_res _ y _ hφy]
    erw [gs_sec (N.pull π) σ (fun _ => c a) (fun _ => c b) y hyk hyl,
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.gm_pull_g N π (𝟙 _) y (fun _ => c a) (fun _ => c b) hyk hyl, Category.id_comp]
  let b := Module.Basis.ofVectorSpace F E
  let e₁ := TensorProduct.equivFinsuppOfBasisRight (M := ∀ a, Γ(Y, V a)) b
  let e₂ := TensorProduct.equivFinsuppOfBasisRight (M := ∀ ab : Fin n × Fin n, Γ(Y, V ab.1 ⊓ V ab.2)) b
  have nat : ∀ u β, e₂ (δ.rTensor E u) β = δ (e₁ u β) := by
    intro u β
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul m a =>
      simp only [LinearMap.rTensor_tmul, e₁, e₂, TensorProduct.equivFinsuppOfBasisRight_apply_tmul,
        Finsupp.mapRange_apply, map_smul]
    | add u v hu hv => simp only [map_add (f := _), Finsupp.add_apply, hu, hv]
  have hβ : ∀ β, dfun N V c hVc (e₁ t β) = 0 := fun β =>
    (hδ _).1 (by rw [← nat, ht, map_zero, Finsupp.zero_apply])
  choose θ hθ using fun β => exists_glue N V c hVc hN hcov (e₁ t β) (hβ β)
  by_contra hcon
  push_neg at hcon
  obtain ⟨j, hj⟩ : ∃ j, π x ∈ V j := TopologicalSpace.Opens.mem_iSup.1 (by rw [hcov]; trivial)
  have hxj : x ∈ π ⁻¹ᵁ V j ⊓ q ⁻¹ᵁ ⊤ := ⟨hj, trivial⟩
  have hxc : x ∈ (N.pull π).U (fun _ => c j) := hV'c j hxj
  have hu := (mem_nonzeroLocus_iff_isUnit σ hxc).1 hx
  rw [← ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_res (𝟙 X) x (hV'c j) hxj] at hu
  change IsUnit (ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs (𝟙 X) x _ (m' j)) at hu
  have hexp : t = (e₁ t).sum fun β m => m ⊗ₜ[F] b β := by
    rw [← TensorProduct.equivFinsuppOfBasisRight_symm_apply, LinearEquiv.symm_apply_apply]
  have hm : m' j = (e₁ t).sum fun β m => (π.appLE (V j) (π ⁻¹ᵁ V j ⊓ q ⁻¹ᵁ ⊤) inf_le_left).hom (m j) *
      algX q (π ⁻¹ᵁ V j ⊓ q ⁻¹ᵁ ⊤) (b β) := by
    have h1 := hpt j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hexp, piLeft_apply_eq, Finsupp.sum, map_sum] at h1
    simp only [LinearMap.rTensor_tmul, LinearMap.proj_apply] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← RingEquiv.apply_symm_apply (eTens p q π H (V j) (hVa j)) (m' j), ← h1, map_sum, Finsupp.sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [eTens_tmul]
  have key : ∀ β, ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs (𝟙 X) x _
      ((π.appLE (V j) (π ⁻¹ᵁ V j ⊓ q ⁻¹ᵁ ⊤) inf_le_left).hom (e₁ t β j)) ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) := fun β => by
    rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_appLE π _ _ _ (𝟙 X) x hxj, Category.id_comp, ← hθ β]
    simp only [ev]
    rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_res π x (hVc j) hj, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      ← mem_nonzeroLocus_iff_pull (θ β) π x (hVc j hj)]
    exact hcon (θ β)
  have hmem : ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs (𝟙 X) x _ (m' j) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hm, Finsupp.sum, ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_eq (𝟙 X) x _ hxj, map_sum, map_sum]
    refine Ideal.sum_mem _ fun β _ => ?_
    rw [map_mul, map_mul, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_eq (𝟙 X) x _ hxj]
    exact Ideal.mul_mem_right _ _ (key β)
  exact (IsLocalRing.mem_maximalIdeal _).1 hmem hu

theorem exists_sec_tens_of_baseChange : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → ∀ (L M : LB Y), L.IsLB → M.IsLB → ∀ x : X, (∃ s : (tens (L.pull π) (M.pull π)).Sec, x ∈ nonzeroLocus s) → ∃ s : (tens L M).Sec, π x ∈ nonzeroLocus s := by
  intro k E _ _ _ Y X p q π H hP L M hL hM x ⟨s, hs⟩
  have : IsProper p := CommonModel.isProper_of_isProjOver hP
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  have : Y.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  have hN := isLB_tens hL hM
  have hNp := LB.isLB_pull hN π
  have hT := isLB_tens (LB.isLB_pull hL π) (LB.isLB_pull hM π)
  have iso : LBIso ((tens L M).pull π) (tens (L.pull π) (M.pull π)) := by
    refine (cls_eq_iff hNp hT).1 ?_
    rw [cls_pull hN π hNp, cls_tens hL hM hN, map_add (f := _), cls_tens (LB.isLB_pull hL π) (LB.isLB_pull hM π) hT,
      cls_pull hL π, cls_pull hM π]
  obtain ⟨s₂, hs₂⟩ := exists_sec_nonzeroLocus_eq_of_lbIso hNp hT iso s
  exact exists_sec_of_pull H hN s₂ x (hs₂ ▸ hs)

end GlobalTheory.FieldDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorDepthUpperBoundOddUnramifiedPrime
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FacUpOdd

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem inPsi_conj_iff (H : Host E) (τ : E →+* ℂ) :
    InPsi H (ComplexEmbedding.conjugate τ) ↔ ¬ InPsi H τ := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hre := congrArg Complex.re H.sqrt_neg_disc_sq
  have him := congrArg Complex.im H.sqrt_neg_disc_sq
  simp [pow_two] at hre him
  have hre0 : H.rt0.re = 0 := by
    by_contra hne
    have : H.rt0.im = 0 := by
      have : H.rt0.re * H.rt0.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [this] at hre
    nlinarith [mul_self_nonneg H.rt0.re]
  have hc : starRingEnd ℂ H.rt0 = -H.rt0 := Complex.ext (by simp [hre0]) (by simp)
  have h0 : H.rt0 ≠ 0 := by
    intro h0
    rw [h0] at hre
    simp at hre
    exact H.d_prime.ne_zero (by exact_mod_cast hre)
  have h3 : ¬ (-H.rt0 = H.rt0) := fun h => h0 (by linear_combination (-1/2 : ℂ) * h)
  have hsq : (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
    rw [H.sqrt_neg_disc_sq, ← map_pow]
    have : ((H.rt : E)) ^ 2 = -(H.d : E) := by
      have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
      simpa using this
    rw [this]; simp
  unfold InPsi
  rw [ComplexEmbedding.conjugate_coe_eq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
  · rw [h, hc]; simp [h3]
  · rw [h, map_neg, hc, neg_neg]; simp [h3]

theorem mult_of_inPsi {H : Host E} (Dw : Datum H) {τ : E →+* ℂ} (h : InPsi H τ) : Dw.mult τ = Dw.p := by
  unfold Datum.mult; rw [if_pos (show τ (H.rt : E) = H.rt0 from h)]

theorem mult_of_not_inPsi {H : Host E} (Dw : Datum H) {τ : E →+* ℂ} (h : ¬ InPsi H τ) : Dw.mult τ = Dw.q := by
  unfold Datum.mult; rw [if_neg (show ¬ τ (H.rt : E) = H.rt0 from h)]

theorem rpow_neg_succ (p : ℕ) (hp : 0 < p) (i : ℕ) :
    (p : ℝ) ^ (-((i : ℝ) + 1)) = ((p : ℝ)⁻¹) ^ (i + 1) := by
  have hp0 : (0 : ℝ) ≤ p := by positivity
  rw [Real.rpow_neg hp0, show ((i : ℝ) + 1) = ((i + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, inv_pow]

theorem tsum_const (p : ℕ) (hp : 1 < p) (q : ℝ) :
    ∑' i : ℕ, (p : ℝ) ^ (-((i : ℝ) + 1)) * q = q / ((p : ℝ) - 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have r0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have r1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  have e : (fun i : ℕ => (p : ℝ) ^ (-((i : ℝ) + 1)) * q) = fun i => ((p : ℝ)⁻¹) ^ i * ((p : ℝ)⁻¹ * q) := by
    funext i; rw [rpow_neg_succ p (by omega), pow_succ]; ring
  rw [e, tsum_mul_right, tsum_geometric_of_lt_one r0 r1]
  have : (p : ℝ) - 1 ≠ 0 := by linarith
  have : (p : ℝ) ≠ 0 := by linarith
  field_simp

theorem tsum_alt (p : ℕ) (hp : 1 < p) (a b : ℝ) :
    ∑' i : ℕ, (p : ℝ) ^ (-((i : ℝ) + 1)) * (if Even i then a else b) = (a * p + b) / ((p : ℝ) ^ 2 - 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  set r : ℝ := (p : ℝ)⁻¹ with hr
  have r0 : (0 : ℝ) ≤ r ^ 2 := by positivity
  have r1 : r ^ 2 < 1 := by
    have : r < 1 := inv_lt_one_of_one_lt₀ hp1
    have : 0 ≤ r := by positivity
    nlinarith
  set g : ℕ → ℝ := fun i => (p : ℝ) ^ (-((i : ℝ) + 1)) * (if Even i then a else b) with hg
  have ge : (fun k => g (2 * k)) = fun k => (r ^ 2) ^ k * (r * a) := by
    funext k
    simp only [hg]
    rw [rpow_neg_succ p (by omega), if_pos (even_two_mul k), ← hr, pow_succ, pow_mul]; ring
  have go : (fun k => g (2 * k + 1)) = fun k => (r ^ 2) ^ k * (r ^ 2 * b) := by
    funext k
    simp only [hg]
    rw [rpow_neg_succ p (by omega), if_neg (Nat.not_even_iff_odd.2 (odd_two_mul_add_one k)), ← hr,
      show 2 * k + 1 + 1 = 2 * k + 2 by ring, pow_add, pow_mul]; ring
  have hs := summable_geometric_of_lt_one r0 r1
  rw [← tsum_even_add_odd (by rw [ge]; exact hs.mul_right _) (by rw [go]; exact hs.mul_right _), ge, go,
    tsum_mul_right, tsum_mul_right, tsum_geometric_of_lt_one r0 r1]
  have h2 : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have h3 : (1 : ℝ) - r ^ 2 ≠ 0 := by linarith
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  rw [hr]
  field_simp

end GlobalTheory.FacUpOdd

namespace GlobalTheory.FacUpOdd

theorem nuFac_le_odd_unram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), ¬ IsUnit (p : T.V) → y.IsAlg → p ≠ 2 → ¬ (p : ℤ) ∣ discr E → ∀ (f : Lt1 Dw) (k : ℕ), InPsi H f.1 → (SplitInK H p → nuFac p y f k ≤ ((k * (Dw.q / ((p : ℝ) - 1)) : ℝ) : EReal)) ∧ (InertInK H p → nuFac p y f k ≤ ((k * (Dw.q / ((p : ℝ) - 1) + ((Dw.p : ℝ) - Dw.q) * p / ((p : ℝ) ^ 2 - 1)) : ℝ) : EReal)) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p _ T io y hnu hy hp2 hdisc f k hpsi
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  obtain ⟨X⟩ := GlobalTheory.CharDepth.nonempty_valExt T p hnu
  obtain ⟨Ch⟩ := (GlobalTheory.IntChartExists.intChart_exists E H Dw l Xo c).1 (fun _ => rfl) T io y
  obtain ⟨hfot, horb⟩ := _root_.GlobalTheory.FrobOrbit.frobOnType_and_orbit E H l c p T io X hdisc
  obtain ⟨τ, i⟩ := f
  obtain ⟨h, hh, -, lab, hl0, hfr, hinj, -⟩ := horb τ
  haveI : NeZero h := ⟨hh.ne'⟩
  subst hl0
  obtain ⟨xs, hxs, hle⟩ := GlobalTheory.CharMinor.colength_bound p (GlobalTheory.ChF.unramified_companion_chart_characters p) hp2 E H Dw l Xo c
    T io y Ch X hy hdisc h lab hinj (fun s x => hfr s x) 0
  have hnu := (GlobalTheory.T.flagStep_characters_of_colength E H Dw l Xo c p T io y Ch X ⟨lab 0, i⟩ xs _ hxs hle).2 k
  have hstep : ∀ n : ℕ, lab ((n + 1 : ℕ) : ZMod h) = lab ((n : ZMod h) + 1) := fun n => by push_cast; rfl
  refine ⟨fun hs => ?_, fun hi => ?_⟩
  · have hall : ∀ n : ℕ, InPsi H (lab (n : ZMod h)) := by
      intro n
      induction n with
      | zero => simpa using hpsi
      | succ n ih => rw [hstep]; exact ((hfot _ _ (hfr _)).1 hs).2 ih
    refine hnu.trans (le_of_eq ?_)
    congr 2
    rw [← tsum_const p hp1]
    refine tsum_congr fun n => ?_
    rw [zero_add, mult_of_not_inPsi Dw ((inPsi_conj_iff H _).1.mt (not_not.2 (hall (n + 1))))]
  · have halt : ∀ n : ℕ, InPsi H (lab (n : ZMod h)) ↔ Even n := by
      intro n
      induction n with
      | zero => simpa using hpsi
      | succ n ih =>
        rw [hstep, ((hfot _ _ (hfr _)).2 hi), inPsi_conj_iff, ih, Nat.even_add_one]
    refine hnu.trans (le_of_eq ?_)
    congr 2
    have e : ∀ n : ℕ, (Dw.mult (ComplexEmbedding.conjugate (lab (0 + ((n + 1 : ℕ) : ZMod h)))) : ℝ) =
        if Even n then (Dw.p : ℝ) else Dw.q := by
      intro n
      rw [zero_add]
      by_cases hn : Even n
      · rw [if_pos hn, mult_of_inPsi Dw ((inPsi_conj_iff H _).2 (fun h' => ?_))]
        have := (halt (n + 1)).1 h'
        rw [Nat.even_add_one] at this
        exact this hn
      · rw [if_neg hn, mult_of_not_inPsi Dw (fun h' => ?_)]
        have := (inPsi_conj_iff H _).1 h'
        rw [halt, Nat.even_add_one, not_not] at this
        exact hn this
    rw [tsum_congr fun n => by rw [e n], tsum_alt p hp1]
    have hp1' : (1 : ℝ) < p := by exact_mod_cast hp1
    have h2 : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    have h3 : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring

end GlobalTheory.FacUpOdd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantAdmissibleFormEqMulDiagonalInStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergInvariant_admissibleForm_eq_mul_diagonalIntegral : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (κ : Type) [Fintype κ] (l : ((κ ⊕ κ → AF F) → ℂ) →ₗ[ℂ] ℂ), l ∈ (adeleClass F).adm (κ ⊕ κ) →
      (∀ x y : κ → AF F, ∀ Φ ∈ schA F (κ ⊕ κ), l (schr ψ (Sum.elim x x, Sum.elim y (-y)) Φ) = l Φ) →
      ∀ μ : @MeasureTheory.Measure (κ → AF F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∃ c : ℂ, ∀ Φ ∈ schA F (κ ⊕ κ), l Φ = c * GlobalTheory.DiagSiegel.diagInt μ Φ := by
  first | exact @GlobalTheory.DiagUniq.eq_mul_diagInt | exact GlobalTheory.DiagUniq.eq_mul_diagInt | (intros; apply GlobalTheory.DiagUniq.eq_mul_diagInt <;> assumption)
end

