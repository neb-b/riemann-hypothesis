module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1848
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1890
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1476
public import Formalism.MeanHeightDescent.AverageDegreeBounds.GlobalBoundRefinements
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1878
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1259

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionSeparatingClosedPoint
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
open GlobalTheory.Twist GlobalTheory.SerreCriterion

set_option autoImplicit false
noncomputable section
namespace GlobalTheory
namespace IsolatedSecZero
variable {X : Scheme.{0}}

theorem exists_germ_eq_zero_of_isolated {F : X.Modules} {y : X} (hy : IsClosed ({y} : Set X))
    {U : X.Opens} (hyU : y ∈ U) (hF : ∀ z ∈ U, z ∈ support F → z = y)
    (t : (F.presheaf.stalk y :)) : ∃ s : Γ(F, ⊤), F.presheaf.germ ⊤ y trivial s = t ∧
      ∀ z, z ≠ y → F.presheaf.germ ⊤ z trivial s = 0 := by
  obtain ⟨V, hyV, s, rfl⟩ := F.presheaf.exists_germ_eq t
  let W : X.Opens := ⟨{y}ᶜ, hy.isOpen_compl⟩
  let C : Bool → X.Opens := fun b => if b then V ⊓ U else W
  have hzero : ∀ (O : X.Opens), O ≤ V ⊓ U ⊓ W → ∀ r : Γ(F, O), r = 0 := fun O hO r => by
    refine TopCat.Presheaf.section_ext (abSheaf F) O r 0 fun z hz => ?_
    have hz' := hO hz
    have hns : z ∉ support F := fun h => hz'.2 (hF z hz'.1.2 h)
    exact (notMem_support_iff.1 hns).elim _ _
  obtain ⟨g, hg⟩ := exists_sec_of_cover (F := F) C (fun _ => le_top)
    (fun z _ => by
      by_cases h : z = y
      · subst h; exact Opens.mem_iSup.2 ⟨true, ⟨hyV, hyU⟩⟩
      · exact Opens.mem_iSup.2 ⟨false, h⟩)
    (fun b => match b with
      | true => resM F (inf_le_left : V ⊓ U ≤ V) s
      | false => 0)
    (fun k l => by
      cases k <;> cases l
      · rfl
      · exact (hzero _ (le_inf inf_le_right inf_le_left) _).trans (hzero _ (le_inf inf_le_right inf_le_left) _).symm
      · exact (hzero _ (le_inf inf_le_left inf_le_right) _).trans (hzero _ (le_inf inf_le_left inf_le_right) _).symm
      · rfl)
  refine ⟨g, ?_, fun z hz => ?_⟩
  · have hyVU : y ∈ V ⊓ U := ⟨hyV, hyU⟩
    have := congrArg (F.presheaf.germ (V ⊓ U) y hyVU) (hg true)
    dsimp only at this
    rw [germ_resM, germ_resM] at this
    exact this
  · have hzW : z ∈ W := hz
    have := congrArg (F.presheaf.germ W z hzW) (hg false)
    dsimp only at this
    rw [germ_resM, map_zero] at this
    exact this
end IsolatedSecZero

theorem exists_sec_mem_nonzeroLocus_of_isolated_zero_else : ∀ (k : Type) [Field k] (X : Scheme.{0})
    [IsIntegral X] (q : X ⟶ Sp k), IsProjOver q → ∀ (L : LB X), L.IsLB →
    ∀ (J : X.IdealSheafData) (x : X) (U : X.Opens), IsClosed ({x} : Set X) → x ∈ U →
    (∀ y ∈ U, y ∈ J.support ↔ y = x) → Subsingleton (coh (twist (idealModule J) L) 1) →
    ∃ s : L.Sec, x ∈ nonzeroLocus s ∧ ∀ y ∈ J.support, y ≠ x → y ∉ nonzeroLocus s := by
  intro k _ X _ q _ N hN J x U hxc hxU hJ h
  set φ := toSubscheme J with hφ
  let S : ShortComplex X.Modules :=
    ShortComplex.mk (kernel.ι φ) (cokernel.π (kernel.ι φ)) (cokernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  have hS' : (S.map (twistFunctor N)).ShortExact := Twist.shortExact_map hN hS
  have hsurj := cohOn.app_surjective hS' ⊤ h
  have hQ : ∀ z ∈ U, z ∈ support (twist S.X₃ N) → z = x := by
    intro z hzU hz
    rw [support_twist hN] at hz
    have := mem_support_iff.1 hz
    refine (hJ z hzU).1 (support_pushforward_subscheme_subset J ?_)
    exact mem_support_iff.2 (stalkLinear_injective (Abelian.factorThruCoimage φ) z).nontrivial
  have hx : x ∈ J.support := (hJ x hxU).2 rfl
  obtain ⟨c, hc⟩ := exists_chart hN x
  let one : Γ(QCoh.structureModule X, ⊤) := (structureModuleSectionsEquiv ⊤).symm 1
  obtain ⟨b, hb, hb0⟩ := IsolatedSecZero.exists_germ_eq_zero_of_isolated hxc hxU hQ
    ((stalkEquiv S.X₃ hN c hc).symm
      (stalkLinear S.g x ((QCoh.structureModule X).presheaf.germ ⊤ x trivial one)))
  obtain ⟨a, rfl⟩ := hsurj b
  refine ⟨secOfTwist (𝟙 _) a, ?_, ?_⟩
  · have hm : x ∈ ⊤ ⊓ N.U c := ⟨trivial, hc⟩
    replace hb := (stalkEquiv_germ hN c hc (V := ⊤) trivial _).symm.trans
      ((LinearEquiv.eq_symm_apply _).1 hb)
    have h₁ : stalkLinear S.g x ((QCoh.structureModule X).presheaf.germ _ x hm
        (coord (F := QCoh.structureModule X) a c)) =
        stalkLinear S.g x ((QCoh.structureModule X).presheaf.germ ⊤ x trivial one) :=
      (stalkLinear_germ S.g x hm _).trans hb
    have h₂ : stalkLinear φ x ((QCoh.structureModule X).presheaf.germ ⊤ x trivial one -
        (QCoh.structureModule X).presheaf.germ _ x hm (coord (F := QCoh.structureModule X) a c)) = 0 := by
      rw [← Abelian.coimage.fac φ, stalkLinear_comp, LinearMap.comp_apply, map_sub]
      exact (congrArg _ (sub_eq_zero.2 h₁.symm)).trans (map_zero _)
    have h₃ := not_isUnit_of_toSubscheme_eq_zero J hx _ h₂
    rw [map_sub] at h₃
    erw [structureModuleStalkEquiv_germ, structureModuleStalkEquiv_germ] at h₃
    have h1 : structureModuleSectionsEquiv ⊤ one = 1 := by simp [one]
    rw [h1, map_one] at h₃
    have hu := (IsLocalRing.isUnit_or_isUnit_one_sub_self _).resolve_right h₃
    refine basicOpen_le_nonzeroLocus _ c ((X.mem_basicOpen _ x hc).2 ?_)
    erw [secOfTwist_f]
    exact (congrArg IsUnit (X.presheaf.germ_res_apply (homOfLE _) x hc _)).mpr hu
  · intro y hy hyx hmem
    obtain ⟨d, hd⟩ := Opens.mem_iSup.1 hmem
    have hyd : y ∈ N.U d := X.basicOpen_le _ hd
    have hm : y ∈ ⊤ ⊓ N.U d := ⟨trivial, hyd⟩
    have e0 := hb0 y hyx
    have h₁ : stalkLinear S.g y ((QCoh.structureModule X).presheaf.germ _ y hm
        (coord (F := QCoh.structureModule X) a d)) = 0 := by
      have := (stalkEquiv_germ hN d hyd (V := ⊤) trivial _).symm.trans
        (congrArg (stalkEquiv S.X₃ hN d hyd) e0)
      rw [map_zero] at this
      exact (stalkLinear_germ S.g y hm _).trans this
    have h₂ : stalkLinear φ y ((QCoh.structureModule X).presheaf.germ _ y hm
        (coord (F := QCoh.structureModule X) a d)) = 0 := by
      rw [← Abelian.coimage.fac φ, stalkLinear_comp, LinearMap.comp_apply]
      exact (congrArg _ h₁).trans (map_zero _)
    have h₃ := not_isUnit_of_toSubscheme_eq_zero J hy _ h₂
    rw [structureModuleStalkEquiv_germ] at h₃
    apply h₃
    erw [secOfTwist_f] at hd
    exact (congrArg IsUnit (X.presheaf.germ_res_apply (homOfLE _) y hyd _)).mp
      ((X.mem_basicOpen _ y hyd).1 hd)
end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianMapModelOfIntegralFramedPoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_sabMap_model_of_integral_frPt : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (y : FrPt Xo c T.Fr) (x : Sp T.V ⟶ Y.X), spMap (algebraMap T.V T.Fr) ≫ x = GlobalTheory.FlagMod.frX y ≫ Y.j → ∀ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m1 : SABMap t' Xo.univ.t y.x) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))), ∃ (ψ : SABMap G Y.t x) (ρ : t'.G.left ⟶ Y.oF.t.G.left), ρ ≫ Y.m0.toSABMap.φ = m1.φ ∧ ρ ≫ Y.oF.t.G.hom = t'.G.hom ≫ GlobalTheory.FlagMod.frX y ∧ ρ ≫ Y.m.φ = m2.φ ≫ ψ.φ := by
  intro E _ _ _ H Dw l Xo c O _ β Y T io
  letI := io.toAlgebra
  intro y x hx G t' m1 m2
  have tr : ∀ {S S' : Scheme.{0}} {s : SAB H S} {s' : SAB H S'} {f g : S' ⟶ S}, f = g → ∀ m : SABMap s' s f,
      ∃ m' : SABMap s' s g, m'.φ = m.φ := by
    intro S S' s s' f g h m
    subst h
    exact ⟨m, rfl⟩
  obtain ⟨m1', hm1⟩ := tr (GlobalTheory.FlagMod.frX_fst y).symm m1
  obtain ⟨ρ, hρ⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m0.toSABMap m1'
  obtain ⟨a, ha⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m ρ
  obtain ⟨a', ha'⟩ := tr hx.symm a
  obtain ⟨G₂, ⟨pull⟩⟩ : ∃ G₂ : SAB H (Sp T.V), Nonempty (SABMap G₂ Y.t x) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull x Y.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨c2, hc2⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ pull a'
  obtain ⟨k, n, hk, hn⟩ := sab_extensions_iso E H Dw l Xo T.V T.Fr y.x G G₂ t' t' m1 m2 m1 c2
  have hk1 : k.φ = 𝟙 _ := by
    apply m1.cart.1.hom_ext
    · rw [Category.id_comp]; exact hk
    · rw [Category.id_comp]; exact k.cart.1.w.trans (Category.comp_id _)
  obtain ⟨b, hb⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ pull n
  obtain ⟨ψ, hψ⟩ := tr (Category.id_comp x) b
  refine ⟨ψ, ρ.φ, by rw [← hρ, hm1], ρ.cart.1.w, ?_⟩
  rw [← ha, ← ha', hc2, hψ, hb, ← Category.assoc, hn, hk1, Category.id_comp]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallScalarReflexIdealSelfDualLattice
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option autoImplicit false

open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.SmallScal


set_option maxHeartbeats 1600000 in
theorem exists_small_scalar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (c : Coeff l) (n : ℕ) (La : GenLat E n), La.Unimod → ∃ s : c.F, s ≠ 0 ∧ Submodule.span (𝓞 c.F) {s} * ∏ τ : E →+* ℂ, idealAt c La.Ln τ ^ Dw.mult τ ≤ ∏ τ : E →+* ℂ, idealAt c La.La τ ^ Dw.mult τ ∧ ∀ σ : c.F →+* ℂ, ‖σ s‖ ^ 2 * ((La.Ln.toAddSubgroup.addSubgroupOf La.La.toAddSubgroup).index : ℝ) ^ (Dw.p + Dw.q) ≤ Real.exp (fieldSz c.F) ^ 2 := by
  intro E _ _ _ H Dw l c n La hU
  haveI : IsTotallyComplex c.F := GlobalTheory.CompHS.isTotallyComplex_coeff c
  obtain ⟨𝔞, h0, h1, h2⟩ := GlobalTheory.BetaEx.exists_index_ideal La.Ln La.La inf_le_left
    (GlobalTheory.BetaEx.bdd_of_unimod La hU) (fun m hm => by
      obtain ⟨a, ha, h⟩ := GlobalTheory.BetaEx.exists_smul_std m
      exact ⟨a, ha, La.La.smul_mem a hm, h⟩)
  set idx : ℕ := (La.Ln.toAddSubgroup.addSubgroupOf La.La.toAddSubgroup).index with hidx
  have h2' : Ideal.absNorm 𝔞 = idx := h2
  have hidx0 : idx ≠ 0 := by
    rw [← h2']; exact fun h => h0 (Ideal.absNorm_eq_zero_iff.1 h)

  have e : ∀ τ, idealAt c La.Ln τ =
      Submodule.span (𝓞 c.F) ((embK c τ) '' (𝔞 : Set (𝓞 E))) * idealAt c La.La τ := by
    intro τ
    unfold idealAt
    rw [← GlobalTheory.BetaEx.span_image_span (embF c τ) (detSet La.Ln),
      ← GlobalTheory.BetaEx.span_image_span (embF c τ) (detSet La.La)]
    have := GlobalTheory.BetaEx.span_image_smul (embF c τ) 𝔞 (GlobalTheory.BetaEx.detSpan La.La)
    rw [← h1] at this
    exact this
  let φ : (E →+* ℂ) → (𝓞 E →+* 𝓞 c.F) := fun τ => RingOfIntegers.mapRingHom (embF c τ)
  let B : FractionalIdeal (𝓞 c.F)⁰ c.F :=
    ∏ τ : E →+* ℂ, ((𝔞.map (φ τ) : Ideal (𝓞 c.F)) : FractionalIdeal (𝓞 c.F)⁰ c.F) ^ Dw.mult τ

  have hS : ∀ τ, Submodule.span (𝓞 c.F) ((embK c τ) '' (𝔞 : Set (𝓞 E))) ≤
      (((𝔞.map (φ τ) : Ideal (𝓞 c.F)) : FractionalIdeal (𝓞 c.F)⁰ c.F) : Submodule (𝓞 c.F) c.F) := by
    intro τ
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    exact (FractionalIdeal.mem_coeIdeal _).2 ⟨φ τ a, Ideal.mem_map_of_mem _ ha, rfl⟩
  have hSB : ∏ τ : E →+* ℂ, Submodule.span (𝓞 c.F) ((embK c τ) '' (𝔞 : Set (𝓞 E))) ^ Dw.mult τ ≤
      (B : Submodule (𝓞 c.F) c.F) := by
    have : (B : Submodule (𝓞 c.F) c.F) = FractionalIdeal.coeSubmoduleHom (𝓞 c.F)⁰ c.F B := rfl
    rw [this, map_prod]
    refine Finset.prod_le_prod' fun τ _ => ?_
    rw [map_pow]
    exact pow_le_pow_left' (hS τ) _

  obtain ⟨k, hk⟩ : ∃ k, k = InfinitePlace.nrComplexPlaces c.F := ⟨_, rfl⟩
  have hnF : Module.finrank ℚ c.F = 2 * k := hk ▸ IsTotallyComplex.finrank c.F
  have hnE : Module.finrank ℚ E = 2 * InfinitePlace.nrComplexPlaces E := IsTotallyComplex.finrank E
  have hk0 : k ≠ 0 := by have := Module.finrank_pos (R := ℚ) (M := c.F); omega
  have hdvd : Module.finrank ℚ E ∣ Module.finrank ℚ c.F :=
    (GlobalTheory.absNorm_map_ringOfIntegers_hom E c.F (φ (Classical.arbitrary _)) 𝔞).1
  have hexp : Module.finrank ℚ c.F / Module.finrank ℚ E * ∑ τ : E →+* ℂ, Dw.mult τ = (Dw.p + Dw.q) * k := by
    rw [GlobalTheory.RefSum.sum_mult]
    obtain ⟨t, ht⟩ := hdvd
    have hE0 : 0 < Module.finrank ℚ E := Module.finrank_pos
    rw [ht, Nat.mul_div_cancel_left _ hE0, hnE, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [ht, hnE] at hnF
    have : InfinitePlace.nrComplexPlaces E * t = k := by linarith
    rw [← this]; ring
  have hNB : FractionalIdeal.absNorm B = ((idx : ℚ) ^ (Dw.p + Dw.q)) ^ k := by
    simp only [B, map_prod, map_pow, FractionalIdeal.coeIdeal_absNorm]
    simp only [fun τ => (GlobalTheory.absNorm_map_ringOfIntegers_hom E c.F (φ τ) 𝔞).2, h2']
    rw [← pow_mul, ← hexp, pow_mul, Finset.prod_pow_eq_pow_sum]
    push_cast
    ring
  have hX0 : (0 : ℝ) < (idx : ℝ) ^ (Dw.p + Dw.q) := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero hidx0) _
  have hB0 : B ≠ 0 := by
    intro hB
    have := hNB
    rw [hB, map_zero] at this
    have h' : ((idx : ℚ) ^ (Dw.p + Dw.q)) ^ k ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (by exact_mod_cast hidx0))
    exact h' this.symm

  set X : ℝ := (idx : ℝ) ^ (Dw.p + Dw.q) with hXdef
  set R : ℝ := Real.exp (fieldSz c.F) ^ 2 with hR
  have hR0 : 0 < R := by positivity
  have hg : 0 < R / X := div_pos hR0 hX0
  have hcard : Fintype.card (InfinitePlace c.F) = k := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero, zero_add, hk]
  have hd1 : (1 : ℝ) ≤ |(discr c.F : ℝ)| := by
    have := Int.one_le_abs (discr_ne_zero c.F)
    exact_mod_cast this
  have hdR : |(discr c.F : ℝ)| ≤ R ^ k := by
    rw [hR, ← pow_mul, ← Real.exp_nat_mul, ← Real.exp_log (lt_of_lt_of_le one_pos hd1)]
    apply Real.exp_le_exp.2
    have hn : (0 : ℝ) < Module.finrank ℚ c.F := by exact_mod_cast Module.finrank_pos
    have hfs := GlobalTheory.CovTop.log_rd_le_fieldSz c.F
    have hlog := Real.log_natCast_nonneg (Module.finrank ℚ c.F)
    have : Real.log |(discr c.F : ℝ)| ≤ (Module.finrank ℚ c.F : ℝ) * fieldSz c.F := by
      rw [div_le_iff₀ hn] at hfs; linarith
    rw [hnF] at this
    push_cast at this ⊢
    linarith
  have hsq : Real.sqrt |(discr c.F : ℝ)| ≤ |(discr c.F : ℝ)| :=
    Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hsq0 : 0 < Real.sqrt |(discr c.F : ℝ)| := Real.sqrt_pos.2 (by linarith)
  obtain ⟨b, hb, hb0, hbw⟩ := Formalism.ExtensionFiltration.mk_lt c.F (Units.mk0 B⁻¹ (inv_ne_zero hB0))
    (fun _ => Real.sqrt (R / X)) (fun _ => Real.sqrt_pos.2 hg) (by
      rw [Units.val_mk0, map_inv₀, hNB, Finset.prod_const, Finset.card_univ, hcard, Real.sq_sqrt hg.le, ← hk,
        div_pow]
      push_cast
      rw [← hXdef]
      have hXk : 0 < X ^ k := pow_pos hX0 k
      rw [inv_mul_eq_div, div_mul_eq_mul_div, div_lt_iff₀ hXk, mul_div_assoc', div_mul_cancel₀ _ hXk.ne']
      calc (2 : ℝ) ^ k * Real.sqrt |(discr c.F : ℝ)| < Real.pi ^ k * Real.sqrt |(discr c.F : ℝ)| :=
            mul_lt_mul_of_pos_right (pow_lt_pow_left₀ (by linarith [Real.pi_gt_three]) (by norm_num) hk0) hsq0
        _ ≤ Real.pi ^ k * R ^ k := by gcongr; exact hsq.trans hdR)
  refine ⟨b, hb0, ?_, fun σ => ?_⟩
  ·
    have hsb : Submodule.span (𝓞 c.F) {b} * (B : Submodule (𝓞 c.F) c.F) ≤ 1 := by
      have h1' : Submodule.span (𝓞 c.F) {b} ≤ ((B⁻¹ : FractionalIdeal (𝓞 c.F)⁰ c.F) : Submodule (𝓞 c.F) c.F) :=
        Submodule.span_le.2 (Set.singleton_subset_iff.2 hb)
      calc Submodule.span (𝓞 c.F) {b} * (B : Submodule (𝓞 c.F) c.F)
          ≤ ((B⁻¹ : FractionalIdeal (𝓞 c.F)⁰ c.F) : Submodule (𝓞 c.F) c.F) * (B : Submodule (𝓞 c.F) c.F) :=
            mul_le_mul' h1' le_rfl
        _ = 1 := by rw [← FractionalIdeal.coe_mul, inv_mul_cancel₀ hB0, FractionalIdeal.coe_one]
    simp only [e, mul_pow, Finset.prod_mul_distrib]
    rw [← mul_assoc]
    calc Submodule.span (𝓞 c.F) {b} * (∏ τ : E →+* ℂ,
            Submodule.span (𝓞 c.F) ((embK c τ) '' (𝔞 : Set (𝓞 E))) ^ Dw.mult τ) *
            ∏ τ : E →+* ℂ, idealAt c La.La τ ^ Dw.mult τ
        ≤ 1 * ∏ τ : E →+* ℂ, idealAt c La.La τ ^ Dw.mult τ :=
          mul_le_mul' ((mul_le_mul' le_rfl hSB).trans hsb) le_rfl
      _ = _ := one_mul _
  ·
    have h1 := hbw (InfinitePlace.mk σ)
    rw [InfinitePlace.apply] at h1
    have h3 : ‖σ b‖ ^ 2 < R / X := (Real.lt_sqrt (norm_nonneg _)).1 h1
    rw [lt_div_iff₀ hX0] at h3
    exact h3.le

end GlobalTheory.SmallScal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulOfTwistedPullbacksSameBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.TwistRatio

theorem exists_smul_of_isTwistPull : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (P : PolAV (Sp K)) (m : ℕ), 1 ≤ m →
    ∀ (th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) (baseOver (Sp K))))
      (α α' : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd (baseOver (Sp K)) P.A).left, (snd (baseOver (Sp K)) P.A ^ m).left]
        ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]))
      (s₁ s₁' : LB.Sec (LPow P.A P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)))), α.IsGen → α'.IsGen →
    IsTwistPull P.A P.L (mulT P.A (baseOver (Sp K)) m) (snd (baseOver (Sp K)) P.A ^ m) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α th s₁ →
    IsTwistPull P.A P.L (mulT P.A (baseOver (Sp K)) m) (snd (baseOver (Sp K)) P.A ^ m) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α' th s₁' →
    ∃ c : K, (SecMod.mk (fst (baseOver (Sp K)) P.A).left s₁' : EA P (𝟙 (Sp K)) (m ^ 2)) = c • SecMod.mk (fst (baseOver (Sp K)) P.A).left s₁ := by
  intro K _ _ _ P m hm th α α' s₁ s₁' hα hα' h h'
  have hG := GlobalTheory.allSixLaws.1.globalFns
  obtain ⟨a, ha⟩ := H1.exists_const P.L P.isLB (fst (baseOver (Sp K)) P.A).left
    (BoxTheta.surj_fst hG P.isAb _)
    (LB.mulGen P.L _ _ _ _ α' (LB.invGen P.L _ _ α))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hα' (DVR.invGen_isGen _ _ _ _ hα)) (fun U _ h => by
      simp [Fintype.prod_sum_type, Fin.prod_univ_two])
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2 a
  refine ⟨c, DVR.SecOps.sec_ext fun j => ?_⟩
  refine sec_ext_val P.isLB (fun y J hJ => ?_) j
  have e1 := VVRank.sv_of_isTwistPull P.A h' (𝟙 _) y hJ
  have e0 := VVRank.sv_of_isTwistPull P.A h (𝟙 _) y hJ
  have ev := ha _ (𝟙 _) y J hJ
  rw [val_mul hJ, val_inv] at ev
  have es := SecMod.value_smul hJ (𝟙 _) c (SecMod.mk (fst (baseOver (Sp K)) P.A).left s₁)
  refine e1.trans (Eq.trans ?_ es.symm)
  have eg : gs (𝟙 _) y ⊤ (scal (fst (baseOver (Sp K)) P.A).left c) =
      gs (𝟙 _ ≫ (fst (baseOver (Sp K)) P.A).left) y ⊤
        ((ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of K)).inv) c) :=
    gs_pull _ _ y ⊤ trivial _
  have eu : (val α' (𝟙 _) y J).val =
      (val α' (𝟙 _) y J * (val α (𝟙 _) y J)⁻¹).val * (val α (𝟙 _) y J).val := by
    rw [← Units.val_mul, inv_mul_cancel_right]
  change _ = _ * VVRank.sv P.A s₁ (𝟙 _) y J
  rw [e0, eg, ← ev, eu, _root_.mul_assoc]

end GlobalTheory.TwistRatio
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelAlgClosedCharZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MBLow

theorem exists_level_algClosed_charZero :
    ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (P : PolAV (Sp C)) (k : ℕ), 1 ≤ k → ∃ ζ : Cˣ, Nonempty (Out.Level P k (unitOn ζ)) := by
  intro C _ _ _ P k hk
  have hL : Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hk0 : (k : C) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have : NeZero (k : C) := ⟨hk0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C k
  let ze : Cˣ := (hζ.isUnit (by omega)).unit
  have hze : IsPrimitiveRoot ze k := IsPrimitiveRoot.coe_units_iff.1 (by simpa [ze] using hζ)
  obtain ⟨pt, hpt, hw⟩ := EllipticLevel.exists_symplectic_system hL P k hk0 ze hze
  have prim : ∀ {R : Type} [CommRing R] [Nontrivial R] (φ : C →+* R),
      IsPrimitiveRoot (Units.map φ.toMonoidHom ze) k := fun φ =>
    hze.map_of_injective (f := Units.map φ.toMonoidHom) (Units.map_injective φ.injective)
  have nt : ∀ (F : Type) [Field F], Nontrivial Γ(Spec (CommRingCat.of F), ⊤) := fun F _ =>
    (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  obtain ⟨lev, -⟩ := exists_level_of_pairing hL.globalFns hL.weil hL.mulN (Sp C) P k (unitOn ze)
    (by have := nt C; exact prim (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom)
    (fun F _ s => by
      have := nt F
      refine ⟨?_, prim (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom)⟩
      have : CharZero F := charZero_of_injective_ringHom (Spec.preimage s).hom.injective
      exact Nat.cast_ne_zero.2 (by omega))
    pt hpt hw
  exact ⟨ze, ⟨lev⟩⟩

end GlobalTheory.MBLow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedFibreOfFramedComplexPoint
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine

theorem exists_isVecs_of_eigBasis {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E}
    {S : Scheme.{0}} {t : SAB H S} {t' : SAB H (Sp ℂ)} {x : Sp ℂ ⟶ S} (m : SABMap t' t x) {g n : ℕ}
    (u : HolUnif t'.G t'.PP.L g) (hd : ∀ v, IsTangent v → ∃! z, u.IsDiff z v)
    (hd' : ∀ z, ∃! v, IsTangent v ∧ u.IsDiff z v) {χ : 𝓞 E →+* ℂ} {v : Fin n → (epsAt x ⟶ t.G)}
    (hv : IsEigBasisAt t.act x χ v) : ∃ V : Fin n → Fin g → ℂ, IsVecs u m.φ v V ∧ LinearIndependent ℂ V := by
  choose v' hv' using fun i => FlatRow.exists_lift m.cart (v i)
  have ix := FlatDegreeCompare.Indep.of_eigBasis (((FlatRow.fibre_iff m.cart hv').2 m.act χ).2 hv)
  choose V hV using fun i => (hd _ (ix.1 i)).exists
  exact ⟨V, fun i => ⟨v' i, hv' i, hV i⟩, FlatDegreeCompare.ArchExists.linearIndependent_of_indep u hd' ix hV⟩

theorem exists_unif_of_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (e : c.F →+* ℂ) (y : Sp ℂ ⟶ Xo.XF c) v w, FrU Xo c U τ e y v w → ∃ (o : Obj D l (baseKA l) (y ≫ toX Xo c ≫ Xo.s)) (m : ObjMap o Xo.univ (y ≫ toX Xo c)) (g : ℕ) (u : HolUnif o.t.G o.t.PP.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (κ : u.Λ → ℂ) (V : Fin D.p → Fin g → ℂ) (W : Fin D.q → Fin g → ℂ), u.IsAH Hm κ ∧ IsVecs u m.toSABMap.φ v V ∧ IsVecs u m.toSABMap.φ w W ∧ LinearIndependent ℂ V ∧ LinearIndependent ℂ W := by
  intro E _ _ _ H D l Xo c U τ e y v w h
  rw [← Category.assoc]
  obtain ⟨t', ⟨n⟩⟩ := exists_sab (y ≫ toX Xo c) Xo.univ.t
  obtain ⟨T, hT, -⟩ := CM.exists_pat_of_obj E H D l _ _ _ _ (ModelCompare.objOfSABMap Xo.univ n)
  obtain rfl : T.t = t' := hT
  obtain ⟨rig, hrig⟩ := T.pol.rigid
  obtain ⟨u, Hm, κ, -, hA, -, hd, hd', -⟩ := thetaUnifAV_all T.pol rig hrig
  obtain ⟨V, hV, iV⟩ := exists_isVecs_of_eigBasis n u hd hd' h.2.2.1
  obtain ⟨W, hW, iW⟩ := exists_isVecs_of_eigBasis n u hd hd' h.2.2.2
  exact ⟨ModelCompare.objOfSABMap Xo.univ n, ModelCompare.objMapOfSABMap Xo.univ n, _, u, Hm, κ, V, W, hA, hV, hW,
    iV, iW⟩

end GlobalTheory.DetLine
end
end

