module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1867
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0548

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSectionInverseImageBaseProductFunction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl

theorem lpow_le {S : Scheme.{0}} (P : PolAV S) (T : Over S) (k : ℤ) (j : Fin 1 → P.L.ι) :
    (LPow P.A P.L k T).U j ≤ (snd T P.A).left ⁻¹ᵁ P.L.U (j 0) :=
  LB.wchart_le P.L (fun _ : Fin 1 => (snd T P.A).left) j 0

theorem appLE_swap {X Y : Scheme.{0}} (φ : Y ⟶ X) {U U' : X.Opens} {V V' : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U) (h' : V' ≤ φ ⁻¹ᵁ U')
    (a : V' ≤ V) (b : U' ≤ U) (f : Γ(X, U)) :
    (Y.presheaf.map (homOfLE a).op).hom ((φ.appLE U V h).hom f) =
      (φ.appLE U' V' h').hom ((X.presheaf.map (homOfLE b).op).hom f) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem linComb_g_one {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (i j : Fin 1 → L.ι) :
    ((LB.LinComb L (fun _ : Fin 1 => φ) (fun _ => ((1 : ℕ) : ℤ))).g i j).val =
      (φ.appLE (L.U (i 0) ⊓ L.U (j 0)) (LB.wchart L (fun _ : Fin 1 => φ) i ⊓ LB.wchart L (fun _ : Fin 1 => φ) j)
        (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : Fin 1 => φ) i 0))
          (inf_le_right.trans (LB.wchart_le L (fun _ : Fin 1 => φ) j 0)))).hom (L.g (i 0) (j 0)).val := by
  unfold LB.LinComb
  dsimp only
  rw [Fin.prod_univ_one, Nat.cast_one, zpow_one]
  rfl

def pullSec1 {S : Scheme.{0}} (P : PolAV S) (T : Over S) (s : P.L.Sec) :
    LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T) where
  f j := ((snd T P.A).left.appLE _ _ (lpow_le P T _ j)).hom (s.f (j 0))
  compat i j := by
    have h := congrArg ((snd T P.A).left.appLE (P.L.U (i 0) ⊓ P.L.U (j 0))
      ((LPow P.A P.L ((1 : ℕ) : ℤ) T).U i ⊓ (LPow P.A P.L ((1 : ℕ) : ℤ) T).U j)
      (le_inf (inf_le_left.trans (lpow_le P T _ i)) (inf_le_right.trans (lpow_le P T _ j)))).hom (s.compat (i 0) (j 0))
    rw [map_mul] at h
    refine (appLE_swap _ _ _ _ _ _).trans (h.trans (congrArg₂ (· * ·) ?_ (appLE_swap _ _ _ _ _ _).symm))
    exact (linComb_g_one P.L (snd T P.A).left i j).symm

theorem pullbackSectionToBaseChangedAbelian_isInverseImage {S : Scheme.{0}} (P : PolAV S) (T : Over S) (s : P.L.Sec) : IsPolAVSectionInverseImage P T s (pullSec1 P T s) :=
  fun _ _ => rfl

theorem ptSecT_snd' {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S} (z : T ⟶ A) :
    (ptSecT A z).left ≫ (snd T A).left = z.left := by
  rw [← Over.comp_left, ptSecT, lift_snd]

theorem valR_appLE' {R : Type} [CommRing R] {X Y : Scheme.{0}} (x : Sp R ⟶ Y) (φ : Y ⟶ X) (U : X.Opens) (V : Y.Opens)
    (h : V ≤ φ ⁻¹ᵁ U) (hx : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) :
    valR x V ((φ.appLE U V h).hom f) = valR (x ≫ φ) U f := by
  have h' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U := fun p hp => h (hx hp)
  rw [valR, valR, dite_eq_left hx, dite_eq_left h', ← CommRingCat.comp_apply (φ.appLE U V h), Scheme.Hom.appLE_comp_appLE]

theorem valR_eq_valAt' {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) : valR x U f = valAt' x U f := by
  unfold valR valAt' valAt
  congr

theorem powerSectionFunctionInFrame_of_inverseImage {P : PolAV (Sp ℂ)} {g : ℕ} (u : HolUnif P.A P.L g) (s : P.L.Sec) (θ) (h : u.IsFn s θ)
    (th) (H : IsPolAVSectionInverseImage P (baseOver (Sp ℂ)) s th) : FnT u 1 th θ := by
  intro i z hz
  have e := ptSecT_snd' P.A (T := baseOver (Sp ℂ)) (u.ex z)
  have hx : ⊤ ≤ (ptSecT P.A (T := baseOver (Sp ℂ)) (u.ex z)).left ⁻¹ᵁ
      (LPow P.A P.L ((1 : ℕ) : ℤ) (baseOver (Sp ℂ))).U (fun _ => i) := fun p hp =>
    val_le P.A P.L (T := baseOver (Sp ℂ)) (u.ex z) (fun _ => i) (Set.mem_iInter.2 fun _ => hz hp)
  rw [H i (lpow_le P _ _ fun _ => i), pow_one, ← h i z hz, ← valR_eq_valAt']
  refine (valR_appLE' _ _ _ _ _ hx _).trans ?_
  exact congrArg (fun y => valR y (P.L.U i) (s.f i)) e

theorem eq_of_fnT {P : PolAV (Sp ℂ)} {g : ℕ} (u : HolUnif P.A P.L g) (k : ℕ)
    (t t' : LB.Sec (LPow P.A P.L (k : ℤ) (baseOver (Sp ℂ)))) (f) (h : FnT u k t f) (h' : FnT u k t' f) (j) :
    t.f j = t'.f j := by
  obtain ⟨i, rfl⟩ : ∃ i : P.L.ι, j = fun _ => i := ⟨j 0, funext fun a => congrArg j (Subsingleton.elim _ _)⟩
  have hp : (baseOver (Sp ℂ) ⊗ P.A).hom = pullback.fst (𝟙 (Sp ℂ)) P.A.hom := Category.comp_id _
  have := P.isAb.smooth
  have : Smooth (baseOver (Sp ℂ) ⊗ P.A).hom := by rw [hp]; infer_instance
  have := isReduced_of_smooth_complex _ (baseOver (Sp ℂ) ⊗ P.A).hom inferInstance
  refine ComplexPoints.eq_of_valAt'_eq (baseOver (Sp ℂ) ⊗ P.A).hom _ _ _ fun x hx hi => ?_
  let x' : baseOver (Sp ℂ) ⟶ baseOver (Sp ℂ) ⊗ P.A := Over.homMk x hx
  obtain ⟨z, hz⟩ := u.ex_onto (x' ≫ snd _ _)
  have e : ptSecT P.A (T := baseOver (Sp ℂ)) (u.ex z) = x' := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [ptSecT, lift_fst]
      refine Over.OverMorphism.ext ?_
      exact ((Category.comp_id _).symm.trans (Over.w (x' ≫ fst _ _))).symm
    · rw [ptSecT, lift_snd]; exact hz
  obtain rfl : (ptSecT P.A (T := baseOver (Sp ℂ)) (u.ex z)).left = x := congrArg (·.left) e
  have hz' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i := by
    intro p hp
    have := lpow_le P _ (k : ℤ) (fun _ => i) (hi hp)
    rw [← ptSecT_snd' P.A (T := baseOver (Sp ℂ)) (u.ex z)]
    exact this
  rw [← valR_eq_valAt', ← valR_eq_valAt']
  exact (h i z hz').trans (h' i z hz').symm

theorem thetaSection_fnT_thetaChar_and_unique : ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (W : Fin g → Fin g → ℂ), NF x hg u τ a b c W → (∃ th, IsPolAVSectionInverseImage x.P (baseOver (Sp ℂ)) x.th th) ∧ (∀ th, IsPolAVSectionInverseImage x.P (baseOver (Sp ℂ)) x.th th → FnT u 1 th fun z => c * thetaChar τ a b z) ∧ ∀ (k : ℕ) (t t' : LB.Sec (LPow x.P.A x.P.L (k : ℤ) (baseOver (Sp ℂ)))) f, FnT u k t f → FnT u k t' f → ∀ j, t.f j = t'.f j :=
  fun _ x _ u _ _ _ _ _ h => ⟨⟨_, pullbackSectionToBaseChangedAbelian_isInverseImage x.P _ x.th⟩, powerSectionFunctionInFrame_of_inverseImage u x.th _ h.2.2.2.2.2.2.2.1,
    fun k t t' f => eq_of_fnT u k t t' f⟩

end GlobalTheory.MBLow.Cl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionNefLeCuspFormGrowth
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct
open NumberField Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.HSApp
open GlobalTheory.AllWt (wtOf cuspOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open Filter
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefCuspGrowth

theorem ofReal_le_growth (D : ℕ) (h : ℕ → ℕ) (r : ℕ → ℕ∞) {c : ℝ} (hc : 0 ≤ c)
    (ht : Tendsto (fun m : ℕ => (h m : ℝ) / (m : ℝ) ^ D) atTop (nhds (c / D.factorial)))
    (hle : ∀ m, (h m : ℕ∞) ≤ r (m + 1)) : ENNReal.ofReal c ≤ CompHt.growth D r := by
  have hf : (0 : ℝ) < D.factorial := by positivity
  have h1 : Tendsto (fun m : ℕ => (m : ℝ) / ((m : ℝ) + 1)) atTop (nhds 1) := tendsto_natCast_div_add_atTop 1
  have h2 : Tendsto (fun m : ℕ => (D.factorial : ℝ) * ((h m : ℝ) / (m : ℝ) ^ D * ((m : ℝ) / ((m : ℝ) + 1)) ^ D))
      atTop (nhds c) := by
    have := (ht.mul (h1.pow D)).const_mul (D.factorial : ℝ)
    rwa [one_pow, mul_one, mul_div_cancel₀ _ hf.ne'] at this
  have h3 := (ENNReal.tendsto_ofReal h2).limsup_eq
  rw [CompHt.growth, ← Filter.limsup_nat_add _ 1, ← h3]
  refine limsup_le_limsup ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have e : (D.factorial : ℝ) * ((h m : ℝ) / (m : ℝ) ^ D * ((m : ℝ) / ((m : ℝ) + 1)) ^ D) =
      (D.factorial : ℝ) * (h m : ℝ) / ((m + 1 : ℕ) : ℝ) ^ D := by
    push_cast
    rw [div_pow]
    field_simp
  rw [e, ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
  exact ENNReal.div_le_div_right (mul_le_mul_right (by exact_mod_cast ENat.toENNReal_le.2 (hle m)) _) _

section Comp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c)

theorem cls_L₀_nsmul (u : AllWt.Weight Dw) (k : ℕ) :
    cls (L₀ X Z (k • u)) (isLB_L₀ X Z (k • u)) = k • cls (L₀ X Z u) (isLB_L₀ X Z u) := by
  induction k with
  | zero =>
    have e := cls_common_add (common₀ X Z) (0 : AllWt.Weight Dw) 0
    simp only [add_zero] at e
    rw [zero_smul]
    exact (left_eq_add.1 e).symm ▸ rfl
  | succ k ih =>
    have e := cls_common_add (common₀ X Z) (k • u) u
    rw [succ_nsmul, succ_nsmul, ← ih]
    exact e

end Comp

section Inj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c)
  {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

theorem mul_mem_vanBd (u : AllWt.Weight Dw) (k : ℕ) (h : u + k • u = (k + 1) • u)
    {θ : H0 (str₀ X Z) (L₀ X Z u) ⊤} (hθ : θ ∈ vanBd X Z u) (g : H0 (str₀ X Z) (L₀ X Z (k • u)) ⊤) :
    ((common₀ X Z).addChart h).mul θ g ∈ vanBd X Z ((k + 1) • u) := by
  intro y hy i hi
  obtain ⟨t, ha, hb, hc⟩ := ((common₀ X Z).addChart h).cover y
  rw [H0.germ_change i (((common₀ X Z).addChart h).c t) y (memTop y) hi hc,
    ((common₀ X Z).addChart h).germ_mul θ g t y (memTop y) ha hb hc]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (hθ y hy _ ha))

theorem finrank_le_rank [IsIntegral (Y₀ X Z)] (u : AllWt.Weight Dw) (k : ℕ) (hC : CuspIso X Z U ((k + 1) • u))
    {θ : H0 (str₀ X Z) (L₀ X Z u) ⊤} (hθ : θ ∈ vanBd X Z u) (hθ0 : θ ≠ 0) :
    (Module.finrank c.F (H0 (str₀ X Z) (L₀ X Z (k • u)) ⊤) : ℕ∞) ≤
      Cardinal.toENat (Module.rank c.F (cuspOn U Z ((k + 1) • wtOf Dw u 0))) := by
  have h : u + k • u = (k + 1) • u := by rw [succ_nsmul, add_comm]
  let C := (common₀ X Z).addChart h
  let φ : H0 (str₀ X Z) (L₀ X Z (k • u)) ⊤ →ₗ[c.F] Cusp Z U ((k + 1) • u) :=
    ofSpace X Z U ((k + 1) • u) ∘ₗ Submodule.inclusion hC.2 ∘ₗ
      LinearMap.codRestrict _ (C.mul θ) (mul_mem_vanBd X Z u k h hθ)
  have hφ : Function.Injective φ := by
    refine (ofSpace_injective X Z U _).comp ((Submodule.inclusion_injective hC.2).comp fun g g' e => ?_)
    have e' : C.mul θ g = C.mul θ g' := congrArg Subtype.val e
    by_contra hne
    refine GlobalTheory.Vanishing.ProdNe.mul_ne_zero C θ (g - g') hθ0 (sub_ne_zero.2 hne) ?_
    rw [map_sub, e', sub_self]
  have e : cuspOn U Z ((k + 1) • wtOf Dw u 0) = Cusp Z U ((k + 1) • u) := by
    rw [CompHt.nsmul_wtOf, smul_zero]
  rw [e]
  have hr := LinearMap.rank_le_of_injective φ hφ
  by_cases hfin : FiniteDimensional c.F (H0 (str₀ X Z) (L₀ X Z (k • u)) ⊤)
  · rw [← Module.finrank_eq_rank] at hr
    exact (Cardinal.toENat_nat _).symm.le.trans (OrderHomClass.mono Cardinal.toENat hr)
  · rw [Module.finrank_of_not_finite hfin]
    exact bot_le

end Inj

theorem topSelf_le_growthOn : GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (Y : Model Xo c (RingHom.id c.F)) (X : FlagCover Y) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
    (u : AllWt.Weight Dw), IsVariety₀ X Z → 1 ≤ dimFlag Dw → (∀ la, CuspIso X Z U la) → (∃ f : Cusp Z U u, f ≠ 0) →
    letI := algebraΓOfHom (str₀ X Z); IsNef c.F (L₀ X Z u) →
    ENNReal.ofReal (topSelfIntersection c.F (L₀ X Z u) (dimFlag Dw) : ℝ) ≤ GlobalTheory.CompHt.growthOn U Z (wtOf Dw u 0) := by
  intro hN E _ _ _ H Dw l Xo c Y X Z r U u hV hD hC hf
  obtain ⟨f, hf⟩ := hf
  letI := algebraΓOfHom (str₀ X Z)
  intro hnef
  let S : LinSys c.F := ⟨Y₀ X Z, str₀ X Z, dimFlag Dw, L₀ X Z u, isLB_L₀ X Z u, 0, Fin.elim0⟩
  have hS : S.IsVariety := ⟨hV.1, hV.2.1, hV.2.2, hD⟩
  haveI : IsIntegral (Y₀ X Z) := hS.isIntegral
  have hp : IsProjOver (strHom c.F (X := (Y₀ X Z))) := by
    rw [strHom_eq (f := str₀ X Z) fun _ => rfl]
    exact hV.2.1
  have hdim : topologicalKrullDim (Y₀ X Z) = dimFlag Dw := ImageDegree.topologicalKrullDim_eq S hS
  have ht := hN.2.2.tendsto hp hdim hnef
  have h0 := hN.2.2.topSelf_nonneg hp hdim hnef
  let θ := ((hC u).1.equiv f).1
  have hθ : θ ∈ vanBd X Z u := (hC u).1.space_le ((hC u).1.equiv f).2
  have hθ0 : θ ≠ 0 := fun e => hf ((hC u).1.equiv.map_eq_zero_iff.1 (Subtype.ext e))
  rw [CompHt.growthOn, dimFlag_eq]
  refine ofReal_le_growth (dimFlag Dw) (fun m => lbH0 c.F (lbPow (L₀ X Z u) m)) _ (Int.cast_nonneg h0) ht fun m => ?_
  rw [lineBundleGlobalSectionsDim_congr_picardClass (isLB_lbPow (isLB_L₀ X Z u) m) (isLB_L₀ X Z (m • u))
    (by rw [cls_lbPow (isLB_L₀ X Z u), cls_L₀_nsmul]), ← H0.finrank_top]
  exact finrank_le_rank X Z U u m (hC _) hθ hθ0

end GlobalTheory.NefCuspGrowth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimClosureEqOfIsAlgebraicResidue
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
open GlobalTheory.QCoh

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ClosureDim

theorem ringKrullDim_quotient_eq_of_trdeg_residueField_eq_zero (F : Type) [Field F]
    {A B : Type} [CommRing A] [CommRing B] [Algebra F A] [Algebra.FiniteType F A]
    (φ : A →+* B)
    (hB : @Algebra.FiniteType F B _ _ (φ.comp (algebraMap F A)).toAlgebra)
    (Q : Ideal B) [Q.IsPrime]
    (h : @Algebra.trdeg (Q.comap φ).ResidueField Q.ResidueField _ _
      (Ideal.ResidueField.map (Q.comap φ) Q φ rfl).toAlgebra = 0) :
    ringKrullDim (B ⧸ Q) = ringKrullDim (A ⧸ Q.comap φ) := by
  letI : Algebra F B := (φ.comp (algebraMap F A)).toAlgebra
  letI : Algebra A B := φ.toAlgebra
  haveI : IsScalarTower F A B := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  set P := Q.comap φ
  letI : Algebra P.ResidueField Q.ResidueField := (Ideal.ResidueField.map P Q φ rfl).toAlgebra
  haveI : IsScalarTower F P.ResidueField Q.ResidueField := IsScalarTower.of_algebraMap_eq fun f ↦ by
    change algebraMap F Q.ResidueField f = Ideal.ResidueField.map P Q φ rfl (algebraMap F P.ResidueField f)
    rw [IsScalarTower.algebraMap_apply F A P.ResidueField, Ideal.ResidueField.map_algebraMap,
      IsScalarTower.algebraMap_apply F B Q.ResidueField]
    rfl
  haveI : Algebra.FiniteType F (A ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F P) Ideal.Quotient.mk_surjective
  haveI : Algebra.FiniteType F (B ⧸ Q) :=
    haveI := hB; Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F Q) Ideal.Quotient.mk_surjective
  have hfaith (S : Type) [CommRing S] [Nontrivial S] [Algebra F S] : FaithfulSMul F S :=
    (faithfulSMul_iff_algebraMap_injective F S).mpr (algebraMap F S).injective
  haveI := hfaith (A ⧸ P); haveI := hfaith (B ⧸ Q); haveI := hfaith P.ResidueField
  haveI : FaithfulSMul (A ⧸ P) P.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr P.injective_algebraMap_quotient_residueField
  haveI : FaithfulSMul (B ⧸ Q) Q.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Q.injective_algebraMap_quotient_residueField
  haveI : FaithfulSMul P.ResidueField Q.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.injective _)
  haveI : Algebra.IsAlgebraic (A ⧸ P) P.ResidueField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (A ⧸ P))
  haveI : Algebra.IsAlgebraic (B ⧸ Q) Q.ResidueField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (B ⧸ Q))
  have h₁ := GlobalTheory.trdeg_eq_of_isAlgebraic_top F (A ⧸ P) P.ResidueField
  have h₂ := GlobalTheory.trdeg_eq_of_isAlgebraic_top F (B ⧸ Q) Q.ResidueField
  have h₃ := trdeg_add_eq F P.ResidueField (A := Q.ResidueField)
  rw [h, add_zero] at h₃
  obtain ⟨d, hd₁, hd₂⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq F (A ⧸ P)
  rw [hd₁]
  exact GlobalTheory.ringKrullDim_eq_of_trdeg_eq F (B ⧸ Q) (by rw [← h₂, ← h₃, h₁, hd₂])

end GlobalTheory.ClosureDim

namespace GlobalTheory.ClosureDim

theorem dim_closure_eq_of_isAlgebraic : ∀ (F : Type) [Field F] (Y X : Scheme.{0}) (π : Y ⟶ X)
    (sX : X ⟶ Sp F) [LocallyOfFiniteType sX] [LocallyOfFiniteType (π ≫ sX)] (y : Y),
    (letI := (π.residueFieldMap y).hom.toAlgebra;
      Algebra.IsAlgebraic (X.residueField (π y)) (Y.residueField y)) →
    topologicalKrullDim (closure {y} : Set Y) = topologicalKrullDim (closure {π y} : Set X) := by
  intro F _ Y X π sX _ _ y halg
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (π y)) isOpen_univ
  have hU : IsAffineOpen U := hU
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (show y ∈ (π ⁻¹ᵁ U : Set Y) from hxU)
      (π ⁻¹ᵁ U).isOpen
  have hV : IsAffineOpen V := hV
  have e : V ≤ π ⁻¹ᵁ U := hVU
  obtain ⟨p, rfl⟩ : y ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hyV
  let φ := π.appLE U V e
  have hsq : Spec.map φ ≫ hU.fromSpec = hV.fromSpec ≫ π := IsAffineOpen.SpecMap_appLE_fromSpec π hU hV e
  have hpt : π (hV.fromSpec p) = hU.fromSpec (Spec.map φ p) := by
    rw [← Scheme.Hom.comp_apply, ← hsq, Scheme.Hom.comp_apply]
  have h0 : @Algebra.trdeg (X.residueField (π (hV.fromSpec p))) (Y.residueField (hV.fromSpec p)) _ _
      (π.residueFieldMap (hV.fromSpec p)).hom.toAlgebra = 0 := by
    letI := (π.residueFieldMap (hV.fromSpec p)).hom.toAlgebra
    exact trdeg_eq_zero (R := X.residueField (π (hV.fromSpec p))) (A := Y.residueField (hV.fromSpec p))
  rw [GlobalTheory.RelDimFibCrit.trdeg_affine π U hU V hV e p] at h0
  let ψ := Spec.preimage (hU.fromSpec ≫ sX)
  have hψ : Spec.map ψ = hU.fromSpec ≫ sX := Spec.map_preimage _
  letI : Algebra F Γ(X, U) := ψ.hom.toAlgebra
  have hA : Algebra.FiniteType F Γ(X, U) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := ψ)).mp (hψ ▸ inferInstance)
  have hB : @Algebra.FiniteType F Γ(Y, V) _ _ (φ.hom.comp (algebraMap F Γ(X, U))).toAlgebra := by
    have h : Spec.map (ψ ≫ φ) = hV.fromSpec ≫ π ≫ sX := by
      rw [Spec.map_comp, hψ, ← Category.assoc, hsq, Category.assoc]
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := ψ ≫ φ)).mp (h ▸ inferInstance)
  rw [hpt, GlobalTheory.topologicalKrullDim_closure_eq_ringKrullDim_quotient (π ≫ sX) hV.fromSpec p,
    GlobalTheory.topologicalKrullDim_closure_eq_ringKrullDim_quotient sX hU.fromSpec (Spec.map φ p)]
  haveI := p.isPrime
  exact ringKrullDim_quotient_eq_of_trdeg_residueField_eq_zero F φ.hom hB p.asIdeal h0

end GlobalTheory.ClosureDim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionRationalOverFiniteExt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.CxPts GlobalTheory.Points
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.TorsRational

open Polynomial

theorem exists_ext_factor (K R : Type) [Field K] [CommRing R] [Algebra K R] [Module.Finite K R] :
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K'), Module.Finite K K' ∧
      ∀ (K'' Ω : Type) [Field K''] [Field Ω] [Algebra K' K''] [Algebra K K''] [IsScalarTower K K' K'']
        (σ : K'' →+* Ω) (φ : R →+* Ω), φ.comp (algebraMap K R) = σ.comp (algebraMap K K'') →
        ∃ φ'' : R →+* K'', σ.comp φ'' = φ := by
  classical
  let b := Module.finBasis K R
  let f : K[X] := ∏ i, minpoly K (b i)
  have hf0 : f ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ =>
    minpoly.ne_zero (Algebra.IsIntegral.isIntegral (b i))
  have hroot : ∀ r ∈ Set.range b, aeval r f = 0 := by
    rintro _ ⟨i, rfl⟩
    simp only [f, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (minpoly.aeval K _)
  refine ⟨f.SplittingField, inferInstance, inferInstance, inferInstance, ?_⟩
  intro K'' Ω _ _ _ _ _ σ φ hφ
  have hs : (f.map (algebraMap K K'')).Splits := by
    rw [IsScalarTower.algebraMap_eq K f.SplittingField K'', ← Polynomial.map_map]
    exact (SplittingField.splits f).map _
  have hmem : ∀ r, φ r ∈ σ.range := by
    intro r
    have hr : r ∈ Submodule.span K (Set.range b) := b.span_eq ▸ Submodule.mem_top
    induction hr using Submodule.span_induction with
    | mem x hx =>
      refine hs.mem_range_of_isRoot (Polynomial.map_ne_zero hf0) ?_
      rw [Polynomial.map_map, ← hφ, Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.hom_eval₂,
        ← Polynomial.aeval_def, hroot x hx, map_zero]
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx =>
      rw [Algebra.smul_def, map_mul]
      refine mul_mem ⟨algebraMap K K'' c, ?_⟩ hx
      rw [← RingHom.comp_apply, ← hφ, RingHom.comp_apply]
  let e := RingEquiv.ofBijective σ.rangeRestrict
    ⟨fun a b h => σ.injective (congrArg Subtype.val h), σ.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (φ.codRestrict σ.range hmem), ?_⟩
  ext r
  exact congrArg Subtype.val (e.apply_symm_apply (φ.codRestrict σ.range hmem r))

theorem exists_ext_points (K : Type) [Field K] (T : Over (Sp K)) (hT : IsFinite T.hom) :
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K'), Module.Finite K K' ∧
      ∀ (K'' Ω : Type) [Field K''] [Field Ω] [Algebra K' K''] [Algebra K K''] [IsScalarTower K K' K'']
        (σ : K'' →+* Ω) (t : Sp Ω ⟶ T.left), t ≫ T.hom = spMap (σ.comp (algebraMap K K'')) →
        ∃ w : Sp K'' ⟶ T.left, spMap σ ≫ w = t := by
  haveI : IsAffine T.left := isAffine_of_isAffineHom T.hom
  obtain ⟨ρ, hρ⟩ := Spec.map_surjective (T.left.isoSpec.inv ≫ T.hom)
  letI : Algebra K Γ(T.left, ⊤) := ρ.hom.toAlgebra
  haveI : Module.Finite K Γ(T.left, ⊤) := by
    have : IsFinite (Spec.map ρ) := by rw [hρ]; infer_instance
    exact (IsFinite.SpecMap_iff ρ).1 this
  obtain ⟨K', _, _, hfin, H⟩ := exists_ext_factor K Γ(T.left, ⊤)
  refine ⟨K', _, _, hfin, fun K'' Ω _ _ _ _ _ σ t ht => ?_⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (t ≫ T.left.isoSpec.hom)
  have h1 : φ.hom.comp (algebraMap K Γ(T.left, ⊤)) = σ.comp (algebraMap K K'') := by
    have : Spec.map (ρ ≫ φ) = Spec.map (CommRingCat.ofHom (σ.comp (algebraMap K K''))) := by
      rw [Spec.map_comp, hφ, hρ, Category.assoc, Iso.hom_inv_id_assoc, ht]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
  obtain ⟨φ'', hφ''⟩ := H K'' Ω σ φ.hom h1
  refine ⟨Spec.map (CommRingCat.ofHom φ'') ≫ T.left.isoSpec.inv, ?_⟩
  have e : CommRingCat.ofHom φ'' ≫ CommRingCat.ofHom σ = φ := by
    ext r
    exact congrArg (fun g => g r) hφ''
  rw [← Category.assoc, spMap, ← Spec.map_comp, e, hφ, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end GlobalTheory.TorsRational
end
end

