module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1878
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0451
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0540
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0539
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstantFunctionNormalCompactification
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.CptConst

theorem exists_eq_algX {F : Type} [Field F] {X Z : Scheme.{0}} (p : X ⟶ Sp F) [IsIntegral X] [UniversallyClosed p]
    (g : Z ⟶ X) [GeometricallyIntegral (g ≫ p)] (f : Γ(X, ⊤)) : ∃ a : F, f = algX p ⊤ a := by
  have : IsIntegral Z := GeometricallyIntegral.isIntegral_of_subsingleton (g ≫ p)
  have hal : ∀ {W : Scheme.{0}} (q : W ⟶ Sp F),
      algX q ⊤ = ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ q.appTop).hom := by
    intro W q
    have : q.appLE ⊤ ⊤ le_top = q.appTop := q.appLE_eq_app
    rw [← this]
    rfl
  have hint : (algX p ⊤).IsIntegral := by
    rw [hal]
    let G := (Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ p.appTop
    have : G.hom.IsIntegral := by
      apply RingHom.isIntegral_respectsIso.2 (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
      exact isIntegral_appTop_of_universallyClosed p
    exact this
  have hcomp : g.appTop.hom.comp (algX p ⊤) = algX (g ≫ p) ⊤ := by
    rw [hal, hal, Scheme.Hom.comp_appTop]
    rfl
  letI := (isField_of_universallyClosed F p).toField
  let φ : Γ(X, ⊤) →+* Z.functionField := (GlobalTheory.Cartier.fnOf ⊤ trivial).comp g.appTop.hom
  have hφ : φ.comp (algX p ⊤) = GlobalTheory.Cartier.constFn (g ≫ p) := by
    rw [RingHom.comp_assoc, hcomp]
    rfl
  obtain ⟨P, hP, hPf⟩ := hint f
  obtain ⟨a, ha⟩ := GlobalTheory.GeomIntConst.mem_range_constFn F Z (g ≫ p) (φ f) ⟨P, hP.ne_zero, by
    rw [← hφ, ← Polynomial.hom_eval₂, hPf, map_zero]⟩
  refine ⟨a, φ.injective ?_⟩
  rw [← ha, ← hφ]
  rfl

theorem exists_eq_constFn_compactOf :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : (Xo.XF c).Opens) (V : (gen Y).Opens), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (gen Y) → IsClosed (U : Set (Xo.XF c)) → GeometricallyConnected (U.ι ≫ toF Xo c) → (V : Set (gen Y)) = compactOf Y U → ∀ f : Γ(gen Y, V), ∃ a : c.F, f = ReciprocityTheory.ChartRestriction.G.Geo.Tor.constFn (genStr Y) V a := by
  intro E _ _ _ H D l Xo c O _ β Y U V hn _ hU hV f
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim _
  have : Smooth (toF Xo c) := inferInstanceAs (Smooth (pullback.snd _ _))
  have hgi : GeometricallyIntegral (U.ι ≫ toF Xo c) := GlobalTheory.geometricallyIntegral_of_smooth _
  have : IsIntegral U.toScheme := GeometricallyIntegral.isIntegral_of_subsingleton (U.ι ≫ toF Xo c)
  have := GlobalTheory.IsNormalScheme.of_pred hn
  have : IsReduced (gen Y) := GlobalTheory.IsNormalScheme.isReduced
  have := isProper_genStr Y
  have hUirr : IsIrreducible (U : Set (Xo.XF c)) :=
    isIrreducible_iff_irreducibleSpace.2 (inferInstanceAs (IrreducibleSpace U.toScheme))
  have hirr : IsIrreducible (V : Set (gen Y)) :=
    hV ▸ (hUirr.image _ Y.jQ.continuous.continuousOn).closure
  have : IrreducibleSpace V.toScheme := Subtype.irreducibleSpace hirr
  have : IsIntegral V.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have : IsClosedImmersion V.ι := IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι, hV]
    exact isClosed_closure)
  have hr : Set.range (U.ι ≫ Y.jQ) ⊆ Set.range V.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι, hV]
    exact subset_closure ⟨x.1, x.2, rfl⟩
  let g : U.toScheme ⟶ V.toScheme := IsOpenImmersion.lift V.ι (U.ι ≫ Y.jQ) hr
  have hg : g ≫ V.ι ≫ genStr Y = U.ι ≫ toF Xo c := by
    rw [IsOpenImmersion.lift_fac_assoc, Category.assoc]
    exact congrArg (U.ι ≫ ·) Y.jQ_over
  have : GeometricallyIntegral (g ≫ V.ι ≫ genStr Y) := hg ▸ hgi
  have hle : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := fun x _ => x.2
  obtain ⟨a, ha⟩ := exists_eq_algX (V.ι ≫ genStr Y) g ((V.ι.appLE V ⊤ hle).hom f)
  refine ⟨a, ?_⟩
  have hiso : IsIso (V.ι.appLE V ⊤ hle) := by
    rw [Scheme.Opens.ι_appLE]
    have : V.ι ''ᵁ ⊤ = V := V.ι_image_top
    have : IsIso (homOfLE (x := V.ι ''ᵁ ⊤) (y := V) this.le) := ⟨homOfLE this.ge, rfl, rfl⟩
    exact Functor.map_isIso _ (homOfLE (x := V.ι ''ᵁ ⊤) (y := V) V.ι_image_top.le).op
  refine (ConcreteCategory.bijective_of_isIso (V.ι.appLE V ⊤ hle)).1 (ha.trans ?_)
  have := Scheme.Hom.appLE_comp_appLE V.ι (genStr Y) ⊤ V ⊤ (fun _ _ => trivial) hle
  exact (congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv.hom a)) this).symm

end GlobalTheory.CptConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationThetaSectionNonvanishingFibres
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.DegTheta

theorem resG_resG {X : Scheme.{0}} {U V W : X.Opens} (h : W ≤ V) (h' : V ≤ U) (z : Γ(X, U)) :
    resG X h (resG X h' z) = resG X (h.trans h') z := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem resG_self {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U) (z : Γ(X, U)) : resG X h z = z := by
  change (X.presheaf.map (homOfLE h).op).hom z = z
  rw [show (homOfLE h).op = 𝟙 (Opposite.op U) from Subsingleton.elim _ _, X.presheaf.map_id]
  rfl

theorem basicOpen_resG {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (z : Γ(X, U)) :
    X.basicOpen (resG X h z) = V ⊓ X.basicOpen z :=
  Scheme.basicOpen_res X z (homOfLE h).op

def secOfSecOn {X : Scheme.{0}} {L : LB X} {V : X.Opens} (hV : ∀ x : X, x ∈ V) (θ : ∀ i, Γ(X, V ⊓ L.U i))
    (hθ : θ ∈ secOn L V) : L.Sec where
  f i := resG X (le_inf (fun x _ => hV x) le_rfl) (θ i)
  compat i j := by
    have e := congrArg (resG X (le_inf (le_inf (fun x _ => hV x) inf_le_left) inf_le_right : L.U i ⊓ L.U j ≤ V ⊓ L.U i ⊓ L.U j)) (hθ i j)
    simp only [map_mul, resG_resG] at e
    change resG X _ (resG X _ (θ i)) = _ * resG X _ (resG X _ (θ j))
    rw [resG_resG, resG_resG, e, resG_self]

end GlobalTheory.DegTheta

namespace GlobalTheory.DegTheta

theorem exists_sec_nonvanishing : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : NumD F) (ν : NumOf D F N), ∃ th : D.P.L.Sec, (∀ s : Sp R, ∃ x : D.P.A.left, D.P.A.hom x = s ∧ x ∈ Out.nonzeroLocus th) ∧ ∀ i : D.P.L.ι, ∀ h : LB.wchart D.P.L (fun _ : Fin 1 => 𝟙 D.P.A.left) (fun _ => i) ≤ D.P.L.U i, ν.th.f (fun _ => i) = resG _ h (th.f i) := by
  intro R _ _ _ _ D F _ _ N ν
  obtain ⟨V, θ, hxV, hθ, H⟩ := GlobalTheory.SecFamily.exists_secOn_nonvanishing GlobalTheory.abelianSchemeLaws_all.1 (Sp R) D.P
    (IsLocalRing.closedPoint R)
  have hVtop : V = ⊤ := (IsLocalRing.closedPoint_mem_iff V).1 hxV
  have hV : ∀ a : D.P.A.left, a ∈ D.P.A.hom ⁻¹ᵁ V := fun a => by rw [hVtop]; trivial
  let θ' : D.P.L.Sec := secOfSecOn hV θ hθ
  obtain ⟨r, hr⟩ := ν.th_gen (DVR.toH0 θ')
  refine ⟨DVR.secOfH0 ν.th, fun s => ?_, fun i h => ?_⟩
  · obtain ⟨a, i, has, ha⟩ := H s (by rw [hVtop]; trivial)
    refine ⟨a, has, ?_⟩
    have haU : a ∈ D.P.L.U i := (D.P.A.left.basicOpen_le (θ i) ha).2
    have e := hr (fun _ => i)
    have h1 : a ∈ D.P.A.left.basicOpen ((DVR.toH0 θ').f (fun _ => i)) := by
      have eq1 : (DVR.toH0 θ').f (fun _ => i) = resG _ ((DVR.h0_le (fun _ => i)).trans
          (le_inf (fun x _ => hV x) le_rfl)) (θ i) := resG_resG _ _ _
      rw [eq1]
      exact (basicOpen_resG _ (θ i)).ge ⟨DVR.chart_le_weighted_chart_single i haU, ha⟩
    rw [e, Scheme.basicOpen_mul] at h1
    have h2 : a ∈ D.P.A.left.basicOpen ((DVR.secOfH0 ν.th).f i) := by
      have eq2 : (DVR.secOfH0 ν.th).f i = resG _ (DVR.chart_le_weighted_chart_single i) (ν.th.f (fun _ => i)) := rfl
      rw [eq2]
      exact (basicOpen_resG (DVR.chart_le_weighted_chart_single i) _).ge ⟨haU, h1.2⟩
    exact (le_iSup (fun k => D.P.A.left.basicOpen ((DVR.secOfH0 ν.th).f k)) i) h2
  · exact ((resG_resG h (DVR.chart_le_weighted_chart_single i) _).trans (resG_self _ _)).symm

end GlobalTheory.DegTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorIdealSheafPrincipalisingFamily
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier

namespace GlobalTheory.DenomIdeal

variable {X : Scheme.{0}} [IsIntegral X] {ι : Type} (w : ι → X.functionField)

def IsDen (V : X.Opens) (a : Γ(X, V)) : Prop :=
  ∀ h : genericPoint X ∈ V, ∀ j, ∀ y ∈ V, RegAt y (fnOf V h a * w j)

def gens (V : X.Opens) : Set Γ(X, V) :=
  {b | ∃ a, IsDen w V a ∧ ∃ j, ∀ h : genericPoint X ∈ V, fnOf V h b = fnOf V h a * w j}

def idealOn (V : X.Opens) : Ideal Γ(X, V) := Ideal.span (gens w V)

variable {w}

theorem IsDen.res {U V : X.Opens} (e : V ≤ U) {a : Γ(X, U)} (ha : IsDen w U a) :
    IsDen w V (resG X e a) := by
  intro h j y hy
  rw [fnOf_resG]
  exact ha (e h) j y (e hy)

theorem res_mem_gens {U V : X.Opens} (e : V ≤ U) {b : Γ(X, U)} (hb : b ∈ gens w U) :
    resG X e b ∈ gens w V := by
  obtain ⟨a, ha, j, hj⟩ := hb
  exact ⟨resG X e a, ha.res e, j, fun h => by rw [fnOf_resG, fnOf_resG, hj]⟩

theorem mem_map_of_mem_gens_basicOpen [Fintype ι] {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U))
    {b : Γ(X, X.basicOpen f)} (hb : b ∈ gens w (X.basicOpen f)) :
    b ∈ (idealOn w U).map (resG X (X.basicOpen_le f)) := by
  by_cases hg : genericPoint X ∈ X.basicOpen f
  swap
  · have : b = 0 := Cartier.fn_ext fun h => (hg h).elim
    rw [this]; exact zero_mem _
  have hU' : genericPoint X ∈ U := X.basicOpen_le f hg
  have := hU.isLocalization_basicOpen f
  obtain ⟨a', ha', j, hj⟩ := hb
  obtain ⟨⟨a, _, n, rfl⟩, e⟩ := IsLocalization.surj (Submonoid.powers f) a'
  have e' : fnOf _ hg a' * fnOf U hU' f ^ n = fnOf U hU' a := by
    have := congrArg (fnOf _ hg) e
    simp only [map_mul, map_pow] at this
    change fnOf _ hg a' * fnOf _ hg (resG X (X.basicOpen_le f) f) ^ n =
      fnOf _ hg (resG X (X.basicOpen_le f) a) at this
    rwa [fnOf_resG, fnOf_resG] at this
  have hreg : ∀ i, ∀ x ∈ X.basicOpen f, RegAt x (fnOf U hU' a * w i) := fun i x hx => by
    rw [← e', mul_right_comm]
    exact (ha' hg i x hx).mul (GlobalTheory.TrueGeo.SmallSec.regAt_pow (regAt_fnOf (X.basicOpen_le f hx) hU' f) n)
  have := fun i => GlobalTheory.InvertIdeal.exists_mul_pow hU hU' f hg (hreg i)
  choose m γ hγ using this
  set M := ∑ i, m i
  have hm : ∀ i, m i ≤ M := fun i => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have key : ∀ i, fnOf U hU' (γ i * f ^ (M - m i)) = fnOf U hU' (a * f ^ M) * w i := fun i => by
    rw [map_mul, map_mul, hγ, map_pow, map_pow, ← Nat.add_sub_cancel' (hm i), pow_add]
    simp only [Nat.add_sub_cancel_left]
    ring
  have hden : IsDen w U (a * f ^ M) := fun h i y hy => by
    rw [← key i]; exact regAt_fnOf hy _ _
  have hgen : γ j * f ^ (M - m j) ∈ gens w U := ⟨_, hden, j, fun h => key j⟩
  have hu : IsUnit (resG X (X.basicOpen_le f) f) := IsLocalization.Away.algebraMap_isUnit f
  have hb0 : resG X (X.basicOpen_le f) (γ j * f ^ (M - m j)) = b * resG X (X.basicOpen_le f) f ^ (n + M) :=
    Cartier.fn_ext fun h => by
      rw [fnOf_resG, key, map_mul (fnOf _ h), map_pow, fnOf_resG, hj, map_mul, map_pow, ← e']
      ring
  have hb : b = resG X (X.basicOpen_le f) (γ j * f ^ (M - m j)) * ((hu.unit⁻¹ : _) : Γ(X, X.basicOpen f)) ^ (n + M) := by
    rw [hb0, mul_assoc, ← mul_pow, hu.mul_val_inv, one_pow, mul_one]
  rw [hb]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.subset_span hgen))


variable (w) in
def idealSheaf [Fintype ι] : X.IdealSheafData where
  ideal U := idealOn w U.1
  map_ideal_basicOpen U f := by
    show Ideal.map (resG X (X.basicOpen_le f)) (idealOn w U.1) = idealOn w (X.basicOpen f)
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      refine Ideal.span_le.2 fun b hb => ?_
      exact Ideal.subset_span (res_mem_gens (X.basicOpen_le f) hb)
    · exact Ideal.span_le.2 fun b hb => mem_map_of_mem_gens_basicOpen U.2 f hb

theorem idealSheaf_ne_bot [Fintype ι] (i₀ : ι) (h1 : w i₀ = 1) : idealSheaf w ≠ ⊥ := by
  classical
  obtain ⟨_, ⟨W, hW, rfl⟩, hηW, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
  have hW' : IsAffineOpen W := hW
  choose β γ hβ hγ using fun j => GlobalTheory.InvertIdeal.exists_denom hW' hηW hηW (regAt_genericPoint (w j))
  have hβ0 : ∀ j, fnOf W hηW (β j) ≠ 0 := fun j => ((unitAt_fnOf_iff hηW hηW (β j)).2 (hβ j)).ne_zero
  set d := ∏ j, β j
  have hd : ∀ j, fnOf W hηW d * w j = fnOf W hηW (γ j) * fnOf W hηW (∏ i ∈ Finset.univ.erase j, β i) := fun j => by
    rw [hγ, show d = β j * ∏ i ∈ Finset.univ.erase j, β i from (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm,
      map_mul]
    ring
  have hden : IsDen w W d := fun h j y hy => by
    rw [hd j]; exact (regAt_fnOf hy _ _).mul (regAt_fnOf hy _ _)
  have hgen : d ∈ gens w W := ⟨d, hden, i₀, fun h => by rw [h1, mul_one]⟩
  have hd0 : fnOf W hηW d ≠ 0 := by
    rw [map_prod]; exact Finset.prod_ne_zero_iff.2 fun j _ => hβ0 j
  intro hbot
  have hmem : d ∈ (idealSheaf w).ideal ⟨W, hW⟩ := Ideal.subset_span hgen
  rw [hbot] at hmem
  exact hd0 (by rw [(Ideal.mem_bot).1 hmem, map_zero])

theorem notMem_support [Finite ι] [Fintype ι] (i₀ : ι) (h1 : w i₀ = 1) {y : X} {k : ι} (hk : w k ≠ 0)
    (hy : ∀ j, RegAt y (w j / w k)) : y ∉ (idealSheaf w).support := by
  obtain ⟨V, hyV, ha⟩ := GlobalTheory.InvertIdeal.exists_common_open hy
  choose a ha using ha
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hyV V.isOpen
  have e : W ≤ V := hWV
  have hηW : genericPoint X ∈ W := gen_mem hyW
  have hfa : ∀ j, fnOf W hηW (resG X e (a j)) = w j / w k := fun j => by rw [fnOf_resG, ha]
  have hden : IsDen w W (resG X e (a i₀)) := fun h j x hx => by
    rw [hfa, h1, one_div, inv_mul_eq_div, ← hfa j]; exact regAt_fnOf hx _ _
  have hgen : (1 : Γ(X, W)) ∈ gens w W :=
    ⟨_, hden, k, fun h => by rw [map_one, hfa, h1, one_div, inv_mul_cancel₀ hk]⟩
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨W, hW⟩) hyW, Scheme.mem_zeroLocus_iff]
  intro H
  exact H 1 (Ideal.subset_span hgen) (by rw [Scheme.basicOpen_one]; exact hyW)

theorem fnOf_appLE {Y' : Scheme.{0}} [IsIntegral Y'] (s : Y' ⟶ X)
    (hη : s (genericPoint Y') ⤳ genericPoint X) {W : X.Opens} {A : Y'.Opens} (hA : A ≤ s ⁻¹ᵁ W)
    (hA' : genericPoint Y' ∈ A) (hW : genericPoint X ∈ W) (c : Γ(X, W)) :
    fnOf A hA' ((s.appLE W A hA).hom c) = GlobalTheory.TrueGeo.SmallSec.fnMap s hη (fnOf W hW c) := by
  rw [GlobalTheory.TrueGeo.SmallSec.fnMap_fnOf s hη hW (hA hA'), ← fnOf_resG hA hA']
  rfl

theorem exists_dvd_of_effCartier [Fintype ι] {Y' : Scheme.{0}} [IsIntegral Y'] (s : Y' ⟶ X)
    (hη : s (genericPoint Y') ⤳ genericPoint X)
    (hE : ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier ((idealSheaf w).comap s)) (y' : Y') :
    ∃ k, GlobalTheory.TrueGeo.SmallSec.fnMap s hη (w k) ≠ 0 ∧ ∀ j,
      RegAt y' (GlobalTheory.TrueGeo.SmallSec.fnMap s hη (w j) / GlobalTheory.TrueGeo.SmallSec.fnMap s hη (w k)) := by
  classical
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (s y')) isOpen_univ
  obtain ⟨U0, f0, sectionFrameQuotient, hf0, hI0⟩ := hE y'
  obtain ⟨t, htle, hyt⟩ := U0.2.exists_basicOpen_le (V := U0.1 ⊓ s ⁻¹ᵁ W) ⟨y', sectionFrameQuotient, hyW⟩ sectionFrameQuotient
  have hAW : Y'.basicOpen t ≤ s ⁻¹ᵁ W := fun x hx => (htle hx).2
  have hA' : genericPoint Y' ∈ Y'.basicOpen t := gen_mem hyt
  have hηW : genericPoint X ∈ W := gen_mem hyW
  set F := resG Y' (Y'.basicOpen_le t) f0 with hFdef
  have hIA : ((idealSheaf w).comap s).ideal (Y'.affineBasicOpen t) = Ideal.span {F} := by
    rw [← Scheme.IdealSheafData.map_ideal_basicOpen, hI0, Ideal.map_span, Set.image_singleton]
  have hmap : Ideal.map (s.appLE W (Y'.basicOpen t) hAW).hom (idealOn w W) = Ideal.span {F} := by
    rw [← hIA, GlobalTheory.Principalise.comapIdealAffine _ s ⟨W, hW⟩ (Y'.affineBasicOpen t) hAW]
    rfl
  set φ := fnOf (Y'.basicOpen t) hA'
  set w' := fun j => GlobalTheory.TrueGeo.SmallSec.fnMap s hη (w j) with hw'
  have hφ : ∀ c : Γ(X, W), φ ((s.appLE W (Y'.basicOpen t) hAW).hom c) =
      GlobalTheory.TrueGeo.SmallSec.fnMap s hη (fnOf W hηW c) := fun c => fnOf_appLE s hη hAW hA' hηW c
  have hF0 : φ F ≠ 0 := by
    have hU0 : genericPoint Y' ∈ U0.1 := Y'.basicOpen_le t hA'
    have : Nontrivial Γ(Y', U0.1) := (fnOf U0.1 hU0).domain_nontrivial
    rw [hFdef, fnOf_resG]
    intro h
    exact nonZeroDivisors.ne_zero hf0 (fnOf_injective _ hU0 (h.trans (map_zero _).symm))
  have key : ∀ x ∈ Ideal.map (s.appLE W (Y'.basicOpen t) hAW).hom (idealOn w W),
      ∃ C : ι → Y'.functionField, φ x = ∑ j, w' j * C j ∧ ∀ i j, ∃ r : Γ(Y', Y'.basicOpen t),
        w' i * C j = φ F * φ r := by
    intro x hx
    rw [idealOn, Ideal.map_span] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, ⟨a, ha, j₀, hb⟩, rfl⟩ := hx
      refine ⟨Pi.single j₀ (GlobalTheory.TrueGeo.SmallSec.fnMap s hη (fnOf W hηW a)), ?_, fun i j => ?_⟩
      · rw [hφ, hb hηW, map_mul, Finset.sum_eq_single j₀ (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mul_zero])
          (by simp), Pi.single_eq_same, mul_comm]
      · by_cases hj : j = j₀
        · subst hj
          rw [Pi.single_eq_same]
          obtain ⟨bi, hbi⟩ := exists_fnOf_eq hηW fun y hy => ha hηW i y hy
          have hmem : (s.appLE W (Y'.basicOpen t) hAW).hom bi ∈ Ideal.span {F} :=
            hmap ▸ Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨a, ha, i, fun _ => hbi⟩)
          obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hmem
          refine ⟨r, ?_⟩
          rw [hw', ← map_mul, mul_comm (w i), ← hbi, ← hφ, ← hr, map_mul, mul_comm]
        · rw [Pi.single_eq_of_ne hj, mul_zero]
          exact ⟨0, by rw [map_zero, mul_zero]⟩
    | zero => exact ⟨0, by simp, fun i j => ⟨0, by simp⟩⟩
    | add x y _ _ hx hy =>
      obtain ⟨C, hC, hC'⟩ := hx
      obtain ⟨D, hD, hD'⟩ := hy
      refine ⟨C + D, by rw [map_add (f := _), hC, hD, ← Finset.sum_add_distrib]; simp only [Pi.add_apply, mul_add],
        fun i j => ?_⟩
      obtain ⟨r, hr⟩ := hC' i j
      obtain ⟨r', hr'⟩ := hD' i j
      exact ⟨r + r', by simp only [Pi.add_apply, mul_add, hr, hr', map_add (f := _)]⟩
    | smul c x _ hx =>
      obtain ⟨C, hC, hC'⟩ := hx
      refine ⟨fun j => φ c * C j, ?_, fun i j => ?_⟩
      · rw [smul_eq_mul, map_mul, hC, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      · obtain ⟨r, hr⟩ := hC' i j
        refine ⟨c * r, ?_⟩
        rw [map_mul, mul_left_comm, hr]
        ring
  obtain ⟨C, hC, hC'⟩ := key F (hmap ▸ Ideal.mem_span_singleton_self F)
  choose r hr using hC'
  have hreg : ∀ i j, RegAt y' (w' i * (C j / φ F)) := fun i j => by
    rw [mul_div_assoc', hr, mul_div_cancel_left₀ _ hF0]
    exact regAt_fnOf hyt _ _
  have he1 : ∑ j, (fun _ => (1 : Y'.functionField)) j * (w' j * (C j / φ F)) = 1 := by
    simp only [one_mul, mul_div_assoc']
    rw [← Finset.sum_div, ← hC, div_self hF0]
  obtain ⟨k, hk⟩ := GlobalTheory.InvertIdeal.exists_unitAt (x := y') (c := fun _ => 1)
    (g := fun j => w' j * (C j / φ F)) (fun _ => ⟨1, map_one _⟩) (fun j => hreg j j) he1
  have hk0 : w' k * (C k / φ F) ≠ 0 := hk.ne_zero
  refine ⟨k, left_ne_zero_of_mul hk0, fun j => ?_⟩
  have e : w' j / w' k = (w' j * (C k / φ F)) * (w' k * (C k / φ F))⁻¹ := by
    have h2 : C k / φ F ≠ 0 := right_ne_zero_of_mul hk0
    rw [← div_eq_mul_inv, mul_div_mul_right _ _ h2]
  change RegAt y' (w' j / w' k)
  rw [e]
  exact (hreg j k).mul hk.inv.regAt

theorem exists_idealSheaf : ∀ (Y : Scheme.{0}) [IsIntegral Y] (N : ℕ) (w : Fin (N + 1) → Y.functionField) (i₀ : Fin (N + 1)) (U : Y.Opens),
    w i₀ = 1 → (∀ y ∈ U, ∃ k, w k ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y (w j / w k)) →
    ∃ I : Y.IdealSheafData, I ≠ ⊥ ∧ (∀ y ∈ U, y ∉ I.support) ∧
      ∀ (Y' : Scheme.{0}) [IsIntegral Y'] (s : Y' ⟶ Y) (hη : s (genericPoint Y') = genericPoint Y),
        ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (I.comap s) → ∀ y' : Y', ∃ k,
          GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w k) ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y'
            (GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w j) / GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w k)) := by
  intro Y _ N w i₀ U h1 hU
  refine ⟨idealSheaf w, idealSheaf_ne_bot i₀ h1, fun y hy => ?_, fun Y' _ s hη hE y' =>
    exists_dvd_of_effCartier s (specializes_of_eq hη) hE y'⟩
  obtain ⟨k, hk, hreg⟩ := hU y hy
  exact notMem_support i₀ h1 hk hreg

end GlobalTheory.DenomIdeal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveCartierDivisorPullbackOfDominant
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
open GlobalTheory.Discrepancy GlobalTheory.QCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cartier.PullDominant

variable {M W : Scheme.{0}} [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f]

theorem unitAt_map {x : M} {u : W.functionField} (h : UnitAt (f x) u) :
    UnitAt x (GlobalTheory.functionFieldMap f u) := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨f.stalkMap x a, ha.map _, (GlobalTheory.functionFieldMap_algebraMap f x a).symm⟩

theorem regAt_map {x : M} {u : W.functionField} (h : RegAt (f x) u) :
    RegAt x (GlobalTheory.functionFieldMap f u) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨f.stalkMap x a, (GlobalTheory.functionFieldMap_algebraMap f x a).symm⟩

abbrev unitsMap : W.functionFieldˣ →* M.functionFieldˣ := Units.map (GlobalTheory.functionFieldMap f).toMonoidHom

theorem germOf_map_eq {D₀ : CartierDiv W} {x : M} {g g' : W.functionFieldˣ}
    (h : D₀.IsEqn (f x) g) (h' : D₀.IsEqn (f x) g') :
    germOf x (unitsMap f g) = germOf x (unitsMap f g') := by
  rw [germOf_eq_iff]
  have := unitAt_map f (h.iff_unitAt.1 h')
  simpa [map_div₀] using this

def pullGerm (D₀ : CartierDiv W) (x : M) : Germ x :=
  germOf x (unitsMap f (D₀.exists_isEqn (f x)).choose)

theorem pullGerm_eq {D₀ : CartierDiv W} {x : M} {g : W.functionFieldˣ} (h : D₀.IsEqn (f x) g) :
    pullGerm f D₀ x = germOf x (unitsMap f g) :=
  germOf_map_eq f (D₀.exists_isEqn (f x)).choose_spec h

def pull (D₀ : CartierDiv W) : CartierDiv M :=
  show cartierGroup M from ⟨pullGerm f D₀, fun x => by
    obtain ⟨U, hU, g, hg⟩ := D₀.exists_isEqn_nhds (f x)
    exact ⟨f ⁻¹ᵁ U, hU, unitsMap f g, fun y hy => pullGerm_eq f (hg (f y) hy)⟩⟩

theorem isEqn_pull {D₀ : CartierDiv W} {x : M} {g : W.functionFieldˣ} (h : D₀.IsEqn (f x) g) :
    (pull f D₀).IsEqn x (unitsMap f g) :=
  pullGerm_eq f h

theorem eff_pull {D₀ : CartierDiv W} (hD : D₀.Eff) : (pull f D₀).Eff := by
  intro x
  obtain ⟨g, hg⟩ := D₀.exists_isEqn (f x)
  refine ⟨unitsMap f g, isEqn_pull f hg, ?_⟩
  rw [one_mul]
  exact regAt_map f (CartierDiv.eff_iff.1 hD _ _ hg)

end GlobalTheory.Cartier.PullDominant


open GlobalTheory.Cartier.PullDominant in
theorem GlobalTheory.Cartier.exists_pull_dominant :
    ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f] (D₀ : CartierDiv W), D₀.Eff → ∃ D₁ : CartierDiv M, D₁.Eff ∧ ∀ x g, D₀.IsEqn (f x) g → D₁.IsEqn x (Units.map (GlobalTheory.functionFieldMap f).toMonoidHom g) := by
  intro M W _ _ f _ D₀ hD
  exact ⟨pull f D₀, eff_pull f hD, fun x g h => isEqn_pull f h⟩
end
end

