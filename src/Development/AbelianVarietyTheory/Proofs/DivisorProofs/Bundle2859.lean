module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2752
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2758
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1535
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.UniqueFactorizationMonoidOfIsRegularRingOfIsLoca
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2063
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2641
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2840
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2773
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2146
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2837
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2110
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2276
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldGluedOpenCover
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LogKS.Glue

variable {Z : Scheme.{0}}

theorem resG_resG {U V W : Z.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (f : Γ(Z, U)) :
    resG Z h2 (resG Z h1 f) = resG Z (h2.trans h1) f := by
  change (Z.presheaf.map (homOfLE h1).op ≫ Z.presheaf.map (homOfLE h2).op).hom f = _
  rw [← Functor.map_comp]
  rfl

variable {J : Type} (V : J → Z.Opens) (e : J → ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O))

def loc (O : Z.Opens) (f : Γ(Z, O)) (i : J) : Γ(Z, O ⊓ V i) :=
  e i (O ⊓ V i) (resG Z inf_le_left f)


open Classical in
def glue (O : Z.Opens) (f : Γ(Z, O)) : Γ(Z, O) :=
  if h : ∃ s : Γ(Z, O), ∀ i, resG Z (inf_le_left : O ⊓ V i ≤ O) s = loc V e O f i then h.choose else 0

variable {V e}

theorem compat (he : ∀ i, IsField (V i) (e i))
    (hc : ∀ i j (O : Z.Opens), O ≤ V i → O ≤ V j → ∀ f, e i O f = e j O f) (O : Z.Opens) (f : Γ(Z, O)) :
    TopCat.Presheaf.IsCompatible Z.sheaf.1 (fun i => O ⊓ V i) (loc V e O f) := by
  intro i j
  change resG Z (inf_le_left : (O ⊓ V i) ⊓ (O ⊓ V j) ≤ O ⊓ V i) (loc V e O f i) =
    resG Z (inf_le_right : (O ⊓ V i) ⊓ (O ⊓ V j) ≤ O ⊓ V j) (loc V e O f j)
  simp only [loc]
  rw [← (he i).2.2 (O ⊓ V i) _ inf_le_left inf_le_right, ← (he j).2.2 (O ⊓ V j) _ inf_le_right inf_le_right,
    resG_resG, resG_resG]
  exact hc i j _ (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) _

theorem glue_ex (he : ∀ i, IsField (V i) (e i))
    (hc : ∀ i j (O : Z.Opens), O ≤ V i → O ≤ V j → ∀ f, e i O f = e j O f) {O : Z.Opens}
    (hO : O ≤ ⨆ i, V i) (f : Γ(Z, O)) :
    ∃! s : Γ(Z, O), ∀ i, resG Z (inf_le_left : O ⊓ V i ≤ O) s = loc V e O f i :=
  Z.sheaf.existsUnique_gluing' (fun i => O ⊓ V i) O (fun i => homOfLE inf_le_left)
    ((le_inf le_rfl hO).trans (inf_iSup_eq _ _).le) (loc V e O f) (compat he hc O f)

theorem glue_eq (he : ∀ i, IsField (V i) (e i))
    (hc : ∀ i j (O : Z.Opens), O ≤ V i → O ≤ V j → ∀ f, e i O f = e j O f) {O : Z.Opens}
    (hO : O ≤ ⨆ i, V i) (f : Γ(Z, O)) (s : Γ(Z, O))
    (hs : ∀ i, resG Z (inf_le_left : O ⊓ V i ≤ O) s = loc V e O f i) : glue V e O f = s := by
  obtain ⟨t, -, hu⟩ := glue_ex he hc hO f
  have h : ∃ s : Γ(Z, O), ∀ i, resG Z (inf_le_left : O ⊓ V i ≤ O) s = loc V e O f i := ⟨s, hs⟩
  rw [glue, dite_eq_left h]
  exact (hu _ h.choose_spec).trans (hu _ hs).symm

theorem res_glue (he : ∀ i, IsField (V i) (e i))
    (hc : ∀ i j (O : Z.Opens), O ≤ V i → O ≤ V j → ∀ f, e i O f = e j O f) {O : Z.Opens}
    (hO : O ≤ ⨆ i, V i) (f : Γ(Z, O)) (i : J) :
    resG Z (inf_le_left : O ⊓ V i ≤ O) (glue V e O f) = loc V e O f i := by
  obtain ⟨t, ht, -⟩ := glue_ex he hc hO f
  rw [glue_eq he hc hO f t ht]
  exact ht i

end GlobalTheory.LogKS.Glue

theorem GlobalTheory.LogKS.isField_glue : ∀ (Z : Scheme.{0}) (J : Type) (V : J → Z.Opens) (e : J → ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)), (∀ i, IsField (V i) (e i)) → (∀ i j (O : Z.Opens), O ≤ V i → O ≤ V j → ∀ f, e i O f = e j O f) → ∃ d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O), IsField (⨆ i, V i) d ∧ ∀ i (O : Z.Opens), O ≤ V i → ∀ f, d O f = e i O f := by
  intro Z J V e he hc
  open GlobalTheory.LogKS.Glue in
  refine ⟨glue V e, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro W hW f f'
    refine glue_eq he hc hW _ _ fun i => ?_
    rw [map_add (f := _), res_glue he hc hW f, res_glue he hc hW f']
    simp only [loc, map_add (f := _)]
    exact ((he i).1 _ inf_le_right _ _).symm
  · intro W hW f f'
    refine glue_eq he hc hW _ _ fun i => ?_
    rw [map_add (f := _), map_mul, map_mul, res_glue he hc hW f, res_glue he hc hW f']
    simp only [loc, map_mul]
    exact ((he i).2.1 _ inf_le_right _ _).symm
  · intro W W' h hW f
    refine glue_eq he hc (h.trans hW) _ _ fun i => ?_
    rw [resG_resG, ← resG_resG (inf_le_left : W ⊓ V i ≤ W) (inf_le_inf_right (V i) h), res_glue he hc hW f]
    simp only [loc]
    rw [← (he i).2.2 _ _ (inf_le_inf_right (V i) h) inf_le_right, resG_resG, resG_resG]
  · intro i O hO f
    refine glue_eq he hc (hO.trans (le_iSup V i)) _ _ fun j => ?_
    simp only [loc]
    rw [← (he i).2.2 O (O ⊓ V j) inf_le_left hO f]
    exact hc i j _ (inf_le_left.trans hO) inf_le_right _
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepDualPairCharactersBetaQuotient
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.WeilTripleW

theorem isHecke_div {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {χ χ' : (AF F ⊗[F] E)ˣ →* Circle} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') := by
  refine ⟨h.1.div' h'.1, fun x => ?_⟩
  simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]

theorem resEtaPow_div {R E : Type} [CommRing R] [CommRing E] [Algebra R E] {K : Subgroup Rˣ}
    {χ χ' : Eˣ →* Circle} {n m : ℕ} (h : GlobalTheory.WeilM.ResEtaPow K χ n) (h' : GlobalTheory.WeilM.ResEtaPow K χ' m) :
    GlobalTheory.WeilM.ResEtaPow K (χ / χ') (n + m) := by
  intro a
  have e1 := h a
  have e2 := h' a
  simp only [MonoidHom.div_apply, Circle.coe_div] at *
  rw [e1, e2]
  split_ifs
  · simp
  · have hm : ((-1 : ℂ) ^ m) * ((-1 : ℂ) ^ m) = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
    rw [div_eq_iff (by simp), pow_add, mul_assoc, hm, mul_one]

end GlobalTheory.WeilTripleW

theorem GlobalTheory.WeilTripleW.exists_isWeil : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m), SquareStanding G t → ∀ (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (X : Spc D.host.F D.host.E (spW G i j).rank) (Y : Spc D.host.F D.host.E ((spW G i j).rank + (spW₁ G i j).rank))
      (r s r' s' : ℕ), X.IsHerm D.sp.cm.sig B r s → Y.IsSkew D.sp.cm.sig B r' s' →
      ∀ Mo : Model D.sp.cm.sig X Y, Mo.IsGood B.ψ →
      ∃ om, Mo.IsWeil B.ψ (beta G i j) (beta G i j / alpha G t i j) om := by
  intro D T L sc G μ₀ hL t i j hS B hB X Y r s r' s' hX hY Mo hMo
  obtain ⟨hb, ha, rb, ra⟩ := GlobalTheory.SquareChars.square_chars hL t i j hS
  exact _root_.GlobalTheory.WeilSchrodinger.exists_isWeil D B hB _ _ X Y r s r' s' hX hY Mo hMo
    (beta G i j) (beta G i j / alpha G t i j) hb (GlobalTheory.WeilTripleW.isHecke_div hb ha) rb
    (GlobalTheory.WeilTripleW.resEtaPow_div rb ra)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepSquarePairCharactersAlphaQuotient
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FunObj

theorem resEtaPow_div {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : (AF F ⊗[F] E)ˣ →* Circle} {n m : ℕ}
    (h : GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ n)
    (h' : GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ' m) :
    GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range (χ / χ') (m + n) := by
  intro a
  have e := h a
  have e' := h' a
  rw [MonoidHom.div_apply, Circle.coe_div, e, e']
  split_ifs
  · simp
  · rw [pow_add]
    rcases neg_one_pow_eq_or ℂ m with hm | hm <;> rw [hm] <;> ring

theorem isHecke_div {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : (AF F ⊗[F] E)ˣ →* Circle} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_self']⟩

theorem squareWeil₁ : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m), SquareStanding G t → ∀ (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (X : Spc D.host.F D.host.E (spW₁ G i j).rank) (Y : Spc D.host.F D.host.E ((spW G i j).rank + (spW₁ G i j).rank))
      (r s r' s' : ℕ), X.IsHerm D.sp.cm.sig B r s → Y.IsSkew D.sp.cm.sig B r' s' →
      ∀ Mo : Model D.sp.cm.sig X Y, Mo.IsGood B.ψ →
      ∃ om, Mo.IsWeil B.ψ (alpha G t i j) (alpha G t i j / beta G i j) om := by
  intro D T L sc G μ₀ hL t i j _hst B hB X Y r s r' s' hX hY Mo hMo
  have hα : GlobalTheory.LFun.IsHecke D.host.F D.host.E (alpha G t i j) := by
    have hm := (hL.mu0 j).1
    have hx := (hL.xi t).1
    have he := hL.eta.1
    refine ⟨(hm.1.mul hx.1).mul (he.1.pow _), fun x => ?_⟩
    have e1 := hm.2 x
    have e2 := hx.2 x
    have e3 := he.2 x
    show L.mu0 ((j : ℕ) + 1) _ * L.xi t _ * (L.eta ^ _) _ = 1
    rw [MonoidHom.pow_apply]
    rw [e1, e2, e3]
    simp
  have hβ : GlobalTheory.LFun.IsHecke D.host.F D.host.E (beta G i j) := by
    have hc := (G.ch.chi_eq (D.R.m - (i : ℕ)) (by omega) (by omega)).1
    have he := hL.eta.1
    refine ⟨hc.1.mul (he.1.pow _), fun x => ?_⟩
    have e1 := hc.2 x
    have e3 := he.2 x
    show G.ch.chi (D.R.m - (i : ℕ)) _ * (L.eta ^ _) _ = 1
    rw [MonoidHom.pow_apply, e1, e3]
    simp
  have h2 : Module.finrank D.host.F D.host.E = 2 := D.sp.cm.deg2
  obtain ⟨rα, rβ⟩ := _root_.GlobalTheory.SquareResChars.resEta_alpha_beta hL t i j
  have pα := GlobalTheory.LFun.resEtaPow_of_resEta _ _ h2 _ _ rα
  have pβ := GlobalTheory.LFun.resEtaPow_of_resEta _ _ h2 _ _ rβ
  exact _root_.GlobalTheory.WeilSchrodinger.exists_isWeil D B hB _ _ X Y r s r' s' hX hY Mo hMo _ _ hα (isHecke_div hα hβ) pα (resEtaPow_div pα pβ)

end GlobalTheory.FunObj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendsToSemiAbelianAwayOfCharts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem ufm_stalk_of_smooth_regularLocal {E : Type} [CommRing E] [IsRegularLocalRing E] {Y : Scheme.{0}} [IsIntegral Y]
    (p : Y ⟶ Sp E) [Smooth p] (y : Y) : UniqueFactorizationMonoid (Y.presheaf.stalk y) := by
  have : IsRegularRing E := GlobalTheory.isRegularRing_of_isRegularLocalRing E
  have := ExtendRig.isRegularRing_stalk isRegularRing_of_smooth E p y
  exact uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing exists_hasProjectiveDimensionLE_of_isRegularLocalRing
    isPrincipal_map_away_of_hasProjectiveDimensionLE _

theorem hasExt_awayMap_of_charts : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (f : R), f ≠ 0 → ∀ (A : Over (Sp (Localization.Away f))) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → RelAmple A L → (∀ x : Sp R, Nonempty (Chart (awayMap f) A x)) → HasExt (awayMap f) A := by
  intro R _ _ _ _ f hf A _ hA L hL hamp hC
  have : IsDomain (Localization.Away f) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  have : IsIntegral A.left := isIntegral_left_of_isAbelianScheme A
  obtain ⟨D, hD, hsym⟩ := GlobalTheory.SymDiv.exists_ampleDiv_symm _ A hA L hL hamp
  let C : ∀ x : Sp R, Chart (awayMap f) A x := fun x => (hC x).some
  have intC : ∀ x, IsIntegral (C x).G.left := fun x =>
    have := (C x).semi
    isIntegral_left_of_isSemiAbelian (C x).G
  choose ρ V φ θ hρ hflat hV hcart hcompat hθ using fun x => chart_part R f hf A hA x (C x)
  have hdiv : ∀ x, ∃ D₁ : CartierDiv (C x).G.left, PPull (V x).ι (φ x) (θ x) D D₁ ∧
      ∀ z, Vert (C x).G.hom (ρ x f) z → D₁.IsEqn z 1 := fun x => by
    have := (C x).semi.smooth
    have : IsLocallyNoetherian (C x).G.left := LocallyOfFiniteType.isLocallyNoetherian (C x).G.hom
    have hρf : Flat (spMap (ρ x)) := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact hflat x
    have hφ : Flat (φ x) := MorphismProperty.of_isPullback (hcart x).flip hρf
    obtain ⟨D₁, h₁, h₂⟩ := exists_cartierDiv_closure (C x).G.left (V x).toScheme A.left
      (ufm_stalk_of_smooth_regularLocal (C x).G.hom) (V x).ι (φ x) (θ x) hφ (hθ x) D
    refine ⟨D₁, h₁, fun z hz => h₂ z ?_ hz.1⟩
    rw [Scheme.Opens.range_ι]
    exact fun hzV => (hV x z).1 hzV hz.2
  choose D₁ hpull hvert using hdiv
  have hamp₁ : ∀ x, AmpleDiv (D₁ x) := fun x => by
    have := (C x).charZero
    have hne : ρ x f ≠ 0 := fun h0 => by
      obtain ⟨l, -⟩ := hθ x
      let v : (V x).toScheme := l (closedPoint _)
      refine (hV x v.1).1 v.2 ?_
      rw [h0]
      exact zero_mem _
    exact ampleDiv_closure_on_chart R f A hA D hD hsym (C x).R (C x).complete (ρ x) (hflat x) hne (C x).G (C x).semi (V x) (φ x) (θ x)
      (D₁ x) (hV x) (hcart x) (C x).y (C x).α (C x).gen (hcompat x) (hθ x) (hpull x)
  exact hasExt_of_setup
    { R := R, f := f, hf := hf, A := A, ab := hA, D := D, amp := hD, C := C, ρ := ρ, hρ := hρ, flat := hflat, V := V,
      hV := hV, φ := φ, cart := hcart, compat := hcompat, θ := θ, hθ := hθ, D₁ := D₁, pull := hpull, noVert := hvert,
      amp₁ := hamp₁ }

end GlobalTheory.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorPairingDiagRelAmple
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.FactorAmple

open GlobalTheory.CechPic

theorem lam_rosati {K : Type} [Field K] {B : Over (Sp K)} [GrpObj B] [IsCommMonObj B] {M : LB B.left} (hM : M.IsLB)
    {u v : B ⟶ B} (h : RosatiAdj B M u v) {T : Over (Sp K)} (x y : T ⟶ B) :
    lam (cls M hM) (x ≫ u) y = lam (cls M hM) x (y ≫ v) := by
  have e := GlobalTheory.AdjPolLocal.lbIso_of_rosatiAdj_local K B M u v hM h
  have h1 : (cubeLB B ![fst B B ≫ u, snd B B] M).IsLB := LB.isLB_linComb hM _ _
  have h2 : (cubeLB B ![fst B B, snd B B ≫ v] M).IsLB := LB.isLB_linComb hM _ _
  have e' := (cls_eq_iff h1 h2).2 e
  rw [cls_cube_two hM, cls_cube_two hM] at e'
  have e'' := congrArg (pull (lift x y : T ⟶ G2 B).left) e'
  rw [pull_lam, pull_lam] at e''
  simpa using e''

theorem act_nsmul {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {O : Type} [Ring O] (ρ : RingAct A O)
    (u : O) (n : ℕ) : ρ.act (n • u) = ρ.act u ^ n := by
  have h0 : ρ.act 0 = 1 := by
    have e := ρ.map_add 0 0
    rw [add_zero] at e
    have e' : ρ.act 0 * 1 = ρ.act 0 * ρ.act 0 := by rw [_root_.mul_one]; exact e.trans (Hom.mul_def _ _).symm
    exact (mul_left_cancel e').symm
  induction n with
  | zero => rw [zero_smul, pow_zero, h0]
  | succ n ih => rw [succ_nsmul, ρ.map_add, ih, pow_succ]; exact (Hom.mul_def _ _).symm

theorem lam_push {S S' : Scheme.{0}} {G : Over S} {H : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj H]
    [IsCommMonObj H] {f : S' ⟶ S} {φ : H.left ⟶ G.left} (hp : IsGrpPullback H G f φ) (c : Pic G.left)
    {T : Over S'} (z w : T ⟶ H) :
    lam c (pushHom hp T z) (pushHom hp T w) = lam (pull φ c) z w := by
  simp only [lam, ← map_mul, ← map_one (pushHom hp T)]
  simp only [← pull_comp]
  rfl

end GlobalTheory.Mum.FactorAmple

namespace GlobalTheory.Mum

open GlobalTheory.CechPic GlobalTheory.Mum.FactorAmple

theorem factorPairing_diag_relAmple : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → Out.RelAmple ((Over.pullback (jK R)).obj G) ((((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull κ₀).pull (lift (𝟙 ((Over.pullback (jK R)).obj G)) (𝟙 ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⟶ G2 ((Over.pullback (jK R)).obj G)).left) := by
  intro R _ _ _ hR D D' F hF A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr hinc hpr hip hpi κ₀ hκ
  have := A'.isAb.comm
  have hp := isGrpPullback_pullback G (jK R)
  have hp' := isGrpPullback_pullback G' (jK R)
  let X := (Over.pullback (jK R)).obj G
  let ιK : X ⟶ (Over.pullback (jK R)).obj G' := (Over.pullback (jK R)).map inc
  let a : X ⟶ A'.A := ιK ≫ U'.gen.hom
  have hM := A'.isLB
  have hL' : U'.LG.L.IsLB := U'.LG.isLB
  have hΛ : (abelian₂ G' U'.LG.L).IsLB := LB.isLB_linComb hL' _ _
  have h1 := pull_isLB hΛ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left
  have h2 := pull_isLB h1 κ₀
  have h3 := pull_isLB h2 (lift (𝟙 X) (𝟙 X) : X ⟶ G2 X).left
  have e1 : pushHom hp X (𝟙 X) ≫ inc = pushHom hp' X ιK := by
    ext1
    show (𝟙 _ ≫ pullback.fst G.hom (jK R)) ≫ inc.left = ιK.left ≫ pullback.fst G'.hom (jK R)
    rw [Category.id_comp]
    exact (pullback.lift_fst _ _ _).symm
  have e2 : pushHom hp X (𝟙 X) ≫ inc ≫ oG.act F.f =
      pushHom hp' X (ιK ≫ (Over.pullback (jK R)).map (oG.act F.f)) := by
    rw [← Category.assoc, e1]
    ext1
    show (ιK.left ≫ pullback.fst G'.hom (jK R)) ≫ (oG.act F.f).left =
      (ιK ≫ (Over.pullback (jK R)).map (oG.act F.f)).left ≫ pullback.fst G'.hom (jK R)
    rw [Over.comp_left, Category.assoc, Category.assoc]
    exact congrArg (ιK.left ≫ ·) (pullback.lift_fst _ _ _).symm
  have eN : cls _ h3 = lam (cls _ hL') (pushHom hp X (𝟙 X) ≫ inc) (pushHom hp X (𝟙 X) ≫ inc ≫ oG.act F.f) := by
    rw [cls_pull h2, cls_pull h1, cls_pull hΛ, ← pull_comp, ← pull_comp]
    rw [← Category.assoc, FactorAdd.lift_square hp hκ, ← Over.comp_left]
    have e : cls (abelian₂ G' U'.LG.L) hΛ = lam (cls _ hL') (fst G' G') (snd G' G') := cls_cube_two hL' _ _ hΛ
    rw [e, pull_lam]
    simp
  have hgen := U'.gen_hom
  have eT : pull (pullback.fst G'.hom (jK R)) (cls _ hL') = pull U'.gen.hom.left (cls _ hM) := by
    obtain ⟨w, hw⟩ := U'.ext
    rw [← cls_pull hL' _ (pull_isLB hL' _), ← cls_pull hM _ (pull_isLB hM _)]
    exact ((cls_eq_iff (pull_isLB hM _) (pull_isLB hL' _)).2 ⟨w, hw⟩).symm
  have eN' : cls _ h3 = lam (cls _ hM) a (a ≫ oA.act F.f) := by
    rw [eN, e2, e1, lam_push hp', eT, lam_pull]
    congr 1
    rw [Category.assoc, Category.assoc, hlin.ext F.f]
  have hie : inc ≫ oG.act F.e = inc := by rw [← hpi, ← Category.assoc, hip, Category.id_comp]
  have ha : a ≫ oA.act F.e = a := by
    show (ιK ≫ U'.gen.hom) ≫ oA.act F.e = ιK ≫ U'.gen.hom
    rw [Category.assoc, ← hlin.ext F.e, ← Category.assoc, ← Functor.map_comp, hie]
  have hΘ : ∃ t : LB.Gen (Theta A'.A A'.L), t.IsGen := GlobalTheory.GenericAmpleDvr.triv_theta A'.isAb hM
  obtain ⟨⟨b, hb, hbe⟩, -, -⟩ := hF
  have rosE : ∀ x y : X ⟶ A'.A, lam (cls _ hM) (x ≫ oA.act F.e) y = lam (cls _ hM) x (y ≫ oA.act (star F.e)) :=
    fun x y => lam_rosati hM (oA.rosati F.e) x y
  have hpow : ∀ (u : F.O) (n : ℕ), (a ≫ oA.act u) ^ n = a ≫ oA.act (n • u) := by
    intro u n
    rw [act_nsmul oA.toRingAct]
    exact (map_pow (preHom (G := A'.A) a) (oA.act u) n).symm
  have eb : b • cls _ h3 = lam (cls _ hM) a a := by
    rw [eN']
    calc b • lam (cls _ hM) a (a ≫ oA.act F.f)
        = b • lam (cls _ hM) (a ≫ oA.act F.e) ((a ≫ oA.act F.e) ≫ oA.act F.f) := by rw [ha]
      _ = b • lam (cls _ hM) a (a ≫ oA.act (star F.e * F.f * F.e)) := by
          rw [rosE, oA.map_mul, oA.map_mul]; simp only [Category.assoc]
      _ = lam (cls _ hM) a ((a ≫ oA.act (star F.e * F.f * F.e)) ^ b) := (lam_pow_right hM hΘ _ _ b).symm
      _ = lam (cls _ hM) a (a ≫ oA.act (star F.e * F.e)) := by rw [hpow, hbe]
      _ = lam (cls _ hM) (a ≫ oA.act F.e) (a ≫ oA.act F.e) := by
          rw [oA.map_mul, ← Category.assoc, ← rosE]
      _ = lam (cls _ hM) a a := by rw [ha]
  have hΛA : (abelian₂ A'.A A'.L).IsLB := LB.isLB_linComb hM _ _
  have hDg := pull_isLB hΛA (lift (𝟙 A'.A) (𝟙 A'.A) : A'.A ⟶ G2 A'.A).left
  have eD : lam (cls _ hM) a a = cls _ (pull_isLB hDg a.left) := by
    have e : cls (abelian₂ A'.A A'.L) hΛA = lam (cls _ hM) (fst A'.A A'.A) (snd A'.A A'.A) := cls_cube_two hM _ _ hΛA
    rw [cls_pull hDg, cls_pull hΛA, e, pull_lam, pull_lam]
    simp
  have hNb := isLB_lbPow h3 b
  have iso := (cls_eq_iff hNb (pull_isLB hDg a.left)).1 (by rw [cls_lbPow h3, eb, eD])
  have := hG'.separated
  have : IsSeparated ((Over.pullback (jK R)).obj G').hom := by dsimp; infer_instance
  let prK : (Over.pullback (jK R)).obj G' ⟶ X := (Over.pullback (jK R)).map pr
  have hs : ιK ≫ prK = 𝟙 X := by rw [← Functor.map_comp, hip]; exact (Over.pullback (jK R)).map_id G
  have : IsSeparated prK.left := by
    have e : prK.left ≫ X.hom = ((Over.pullback (jK R)).obj G').hom := Over.w prK
    have : IsSeparated (prK.left ≫ X.hom) := by rw [e]; infer_instance
    exact IsSeparated.of_comp prK.left X.hom
  have : IsClosedImmersion ιK.left := by
    have : IsClosedImmersion (ιK.left ≫ prK.left) := by
      rw [← Over.comp_left, hs]; exact inferInstanceAs (IsClosedImmersion (𝟙 _))
    exact IsClosedImmersion.of_comp ιK.left prK.left
  have : IsIso U'.gen.hom.left := ((Over.forget _).mapIso U'.gen).isIso_hom
  have : IsFinite a.left := by
    show IsFinite (ιK ≫ U'.gen.hom).left
    rw [Over.comp_left]; infer_instance
  have := A'.isAb.proper
  have : IsProper X.hom := by
    have e : a.left ≫ A'.A.hom = X.hom := Over.w a
    rw [← e]; infer_instance
  have hDgA := GlobalTheory.isAmpleLB_of_relAmple_of_isAffine A'.A hDg
    (GlobalTheory.EighthPowerFactor.relAmple_diag_lam A'.isAb hM hΘ A'.ample)
  have hNa := (hDgA.pull_of_isFinite a.left).of_lbIso hNb iso
  exact (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine X h3).2 ((GlobalTheory.isAmpleLB_pow_iff h3 hb).1 hNa)

end GlobalTheory.Mum
end
end

