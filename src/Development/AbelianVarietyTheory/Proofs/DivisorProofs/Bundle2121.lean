module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1003
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0865
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilyTermTranslateBoundFunctionalEquation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2040
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1704
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1884
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1588
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1966
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensHomTmul
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

namespace GlobalTheory.Obs.BC

variable {R₀ R₁ : Type} [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁]

theorem isAffine_aff {X : Scheme.{0}} (U : X.affineOpens) : IsAffineOpen U.1 := U.2

def preAff {X₀ X₁ : Scheme.{0}} (pr : X₁ ⟶ X₀) [IsAffineHom pr] : AffOp X₀ ⥤ AffOp X₁ where
  obj U := op ⟨pr ⁻¹ᵁ U.unop.1, (isAffine_aff U.unop).preimage pr⟩
  map a := (homOfLE (pr.preimage_mono (leOfHom a.unop))).op

def natCoef {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F F' : C ⥤ CommAlgCat.{0} R}
    (α : ∀ T, F.obj T →+* F'.obj T) (nat : ∀ {T T' : C} (a : T ⟶ T') (b : F.obj T), α T' (mp F a b) = mp F' a (α T b))
    (smul : ∀ T (r : R) (b : F.obj T), α T (r • b) = r • α T b) : CoefMap (RingHom.id R) F F' where
  G := 𝟭 C
  α := α
  naturality := nat
  smul := smul

variable {X₀ X₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}

def prSec (w : pr ≫ s₀ = s₁ ≫ spMap (algebraMap R₀ R₁)) (U : X₀.affineOpens) (hU : IsAffineOpen (pr ⁻¹ᵁ U.1)) :
    Sec s₀ U.1 →+* Sec s₁ (pr ⁻¹ᵁ U.1) :=
  GlobalTheory.CechDR.secPull (φ := pr) s₀ s₁ ⟨(⟨pr ⁻¹ᵁ U.1, hU⟩, U), le_rfl⟩

def tensHom (w : pr ≫ s₀ = s₁ ≫ spMap (algebraMap R₀ R₁)) (U : X₀.affineOpens) (hU : IsAffineOpen (pr ⁻¹ᵁ U.1)) :
    R₁ ⊗[R₀] Sec s₀ U.1 →ₐ[R₁] Sec s₁ (pr ⁻¹ᵁ U.1) :=
  letI : Algebra R₀ (Sec s₁ (pr ⁻¹ᵁ U.1)) := ((algebraMap R₁ _).comp (algebraMap R₀ R₁)).toAlgebra
  haveI : IsScalarTower R₀ R₁ (Sec s₁ (pr ⁻¹ᵁ U.1)) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  Algebra.TensorProduct.lift (Algebra.ofId R₁ _)
    { prSec w U hU with commutes' := fun r ↦ (semiHom_secPull w (⟨(⟨pr ⁻¹ᵁ U.1, hU⟩, U), le_rfl⟩ : Pair pr)).map_algebraMap r }
    (fun _ _ ↦ Commute.all _ _)

theorem tensHom_tmul (w : pr ≫ s₀ = s₁ ≫ spMap (algebraMap R₀ R₁)) (U : X₀.affineOpens)
    (hU : IsAffineOpen (pr ⁻¹ᵁ U.1)) (r : R₁) (b : Sec s₀ U.1) :
    tensHom w U hU (r ⊗ₜ b) = algebraMap R₁ _ r * prSec w U hU b := by
  simp [tensHom, Algebra.ofId_apply]; rfl

variable [IsAffineHom pr]

theorem prSec_res (w : pr ≫ s₀ = s₁ ≫ spMap (algebraMap R₀ R₁)) {U V : AffOp X₀} (a : U ⟶ V) (b : Sec s₀ U.unop.1) :
    prSec w V.unop ((isAffine_aff V.unop).preimage pr) (mp (OAff s₀) a b) =
      Sec.res s₁ (pr.preimage_mono (leOfHom a.unop)) (prSec w U.unop ((isAffine_aff U.unop).preimage pr) b) :=
  (pairPull w).naturality (T := op ⟨(⟨pr ⁻¹ᵁ U.unop.1, (isAffine_aff U.unop).preimage pr⟩, U.unop), le_rfl⟩)
    (T' := op ⟨(⟨pr ⁻¹ᵁ V.unop.1, (isAffine_aff V.unop).preimage pr⟩, V.unop), le_rfl⟩)
    (homOfLE (show (⟨(⟨pr ⁻¹ᵁ V.unop.1, (isAffine_aff V.unop).preimage pr⟩, V.unop), le_rfl⟩ : Pair pr) ≤
      ⟨(⟨pr ⁻¹ᵁ U.unop.1, (isAffine_aff U.unop).preimage pr⟩, U.unop), le_rfl⟩ from
        ⟨pr.preimage_mono (leOfHom a.unop), leOfHom a.unop⟩)).op b

def tensCoef (w : pr ≫ s₀ = s₁ ≫ spMap (algebraMap R₀ R₁)) :
    CoefMap (RingHom.id R₁) (ext R₁ (OAff s₀)) (preAff pr ⋙ OAff s₁) :=
  natCoef (fun U ↦ (tensHom w U.unop ((isAffine_aff U.unop).preimage pr) : R₁ ⊗[R₀] Sec s₀ U.unop.1 →+* Sec s₁ (pr ⁻¹ᵁ U.unop.1)))
    (fun {U V} a b ↦ by
      change tensHom w V.unop _ (extHom R₁ (mp (OAff s₀) a) b) =
        Sec.res s₁ (pr.preimage_mono (leOfHom a.unop)) (tensHom w U.unop _ b)
      induction b using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul r x =>
        rw [Algebra.TensorProduct.map_tmul, tensHom_tmul, tensHom_tmul, map_mul, AlgHom.id_apply, prSec_res]
        congr 1
        exact ((Sec.res s₁ (pr.preimage_mono (leOfHom a.unop))).commutes r).symm
      | add x y hx hy => simp only [map_add (f := _), hx, hy])
    (fun U r b ↦ map_smul (tensHom w U.unop ((isAffine_aff U.unop).preimage pr)) r b)

variable {Y₀ Y₁ : Scheme.{0}} {pr' : Y₁ ⟶ Y₀} [IsAffineHom pr']

def pairBCObj (pr : X₁ ⟶ X₀) (pr' : Y₁ ⟶ Y₀) [IsAffineHom pr] [IsAffineHom pr'] {f₀ : Y₀ ⟶ X₀} {f₁ : Y₁ ⟶ X₁}
    (e : f₁ ≫ pr = pr' ≫ f₀) (p : Pair f₀) : Pair f₁ :=
  ⟨(⟨pr' ⁻¹ᵁ p.1.1.1, (isAffine_aff p.1.1).preimage pr'⟩,
    ⟨pr ⁻¹ᵁ p.1.2.1, (isAffine_aff p.1.2).preimage pr⟩), by
    change pr' ⁻¹ᵁ p.1.1.1 ≤ f₁ ⁻¹ᵁ pr ⁻¹ᵁ p.1.2.1
    rw [← Scheme.Hom.comp_preimage, e, Scheme.Hom.comp_preimage]
    exact pr'.preimage_mono p.2⟩

def pairBC (pr : X₁ ⟶ X₀) (pr' : Y₁ ⟶ Y₀) [IsAffineHom pr] [IsAffineHom pr'] {f₀ : Y₀ ⟶ X₀} {f₁ : Y₁ ⟶ X₁}
    (e : f₁ ≫ pr = pr' ≫ f₀) : (Pair f₀)ᵒᵖ ⥤ (Pair f₁)ᵒᵖ where
  obj p := op (pairBCObj pr pr' e p.unop)
  map {p q} a := (homOfLE (show pairBCObj pr pr' e q.unop ≤ pairBCObj pr pr' e p.unop from
    Subtype.coe_le_coe.1 (Prod.mk_le_mk.2 ⟨pr'.preimage_mono (Pair.le_fst (leOfHom a.unop)),
      pr.preimage_mono (Pair.le_snd (leOfHom a.unop))⟩))).op

variable {t₀ : Y₀ ⟶ Sp R₀} {t₁ : Y₁ ⟶ Sp R₁}

def tensPair (w' : pr' ≫ t₀ = t₁ ≫ spMap (algebraMap R₀ R₁)) {f₀ : Y₀ ⟶ X₀} {f₁ : Y₁ ⟶ X₁}
    (e : f₁ ≫ pr = pr' ≫ f₀) : CoefMap (RingHom.id R₁) (ext R₁ (OPair f₀ t₀)) (pairBC pr pr' e ⋙ OPair f₁ t₁) :=
  natCoef (fun p ↦ (tensCoef w').α ((pairFst f₀).obj p)) (fun a b ↦ (tensCoef w').naturality ((pairFst f₀).map a) b)
    (fun p r b ↦ (tensCoef w').smul ((pairFst f₀).obj p) r b)

end GlobalTheory.Obs.BC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralArchimedeanInvariant
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThetaRightTranslate

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_eq_sigR (σ : E →ₐ[F] E) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) : cA σ z = sigR (AF F) σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [cA, sigR]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem ug_eq_uj (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    UG (cA σ) (incM F J) = Formalism.UG.UJ (sigR (AF F) σ) (JR (AF F) Jᵀ) := by
  ext g
  show (g : Matrix _ _ _)ᵀ * incM F J * (g : Matrix _ _ _).map (cA σ) = incM F J ↔
    Formalism.UG.cT (sigR (AF F) σ) (g : Matrix _ _ _) * JR (AF F) Jᵀ * (g : Matrix _ _ _) = JR (AF F) Jᵀ
  have hc : (g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).map (cA σ) = (g : Matrix _ _ _).map (sigR (AF F) σ) := by
    ext i j; exact cA_eq_sigR σ _
  have hJ : JR (AF F) Jᵀ = (incM F J)ᵀ := rfl
  rw [hc, hJ, Formalism.UG.cT]
  constructor
  · intro h
    have := congrArg Matrix.transpose h
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  · intro h
    have := congrArg Matrix.transpose h
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this

def toHA (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : UA σ J ≃ₜ* HA (AF F) σ Jᵀ where
  toMulEquiv := MulEquiv.subgroupCongr (ug_eq_uj σ J)
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

theorem isMulRightInvariant_of_equiv {G H : Type} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]
    [MeasurableSpace G] [MeasurableSpace H] [BorelSpace G] [BorelSpace H]
    (e : G ≃ₜ* H) (μ : Measure G) (h : (μ.map e).IsMulRightInvariant) :
    μ.IsMulRightInvariant := by
  have he : Measurable e := e.continuous.measurable
  have hs : Measurable e.symm := e.symm.continuous.measurable
  have hμ : μ = (μ.map e).map e.symm := by
    rw [Measure.map_map hs he]
    have : (e.symm : H → G) ∘ e = id := by ext x; simp
    rw [this, Measure.map_id]
  refine ⟨fun g => ?_⟩
  have h1 := h.map_mul_right_eq_self (e g)
  have hc : (fun x : G => x * g) ∘ (e.symm : H → G) = (e.symm : H → G) ∘ (fun y : H => y * e g) := by
    ext y; simp
  conv_lhs => rw [hμ]
  rw [Measure.map_map (measurable_mul_const g) hs, hc,
    ← Measure.map_map hs (measurable_mul_const _), h1, ← hμ]

theorem isMulRightInvariant (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (hd : IsUnit J.det) (μ : Measure (UA σ J)) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant := by
  haveI : IsTopologicalRing (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  haveI : IsTopologicalGroup (HA (AF F) σ Jᵀ) := inferInstanceAs (IsTopologicalGroup (HR (AF F) σ Jᵀ))
  haveI : BorelSpace (HA (AF F) σ Jᵀ) := ⟨rfl⟩
  refine isMulRightInvariant_of_equiv (toHA σ J) μ ?_
  haveI : (μ.map (toHA σ J)).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ (toHA σ J)
  obtain ⟨d, hd'⟩ := GlobalTheory.HermLineZeros.exists_conj_ne hcm
  have hss := GlobalTheory.HermLineZeros.conj_invol hcm
  have hJ' : IsHermND σ Jᵀ := ⟨fun i j => hJ j i, by rw [Matrix.det_transpose]; exact hd.ne_zero⟩
  exact @GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_adelic F E _ _ _ _ _ σ hss (σ d - d) (sub_ne_zero.2 hd')
    (by rw [map_sub, hss]; abel) n Jᵀ hJ' (μ.map (toHA σ J)) this

theorem countable_subgroupOf_range {G H : Type} [Group G] [Group H] [Countable G] (f : G →* H)
    (K : Subgroup H) : Countable ((f.range).subgroupOf K) := by
  have hc : (Set.range f).Countable := Set.countable_range f
  haveI := hc.to_subtype
  refine Function.Injective.countable (f := fun γ : (f.range).subgroupOf K =>
    (⟨γ.1.1, MonoidHom.mem_range.1 (Subgroup.mem_subgroupOf.1 γ.2)⟩ : Set.range f)) ?_
  intro a b hab
  exact Subtype.ext (Subtype.ext (Subtype.mk.inj hab))

theorem countable_ratU (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Countable (ratU σ J) := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  haveI : Countable (GL (Fin n) E) := Function.Injective.countable (f := (Units.val : GL (Fin n) E → Matrix (Fin n) (Fin n) E)) (fun a b h => Units.ext h)
  unfold ratU
  exact countable_subgroupOf_range _ _

end GlobalTheory.ThetaRightTranslate
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupStalkNoetherianNormalFractionRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem stalk_isNoetherian_normal_fractionRing : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ)
    (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z),
    letI : Algebra (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ := (X₁.M.stalkHom z₁).toAlgebra;
    IsDomain (X₁.M.Z.presheaf.stalk z₁) ∧ IsFractionRing (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ ∧
      IsIntegrallyClosed (X₁.M.Z.presheaf.stalk z₁) ∧ IsNoetherianRing (X₁.M.Z.presheaf.stalk z₁) := by
  intro g n F W Z i X₁ z₁
  letI : Algebra (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ := (X₁.M.stalkHom z₁).toAlgebra
  have hN := X₁.normal
  refine ⟨GlobalTheory.IsNormalScheme.isDomain_stalk z₁, ?_, GlobalTheory.IsNormalScheme.isIntegrallyClosed_stalk z₁, ?_⟩
  · have : FaithfulSMul (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 (X₁.M.stalkHom_injective z₁)
    refine IsFractionRing.of_field _ _ fun x => ?_
    obtain ⟨a, b, -, hx⟩ := IsFractionRing.div_surjective (A := X₁.M.O z₁) x
    refine ⟨(X₁.M.stalkEquiv z₁).symm a, (X₁.M.stalkEquiv z₁).symm b, ?_⟩
    have h : ∀ c : X₁.M.O z₁, algebraMap (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ ((X₁.M.stalkEquiv z₁).symm c) = c := fun c => by
      change X₁.M.stalkHom z₁ _ = _
      rw [← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply]
    rw [h, h, ← hx]
    rfl
  · have : IsDedekindDomain X₁.o₁ := X₁.ar.ded
    have := X₁.M.lft
    have : IsLocallyNoetherian (Sp X₁.o₁) :=
      inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of X₁.o₁)))
    have : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian X₁.M.s
    infer_instance

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTranslateTermsJetsBounded
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.MBLow

theorem jc_bound_k (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V))
    (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing V) C]
    (hC : CExt V (IsLocalRing.maximalIdeal V) C) (N : NumD C) (ν : NumOf D.toPre C N) (hν : ν.IntN)
    (q : QuadraticMap ℤ N.X ℝ) (hq : N.Int q) (k : ℕ) (hk1 : 1 ≤ k) (s : Fam D.toPre C k) (gm₀ : GtPt D.toPre (epsR V))
    (gm : GtPt D.toPre (TE V C)) (htan : GtTan gm₀) (hpull : GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm) :
    ∃ b : ℝ, ∀ α, ‖(jc ν s gm α).fst / ν.rg ^ k‖ ≤ b * Real.exp (-(q α / (k : ℝ))) ∧
      ‖(jc ν s gm α).snd / ν.rg ^ k‖ ≤ b * Real.exp (-(q α / (k : ℝ))) := by
  have H1 := _root_.GlobalTheory.MBLow.TranslBound.main V D C hC N ν hν q hq k hk1 s gm₀ gm htan hpull
  have H2 := _root_.GlobalTheory.MBLow.trVal_bounded V D C hC N ν hν k hk1 s gm₀ gm htan hpull
  choose bb hbb using H2
  have hk0 : (0 : ℤ) < k := by exact_mod_cast hk1
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
  let bs := Module.Free.chooseBasis ℤ N.X
  let g : (Module.Free.ChooseBasisIndex ℤ N.X → Fin k) → N.X := fun c => ∑ i, ((c i : ℕ) : ℤ) • bs i
  let quo : N.X → N.X := fun χ => ∑ i, (bs.repr χ i / (k : ℤ)) • bs i
  let cOf : N.X → Module.Free.ChooseBasisIndex ℤ N.X → Fin k := fun χ i =>
    ⟨(bs.repr χ i % (k : ℤ)).toNat, by
      have h1 := Int.emod_nonneg (bs.repr χ i) hk0.ne'
      have h2 := Int.emod_lt_of_pos (bs.repr χ i) hk0
      omega⟩
  have hdec : ∀ χ, χ = g (cOf χ) + k • quo χ := by
    intro χ
    have e1 : ∀ i, (((cOf χ i : ℕ) : ℤ)) = bs.repr χ i % (k : ℤ) := fun i =>
      Int.toNat_of_nonneg (Int.emod_nonneg _ hk0.ne')
    have e2 : k • quo χ = ∑ i, ((k : ℤ) * (bs.repr χ i / (k : ℤ))) • bs i := by
      rw [← natCast_zsmul, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => smul_smul _ _ _
    rw [e2]
    simp only [g, e1, ← Finset.sum_add_distrib, ← add_smul]
    conv_lhs => rw [← bs.sum_repr χ]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    have := Int.mul_ediv_add_emod (bs.repr χ i) (k : ℤ)
    linarith
  have hqk : ∀ a mu : N.X, q (a + k • mu) = q a + (k : ℝ) ^ 2 * q mu + (k : ℝ) * QuadraticMap.polar q mu a := by
    intro a mu
    have e1 : q (k • mu + a) = q (k • mu) + q a + QuadraticMap.polar q (k • mu) a := by
      simp only [QuadraticMap.polar]; ring
    have e2 : q (k • mu) = ((k : ℤ) * (k : ℤ)) • q mu := by
      rw [← natCast_zsmul]; exact QuadraticMap.map_smul q _ _
    have e3 : QuadraticMap.polar q (k • mu) a = (k : ℤ) • QuadraticMap.polar q mu a := by
      rw [← natCast_zsmul]; exact QuadraticMap.polar_smul_left q _ _ _
    rw [add_comm, e1, e2, e3, zsmul_eq_mul, zsmul_eq_mul]
    push_cast; ring
  have hexp : ∀ a mu : N.X, Real.exp (-((k : ℝ) * q mu + QuadraticMap.polar q mu a)) =
      Real.exp (q a / k) * Real.exp (-(q (a + k • mu) / k)) := by
    intro a mu
    rw [← Real.exp_add, hqk]
    congr 1
    field_simp
    ring
  let B : ℝ := ∑ c, max 0 (bb (g c) * Real.exp (q (g c) / k))
  have hB : ∀ c, bb (g c) * Real.exp (q (g c) / k) ≤ B := fun c =>
    (le_max_right _ _).trans (Finset.single_le_sum (f := fun c => max 0 (bb (g c) * Real.exp (q (g c) / k)))
      (fun _ _ => le_max_left _ _) (Finset.mem_univ c))
  refine ⟨‖ν.rg ^ k‖⁻¹ * B, fun α => ?_⟩
  have hα := hdec α
  obtain ⟨h1, h2⟩ := H1 (g (cOf α)) (quo α)
  obtain ⟨h3, h4⟩ := hbb (g (cOf α)) (quo α)
  have hE := hexp (g (cOf α)) (quo α)
  rw [← hα] at h1 h2 hE
  have key : ∀ x : ℝ, x ≤ Real.exp (-((k : ℝ) * q (quo α) + QuadraticMap.polar q (quo α) (g (cOf α)))) * bb (g (cOf α)) →
      x ≤ B * Real.exp (-(q α / k)) := by
    intro x hx
    refine hx.trans ?_
    rw [hE]
    calc Real.exp (q (g (cOf α)) / k) * Real.exp (-(q α / k)) * bb (g (cOf α)) =
        (bb (g (cOf α)) * Real.exp (q (g (cOf α)) / k)) * Real.exp (-(q α / k)) := by ring
      _ ≤ B * Real.exp (-(q α / k)) := mul_le_mul_of_nonneg_right (hB _) (Real.exp_pos _).le
  have hE0 := Real.exp_pos (-((k : ℝ) * q (quo α) + QuadraticMap.polar q (quo α) (g (cOf α))))
  have hr0 : 0 ≤ ‖ν.rg ^ k‖⁻¹ := inv_nonneg.2 (norm_nonneg _)
  constructor
  · rw [norm_div, div_eq_mul_inv, mul_comm, _root_.mul_assoc]
    exact mul_le_mul_of_nonneg_left (key _ (h1.trans (mul_le_mul_of_nonneg_left h3 hE0.le))) hr0
  · rw [norm_div, div_eq_mul_inv, mul_comm, _root_.mul_assoc]
    exact mul_le_mul_of_nonneg_left (key _ (h2.trans (mul_le_mul_of_nonneg_left (max_le h3 h4) hE0.le))) hr0

theorem jc_bound : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ∀ q, N.Int q → ∀ (m : ℕ), Odd m → ∀ (p : N.QT (m ^ 2)) (s : Fam D.toPre C (m ^ 2)) (f : N.X → N.A → C), ν.FamV s f → IsEvFam N m p f → ∀ (gm₀ : GtPt D.toPre (epsR V)) (gm : GtPt D.toPre (TE V C)), GtTan gm₀ → GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm → ∃ b : ℝ, ∀ α, ‖(jc ν s gm α).fst / ν.rg ^ (m ^ 2)‖ ≤ b * Real.exp (-(q α / (m : ℝ) ^ 2)) ∧ ‖(jc ν s gm α).snd / ν.rg ^ (m ^ 2)‖ ≤ b * Real.exp (-(q α / (m : ℝ) ^ 2)) := by
  intro V _ _ _ D C _ _ _ _ _ hC N ν hν q hq m hm p s f hf hev gm₀ gm htan hpull
  have hk1 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm.pos
  obtain ⟨b, hb⟩ := jc_bound_k V D C hC N ν hν q hq (m ^ 2) hk1 s gm₀ gm htan hpull
  refine ⟨b, fun α => ?_⟩
  have hcast : (((m ^ 2 : ℕ) : ℝ)) = (m : ℝ) ^ 2 := by push_cast; ring
  rw [← hcast]
  exact hb α

end GlobalTheory.MBLow

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTrivialAtPlaceProduct
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.PureAway

theorem pure_away : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (g : UA σ G.V'.J) (h : UA σ G.W.J), (∀ u : AF F, At (evFin F v) u → u • (mat g - 1) = 0) →
    (∀ u : AF F, At (evFin F v) u → u • (mat h - 1) = 0) →
    ∀ (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ᶠ w in Filter.cofinite, φ w = G.M'.vac w) →
    ∃ (f₂ : SInf F (Fin a' × Fin (a + a'))) (φ₂ : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ),
      (∀ w, φ₂ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) ∧ (∀ᶠ w in Filter.cofinite, φ₂ w = G.M'.vac w) ∧ φ₂ v = φ v ∧
      om' (g, h) (pure f φ) = pure f₂ φ₂ := by
  classical
  intro P F E _ _ _ _ _ σ B a a' G X om om' hT v g h hg hh f φ hφ hφv
  obtain ⟨S, g₁, g₂, g₃, h₁, h₂, h₃, hvS, rfl, rfl, a1, a2, b1, b2, c1, c2, c3, c4, c5, c6⟩ :=
    GlobalTheory.T.theta_local_factor_finite_place F E σ B a a' G X om om' hT v g h hg hh φ hφv
  obtain ⟨c, hc⟩ := GlobalTheory.T.theta_trivial_at_infinity_set P F E σ B a a' G X om om' hT (insert v S) g₃ h₃ c1 c2
    (fun w hw => c3 w (Finset.mem_insert.mp hw)) (fun w hw => c4 w (Finset.mem_insert.mp hw))
    (fun w hw => c5 w (fun e => hw (e ▸ Finset.mem_insert_self _ _)) (fun e => hw (Finset.mem_insert_of_mem e))) f φ hφ
    (fun w hw => c6 w (fun e => hw (e ▸ Finset.mem_insert_self _ _)) (fun e => hw (Finset.mem_insert_of_mem e)))
  obtain ⟨φ₁, hφ₁, hφ₁e, he₁⟩ := GlobalTheory.T.theta_trivial_at_finite_set P F E σ B a a' G X om om' hT S g₂ h₂ b1 b2 f φ hφ hφv
  have hφ₁v : ∀ᶠ w in Filter.cofinite, φ₁ w = G.M'.vac w := by
    filter_upwards [hφv, S.finite_toSet.compl_mem_cofinite] with w hw hwS
    rw [hφ₁e w hwS, hw]
  obtain ⟨f₂, he₂⟩ := GlobalTheory.T.archimedean_theta_local_action P F E σ B a a' G X om om' hT g₁ h₁ a1 a2 f φ₁ hφ₁ hφ₁v
  refine ⟨c • f₂, φ₁, hφ₁, hφ₁v, hφ₁e v hvS, ?_⟩
  have hmul : ((g₁ * g₂ * g₃, h₁ * h₂ * h₃) : UA σ G.V'.J × UA σ G.W.J) = (g₁, h₁) * (g₂, h₂) * (g₃, h₃) := rfl
  rw [hmul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hc, map_smul, he₁, map_smul, he₂]
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

end GlobalTheory.PureAway
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormDerivationDetPairingChangeMatrixStatement
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topFormDerivationDetPairing_change_matrix : ∀ {k A : Type} [CommRing k] [CommRing A] (α : k →+* A) {n : ℕ}
    (D D' : Fin n → (letI := α.toAlgebra; Derivation k A A)) (L : Matrix (Fin n) (Fin n) A),
    (letI := α.toAlgebra; ∀ j, D j = ∑ i, L i j • D' i) →
    ∀ η, GlobalTheory.LogKSDiv.topPair α D η = L.det * GlobalTheory.LogKSDiv.topPair α D' η := by
  first | exact @GlobalTheory.LogKSDiv.topPair_change_matrix | exact GlobalTheory.LogKSDiv.topPair_change_matrix | (intros; apply GlobalTheory.LogKSDiv.topPair_change_matrix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFrameInvariantUnderDescentDatum
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LBDescent

theorem twist_frame_descent : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (L : LB X) (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ)
    (V : Y.Opens) (t : ∀ i, Γ(X, f ⁻¹ᵁ V ⊓ L.U i)ˣ), (∀ (i j : L.ι) (x : X), f x ∈ V → x ∈ L.U i → x ∈ L.U j →
      gm (𝟙 X) x _ (t i) = gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (t j)) →
    ∀ (c : Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V)ˣ),
      (∀ (z : ↥(pullback f f)) (i j : L.ι), f (pullback.fst f f z) ∈ V → pullback.fst f f z ∈ L.U i →
        pullback.snd f f z ∈ L.U j →
        gm (𝟙 _) z _ c = gm (pullback.fst f f) z _ (t i) * gm (𝟙 _) z _ (φ i j) * (gm (pullback.snd f f) z _ (t j))⁻¹) →
    ∀ (V' : Y.Opens), V' ≤ V → ∀ u : Γ(X, f ⁻¹ᵁ V')ˣ, (∀ z : ↥(pullback f f), f (pullback.fst f f z) ∈ V' →
        gm (pullback.fst f f) z _ u * gm (𝟙 _) z _ c = gm (pullback.snd f f) z _ u) →
    ∃ s : ∀ i, Γ(X, f ⁻¹ᵁ V' ⊓ L.U i)ˣ,
      (∀ (i j : L.ι) (x : X), f x ∈ V' → x ∈ L.U i → x ∈ L.U j →
        gm (𝟙 X) x _ (s i) = gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (s j)) ∧
      ∀ (z : ↥(pullback f f)) (i j : L.ι), f (pullback.fst f f z) ∈ V' → pullback.fst f f z ∈ L.U i →
        pullback.snd f f z ∈ L.U j →
        gm (pullback.fst f f) z _ (s i) * gm (𝟙 _) z _ (φ i j) = gm (pullback.snd f f) z _ (s j) := by
  intro X Y f L φ V t ht c hc V' hV' u hu
  have h1 : ∀ i, f ⁻¹ᵁ V' ⊓ L.U i ≤ f ⁻¹ᵁ V' := fun i => inf_le_left
  have h2 : ∀ i, f ⁻¹ᵁ V' ⊓ L.U i ≤ f ⁻¹ᵁ V ⊓ L.U i := fun i =>
    inf_le_inf_right _ (fun x hx => hV' hx)
  refine ⟨fun i => res (h1 i) u * res (h2 i) (t i), ?_, ?_⟩
  · intro i j x hx hi hj
    have mi : (𝟙 X) x ∈ f ⁻¹ᵁ V' ⊓ L.U i := ⟨hx, hi⟩
    have mj : (𝟙 X) x ∈ f ⁻¹ᵁ V' ⊓ L.U j := ⟨hx, hj⟩
    rw [map_mul, map_mul, gm_res _ x _ mi, gm_res _ x _ mi, gm_res _ x _ mj, gm_res _ x _ mj,
      ht i j x (hV' hx) hi hj]
    exact mul_left_comm _ _ _
  · intro z i j hz hi hj
    have hfz : f (pullback.snd f f z) = f (pullback.fst f f z) := by
      have := congrArg (fun g => g z) (congrArg (fun g => g.base) (pullback.condition (f := f) (g := f)))
      simpa using this.symm
    have mi : pullback.fst f f z ∈ f ⁻¹ᵁ V' ⊓ L.U i := ⟨hz, hi⟩
    have mj : pullback.snd f f z ∈ f ⁻¹ᵁ V' ⊓ L.U j := ⟨show f (pullback.snd f f z) ∈ V' by rw [hfz]; exact hz, hj⟩
    rw [map_mul, map_mul, gm_res _ z _ mi, gm_res _ z _ mi, gm_res _ z _ mj, gm_res _ z _ mj, ← hu z hz,
      hc z i j (hV' hz) hi hj]
    group

end GlobalTheory.LBDescent
end
end

