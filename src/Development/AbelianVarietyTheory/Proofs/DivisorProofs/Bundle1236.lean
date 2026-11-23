module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.IrreducibleOfIrreducibleMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormIntExistsAndChowFormExists
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1221

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantOneMemCuspFormsOfWittIndexZero
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory

theorem constant_one_mem_cuspForms_of_wittIndex_zero : ∀ {D : D7} {θ : InfFam D} {A B : HSp D} {sA : RealMat A} {sB : RealMat B} {t : ℕ} {cA : CptF A}, HidaSetting θ A B sA sB t cA → wittIndex A = 0 → (fun _ : GA D A => (1 : ℂ)) ∈ A0 θ A cA := by
  intro D θ A B sA sB t cA _ h
  rw [wittIndex_eq_zero_iff_isAniso] at h
  exact (mem_cuspForms).2 ⟨⟨isAutFunSm_const θ A 1, fun r C hC => absurd hC (h r C)⟩, .of_invariant fun _ _ _ => rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCoeffOfSeparating
section
namespace GlobalTheory.ContinuousRepresentationCoefficients

theorem continuous_coeff_of_separating {X V ι : Type} [TopologicalSpace X] [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (L : ι → V →ₗ[ℂ] ℂ)
    (hL : ∀ v, (∀ i, L i v = 0) → v = 0) (f : X → V) (hf : ∀ i, Continuous fun x => L i (f x))
    (ℓ : Module.Dual ℂ V) : Continuous fun x => ℓ (f x) := by
  have hmem : ℓ ∈ Submodule.span ℂ (Set.range L) := by
    apply FiniteDimensional.mem_span_of_iInf_ker_le_ker
    intro v hv
    have h0 : v = 0 := hL v fun i => by
      simpa using (Submodule.mem_iInf _).1 hv i
    simp [h0]
  induction hmem using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hf i
  | zero => simpa using continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact (continuous_const (y := c)).mul hx

theorem continuous_translate {E : Type} [Field E] [NumberField E] [NumberField.IsTotallyComplex E]
    {a : ℕ} (φ : GlobalTheory.CuspRep.Sm E a) (g : GlobalTheory.CuspRep.GA E a) :
    Continuous fun k : GlobalTheory.CuspRep.Kinf E a =>
      ((GlobalTheory.CuspRep.cptRep E a k φ : GlobalTheory.CuspRep.Sm E a) : GlobalTheory.CuspRep.GA E a → ℂ) g := by
  have h1 : ContinuousOn (GlobalTheory.CuspRep.chart φ.1 g) (GlobalTheory.CuspRep.invSet E a) :=
    (φ.2 g).continuousOn
  have hu : ∀ k : GlobalTheory.CuspRep.Kinf E a,
      IsUnit (Matrix.of (k.1 : GlobalTheory.CuspRep.Lie E a)) := fun k => (Unitary.toUnits k).isUnit
  have h2 : Continuous fun k : GlobalTheory.CuspRep.Kinf E a => (k.1 : GlobalTheory.CuspRep.Lie E a) :=
    continuous_subtype_val
  have h3 := h1.comp_continuous h2 hu
  refine h3.congr fun k => ?_
  have h4 : (hu k).unit = Unitary.toUnits k := Units.ext rfl
  show GlobalTheory.CuspRep.chart φ.1 g (k.1 : GlobalTheory.CuspRep.Lie E a) = _
  unfold GlobalTheory.CuspRep.chart
  rw [dite_eq_left (hu k), h4]
  rfl

theorem isContRep_sub {E : Type} [Field E] [NumberField E] [NumberField.IsTotallyComplex E]
    {a : ℕ} (W : Submodule ℂ (GlobalTheory.CuspRep.Sm E a))
    (hW : ∀ (k : GlobalTheory.CuspRep.Kinf E a), ∀ w ∈ W, GlobalTheory.CuspRep.cptRep E a k w ∈ W)
    [FiniteDimensional ℂ W] :
    GlobalTheory.Published.AutFin.IsContRep (GlobalTheory.PRep.sub (GlobalTheory.CuspRep.cptRep E a) W hW) := by
  intro ℓ w
  refine continuous_coeff_of_separating
    (fun g : GlobalTheory.CuspRep.GA E a =>
      (LinearMap.proj g : (GlobalTheory.CuspRep.GA E a → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
        (GlobalTheory.CuspRep.Sm E a).subtype ∘ₗ W.subtype) ?_ _ ?_ ℓ
  · intro v hv
    exact Subtype.ext (Subtype.ext (funext hv))
  · intro g
    exact continuous_translate w.1 g

end GlobalTheory.ContinuousRepresentationCoefficients
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentFormOfSqZeroPointLinearNatural
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.SqZeroPt

theorem eq_map_of_isSum {O : Type} [CommRing O] {M M' : Type} [AddCommGroup M] [Module O M]
    [Module Oᵐᵒᵖ M] [IsCentralScalar O M] [AddCommGroup M'] [Module O M'] [Module Oᵐᵒᵖ M']
    [IsCentralScalar O M'] (f : M →ₗ[O] M') (β : TrivSqZeroExt O M →+* TrivSqZeroExt O M')
    (hβ : GlobalTheory.AbTan.IsSum β id f) : β = (TrivSqZeroExt.map f).toRingHom := by
  ext x
  all_goals
    rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq x, map_add (f := _), hβ.1, hβ.2]
    simp

theorem Phi_linear_natural : ∀ (O : Type) [CommRing O] (A : Over (Sp O)) [GrpObj A] (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (v : GlobalTheory.SqZeroPt.TM O M ⟶ A) (h : GlobalTheory.SqZeroPt.zeroSec O M ≫ v = η[A]), (∀ (r : O) w, GlobalTheory.SqZeroPt.Phi v h (r • w) = r • GlobalTheory.SqZeroPt.Phi v h w) ∧ ∀ (M' : Type) [AddCommGroup M'] [Module O M'] [Module Oᵐᵒᵖ M'] [IsCentralScalar O M'] (f : M →ₗ[O] M') (β : TrivSqZeroExt O M →+* TrivSqZeroExt O M'), IsSum β id f → ∀ (v' : GlobalTheory.SqZeroPt.TM O M' ⟶ A) (h' : GlobalTheory.SqZeroPt.zeroSec O M' ≫ v' = η[A]), v'.left = spMap β ≫ v.left → ∀ w, GlobalTheory.SqZeroPt.Phi v' h' w = f (GlobalTheory.SqZeroPt.Phi v h w) := by
  intro O _ A _ M _ _ _ _ v h
  refine ⟨fun r w => Phi_smul O M A v h r w, ?_⟩
  intro M' _ _ _ _ f β hβ v' h' hv w
  have e : v' = GlobalTheory.GrpTangent.sqZeroMap f ≫ v := by
    apply Over.OverMorphism.ext
    rw [hv, eq_map_of_isSum f β hβ]
    rfl
  subst e
  exact Phi_sqZeroMap_comp O M M' A f v h h' w

end GlobalTheory.SqZeroPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubWeilOneOfTrivPull
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.RaynaudAxis

theorem cubN_mul_pow {A U : Type} [CommGroup A] [CommGroup U] (t : A → U) (θ : A → A → A → U)
    (h : ∀ p q w, θ p q w * t (p * q) * t (p * w) * t (q * w) * t 1 = t (p * q * w) * t p * t q * t w)
    (a b : A) (n : ℕ) :
    cubN θ n 1 a b * (t (a * b) * t 1 * (t a)⁻¹ * (t b)⁻¹) ^ n = t (a ^ n * b) * t 1 * (t (a ^ n))⁻¹ * (t b)⁻¹ := by
  induction n with
  | zero => simp [cubN]
  | succ n ih =>
    have e := h (a ^ n) a b
    simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
    rw [pow_succ, pow_succ]
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    have ih' := congrArg Additive.ofMul ih
    simp only [ofMul_mul, ofMul_inv, ofMul_pow] at e' ih' ⊢
    linear_combination (norm := abel) e' + ih'

theorem cubN_of_torsion {A U : Type} [CommGroup A] [CommGroup U] (t : A → U) (θ : A → A → A → U)
    (h : ∀ p q w, θ p q w * t (p * q) * t (p * w) * t (q * w) * t 1 = t (p * q * w) * t p * t q * t w)
    (a b : A) (N : ℕ) (ha : a ^ N = 1) :
    cubN θ N 1 a b * (t (a * b) * t 1 * (t a)⁻¹ * (t b)⁻¹) ^ N = 1 := by
  rw [cubN_mul_pow t θ h, ha, _root_.one_mul, mul_inv_cancel_right, mul_inv_cancel]

variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H]

def tV {L : RigLB G} (i : H ⟶ G) (τ : LB.Gen (L.L.pull i.left)) {T : Over S} (z : T.left)
    (J : (T.left ⟶ G.left) → L.L.ι) (x : T ⟶ H) : (T.left.presheaf.stalk z)ˣ :=
  val (L := L.L) (φ := fun _ : PUnit => i.left) (ε := fun _ => 1) τ x.left z J

theorem prod_tt (i : H ⟶ G) {Y : Over S} (p : Y ⟶ H) {U : Type} [CommGroup U] (h : (Y.left ⟶ G.left) → U) :
    ∏ k : PUnit, h ((fun _ : PUnit => p.left ≫ i.left) k) ^ ((fun _ : PUnit => (1 : ℤ)) k) = h (p ≫ i).left := by
  rw [Fintype.prod_unique, zpow_one]; rfl

end GlobalTheory.RaynaudAxis

namespace GlobalTheory.RaynaudAxis
variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H]

theorem cub_tV (hG : GlobalFnsSt) (hA : IsAbelianScheme H) (i : H ⟶ G) [IsMonHom i] {L : RigLB G}
    (c : CubicalStr G L) (τ : LB.Gen (L.L.pull i.left)) (hτ : τ.IsGen) (T : Over S) (x y u : T ⟶ H) (z : T.left)
    (J : (T.left ⟶ G.left) → L.L.ι) (hJ : Good L.L z J) :
    cubV c z J (x ≫ i) (y ≫ i) (u ≫ i) * tV i τ z J (x * y) * tV i τ z J (x * u) * tV i τ z J (y * u) *
        tV i τ z J 1 = tV i τ z J (x * y * u) * tV i τ z J x * tV i τ z J y * tV i τ z J u := by
  haveI := hA.comm
  have h3 := surjective_cube hG hA
  let a := x3 H 0
  let b := x3 H 1
  let d := x3 H 2
  let tt := fun p : G3 H ⟶ H => LB.pullGen L.L (fun _ : PUnit => i.left) (fun _ => 1) τ p.left
  let cu := LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift (a ≫ i) (lift (b ≫ i) (d ≫ i))).left
  have gt : ∀ p, (tt p).IsGen := fun p => DVR.pullGen_isGen _ _ _ _ hτ _
  have gc : cu.IsGen := DVR.pullGen_isGen _ _ _ _ c.isGen _
  have vt : ∀ {T' : Over S} (σ : T' ⟶ G3 H) {z : T'.left} {J}, Good L.L z J → ∀ p,
      val (tt p) σ.left z J = tV i τ z J (σ ≫ p) := fun σ z J hJ p => val_pull hJ _ _ _
  let t₁ := LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ cu
    (tt (a * b))) (tt (a * d))) (tt (b * d))) (tt 1)
  let t₂ := LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (tt (a * b * d)) (tt a)) (tt b))
    (tt d)
  have ev : ∀ {T' : Over S} (σ : T' ⟶ G3 H) {z : T'.left} {J}, Good L.L z J →
      val t₁ σ.left z J = cubV c z J (σ ≫ a ≫ i) (σ ≫ b ≫ i) (σ ≫ d ≫ i) * tV i τ z J (σ ≫ (a * b)) *
        tV i τ z J (σ ≫ (a * d)) * tV i τ z J (σ ≫ (b * d)) * tV i τ z J (σ ≫ 1) ∧
      val t₂ σ.left z J = tV i τ z J (σ ≫ (a * b * d)) * tV i τ z J (σ ≫ a) * tV i τ z J (σ ≫ b) *
        tV i τ z J (σ ≫ d) := fun σ z J hJ => by
    constructor
    · exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
          (val_cub c σ hJ _ _ _) (vt σ hJ _))) (vt σ hJ _))) (vt σ hJ _))) (vt σ hJ _))
    · exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vt σ hJ _) (vt σ hJ _))) (vt σ hJ _))) (vt σ hJ _))
  let e : 𝟙_ (Over S) ⟶ G3 H := lift 1 (lift 1 1)
  have e₀ : e ≫ a = 1 := by simp [e, a, x3]
  have e₁ : e ≫ b = 1 := by simp [e, b, x3]
  have e₂ : e ≫ d = 1 := by simp [e, d, x3]
  let ρ : T ⟶ G3 H := lift x (lift y u)
  have r₀ : ρ ≫ a = x := by simp [ρ, a, x3]
  have r₁ : ρ ≫ b = y := by simp [ρ, b, x3]
  have r₂ : ρ ≫ d = u := by simp [ρ, d, x3]
  have key : val t₁ ρ.left z J = val t₂ ρ.left z J := by
    refine gen_unique' L.isLB (fun V _ k => ?_) (G3 H).hom e.left (Over.w e) h3
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
        (DVR.mulGen_isGen _ _ _ _ _ _ _ gc (gt _)) (gt _)) (gt _)) (gt _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (gt _)
        (gt _)) (gt _)) (gt _)) (fun y I hI => ?_) _ ρ.left z J hJ
    · refine (DVR.prod_sum₂ (U := V) _ (DVR.prod_sum₂ (U := V) _ (DVR.prod_sum₂ (U := V) _
        (prod_tt i (a * b * d) k) (prod_tt i a k)) (prod_tt i b k)) (prod_tt i d k)).trans (Eq.trans ?_
        (DVR.prod_sum₂ (U := V) _ (DVR.prod_sum₂ (U := V) _ (DVR.prod_sum₂ (U := V) _ (DVR.prod_sum₂ (U := V) _
          (prod_cub (a ≫ i) (b ≫ i) (d ≫ i) k) (prod_tt i (a * b) k)) (prod_tt i (a * d) k))
          (prod_tt i (b * d) k)) (prod_tt i 1 k)).symm)
      simp only [MonObj.mul_comp, MonObj.one_comp]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    · refine (ev e hI).1.trans (Eq.trans ?_ (ev e hI).2.symm)
      have C := isCub_cubV c (T := 𝟙_ (Over S)) hI
      simp only [← Category.assoc, MonObj.comp_mul, MonObj.comp_one, e₀, e₁, e₂, MonObj.one_comp, _root_.mul_one]
      rw [C.face, _root_.one_mul]
  have := (ev ρ hJ).1.symm.trans (key.trans (ev ρ hJ).2)
  simp only [← Category.assoc, MonObj.comp_mul, MonObj.comp_one, r₀, r₁, r₂] at this
  exact this

end GlobalTheory.RaynaudAxis

namespace GlobalTheory.RaynaudAxis

theorem cubWeil_one_of_triv_pull : ∀ (S : Scheme.{0}) (G H : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj H]
    (i : H ⟶ G), IsAbelianScheme H → IsMonHom i → ∀ (L : RigLB G) (c : CubicalStr G L), Triv (L.L.pull i.left) →
    ∀ (N : ℕ) (T : Over S) (a b : T ⟶ H), a ^ N = 1 → b ^ N = 1 → CubWeil c N (a ≫ i) (b ≫ i) 1 := by
  intro S G H _ _ _ i hA hi L c ⟨τ, hτ⟩ N T a b ha hb
  haveI := hA.comm
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  refine ⟨by rw [← MonObj.pow_comp, ha, MonObj.one_comp], by rw [← MonObj.pow_comp, hb, MonObj.one_comp],
    fun z J hJ => ?_⟩
  let θ : (T ⟶ H) → (T ⟶ H) → (T ⟶ H) → (T.left.presheaf.stalk z)ˣ :=
    fun p q w => cubV c z J (p ≫ i) (q ≫ i) (w ≫ i)
  have h := cub_tV hG hA i c τ hτ T (z := z) (J := J) (hJ := hJ)
  have tr : ∀ p q : T ⟶ H, cubN (cubV c z J) N 1 (p ≫ i) (q ≫ i) = cubN θ N 1 p q := fun p q =>
    Finset.prod_congr rfl fun k _ => by
      simp only [θ, _root_.one_mul, MonObj.pow_comp]
  have e₁ := cubN_of_torsion (tV i τ z J) θ (fun p q w => h p q w) a b N ha
  have e₂ := cubN_of_torsion (tV i τ z J) θ (fun p q w => h p q w) b a N hb
  rw [mul_comm b a, mul_right_comm _ (tV i τ z J b)⁻¹] at e₂
  rw [map_one, _root_.one_mul, tr, tr]
  exact mul_right_cancel (e₁.trans e₂.symm)

end GlobalTheory.RaynaudAxis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeEqHilbertDegreeOfIsChowForm
section
set_option autoImplicit false

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.ChowDegree

attribute [local instance] MvPolynomial.gradedAlgebra

theorem degree_eq_hilbertDegree_of_isChowForm : ∀ (F : Type) [Field F] [CharZero F] (D N δ : ℕ) (I : Ideal (MvPolynomial (Fin N) F)) (f : MvPolynomial (Fin (D + 1) × Fin N) F), IsChowForm I D δ f → I.IsPrime → (∀ g ∈ I, ∀ n : ℕ, homogeneousComponent n g ∈ I) → δ = hilbertDegree I := by
  intro F _ _ D N δ I f hf hp hI
  haveI := hp
  exact GlobalTheory.ChowExists.degree_eq_hilbertDegree (GlobalTheory.ChowExists.isHomogeneous_of_component hI)
    hf.isChowFormInt

end GlobalTheory.ChowDegree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalIntegralInvariantFormDiagonalLagrangian
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

noncomputable section
attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField
  GlobalTheory.DiagForm.measAf GlobalTheory.DiagForm.borelAf

namespace GlobalTheory.DiagLagrNorm
open MeasureTheory GlobalTheory.DiagForm IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem map_eI_eq : ∃ k : NNReal, k ≠ 0 ∧
    Measure.map (eI F κ) (volume : Measure (Vi F κ)) = k • (volume : Measure (κ → mixedEmbedding.mixedSpace F)) := by
  have : MeasurableAdd (mixedEmbedding.mixedSpace F) := inferInstance
  have : SigmaFinite (volume : Measure (mixedEmbedding.mixedSpace F)) := inferInstance
  have : (volume : Measure (κ → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure :=
    Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfSigmaFinite
  have : (Measure.map (eI F κ) (volume : Measure (Vi F κ))).IsAddHaarMeasure :=
    (eI F κ).isAddHaarMeasure_map volume
  exact ⟨_, (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne',
    Measure.isAddLeftInvariant_eq_smul _ _⟩

theorem integral_compD {k : NNReal}
    (hk : Measure.map (eI F κ) (volume : Measure (Vi F κ)) = k • (volume : Measure (κ → mixedEmbedding.mixedSpace F)))
    (f : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ) :
    SchwartzMap.integralCLM ℂ (volume : Measure (Vi F κ)) (compD F κ f) =
      (k : ℂ) * ∫ x : κ → mixedEmbedding.mixedSpace F, f (Sum.elim x x) := by
  rw [SchwartzMap.integralCLM_apply]
  have e : ∀ u, compD F κ f u = (fun x : κ → mixedEmbedding.mixedSpace F => f (Sum.elim x x)) (eI F κ u) :=
    fun u => rfl
  simp only [e]
  have h1 := integral_map_equiv (μ := (volume : Measure (Vi F κ))) (eI F κ).toHomeomorph.toMeasurableEquiv
    (fun x : κ → mixedEmbedding.mixedSpace F => f (Sum.elim x x))
  change ∫ y, f (Sum.elim y y) ∂(Measure.map (eI F κ) volume) = ∫ x, f (Sum.elim (eI F κ x) (eI F κ x)) at h1
  rw [hk, integral_smul_nnreal_measure] at h1
  rw [← h1, NNReal.smul_def, Complex.real_smul]

theorem exists_SB_ne : ∃ g ∈ SB (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F),
    (∫ v : Vf F κ, g (Sum.elim v v) ∂Measure.addHaar) ≠ 0 := by
  obtain ⟨hO, hK⟩ := PI.IntAdCpctOpenWork.main F
  set O := {x : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), x v ∈ v.adicCompletionIntegers F}
  have h0 : (0 : FiniteAdeleRing (𝓞 F) F) ∈ O := fun v => (v.adicCompletionIntegers F).zero_mem
  set U : Set (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) := Set.univ.pi fun _ => O
  have hUo : IsOpen U := isOpen_set_pi Set.finite_univ fun _ _ => hO
  have hUc : IsCompact U := isCompact_univ_pi fun _ => hK
  set g : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ := U.indicator fun _ => 1
  have hg : g ∈ SB (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) :=
    ⟨(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) ⟨hUc.isClosed, hUo⟩).isLocallyConstant,
      HasCompactSupport.intro hUc fun z hz => Set.indicator_of_notMem hz _⟩
  set V : Set (Vf F κ) := Set.univ.pi fun _ => O
  have hVo : IsOpen V := isOpen_set_pi Set.finite_univ fun _ _ => hO
  have hVc : IsCompact V := isCompact_univ_pi fun _ => hK
  have hgV : (fun v : Vf F κ => g (Sum.elim v v)) = V.indicator fun _ => (1 : ℂ) := by
    funext v
    simp only [g, U, V, Set.indicator_apply, Set.mem_univ_pi, Sum.forall, Sum.elim_inl, Sum.elim_inr, and_self]
  refine ⟨g, hg, ?_⟩
  rw [hgV, integral_indicator_const _ hVo.measurableSet]
  have hpos : 0 < (Measure.addHaar : Measure (Vf F κ)) V := hVo.measure_pos _ ⟨0, fun i _ => h0⟩
  have hfin : (Measure.addHaar : Measure (Vf F κ)) V < ⊤ := hVc.measure_lt_top
  have : 0 < (Measure.addHaar : Measure (Vf F κ)).real V := ENNReal.toReal_pos hpos.ne' hfin.ne
  simpa using this.ne'

end GlobalTheory.DiagLagrNorm

namespace GlobalTheory.RealLift

open MeasureTheory GlobalTheory.DiagForm GlobalTheory.DiagLagrNorm

theorem diagLagr_invForm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type)
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ) (JA : Matrix α α (AE F E))
    (JB : Matrix β β (AE F E)) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) JA (dbl JB)) (κ ⊕ κ)),
    IsStd ψ → IsDblCoord (cA σ) (-1) JA JB d dd →
    ∃ l ∈ (adeleClass F).adm (κ ⊕ κ), (∀ z : Matrix α β (AE F E), ∀ φ ∈ (adeleClass F).sp (κ ⊕ κ),
      l (dd.rho ψ (z * (diagCols β : Matrix (β ⊕ β) β (AE F E))ᵀ) φ) = l φ) ∧
      ∃ g ∈ SB (κ ⊕ κ → Af F), ∀ f : SInf F (κ ⊕ κ),
        l (pureA F f g) = ∫ x : κ → mixedEmbedding.mixedSpace F, f (Sum.elim x x) := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ ψ JA JB d dd _ hdd
  obtain ⟨k, hk0, hk⟩ := map_eI_eq (F := F) (κ := κ)
  obtain ⟨g, hg, hc⟩ := exists_SB_ne (F := F) (κ := κ)
  set c : ℂ := (∫ v : Vf F κ, g (Sum.elim v v) ∂Measure.addHaar) * (k : ℂ) with hcdef
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk0
  have hc0 : c ≠ 0 := mul_ne_zero hc hk'
  refine ⟨c⁻¹ • lDiag F κ, ?_, ?_, g, hg, ?_⟩
  · intro g' hg'
    obtain ⟨T, hT⟩ := lDiag_adm (F := F) (κ := κ) g' hg'
    exact ⟨c⁻¹ • T, fun f => by simp [hT f]⟩
  · intro z φ hφ
    have hz : z * (diagCols β : Matrix (β ⊕ β) β (AE F E))ᵀ = Matrix.fromCols z z := by
      rw [diagCols, Matrix.transpose_fromRows, Matrix.transpose_one, Matrix.mul_fromCols, Matrix.mul_one]
    have hr : dd.rho ψ (z * (diagCols β : Matrix (β ⊕ β) β (AE F E))ᵀ) φ =
        schr ψ (Sum.elim (d.e z).1 (d.e z).1, Sum.elim (d.e z).2 (-(d.e z).2)) φ := by
      rw [hz, Darboux.rho, hdd z z]
    simp only [LinearMap.smul_apply]
    rw [hr, lDiag_schr ψ _ _ hφ]
  · intro f
    simp only [LinearMap.smul_apply]
    rw [lDiag_pureA f hg, integral_compD hk, smul_eq_mul, hcdef]
    field_simp

end GlobalTheory.RealLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledHermitianSpaceFrameOfFrame
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

noncomputable section

namespace GlobalTheory.RealLift.Dbl

theorem dblM_gram {β : Type} [Fintype β] [DecidableEq β] {R S : ℕ} (N : Matrix β β ℂ) (C : Matrix β (Ix R S) ℂ)
    (h : Cᵀ * N * C.map star = Jm R S) :
    (dblM C)ᵀ * Matrix.fromBlocks N 0 0 (-N) * (dblM C).map star = Jm (R + S) (S + R) := by
  have hG : ∀ a a', ∑ x, (∑ y, C y a * N y x) * (starRingEnd ℂ) (C x a') = Jm R S a a' := by
    intro a a'
    have := congrFun (congrFun h a) a'
    simpa [Matrix.mul_apply] using this
  ext j k
  rcases j with p | p <;> rcases k with q | q <;>
  · obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective p
    obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective q
    rcases x with r | s <;> rcases y with r' | s' <;>
      simp [Matrix.mul_apply, Fintype.sum_sum_type, dblM, dblCol, hG, Jm, Formalism.UG.Jpq, Matrix.one_apply,
        Finset.sum_neg_distrib, Matrix.neg_apply, Fin.ext_iff, Function.swap] <;> omega

theorem dblM_rinv {β : Type} [Fintype β] [DecidableEq β] {R S : ℕ} (C : Matrix β (Ix R S) ℂ)
    (h : ∃ C' : Matrix (Ix R S) β ℂ, C * C' = 1) :
    ∃ D : Matrix (Ix (R + S) (S + R)) (β ⊕ β) ℂ, dblM C * D = 1 := by
  obtain ⟨C', hC'⟩ := h
  refine ⟨(dblM C'ᵀ)ᵀ, ?_⟩
  have hI : ∀ i i', ∑ r, C i (Sum.inl r) * C' (Sum.inl r) i' + ∑ s, C i (Sum.inr s) * C' (Sum.inr s) i' =
      (1 : Matrix β β ℂ) i i' := by
    intro i i'
    rw [← hC', Matrix.mul_apply, Fintype.sum_sum_type]
  ext i i'
  rcases i with i | i <;> rcases i' with i' | i' <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_add, dblM, dblCol, Matrix.one_apply, hI, add_comm, Function.swap]

theorem dblM_isFrame {β : Type} [Fintype β] [DecidableEq β] {R S : ℕ} (N : Matrix β β ℂ) (C : Matrix β (Ix R S) ℂ)
    (h : IsFrame N C) : IsFrame (Matrix.fromBlocks N 0 0 (-N)) (dblM C) :=
  ⟨dblM_gram N C h.1, dblM_rinv C h.2⟩

theorem framed_dbl (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (α β : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (P Q R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) :
    Framed τ JA JB a b A C → Framed τ JA (dbl JB) a b A (fun w => dblM (C w)) := by
  rintro ⟨hab, hA, hC⟩
  refine ⟨hab, hA, fun w => ?_⟩
  have key : b • (dbl JB).map (piInf (τ w)) =
      Matrix.fromBlocks (b • JB.map (piInf (τ w))) 0 0 (-(b • JB.map (piInf (τ w)))) := by
    simp [dbl, Matrix.fromBlocks_map, Matrix.fromBlocks_smul, Matrix.map_neg]
  rw [key]
  exact dblM_isFrame _ _ (hC w)

end GlobalTheory.RealLift.Dbl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialSpaceEqFockImageOfArchLawsStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws : GlobalTheory.RealLift.ActsLaws → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.PolRange := by
  first | exact @GlobalTheory.RealLift.PolRangePf.polRange_of | exact GlobalTheory.RealLift.PolRangePf.polRange_of | (intros; apply GlobalTheory.RealLift.PolRangePf.polRange_of <;> assumption)
end

