module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOfPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautBaseChangeTripleLiftLeft
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentials
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2151
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2223
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SplitsAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2158
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFromBase
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc.Sep
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg.TautFrom

open GlobalTheory.PolDeg.TautEx

section Chart

variable {Y Y' : Scheme.{0}}

theorem chartPull_le {A' B' : LB Y'} {A B : LB Y} {h : Y' ⟶ Y} (a : ChartPull A' A h) (b : ChartPull B' B h)
    (p : B'.ι × A'.ι) : B'.U p.1 ⊓ A'.U p.2 ≤ h ⁻¹ᵁ (B.U (b.idx p.1) ⊓ A.U (a.idx p.2)) :=
  fun _ hy => ⟨b.le _ hy.1, a.le _ hy.2⟩

def isoPull {A' B' : LB Y'} {A B : LB Y} {h : Y' ⟶ Y} (a : ChartPull A' A h) (b : ChartPull B' B h)
    (w : LB.Iso A B) : LB.Iso A' B' :=
  ⟨fun p => res (chartPull_le a b p) (pullU h _ (w.s (b.idx p.1, a.idx p.2)))⟩

theorem gm_isoPull {A' B' : LB Y'} {A B : LB Y} {h : Y' ⟶ Y} (a : ChartPull A' A h) (b : ChartPull B' B h)
    (w : LB.Iso A B) {Z : Scheme.{0}} (r : Z ⟶ Y') (z : Z) (p : B'.ι × A'.ι) (hz : r z ∈ B'.U p.1 ⊓ A'.U p.2) :
    gm r z (B'.U p.1 ⊓ A'.U p.2) ((isoPull a b w).s p) =
      gm (r ≫ h) z (B.U (b.idx p.1) ⊓ A.U (a.idx p.2)) (w.s (b.idx p.1, a.idx p.2)) :=
  (gm_res r z (chartPull_le a b p) hz _).trans (gm_pull r h z _ (chartPull_le a b p hz) _)

theorem isoPull_isGen {A' B' : LB Y'} {A B : LB Y} {h : Y' ⟶ Y} (a : ChartPull A' A h) (b : ChartPull B' B h)
    (w : LB.Iso A B) (hw : w.IsGen) : (isoPull a b w).IsGen := by
  intro p q
  refine unit_ext fun y hy => ?_
  have val : ∀ p : B'.ι × A'.ι, y ∈ B'.U p.1 ⊓ A'.U p.2 →
      gm (𝟙 Y') y _ ((isoPull a b w).s p) =
        gm h y (B.U (b.idx p.1) ⊓ A.U (a.idx p.2)) (w.s (b.idx p.1, a.idx p.2)) := fun p hp =>
    (gm_isoPull a b w (𝟙 Y') y p hp).trans (by rw [Category.id_comp])
  have hm : h y ∈ B.U (b.idx p.1) ⊓ A.U (a.idx p.2) ⊓ (B.U (b.idx q.1) ⊓ A.U (a.idx q.2)) :=
    ⟨chartPull_le a b p hy.1, chartPull_le a b q hy.2⟩
  have e := congrArg (gm h y (B.U (b.idx p.1) ⊓ A.U (a.idx p.2) ⊓ (B.U (b.idx q.1) ⊓ A.U (a.idx q.2))))
    (hw (b.idx p.1, a.idx p.2) (b.idx q.1, a.idx q.2))
  have e' := (gm_res h y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div A B h y (b.idx p.1, a.idx p.2) (b.idx q.1, a.idx q.2) hm) (gm_res h y _ hm _))))
  refine ((gm_res (𝟙 Y') y _ hy _).trans (val p hy.1)).trans (e'.trans (Eq.symm ?_))
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_div A' B' (𝟙 Y') y p q hy).trans ?_)
    ((gm_res (𝟙 Y') y _ hy _).trans (val q hy.2)))
  rw [a.g y _ _ hy.1.2 hy.2.2, b.g y _ _ hy.1.1 hy.2.1]

end Chart

end GlobalTheory.PolDeg.TautFrom

namespace GlobalTheory.PolDeg.TautFrom

open GlobalTheory.PolDeg.TautEx GlobalTheory.PrimCocycle

section Base

variable {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (N : ℕ)

end Base

end GlobalTheory.PolDeg.TautFrom

namespace GlobalTheory.PolDeg.TautFrom

open GlobalTheory.PolDeg.TautEx GlobalTheory.PrimCocycle

section Iso

variable {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (N : ℕ)

end Iso

end GlobalTheory.PolDeg.TautFrom

namespace GlobalTheory.PolDeg.TautFrom

open GlobalTheory.PolDeg.TautEx GlobalTheory.PrimCocycle

section Val

variable {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (N : ℕ)

end Val

end GlobalTheory.PolDeg.TautFrom

namespace GlobalTheory.PolDeg.TautFrom

open GlobalTheory.PolDeg.TautEx GlobalTheory.PrimCocycle

section Main

variable {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (N : ℕ)

end Main

end GlobalTheory.PolDeg.TautFrom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctorialLiftsOfObstructionTwoZero
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.Obs

theorem exists_isFun_of_isOb2_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Par s₀ → Module.Projective R₀ (GlobForm s₀) → ∀ L : Pre I π (OAff s₀), (∀ w, L.IsOb2 α w 0) → ∃ L' : Pre I π (OAff s₀), L'.IsFun := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ hpar hproj L hob

  obtain ⟨θ, -, -, hθ, -⟩ := hob 0

  let Wm : Submodule R (∀ (T T' : AffOp X₀) (_ : T ⟶ T'), L.B T') :=
    { carrier := {g | ∀ T T' a, g T T' a ∈ I.map (algebraMap R (L.B T'))}
      add_mem' := fun hx hy T T' a ↦ Ideal.add_mem _ (hx T T' a) (hy T T' a)
      zero_mem' := fun T T' a ↦ Ideal.zero_mem _
      smul_mem' := fun r g hg T T' a ↦ by
        show r • g T T' a ∈ _
        rw [Algebra.smul_def]; exact Ideal.mul_mem_left _ _ (hg T T' a) }
  let q : (∀ (T T' : AffOp X₀) (_ : T ⟶ T'), L.B T') →ₗ[R]
      (∀ (T T' T'' : AffOp X₀) (_ : T ⟶ T') (_ : T' ⟶ T''), L.B T'') :=
    { toFun := fun g T T' T'' a b ↦ L.ρ b (g T T' a) - g T T'' (a ≫ b) + g T' T'' b
      map_add' := fun g g' ↦ by
        funext T T' T'' a b
        simp only [Pi.add_apply, map_add (f := _)]; abel
      map_smul' := fun r g ↦ by
        funext T T' T'' a b
        simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_sub, smul_add] }
  let v : GlobForm s₀ →+ (∀ (T T' T'' : AffOp X₀) (_ : T ⟶ T') (_ : T' ⟶ T''), L.B T'') :=
    { toFun := fun w T T' T'' a b ↦ θ T T' T'' a b (w.1 T)
      map_zero' := by funext T T' T'' a b; simp
      map_add' := fun w w' ↦ by funext T T' T'' a b; simp }
  have hv : ∀ (r : R) (w : GlobForm s₀), v (π r • w) = r • v w := by
    intro r w
    funext T T' T'' a b
    show θ T T' T'' a b (π r • w.1 T) = r • θ T T' T'' a b (w.1 T)
    have e : π r • w.1 T = L.p T (algebraMap R (L.B T) r) • w.1 T := by
      rw [SemiHom.map_algebraMap (L.semi T), algebraMap_smul]
    rw [e, (hθ T T' T'' a b).smul, AlgHom.commutes, ← Algebra.smul_def]
  have hW : ∀ (r : R), π r = 0 → ∀ m ∈ Wm, r • m = 0 := by
    intro r hr m hm
    have hrI : r ∈ I := hk ▸ RingHom.mem_ker.2 hr
    funext T T' a
    show r • m T T' a = 0
    rw [Algebra.smul_def]
    exact mul_eq_zero_of_mem_map hI (Ideal.mem_map_of_mem _ hrI) (hm T T' a)
  have hex : ∀ w : GlobForm s₀, ∃ m ∈ Wm, q m = v w := by
    intro w
    obtain ⟨g, hg, hgθ⟩ := _root_.GlobalTheory.ObsCob.exists_cob R R₀ I hI π hπ hk R₁ α _ (OAff s₀) L w θ hθ (hob w)
    refine ⟨g, hg, ?_⟩
    funext T T' T'' a b
    exact (hgθ T T' T'' a b).symm
  obtain ⟨u, hus, huW, huq⟩ := exists_semilinear_lift_of_projective R R₀ π hπ (GlobForm s₀) hproj _ _ Wm hW q v hv hex

  have hext : ∀ (T T' : AffOp X₀) (a : T ⟶ T'), ∃! ξ : Ω[Sec s₀ T.unop.1⁄R₀] →+ L.B T',
      (∀ b w, ξ (L.p T b • w) = L.ρ a b * ξ w) ∧ (∀ w, ξ w ∈ I.map (algebraMap R (L.B T'))) ∧
        ∀ w : GlobForm s₀, ξ (w.1 T) = u w T T' a := fun T T' a ↦
    exists_unique_formExt R R₀ I hI π hπ hk X₀ s₀ hpar T _ _ (L.p T) (L.semi T) (L.surj T) (L.ker T) (L.ρ a)
      ((Pi.evalAddMonoidHom (fun _ ↦ L.B T') a).comp ((Pi.evalAddMonoidHom _ T').comp ((Pi.evalAddMonoidHom _ T).comp u)))
      (fun r w ↦ by
        show u (π r • w) T T' a = r • u w T T' a
        rw [hus]; rfl) (fun w ↦ huW w T T' a)
  choose ξ hξ huniq using hext
  have hβ : ∀ (T T' : AffOp X₀) (a : T ⟶ T'), ∃ β : L.B T →ₐ[R] L.B T', IsTheta I (L.p T) (L.ρ a) β (ξ T T' a) :=
    fun T T' a ↦ (theta_classify R R₀ _ _ _ I hI π hπ (L.p T) (L.semi T) (L.surj T) (L.ker T) (L.ρ a)).2
      (ξ T T' a) (hξ T T' a).1 (hξ T T' a).2.1
  choose ρ' hρ' using hβ
  have hρ'e : ∀ (T T' : AffOp X₀) (a : T ⟶ T') x, ρ' T T' a x = L.ρ a x - ξ T T' a (D R₀ _ (L.p T x)) := by
    intro T T' a x
    rw [(hρ' T T' a).der]; abel
  have hp0 : ∀ (T T' : AffOp X₀) (a : T ⟶ T') y, L.p T' (ξ T T' a y) = 0 :=
    fun T T' a y ↦ (L.ker T' _).2 ((hξ T T' a).2.1 y)
  have hnat : ∀ (T T' : AffOp X₀) (a : T ⟶ T') x, L.p T' (ρ' T T' a x) = mp (OAff s₀) a (L.p T x) := by
    intro T T' a x
    rw [hρ'e, map_sub, hp0, sub_zero, L.nat]
  let L' : Pre I π (OAff s₀) :=
    { B := L.B, p := L.p, semi := L.semi, surj := L.surj, ker := L.ker, smooth := L.smooth
      ρ := fun {T T'} a ↦ ρ' T T' a
      nat := fun {T T'} a x ↦ hnat T T' a x }
  refine ⟨L', ?_⟩

  have hcomp : ∀ (T T' T'' : AffOp X₀) (a : T ⟶ T') (b : T' ⟶ T'') (y : Ω[Sec s₀ T.unop.1⁄R₀]),
      ξ T T'' (a ≫ b) y = L.ρ b (ξ T T' a y) + ξ T' T'' b (p1 (OAff s₀) a y) - θ T T' T'' a b y := by
    intro T T' T'' a b
    let ψ : Ω[Sec s₀ T.unop.1⁄R₀] →+ L.B T'' :=
      AddMonoidHom.mk' (fun y ↦ L.ρ b (ξ T T' a y) + ξ T' T'' b (p1 (OAff s₀) a y) - θ T T' T'' a b y)
        (fun y z ↦ by simp only [map_add (f := _)]; abel)
    have hψm : ∀ y, ψ y ∈ I.map (algebraMap R (L.B T'')) := fun y ↦
      Ideal.sub_mem _ (Ideal.add_mem _ (algHom_mem_map I (L.ρ b) ((hξ T T' a).2.1 y)) ((hξ T' T'' b).2.1 _))
        ((hθ T T' T'' a b).mem y)
    have e : ψ = ξ T T'' (a ≫ b) := by
      refine huniq T T'' (a ≫ b) ψ ⟨fun c y ↦ ?_, hψm, fun w ↦ ?_⟩
      · have h1 : ψ (L.p T c • y) = L.ρ b (L.ρ a c) * ψ y := by
          show L.ρ b (ξ T T' a (L.p T c • y)) + ξ T' T'' b (p1 (OAff s₀) a (L.p T c • y)) -
              θ T T' T'' a b (L.p T c • y) = L.ρ b (L.ρ a c) * (L.ρ b (ξ T T' a y) + ξ T' T'' b (p1 (OAff s₀) a y) - θ T T' T'' a b y)
          rw [(hξ T T' a).1, oneFormsMapOfFunctorMorphism_smul, ← L.nat, (hξ T' T'' b).1, (hθ T T' T'' a b).smul, map_mul]
          simp only [AlgHom.comp_apply]; ring
        have h2 : L.ρ b (L.ρ a c) = L.ρ (a ≫ b) c + θ T T' T'' a b (D R₀ _ (L.p T c)) := by
          rw [(hθ T T' T'' a b).der]; simp
        rw [h1, h2, add_mul, mul_eq_zero_of_mem_map hI ((hθ T T' T'' a b).mem _) (hψm y), add_zero]
      · show L.ρ b (ξ T T' a (w.1 T)) + ξ T' T'' b (p1 (OAff s₀) a (w.1 T)) - θ T T' T'' a b (w.1 T) = u w T T'' (a ≫ b)
        rw [← w.2 a, (hξ T T' a).2.2, (hξ T' T'' b).2.2]
        have := congrFun (congrFun (congrFun (congrFun (congrFun (huq w) T) T') T'') a) b
        change L.ρ b (u w T T' a) - u w T T'' (a ≫ b) + u w T' T'' b = θ T T' T'' a b (w.1 T) at this
        rw [← this]; abel
    intro y
    rw [← e]; rfl
  intro T T' T'' a b x
  change ρ' T T'' (a ≫ b) x = ρ' T' T'' b (ρ' T T' a x)
  have hD : D R₀ _ (L.p T' (ρ' T T' a x)) = p1 (OAff s₀) a (D R₀ _ (L.p T x)) := by
    rw [hnat, p1_D]
  rw [hρ'e T' T'' b, hD, hρ'e T T' a, map_sub, hρ'e, hcomp]
  have h2 : L.ρ b (L.ρ a x) = L.ρ (a ≫ b) x + θ T T' T'' a b (D R₀ _ (L.p T x)) := by
    rw [(hθ T T' T'' a b).der]; simp
  rw [h2]; abel

end GlobalTheory.Obs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisClosureLocalDomainExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.GalClosure

theorem exists_galois_embedding (R R' : Type) [CommRing R] [IsDomain R] [CharZero R] [CommRing R'] [IsDomain R']
    [Algebra R R'] [Module.Finite R R'] (hinj : Function.Injective (algebraMap R R')) :
    ∃ L : IntermediateField (FractionRing R) (AlgebraicClosure (FractionRing R)),
      FiniteDimensional (FractionRing R) L ∧ IsGalois (FractionRing R) L ∧
      ∃ j : R' →ₐ[R] L, Function.Injective j := by
  first
  | exact @_root_.GlobalTheory.GaloisEmbeddingExistence.exists_galois_embedding
  | exact _root_.GlobalTheory.GaloisEmbeddingExistence.exists_galois_embedding
  | (apply _root_.GlobalTheory.GaloisEmbeddingExistence.exists_galois_embedding <;> assumption)
  | (intros; apply _root_.GlobalTheory.GaloisEmbeddingExistence.exists_galois_embedding <;> assumption)
  | (intros; apply @_root_.GlobalTheory.GaloisEmbeddingExistence.exists_galois_embedding <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.GaloisEmbeddingExistence.exists_galois_embedding ..)

end GlobalTheory.GalClosure

namespace GlobalTheory.GalClosure

theorem isGal_integralClosure_of_tower (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (L : Type) [Field L]
    [Algebra (FractionRing R) L] [FiniteDimensional (FractionRing R) L] [IsGalois (FractionRing R) L] [Algebra R L]
    [IsScalarTower R (FractionRing R) L] :
    IsGal (algebraMap R (integralClosure R L)) := by
  set K := FractionRing R
  set B := integralClosure R L
  haveI : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension K L
  have hRL : ∀ r : R, algebraMap B L (algebraMap R B r) = algebraMap K L (algebraMap R K r) := fun r => by
    rw [← IsScalarTower.algebraMap_apply R K L]; rfl
  have hfix : ∀ τ : Gal (algebraMap R B), ∀ k : K,
      IsFractionRing.ringEquivOfRingEquiv (K := L) (L := L) τ.1 (algebraMap K L k) = algebraMap K L k := by
    intro τ k
    have h := IsLocalization.ringHom_ext (M := nonZeroDivisors R) (S := K)
      (j := (IsFractionRing.ringEquivOfRingEquiv (K := L) (L := L) τ.1).toRingHom.comp (algebraMap K L))
      (k := algebraMap K L) (by
        ext r
        simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
        rw [← hRL, IsFractionRing.ringEquivOfRingEquiv_algebraMap, τ.2 r])
    exact congrArg (fun f => f k) h
  let toAut : Gal (algebraMap R B) → (L ≃ₐ[K] L) := fun τ => AlgEquiv.ofRingEquiv (hfix τ)
  have htoAut : ∀ τ b, toAut τ (algebraMap B L b) = algebraMap B L (τ.1 b) := fun τ b =>
    IsFractionRing.ringEquivOfRingEquiv_algebraMap _ b
  refine ⟨Finite.of_injective toAut fun τ τ' h => Subtype.ext (RingEquiv.ext fun b => ?_), fun x hx => ?_⟩
  · apply IsFractionRing.injective B L
    rw [← htoAut, ← htoAut, h]
  · have hg : ∀ g : L ≃ₐ[K] L, g (x : L) = x := by
      intro g
      let gR : L →ₐ[R] L := (g : L →ₐ[K] L).restrictScalars R
      let gR' : L →ₐ[R] L := (g.symm : L →ₐ[K] L).restrictScalars R
      let τ : B ≃+* B :=
        { toFun := fun b => ⟨g b, (mem_integralClosure_iff R L).2 ((b.2 : IsIntegral R (b : L)).map gR)⟩
          invFun := fun b => ⟨g.symm b, (mem_integralClosure_iff R L).2 ((b.2 : IsIntegral R (b : L)).map gR')⟩
          left_inv := fun b => Subtype.ext (g.symm_apply_apply (b : L))
          right_inv := fun b => Subtype.ext (g.apply_symm_apply (b : L))
          map_mul' := fun a b => Subtype.ext (map_mul g (a : L) b)
          map_add' := fun a b => Subtype.ext (map_add g (a : L) b) }
      have hτ : τ ∈ Gal (algebraMap R B) := fun r => Subtype.ext (by
        show g ((algebraMap R B r : B) : L) = ((algebraMap R B r : B) : L)
        have e : ((algebraMap R B r : B) : L) = algebraMap K L (algebraMap R K r) := hRL r
        rw [e, AlgEquiv.commutes])
      exact congrArg Subtype.val (hx τ hτ)
    obtain ⟨k, hk⟩ := IntermediateField.mem_bot.1 ((IsGalois.mem_bot_iff_fixed (F := K) (x : L)).2 hg)
    have hint : IsIntegral R k := by
      have h1 : IsIntegral R (algebraMap K L k) := hk ▸ (x.2 : IsIntegral R (x : L))
      exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom R K L) (algebraMap K L).injective).1 h1
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    refine ⟨r, Subtype.ext ?_⟩
    have := hRL r
    rw [hr, hk] at this
    exact this

end GlobalTheory.GalClosure

namespace GlobalTheory.GalClosure

theorem exists_galois_finExt_isLocalHom : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R']
    [IsLocalRing R'] (ρ : R →+* R'), Base R → FinExt ρ → ∃ (R'' : Type) (_ : CommRing R'') (_ : IsDomain R'')
    (_ : IsLocalRing R'') (σ : R' →+* R''), FinExt σ ∧ IsLocalHom σ ∧ FinExt (σ.comp ρ) ∧ IsGal (σ.comp ρ) := by
  intro R R' _ _ _ _ _ _ ρ hR hρ
  obtain ⟨⟨hRn, -, hRic, hRc⟩, hR0⟩ := hR
  obtain ⟨-, hinj, hfin⟩ := hρ
  letI : Algebra R R' := ρ.toAlgebra
  haveI : Module.Finite R R' := hfin
  obtain ⟨L, hLf, hLg, j, hj⟩ := exists_galois_embedding R R' hinj
  set B := integralClosure R L
  obtain ⟨hBfin, hBloc, hBn, hBic, -⟩ := GlobalTheory.integralClosure_finite_local_of_isAdicComplete R hRc L
  have hmem : ∀ x : R', j x ∈ B := fun x => (Algebra.IsIntegral.isIntegral (R := R) x).map j
  let jB : R' →ₐ[R] B := j.codRestrict B hmem
  let σ : R' →+* B := jB.toRingHom
  have hcomp : σ.comp ρ = algebraMap R B := RingHom.ext fun r => jB.commutes r
  have hadm : AdmBase B (maximalIdeal B) :=
    ⟨hBn, inferInstance, hBic, GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local R B⟩
  have hσinj : Function.Injective σ := fun a b h => hj (congrArg (fun y : B => (y : L)) h)
  have hcfin : (σ.comp ρ).Finite := hcomp ▸ RingHom.finite_algebraMap.2 hBfin
  have hσfin : σ.Finite := RingHom.Finite.of_comp_finite hcfin
  refine ⟨B, inferInstance, inferInstance, hBloc, σ, ⟨hadm, hσinj, hσfin⟩,
    RingHom.IsIntegral.isLocalHom hσfin.to_isIntegral hσinj, ⟨hadm, hσinj.comp hinj, hcfin⟩, ?_⟩
  rw [hcomp]
  exact isGal_integralClosure_of_tower R L

end GlobalTheory.GalClosure
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisQuotientInvariantOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_quotient_of_invariant_open {Γ : Type} [Group Γ] [Finite Γ] {Y S : Scheme.{0}} (act : Γ → (Y ⟶ Y))
    (h1 : act 1 = 𝟙 _) (hm : ∀ σ τ, act (σ * τ) = act σ ≫ act τ) (s : Y ⟶ S) (hs : ∀ σ, act σ ≫ s = s)
    (H : Y.Opens) (hH : ∀ σ, act σ ⁻¹ᵁ H = H)
    (hO : ∀ x ∈ H, ∃ O : Y.Opens, IsAffineOpen O ∧ O ≤ H ∧ ∀ σ, act σ x ∈ O) :
    ∃ (X : Over S) (π : H.toScheme ⟶ X.left), π ≫ X.hom = H.ι ≫ s ∧ IsAffineHom π ∧ Surjective π ∧
      (∀ σ, (act σ).resLE H H (hH σ).ge ≫ π = π) ∧
      (∀ x y : H.toScheme, π x = π y → ∃ σ, act σ (H.ι x) = H.ι y) ∧
      ∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V),
        (∀ σ (h : π ⁻¹ᵁ V ≤ ((act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)),
          (((act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom := by
  let r : Γ → (H.toScheme ⟶ H.toScheme) := fun σ => (act σ).resLE H H (hH σ).ge
  have hr : ∀ σ, r σ ≫ H.ι = H.ι ≫ act σ := fun σ => Scheme.Hom.resLE_comp_ι _ _
  have r1 : r 1 = 𝟙 _ := by
    rw [← cancel_mono H.ι, hr, h1, Category.id_comp, Category.comp_id]
  have rm : ∀ σ τ, r (σ * τ) = r σ ≫ r τ := fun σ τ => by
    rw [← cancel_mono H.ι, hr, hm, Category.assoc, hr, reassoc_of% hr]
  let ρ : Γ →* Aut H.toScheme := MonoidHom.mk'
    (fun σ => ⟨r σ⁻¹, r σ, by rw [← rm, inv_mul_cancel, r1], by rw [← rm, mul_inv_cancel, r1]⟩)
    (fun σ τ => Aut.ext (Iso.ext (show r (σ * τ)⁻¹ = r τ⁻¹ ≫ r σ⁻¹ by rw [mul_inv_rev, rm])))
  have hρ : ∀ σ, (ρ σ).asIso.hom = r σ⁻¹ := fun _ => rfl
  have hρ' : ∀ σ, r σ = (ρ σ⁻¹).asIso.hom := fun σ => by rw [hρ, inv_inv]
  have hpt : ∀ σ (x : H.toScheme), H.ι (r σ x) = act σ (H.ι x) := fun σ x => congr($(hr σ) x)
  have : OrbitsInAffineOpens ρ := ⟨fun x => by
    obtain ⟨O, hO₁, hO₂, hO₃⟩ := hO (H.ι x) x.2
    refine ⟨H.ι ⁻¹ᵁ O, hO₁.preimage_of_isOpenImmersion H.ι (by rwa [Scheme.Opens.opensRange_ι]), fun g => ?_⟩
    change H.ι (r g⁻¹ x) ∈ O
    rw [hpt]
    exact hO₃ _⟩
  obtain ⟨X', π, hπ⟩ := QuotientGluing.exists_isAffineQuotient ρ
  have hinv : ∀ g, (ρ g).asIso.hom ≫ H.ι ≫ s = H.ι ≫ s := fun g => by
    rw [hρ, reassoc_of% hr, hs]
  refine ⟨Over.mk (hπ.desc (H.ι ≫ s) hinv), π, hπ.comp_desc _ hinv, hπ.isAffineHom, hπ.surjective, fun σ => ?_,
    fun x y hxy => ?_, fun V => ⟨hπ.app_injective V, fun f hf => ?_⟩⟩
  · exact (congrArg (· ≫ π) (hρ' σ)).trans (hπ.comp_eq _)
  · obtain ⟨g, rfl⟩ := (hπ.apply_eq_iff x y).mp hxy
    exact ⟨g⁻¹, (hpt _ _).symm⟩
  · exact hπ.mem_range_app V f fun g => ⟨hπ.preimage_le V g, hf g⁻¹ _⟩

theorem exists_galois_quotient : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∀ (H : G'.left.Opens) (hH : ∀ σ, a.act σ ⁻¹ᵁ H = H), (∀ x ∈ H, ∃ O : G'.left.Opens, IsAffineOpen O ∧ O ≤ H ∧ ∀ σ, a.act σ x ∈ O) → ∃ (X : Over (Sp R)) (π : H.toScheme ⟶ X.left), π ≫ X.hom = H.ι ≫ G'.hom ≫ spMap ρ ∧ IsAffineHom π ∧ Surjective π ∧ (∀ σ, (a.act σ).resLE H H (hH σ).ge ≫ π = π) ∧ (∀ x y : H.toScheme, π x = π y → ∃ σ, a.act σ (H.ι x) = H.ι y) ∧ ∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V), (∀ σ (h : π ⁻¹ᵁ V ≤ ((a.act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)), (((a.act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom := by
  intro R _ _ _ _ R' _ _ _ ρ _ hG D D' hD A' G' _ _ _ U' a H hH hO
  have := hG.1
  refine exists_quotient_of_invariant_open a.act a.act_one a.act_mul (G'.hom ≫ spMap ρ) (fun σ => ?_) H hH hO
  have e : spMap (Gal.hom σ) ≫ spMap ρ = spMap ρ := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact σ.2 x
  rw [← Category.assoc, (a.cart σ).1.w, Category.assoc, e]

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericOfFormal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.GenericEnd

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem eq_of_generic (U : UnifPre I D A G) {g g' : G ⟶ G}
    (h : (Over.pullback (jK R)).map g = (Over.pullback (jK R)).map g') : g = g' := by
  have := U.smooth
  have := U.separated
  have : IsSchemeTheoreticallyDominant (jK R) :=
    schDom_spec_map _ (IsFractionRing.injective R (FractionRing R))
  have : QuasiCompact (jK R) :=
    inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))
  have : IsSchemeTheoreticallyDominant (pullback.fst G.hom (jK R)) :=
    .of_isPullback (IsPullback.of_hasPullback G.hom (jK R)).flip
  ext1
  refine ext_of_schDom G.hom (by rw [Over.w g, Over.w g']) (pullback.fst G.hom (jK R)) ?_
  have e := congrArg (fun k => k.left ≫ pullback.fst G.hom (jK R)) h
  simp only [Over.pullback_map_left, pullback.lift_fst] at e
  exact e

theorem exists_generic_of_formal (U : UnifPre I D A G) (a : D.toPre.P.A ⟶ D.toPre.P.A) (h' : D.toPre.X →+ D.toPre.X)
    (b : ∀ e : ℕ, thickObj R I e G ⟶ thickObj R I e G) (hb : FormalEnd U a h' b) (g : G ⟶ G) (hg : IsMonHom g)
    (hgb : ∀ e, (Over.pullback (thick R I e)).map g = b e) :
    ∃ f : A.A ⟶ A.A, IsMonHom f ∧ ∀ g' : G ⟶ G, IsMonHom g' →
      (Over.pullback (jK R)).map g' ≫ U.gen.hom = U.gen.hom ≫ f → ActsAs U a h' g' := by
  have := U.gen_hom
  refine ⟨U.gen.inv ≫ (Over.pullback (jK R)).map g ≫ U.gen.hom, inferInstance, fun g' _ hg' => ?_⟩
  obtain rfl : g' = g := eq_of_generic U (by
    rw [← cancel_mono U.gen.hom, hg', Iso.hom_inv_id_assoc])
  intro e
  obtain ⟨t, ht, hi⟩ := hb.2.2.2 e
  exact ⟨by rw [hgb]; exact hb.2.2.1 e, t, ht, by rw [hgb]; exact hi⟩

end GlobalTheory.Mum.GenericEnd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectOverLieTateLocusStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_harrisTaylorObject_over_lieTate_locus : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∀ (X : Scheme.{0}) (πX : X ⟶ S) (AX : Over X) [GrpObj AX] [IsCommMonObj AX] (φX : AX.left ⟶ c.A.left) (φ₂X : (G2 AX).left ⟶ (G2 c.A).left) (actX : OActN D.O AX) (ηX : D.La → (𝟙_ (Over X) ⟶ AX)), IsGrpPullback AX c.A πX φX → IsSquare φX φ₂X → RosatiFor D actX (c.P.pull φ₂X) → EtaOK D N actX ηX → ∀ (Z : Scheme.{0}) (j : Z ⟶ X), (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Z), x ≫ j ≫ πX ≫ t = spMap β → LieHer b actX β (x ≫ j)) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Z) (β : R →+* k), x ≫ j ≫ πX ≫ t = spMap β → GeomAt D N actX (c.P.pull φ₂X) ηX k (x ≫ j)) → ∃ (u : Obj b N ((j ≫ πX) ≫ t)) (ψ : u.A.left ⟶ AX.left) (ψ₂ : (G2 u.A).left ⟶ (G2 c.A).left), IsGrpPullback u.A AX j ψ ∧ IsSquare (ψ ≫ φX) ψ₂ ∧ LBIso u.P (c.P.pull ψ₂) ∧ (∀ a : D.O, (u.act.act a).left ≫ ψ = ψ ≫ (actX.act a).left) ∧ ∀ y, (u.eta y).left ≫ ψ = j ≫ (ηX y).left := by
  first | (exact @GlobalTheory.HTMkObj.exists_obj_of_locus) | (exact GlobalTheory.HTMkObj.exists_obj_of_locus) | (intros; apply GlobalTheory.HTMkObj.exists_obj_of_locus <;> assumption)
end

