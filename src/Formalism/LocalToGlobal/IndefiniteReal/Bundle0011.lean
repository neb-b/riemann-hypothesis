module

public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
public import Formalism.LocalToGlobal.Columns.RowFormsAdelic
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.BridgeColPts
section
open NumberField

noncomputable section

namespace Formalism.IndefR.Bridge

open Formalism.L2

section ColPts

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Formalism.L2.DIV.Pl E))
  (H : Subgroup (Col.GLG (E := E) (n := n) (SG := SG)))

def colJ : Subgroup (Col.UAd hc n) := (Col.JH hc n ST SG H).map (Col.ToUnitaryAdelic hc n ST)

abbrev principalCongruenceSubgroup : Subgroup (Col.UAd hc n) := (Col.K1 hc n ST SG).subgroupOf (Col.UAd hc n)

theorem J0toU_injective : Function.Injective (Col.ToUnitaryAdelic hc n ST) := Subgroup.inclusion_injective _

def colJEquiv : Col.JH hc n ST SG H ≃* colJ hc n ST SG H :=
  (Col.JH hc n ST SG H).equivMapOfInjective _ (J0toU_injective hc n ST)

theorem colJEquiv_symm_coe (k : colJ hc n ST SG H) :
    Col.ToUnitaryAdelic hc n ST (((colJEquiv hc n ST SG H).symm k : Col.JH hc n ST SG H) : Col.J0 hc n ST) = (k : Col.UAd hc n) := by
  rw [← Subgroup.coe_equivMapOfInjective_apply (Col.JH hc n ST SG H) (Col.ToUnitaryAdelic hc n ST) (J0toU_injective hc n ST)]
  exact congrArg Subtype.val ((colJEquiv hc n ST SG H).apply_symm_apply k)

theorem mem_principal_congruence_iff (m : Col.J0 hc n ST) : Col.ToUnitaryAdelic hc n ST m ∈ principalCongruenceSubgroup hc n ST SG ↔ Col.redG hc n ST SG m = 1 := by
  constructor
  · intro h
    obtain ⟨m', hm', he⟩ := Subgroup.mem_subgroupOf.1 h
    have e : m' = m := Subtype.ext he
    rw [← e]
    exact MonoidHom.mem_ker.1 hm'
  · intro h
    exact Col.mem_principal_congruence_of hc n ST SG h

theorem principal_congruence_le_level_subgroup : principalCongruenceSubgroup hc n ST SG ≤ colJ hc n ST SG H := by
  intro a ha
  obtain ⟨m, hm, hma⟩ := Subgroup.mem_subgroupOf.1 ha
  refine Subgroup.mem_map.2 ⟨m, Subgroup.mem_comap.2 ?_, Subtype.ext hma⟩
  rw [MonoidHom.mem_ker.1 hm]
  exact H.one_mem

def colToAdG : Col.URat hc n × colJ hc n ST SG H →* Col.AdG hc n ST SG H :=
  show Col.URat hc n × colJ hc n ST SG H →* Col.URat hc n × (Col.JH hc n ST SG H ⧸ (Col.redH hc n ST SG H).ker) from
    MonoidHom.prodMap (MonoidHom.id _)
      ((QuotientGroup.mk' (Col.redH hc n ST SG H).ker).comp (colJEquiv hc n ST SG H).symm.toMonoidHom)

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : Col.GSD K}

variable {hc n ST SG H}

def colGl (o : Col.OnDeco n ST SG H S) : Col.URat hc n × colJ hc n ST SG H →* S.G :=
  o.eG.toMonoidHom.comp ((Col.adHom hc n ST SG H).comp (colToAdG hc n ST SG H))

def colQ (o : Col.OnDeco n ST SG H S) (x : Col.UAd hc n) : S.D :=
  o.eD (Col.decoPt hc n ST SG (QuotientGroup.mk x : Col.adPt hc n ST SG))

variable (o : Col.OnDeco n ST SG H S)

theorem colGl_apply (γ : Col.URat hc n) (k : colJ hc n ST SG H) :
    colGl o (γ, k) = o.eG (Col.ratHom hc n γ, Col.redH hc n ST SG H ((colJEquiv hc n ST SG H).symm k)) := rfl

theorem colGl_surj (hR : Col.RedHSurj hc n ST SG H) : Function.Surjective (colGl (hc := hc) o) := by
  intro g
  obtain ⟨⟨u, h⟩, rfl⟩ := o.eG.surjective g
  obtain ⟨γ, hγ⟩ := (Col.ratHom_bijective hc n).2 u
  obtain ⟨k, hk⟩ := hR h
  refine ⟨(γ, colJEquiv hc n ST SG H k), ?_⟩
  rw [colGl_apply, MulEquiv.symm_apply_apply, hγ, hk]

theorem colGl_ker (γ : Col.URat hc n) (k : colJ hc n ST SG H) :
    colGl o (γ, k) = 1 ↔ γ = 1 ∧ (k : Col.UAd hc n) ∈ principalCongruenceSubgroup hc n ST SG := by
  rw [colGl_apply, MulEquiv.map_eq_one_iff, Prod.mk_eq_one,
    (injective_iff_map_eq_one' _).1 (Col.ratHom_bijective hc n).1, ← colJEquiv_symm_coe, mem_principal_congruence_iff]
  exact and_congr Iff.rfl Subtype.ext_iff

theorem colQ_surj (hS : Col.DecoPtSurj hc n ST SG) : Function.Surjective (colQ (hc := hc) o) := by
  intro d
  obtain ⟨d', rfl⟩ := o.eD.surjective d
  obtain ⟨p, rfl⟩ := hS d'
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective p
  exact ⟨x, rfl⟩

theorem colQ_fib (x x' : Col.UAd hc n) :
    colQ o x = colQ o x' ↔ ∃ k1 ∈ principalCongruenceSubgroup hc n ST SG, x' = x * k1 := by
  unfold colQ
  rw [o.eD.injective.eq_iff, (Col.decoPt_injective' hc n ST SG).eq_iff, QuotientGroup.eq]
  constructor
  · intro h
    exact ⟨_, h, by rw [mul_inv_cancel_left]⟩
  · rintro ⟨k1, hk1, rfl⟩
    rwa [inv_mul_cancel_left]

theorem colQ_eqv (γ : Col.URat hc n) (k : colJ hc n ST SG H) (x : Col.UAd hc n) :
    colQ o (Col.ratIn hc n γ * x * (k : Col.UAd hc n)⁻¹) = colGl o (γ, k) • colQ o x := by
  have e1 : Col.ratIn hc n γ * x * (k : Col.UAd hc n)⁻¹ =
      Col.rawSm hc n ST γ (((colJEquiv hc n ST SG H).symm k : Col.JH hc n ST SG H) : Col.J0 hc n ST) x := by
    unfold Col.rawSm
    rw [colJEquiv_symm_coe]
  have e2 := Col.decorated_point_equivariant hc n ST SG H
    ((γ, (((colJEquiv hc n ST SG H).symm k : Col.JH hc n ST SG H) : Col.JH hc n ST SG H ⧸ (Col.redH hc n ST SG H).ker)) :
      Col.AdG hc n ST SG H) (QuotientGroup.mk x : Col.adPt hc n ST SG)
  unfold colQ
  rw [e1, Col.adSmul_mk] at *
  rw [e2, o.smul]
  rfl

def colAdPts (hS : Col.DecoPtSurj hc n ST SG) : AdPts S (Col.ratIn hc n) (colJ hc n ST SG H) where
  K1 := principalCongruenceSubgroup hc n ST SG
  principal_congruence_le := principal_congruence_le_level_subgroup hc n ST SG H
  q := colQ o
  gl := colGl o
  gl_surj := colGl_surj o (Col.redHSurj_of hc n ST SG H (Col.decorated_lattice_exists hc n ST SG) hS)
  gl_ker := colGl_ker o
  q_surj := colQ_surj o hS
  q_eqv := colQ_eqv o
  q_fib := colQ_fib o


def colClassPres (hS : Col.DecoPtSurj hc n ST SG) (h : S.Ok) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (σ : K →+* ℂ) (ρ : Col.URat hc n →* Module.End ℂ W) (χ : colJ hc n ST SG H →* ℂˣ)
    (coef : S.V →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => coef (S.bV i))
    (hspan : Submodule.span ℂ (Set.range fun i => coef (S.bV i)) = ⊤)
    (hpair : ∀ x x', inner ℂ (coef x) (coef x') = σ (S.pair x x'))
    (hK1 : ∀ k : colJ hc n ST SG H, (k : Col.UAd hc n) ∈ principalCongruenceSubgroup hc n ST SG → χ k = 1)
    (hgl : ∀ (γ : Col.URat hc n) (k : colJ hc n ST SG H) (v : S.V),
      coef (S.ρ (colGl o (γ, k)) v) = ((χ k)⁻¹ : ℂˣ) • ρ γ (coef v)) :
    ClassPres (Col.ratIn hc n) (S.toCSD h) σ ρ (colJ hc n ST SG H) χ :=
  classPresOf (colAdPts o hS) h σ ρ χ coef hli hspan hpair hK1 hgl

end ColPts

section Forms

variable {X : Col.Fields} (hc : Formalism.BasicNotions.CMData X.F X.E) {n : ℕ} [NeZero n]
  {ST SG : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 X.E))}

end Forms

end Formalism.IndefR.Bridge
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.IsWeilDatum
section
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Formalism.IndefR.Heis

section Law

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

@[ext] structure HeisG (B : M →ₗ[R] M →ₗ[R] R) where

  w : M

  t : R

namespace HeisG

variable {B : M →ₗ[R] M →ₗ[R] R} [Invertible (2 : R)]

end HeisG

end Law

section Rat

variable {E : Type*} [Field E] [NumberField E] (c : E →+* E)

structure HermSp where

  n : ℕ

  J : Matrix (Fin n) (Fin n) E
  herm : J.transpose = J.map c
  nondeg : J.det ≠ 0

variable {c}

def hf (V : HermSp c) (v u : Fin V.n → E) : E := ∑ i, ∑ j, v i * V.J i j * c (u j)

end Rat

section Ad

variable {𝔸 WA : Type*} [CommRing 𝔸] [AddCommGroup WA] [Module 𝔸 WA]

variable [Invertible (2 : 𝔸)] (ψ : AddChar 𝔸 ℂ) (B : WA →ₗ[𝔸] WA →ₗ[𝔸] 𝔸)

end Ad

section D7

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def Hth (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) : Submodule ℂ (WA V W → ℂ) where
  carrier := {f | IsThetaFun ψ V W f}
  zero_mem' := by
    refine ⟨fun γ w => by simp, ⟨⊤, isOpen_univ, fun u _ _ => ?_⟩, continuous_const, fun k L _ _ w => contDiff_const⟩
    funext w; simp [Heisenberg₂]
  add_mem' := by
    intro f g hf hg
    obtain ⟨U, hU, hUf⟩ := hf.level
    obtain ⟨U', hU', hUg⟩ := hg.level
    refine ⟨fun γ w => ?_, ⟨U ⊓ U', ?_, fun u hu h0 => ?_⟩, hf.cont.add hg.cont, fun k L hL hL0 w => ?_⟩
    · simp only [Pi.add_apply, hf.quasi γ w, hg.quasi γ w, mul_add]
    · rw [AddSubgroup.coe_inf]; exact hU.inter hU'
    · funext w
      have e1 := congrFun (hUf u hu.1 h0) w
      have e2 := congrFun (hUg u hu.2 h0) w
      simp only [Heisenberg₂, Pi.add_apply] at e1 e2 ⊢
      rw [mul_add, e1, e2]
    · exact (hf.smooth k L hL hL0 w).add (hg.smooth k L hL hL0 w)
  smul_mem' := by
    intro a f hf
    obtain ⟨U, hU, hUf⟩ := hf.level
    refine ⟨fun γ w => ?_, ⟨U, hU, fun u hu h0 => ?_⟩, continuous_const.mul hf.cont, fun k L hL hL0 w => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, hf.quasi γ w]; ring
    · funext w
      have e1 := congrFun (hUf u hu h0) w
      simp only [Heisenberg₂, Pi.smul_apply, smul_eq_mul] at e1 ⊢
      rw [mul_left_comm, e1]
    · exact contDiff_const.mul (hf.smooth k L hL hL0 w)

def FinCovol (V W : HSp D) : Prop :=
  (∃ (μ : Measure (WA V W)) (𝓕 : Set (WA V W)), μ.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratL V W) 𝓕 μ) ∧
    ∀ (μ : Measure (WA V W)) (𝓕 : Set (WA V W)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL V W) 𝓕 μ → μ 𝓕 < ⊤

end D7

end Formalism.IndefR.Heis

end
end

