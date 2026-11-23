module

public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0002
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0004
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0006
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0081

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousPsiT
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct ContDiff ENNReal

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D} {k : ℕ}

theorem continuous_psiT (τ : D.what₂.Tau) : Continuous (psiT D τ) := by
  have heq : (psiT D τ : AE D → ℂ) = fun x => gW D (plW D τ) (fstA D.host.F ((basAF D).repr x 0)) +
      gW D (plW D τ) (fstA D.host.F ((basAF D).repr x 1)) * betaT D τ := by
    funext x
    simp only [psiT, RingHom.coe_comp, Function.comp_apply]
    rw [thetaC_decomp, repr_infPart, repr_infPart]
  rw [heq]
  have hc : ∀ k : Fin 2, Continuous fun x : AE D => (basAF D).repr x k := fun k => by
    have := (continuous_apply k).comp (G5.tensCoordH (basE D) (AF D.host.F)).continuous
    convert this using 1
    rfl
  have hf : Continuous (fstA D.host.F) := continuous_fst
  exact ((continuous_gW (D := D) _).comp (hf.comp (hc 0))).add
    (((continuous_gW (D := D) _).comp (hf.comp (hc 1))).mul continuous_const)

end Formalism.IndefR.Eqv

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GEqMain
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Eqv.Act

open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Links.RealDat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem flag_character_eq_principal (t : T) (k : GA D (Yc D 0)) :
    levChi (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) k = levChi (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv)) k := by
  unfold levChi
  congr 1
  have e1 : levFn (R.βY 0) (R.datYt t 0 R.triv) (finE (Yc D 0) k) =
      levFn (R.βY 0) (withP (R.datYt t 0 R.triv) (LevelP.triv (R.datYt t 0 R.triv).Pg (R.datYt t 0 R.triv).r ℂ))
        (finE (Yc D 0) k) := rfl
  rw [e1, levFn_withP]
  rw [show ext1 (LevelP.triv (R.datYt t 0 R.triv).Pg (R.datYt t 0 R.triv).r ℂ).H
      (⇑(LevelP.triv (R.datYt t 0 R.triv).Pg (R.datYt t 0 R.triv).r ℂ).chi)
      (rTup (R.βY 0) (R.datYt t 0 R.triv) (finE (Yc D 0) k)) = 1 from subgroupCharExtension_one_apply _ _, one_mul, levFn_flag1]
  unfold LevCh.datYt LevCh.dat0
  exact levFn_datY_noQ rank_lowerChainSpace_zero_le (r_le_Y 0) D.R.t 0 R.Pg (R.Q t) R.triv R.chi (R.xiR t) (fun _ => 1) Frm.B _

end Formalism.IndefR.Eqv.Act

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GEqTie
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Eqv.Act

open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Links.RealDat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lift

variable {D : D7} (V : HSp D)

theorem thetaC_inj {y y' : Ainf D.host.F ⊗[D.host.F] D.host.E} (h : ∀ τ, thetaC D τ y = thetaC D τ y') : y = y' :=
  (splitEquiv D).injective (funext h)

theorem infHom_infOnly (h : GA D V) : infHom V (infOnly D V h) = infHom V h := by
  apply Units.ext
  funext i j
  show infPart D (matA D V (infOnly D V h) i j) = infPart D (matA D V h i j)
  apply thetaC_inj
  intro τ
  have e := congrFun (congrFun (infMat_infOnly D V h τ) i) j
  rw [infMat_thetaC, infMat_thetaC] at e
  exact e

theorem exists_finLift (q : Bridge.Gf V) : ∃ κ ∈ GfC V, finHom V κ = q := by
  obtain ⟨κ0, hκ0⟩ := q.2
  refine ⟨(infOnly D V κ0)⁻¹ * κ0, ?_, ?_⟩
  · show infHom V ((infOnly D V κ0)⁻¹ * κ0) = 1
    rw [map_mul, map_inv, infHom_infOnly, inv_mul_cancel]
  · have h1 : finHom V (infOnly D V κ0) = 1 := infOnly_mem_GinfC D V κ0
    rw [map_mul, map_inv, h1, inv_one, one_mul, hκ0]

end Lift

section Ad

variable {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ι : Γ →* G)

end Ad

section Coef

variable {D : D7} {V : HSp D} (c : CoefA V)

theorem coefExt_mul (hc : c.Is) (f : Bridge.Gf V → c.W) (h κ : GA D V) (hκ : κ ∈ GfC V) :
    c.ext f (h * κ) = c.ρ h⁻¹ (f ((finHom V).rangeRestrict h * (finHom V).rangeRestrict κ)) := by
  have e1 : (finHom V).rangeRestrict (h * κ) = (finHom V).rangeRestrict h * (finHom V).rangeRestrict κ := map_mul _ _ _
  have e2 : c.ρ (h * κ)⁻¹ = c.ρ h⁻¹ := by
    rw [_root_.mul_inv_rev, map_mul, hc.1 _ (Subgroup.inv_mem _ hκ), one_mul]
  exact congrArg₂ (fun (L : Module.End ℂ c.W) z => L (f z)) e2 e1

end Coef

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

end Formalism.IndefR.Eqv.Act

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.VanishTranslates
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Eqv.KerDiag

open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Links.RealDat Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Gen

variable {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
  (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ)

def KfLow (τ : D.what₂.Tau) : Submodule ℂ (M.sm τ) :=
  Submodule.span ℂ {w | ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∃ w0 : lowT M τ,
    (w : M.H τ) = M.rep τ g ((w0 : M.sm τ) : M.H τ)}


open Classical in
theorem mult_equiv {T : MMap M} (hT : T ∈ Mult θ M J χ) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (v : M.Vec) (w : M.sm τ) (hw : (w : M.H τ) = M.rep τ g (v τ)) :
    T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v) := by
  induction hT using Submodule.span_induction with
  | mem T hT => exact hT.equiv τ g hg v w hw
  | zero => rfl
  | add T T' _ _ h1 h2 =>
    simp only [_root_.add_apply, h1, h2]
    rfl
  | smul c T _ h =>
    simp only [_root_.smul_apply, h]
    rfl


open Classical in
theorem vanish_KfLow {T : MMap M} (hT : T ∈ Mult θ M J χ)
    (hlow : ∀ v : ∀ ρ, lowT M ρ, T (fun ρ => v ρ) = 0) :
    ∀ (s : Finset D.what₂.Tau) (v : M.Vec), (∀ τ ∈ s, v τ ∈ KfLow M τ) →
      (∀ τ ∉ s, ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∃ w0 : lowT M τ,
        (v τ : M.H τ) = M.rep τ g ((w0 : M.sm τ) : M.H τ)) → T v = 0 :=
  by apply _root_.UpperTheory.Reformulated.B.LowTypeThetaMapVanishing.vanish_KfLow <;> assumption

end Gen

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def DensLow : Prop :=
  ∀ i τ (ℓ : (R.MW i (sg0 D A)).H τ →ₗ[ℂ] ℂ),
    Sobolev₂ (lieAt (Wc D i) τ) ((R.MW i (sg0 D A)).rep τ) ℓ →
      (∀ w ∈ KfLow (R.MW i (sg0 D A)) τ, ℓ (w : (R.MW i (sg0 D A)).H τ) = 0) →
        ∀ w : (R.MW i (sg0 D A)).sm τ, ℓ (w : (R.MW i (sg0 D A)).H τ) = 0

open Classical in
theorem spanP_of (h : DensLow R) : Formalism.IndefR.Eqv.Act.SpanP R := by
  intro i F hS hlow
  let M := R.MW i (sg0 D A)
  let Kf : ∀ τ, Submodule ℂ (M.sm τ) := fun τ => KfLow M τ
  let Tm : ℂ →ₗ[ℂ] (⨂[ℂ] τ, Kf τ) →ₗ[ℂ] (⨂[ℂ] τ, M.sm τ) :=
    LinearMap.smulRight (LinearMap.id : ℂ →ₗ[ℂ] ℂ) (PiTensorProduct.map fun τ => (Kf τ).subtype)
  have hS' : F ∈ Mult R.θ M (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) := hS
  have hu : PiTensorProduct.lift F ∈ MultT R.θ M (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) := by
    rw [mem_multT, LinearEquiv.symm_apply_apply]; exact hS'
  have hvan0 : ∀ v : ∀ τ, Kf τ, F (fun τ => (v τ : M.sm τ)) = 0 := fun v =>
    vanish_KfLow R.θ M _ _ hS' hlow Finset.univ _ (fun τ _ => (v τ).2) (fun τ h => absurd (Finset.mem_univ τ) h)
  have hvan : ∀ (φ : ℂ) (w : ⨂[ℂ] τ, Kf τ), PiTensorProduct.lift F (Tm φ w) = 0 := by
    intro φ w
    simp only [Tm, LinearMap.smulRight_apply, LinearMap.id_apply, LinearMap.smul_apply, map_smul]
    rw [smul_eq_zero]
    right
    induction w using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul, PiTensorProduct.map_tprod, map_smul, PiTensorProduct.lift.tprod]
      simp only [Submodule.subtype_apply]
      rw [hvan0 v, smul_zero]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]
  have hspan : ∀ v : ∀ τ, M.sm τ, (∀ τ, v τ ∈ Kf τ) →
      PiTensorProduct.tprod ℂ v ∈ Submodule.span ℂ {x | ∃ φ w, Tm φ w = x} := by
    intro v hv
    refine Submodule.subset_span ⟨1, PiTensorProduct.tprod ℂ (fun τ => (⟨v τ, hv τ⟩ : Kf τ)), ?_⟩
    simp only [Tm, LinearMap.smulRight_apply, LinearMap.id_apply, LinearMap.smul_apply, one_smul,
      PiTensorProduct.map_tprod]
    rfl
  have h0 := Formalism.IndefR.Eqv.ioUniqueAt_holds D _ _ M R.θ _ _ Kf ℂ (⨂[ℂ] τ, Kf τ) Tm (fun τ ℓ hℓ hK => h i τ ℓ hℓ hK)
    hspan _ hu hvan
  have : F = PiTensorProduct.lift.symm (PiTensorProduct.lift F) := by simp
  rw [this, h0, map_zero]

end Formalism.IndefR.Eqv.KerDiag

end
end

