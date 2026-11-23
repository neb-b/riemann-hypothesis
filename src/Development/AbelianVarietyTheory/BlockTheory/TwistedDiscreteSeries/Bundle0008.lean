module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GeneralDiagonalMatrix
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lattice

variable {D : D7}

def StabLat (V : HSp D) (κ : GA D V) : Prop :=
  κ ∈ GfC V ∧ gLat V κ = (latHat V : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E))

def LevAgrees (V : HSp D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (M : ℕ) (Mh : Ideal (𝓞 D.host.E)) (κ : GA D V)
    (lev : La →ₗ[𝓞 D.host.E] La) : Prop :=
  ∀ a ∈ Mh • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V 1,
    finVec V (ι (lev a)) - (finHom V κ).1.mulVec (finVec V (ι a)) = M • w

end Lattice

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

end Frames

section Statement

variable {D : D7} (T : CoreJ D) (hT : LawsJ T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ) (hσ : GoodEmb T.Q.c σ)


include hT hj hσ in
theorem dict_mem_dom (h : GA D (T.V j σ)) : (T.dict j σ h).2 ∈ ((T.U j σ).X (T.dict j σ h).1).dom := by
  obtain ⟨_, _, _, hd⟩ := hT.dictU j hj σ hσ
  exact hd.2.2.2.1 h


end Statement

end GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitLinearModelNorm
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum IsDedekindDomain NumberField
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def absV (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (y : (Fv F v)ˣ) : ℝ :=
  ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (WithZero.log (Valued.v (y : Fv F v)))

theorem absV_pos (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (y : (Fv F v)ˣ) :
    0 < absV F v y := by
  unfold absV
  refine zpow_pos ?_ _
  have : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  exact_mod_cast Nat.pos_of_ne_zero this

def normV (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : (AE D)ˣ →* (Fv D.host.F v)ˣ :=
  Units.map (((evalV D.host.F v).comp (sndA D.host.F)).toRingHom.toMonoidHom.comp
    (Algebra.norm (AF D.host.F) (S := AE D)))

def normFin (D : D7) : (AE D)ˣ →* (Af D.host.F)ˣ :=
  Units.map ((sndA D.host.F).toRingHom.toMonoidHom.comp (Algebra.norm (AF D.host.F) (S := AE D)))

def absFin (D : D7) (x : (AE D)ˣ) : ℝ := ∏ᶠ v, absV D.host.F v (normV D v x)

theorem absFin_finite (D : D7) (x : (AE D)ˣ) :
    (Function.mulSupport fun v => absV D.host.F v (normV D v x)).Finite := by
  have h1 := ((normFin D x : Af D.host.F)).2
  have h2 := (((normFin D x)⁻¹ : (Af D.host.F)ˣ) : Af D.host.F).2
  have h := h1.and h2
  rw [Filter.eventually_cofinite] at h
  refine h.subset fun v hv => ?_
  intro hh
  apply hv
  have e1 : ((normV D v x : (Fv D.host.F v)ˣ) : Fv D.host.F v) = (normFin D x : Af D.host.F).1 v := rfl
  have e2 : (((normV D v x)⁻¹ : (Fv D.host.F v)ˣ) : Fv D.host.F v) =
      (((normFin D x)⁻¹ : (Af D.host.F)ˣ) : Af D.host.F).1 v := rfl
  have a1 : Valued.v ((normV D v x : (Fv D.host.F v)ˣ) : Fv D.host.F v) ≤ 1 := by rw [e1]; exact hh.1
  have a2 : Valued.v (((normV D v x)⁻¹ : (Fv D.host.F v)ˣ) : Fv D.host.F v) ≤ 1 := by rw [e2]; exact hh.2
  have hne : Valued.v ((normV D v x : (Fv D.host.F v)ˣ) : Fv D.host.F v) ≠ 0 := by
    simp
  rw [Units.val_inv_eq_inv_val, map_inv₀, inv_le_one₀ (zero_lt_iff.mpr hne)] at a2
  have : Valued.v ((normV D v x : (Fv D.host.F v)ˣ) : Fv D.host.F v) = 1 := le_antisymm a1 a2
  simp [absV, this]

theorem absFin_pos (D : D7) (x : (AE D)ˣ) : 0 < absFin D x :=
  finprod_induction (fun r : ℝ => 0 < r) one_pos (fun _ _ => mul_pos) fun v => absV_pos _ v _

variable {D : D7}

def subst (S T : HSp D) (g : GA D S) (h : GA D T) (x : WO S T) : WO S T :=
  HMul.hMul (HMul.hMul (mt T h⁻¹) (x : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (mt S g)

def modFac (S T : HSp D) (x y : (AE D)ˣ) : ℝ :=
  absFin D x ^ ((T.rank : ℝ) / 2) * absFin D y ^ (-(S.rank : ℝ) / 2)

theorem modFac_pos (S T : HSp D) (x y : (AE D)ˣ) : 0 < modFac S T x y :=
  mul_pos (Real.rpow_pos_of_pos (absFin_pos D x) _) (Real.rpow_pos_of_pos (absFin_pos D y) _)

def SplitLinearModel (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
    ∀ (f₀ : WO S T → ℂ), IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f₀ →
    ∀ (c : ℂ), c ≠ 0 → ∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ),
      IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) c f₀ Tm →
    ∀ (g : GA D S) (h : GA D T), SuppAt e S g → SuppAt e T h →
    ∀ x y : (AE D)ˣ, IsDetAt e S g x → IsDetAt e T h y →
    ∀ Φ : WO S T → ℂ, IsSBHalf e (latO S T ΛS ΛT fun _ => True) Φ →
      om (g, h) (Tm Φ) =
        Tm fun t => (splitFacO χS χT x y : ℂ) * (modFac S T x y : ℂ) * Φ (subst S T g h t)

def SplitLinearModelConj (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
    ∀ (f₀ : WO S T → ℂ), IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f₀ →
    ∀ (c : ℂ), c ≠ 0 → ∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ),
      IsPlaceModel ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T ΛS ΛT fun _ => True) c f₀ Tm →
    ∀ (g : GA D S) (h : GA D T), SuppAt e S g → SuppAt e T h →
    ∀ x y : (AE D)ˣ, IsDetAt e S g x → IsDetAt e T h y →
    ∀ Φ : WO S T → ℂ, IsSBHalf (cA D e) (latO S T ΛS ΛT fun _ => True) Φ →
      om (g, h) (Tm Φ) =
        Tm fun t => (splitFacO χS χT x y : ℂ) * ((modFac S T x y)⁻¹ : ℝ) * Φ (subst S T g h t)

end GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitSumStabLattice
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsSplitSum (e : AE D) : Prop :=
  IsSplitIdem D e ∨ ∃ P : Finset (Formalism.L2.DIV.Pl D.host.E), IsIdemSum e P

def StabLat (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (g : GA D V) : Prop :=
  ∀ y : Fin V.rank → Formalism.IndefR.Lev.EAf D,
    y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔
      (Formalism.IndefR.Lev.finE V g).val.mulVec y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ

def pullPt (S T : HSp D) (g : GA D S) (h : GA D T) (t : WO S T) : WO S T :=
  HMul.hMul (HMul.hMul (mt T h⁻¹) (t : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (mt S g)

def LinearLaw (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (e a : AE D) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)) : Prop :=
  ∀ (g : GA D S) (h : GA D T), SuppAt e S g → SuppAt e T h → StabLat S ΛS g → StabLat T ΛT h →
    ∀ x y : (AE D)ˣ, IsDetAt e S g x → IsDetAt e T h y →
      ∀ Φ : WO S T → ℂ, IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ →
        om (g, h) (Tm Φ) = (((χT x : ℂ))⁻¹ * (χS y : ℂ)) • Tm (fun t => Φ (pullPt S T g h t))

def WeilSplitFormula (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
      (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
      IsSelfDualC S ΛS → IsSelfDualC T ΛT →
      ∀ f₀ : WO S T → ℂ, IsVacO ψ θ S T sS sT ΛS ΛT f₀ →
      ∀ e : AE D, IsSplitSum e →
        (∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm →
          LinearLaw S T χS χT om ΛS ΛT e e Tm) ∧
        (∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm →
          LinearLaw S T χS χT om ΛS ΛT e (cA D e) Tm)

theorem pullPt_eq_actO (S T : HSp D) (g : GA D S) (h : GA D T) (t : WO S T) :
    pullPt S T g h t = actO S T g⁻¹ h⁻¹ t := by
  unfold pullPt actO; rw [inv_inv]

theorem factor_eq (χS χT : (AE D)ˣ →* Circle) (x y : (AE D)ˣ) :
    ((χT x : ℂ))⁻¹ * (χS y : ℂ) = (splitFacO χS χT x y : ℂ) := by
  simp [splitFacO]

theorem mulVec_mem_hatL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)} (hβ : Formalism.L2.DIV.IsFrame β Λ)
    {k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hk : k ∈ Formalism.L2.DIV.St β) {y : Fin n → E ⊗[F] Formalism.L2.Herm.Af F}
    (hy : y ∈ Formalism.L2.Herm.hatL (F := F) Λ) : k.val.mulVec y ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  obtain ⟨u, rfl⟩ := hk
  have hy' := (hβ y).1 hy
  refine (hβ _).2 fun i => ?_
  have e0 : β⁻¹ * Formalism.L2.DIV.frGL β u = Formalism.L2.DIV.intGL F E n u * β⁻¹ := by
    show β⁻¹ * (β * Formalism.L2.DIV.intGL F E n u * β⁻¹) = _
    group
  have e1 : (β⁻¹).val.mulVec ((Formalism.L2.DIV.frGL β u).val.mulVec y) =
      (Formalism.L2.DIV.intGL F E n u).val.mulVec ((β⁻¹).val.mulVec y) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, e0]
  rw [e1]
  show ∑ j, (Formalism.L2.DIV.intGL F E n u).val i j * ((β⁻¹).val.mulVec y) j ∈ _
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (u.val i j).2 (hy' j)

theorem mulVec_mem_hatL_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)} (hβ : Formalism.L2.DIV.IsFrame β Λ)
    {k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hk : k ∈ Formalism.L2.DIV.St β) (y : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) :
    y ∈ Formalism.L2.Herm.hatL (F := F) Λ ↔ k.val.mulVec y ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  refine ⟨mulVec_mem_hatL hβ hk, fun hy => ?_⟩
  have := mulVec_mem_hatL hβ (Subgroup.inv_mem _ hk) hy
  rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this

theorem stabLat_of_mem_St (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (hβ : Formalism.L2.DIV.IsFrame β Λ) (g : GA D V)
    (hg : Formalism.IndefR.Lev.finE V g ∈ Formalism.L2.DIV.St β) : StabLat V Λ g :=
  fun y => mulVec_mem_hatL_iff hβ hg y

end GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice

end
end

