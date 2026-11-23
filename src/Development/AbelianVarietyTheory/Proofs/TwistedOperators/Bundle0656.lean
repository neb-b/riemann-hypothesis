module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentPeriodAdelicClausesOfReal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0554
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefficientPoincareSeriesIsAutomorphic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0560
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefficientDecayKFiniteSecondVector
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0517
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0651
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0927
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0421
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0585
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0584
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0636
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0628
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0638

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCuspFormPeriodNeZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SepPer.PerNe

theorem multT_apply_mul_lev {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S}
    {J : Set (GA D V)} {χ : GA D V → ℂ} {F : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hF : F ∈ MultT θ M J χ) (v : SmT M) :
    ∀ k ∈ J, ∀ g, F v (g * k) = χ k * F v g := by
  obtain ⟨T, hT, rfl⟩ := hF
  induction hT using Submodule.span_induction generalizing v with
  | mem T hT =>
    induction v using PiTensorProduct.induction_on with
    | smul_tprod r w =>
      intro k hk g
      simp only [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod, Pi.smul_apply, smul_eq_mul]
      rw [hT.lev w k hk g]; ring
    | add x y hx hy =>
      intro k hk g
      simp only [map_add (f := _), Pi.add_apply]
      rw [hx k hk g, hy k hk g]; ring
  | zero => intro k hk g; simp
  | add T₁ T₂ _ _ h₁ h₂ =>
    intro k hk g
    simp only [map_add (f := _), LinearMap.add_apply, Pi.add_apply]
    rw [h₁ v k hk g, h₂ v k hk g]; ring
  | smul c T _ h =>
    intro k hk g
    simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    rw [h v k hk g]; ring

theorem apply_tprod_eq {ι : Type} [Fintype ι] {E : ι → Type} [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
    {X : Type} [AddCommGroup X] [Module ℂ X] (y : (⨂[ℂ] i, E i) →ₗ[ℂ] X) (a : ∀ i, E i) :
    y (PiTensorProduct.tprod ℂ a) = PiTensorProduct.lift.symm y a := by
  conv_lhs => rw [← PiTensorProduct.lift.apply_symm_apply y]
  exact PiTensorProduct.lift.tprod _

end GlobalTheory.SepPer.PerNe

namespace GlobalTheory.SepPer

end GlobalTheory.SepPer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalModelMovedFrames
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

namespace GlobalTheory.FlatPlace.MoveModel

variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k]
  {Y Y' Z Z' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] [Fintype Z'] [DecidableEq Z']

def subH (εS : GL Y' k) (εT : GL Y k) (σS : Z' ≃ Y') (σT : Z ≃ Y) : Matrix Y Y' k ≃ₜ Matrix Z Z' k where
  toFun x := ((εT⁻¹).val * x * εS.val).submatrix σT σS
  invFun z := εT.val * z.submatrix σT.symm σS.symm * (εS⁻¹).val
  left_inv x := by
    simp only [Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id, Matrix.mul_assoc, Units.mul_inv,
      Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  right_inv z := by
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.submatrix_submatrix, Equiv.symm_comp_self,
      Equiv.symm_comp_self, Matrix.submatrix_id_id]
  continuous_toFun := ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_submatrix _ _
  continuous_invFun := ((continuous_const.matrix_mul (continuous_id.matrix_submatrix _ _)).matrix_mul continuous_const)

theorem subH_apply (εS : GL Y' k) (εT : GL Y k) (σS : Z' ≃ Y') (σT : Z ≃ Y) (x : Matrix Y Y' k) :
    subH εS εT σS σT x = ((εT⁻¹).val * x * εS.val).submatrix σT σS := rfl

theorem subH_add (εS : GL Y' k) (εT : GL Y k) (σS : Z' ≃ Y') (σT : Z ≃ Y) (x y : Matrix Y Y' k) :
    subH εS εT σS σT (x + y) = subH εS εT σS σT x + subH εS εT σS σT y := by
  simp only [subH_apply, Matrix.mul_add, Matrix.add_mul]
  rfl

def pullS (εS : GL Y' k) (εT : GL Y k) (σS : Z' ≃ Y') (σT : Z ≃ Y) : SB (Matrix Z Z' k) →ₗ[ℂ] SB (Matrix Y Y' k) where
  toFun Φ := ⟨fun x => Φ.1 (subH εS εT σS σT x),
    ⟨Φ.2.1.comp_continuous (subH εS εT σS σT).continuous, Φ.2.2.comp_homeomorph (subH εS εT σS σT)⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem sub_mul_sub {n m : Type} [Fintype n] [Fintype m] (P : Matrix Y n k) (Q : Matrix n m k) (R : Matrix m Y' k)
    (σS : Z' ≃ Y') (σT : Z ≃ Y) : P.submatrix σT id * Q * R.submatrix id σS = (P * Q * R).submatrix σT σS := by
  ext i j
  simp [Matrix.mul_apply]

end GlobalTheory.FlatPlace.MoveModel

namespace GlobalTheory.FlatPlace.MoveModel

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
  {Y Y' Z Z' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] [Fintype Z'] [DecidableEq Z']

theorem map_mt_inv_mul {S : HSp D} (g : GA D S) : (mt S g⁻¹).map p.π * (mt S g).map p.π = 1 := by
  rw [← Matrix.map_mul]
  have : mt S g⁻¹ * mt S g = 1 := by
    rw [show mt S g⁻¹ * mt S g = mt S (g⁻¹ * g) by simp [Formalism.L2.Theta.mt], inv_mul_cancel]
    simp [Formalism.L2.Theta.mt]
  rw [this, Matrix.map_one _ (map_zero _) (map_one _)]

theorem actO_up_mvFr {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (a : GA D S) (b : GA D T)
    (εS : GL Y' k) (εT : GL Y k) (σS : Z' ≃ Y') (σT : Z ≃ Y) (x : Matrix Y Y' k) :
    actO S T a b (p.up FS FT x) = p.up (mvFr p a FS εS σS) (mvFr p b FT εT σT) (subH εS εT σS σT x) := by
  have h1 : IsHalf p.e (actO S T a b (p.up FS FT x)) :=
    GlobalTheory.SplitHecke.isHalf_actO a b (Witness.up_half p FS FT x)
  rw [← Witness.up_down p (mvFr p a FS εS σS) (mvFr p b FT εT σT) h1]
  congr 1
  have hu : (p.up FS FT x).map p.π = FT.β * x * FS.γ := Matrix.ext fun _ _ => p.π_ι _
  have hA := map_mt_inv_mul p a
  have hB := map_mt_inv_mul p b
  unfold Place.down actO
  rw [Matrix.map_mul, Matrix.map_mul, hu, subH_apply]
  change ((εT⁻¹).val * FT.γ * (mt T b⁻¹).map p.π).submatrix σT id * _ * ((mt S a).map p.π * FS.β * εS.val).submatrix id σS = _
  rw [sub_mul_sub]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((mt T b⁻¹).map p.π), hB, Matrix.one_mul, ← Matrix.mul_assoc FT.γ FT.β, FT.γβ, Matrix.one_mul,
    ← Matrix.mul_assoc ((mt S a⁻¹).map p.π), hA, Matrix.one_mul, ← Matrix.mul_assoc FS.γ FS.β, FS.γβ, Matrix.one_mul]

end GlobalTheory.FlatPlace.MoveModel

namespace GlobalTheory.FlatPlace


open GlobalTheory.FlatPlace.MoveModel in
theorem exists_isModel_mvFr : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT ω → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (Z Z' : Type) [Fintype Z] [DecidableEq Z] [Fintype Z'] [DecidableEq Z'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) Tm, p.IsModel ψ FS FT Tm → ∀ (a : GA D S) (b : GA D T) (εS : GL Y' k) (εT : GL Y k) (σS : Z' ≃ Y') (σT : Z ≃ Y), ∃ Tm', p.IsModel ψ (mvFr p a FS εS σS) (mvFr p b FT εT σT) Tm' ∧ ∀ (Φ : SB (Matrix Y Y' k)) (Φ' : SB (Matrix Z Z' k)), (∀ x, Φ.1 x = Φ'.1 (((εT⁻¹).val * x * εS.val).submatrix σT σS)) → Tm' Φ' = ω (a, b) (Tm Φ) := by
  intro D k _ _ _ _ p ψ S T χS χT ω hW Y Y' _ _ _ _ Z Z' _ _ _ _ FS FT Tm hm a b εS εT σS σT
  let L := pullS (k := k) εS εT σS σT
  let W₀ : Module.End ℂ (WO S T → ℂ) := ω (a, b)
  have hA := actO_up_mvFr p FS FT a b εS εT σS σT
  refine ⟨W₀ ∘ₗ Tm ∘ₗ L, ⟨fun Φ => hW.om_pres _ _ (hm.theta _), fun z Φ Φ₁ hΦ => ?_, fun y hy Φ Φ₁ hΦ => ?_⟩, fun Φ Φ' e => ?_⟩
  · set x := (subH εS εT σS σT).symm z with hx
    have hz : subH εS εT σS σT x = z := (subH εS εT σS σT).apply_symm_apply z
    have h1 : ∀ t, (L Φ₁).1 t = (L Φ).1 (t + x) := fun t => by
      change Φ₁.1 (subH εS εT σS σT t) = Φ.1 (subH εS εT σS σT (t + x))
      rw [hΦ, subH_add, hz]
    have h2 := hm.trans x (L Φ) (L Φ₁) h1
    simp only [LinearMap.comp_apply]
    rw [h2]
    show ω (a, b) _ = _
    rw [hW.om_heis _ _ _ _ (hm.theta _), hA, hz]
  · set y₀ := actO S T a⁻¹ b⁻¹ y
    have hy₀ : IsHalf (cA D p.e) y₀ := GlobalTheory.SplitHecke.isHalf_actO a⁻¹ b⁻¹ hy
    have hyy : actO S T a b y₀ = y := by
      have := GlobalTheory.SplitHecke.actO_inv_actO a⁻¹ b⁻¹ y
      rwa [inv_inv, inv_inv] at this
    have h1 : ∀ t, (L Φ₁).1 t = ψ (symplO S T (p.up FS FT t) y₀) * (L Φ).1 t := fun t => by
      change Φ₁.1 (subH εS εT σS σT t) = _ * Φ.1 (subH εS εT σS σT t)
      rw [hΦ, ← hA, ← hyy, GlobalTheory.SplitHecke.symplO_actO]
    have h2 := hm.modul y₀ hy₀ (L Φ) (L Φ₁) h1
    simp only [LinearMap.comp_apply]
    rw [h2]
    show ω (a, b) _ = _
    rw [hW.om_heis _ _ _ _ (hm.theta _), hyy]
  · have : L Φ' = Φ := Subtype.ext (funext fun x => (e x).symm)
    show ω (a, b) (Tm (L Φ')) = _
    rw [this]

end GlobalTheory.FlatPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalModelOfSplitPlaceThetaFun
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

namespace GlobalTheory.LocMod.Witness

theorem exists_isModel_of_isThetaAt : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y), (∀ x, p.up FS FT x ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) ↔ ∀ a b, x a b ∈ Valuation.integer (ValuativeRel.valuation k)) → ∀ f₀ φ f : WO S T → ℂ, IsThetaFunO ψ S T f₀ → IsSBHalf p.e (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) φ → IsThetaAt ψ (symplO S T) (heisO ψ S T) p.e (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) 1 f₀ φ f → ∃ Tm, p.IsModel ψ FS FT Tm ∧ (∀ O, IsOne O → Tm O = f₀) ∧ ∃ Φ : SB (Matrix Y Y' k), (∀ x, Φ.1 x = φ (p.up FS FT x)) ∧ Tm Φ = f := by
  classical
  intro D k _ _ _ _ p ψ hψ S T ΛS ΛT hS hT Y Y' _ _ _ _ FS FT hlat f₀ φ f hf₀ hφ hθ
  obtain ⟨⟨T₀, h₀⟩, hall⟩ := hθ
  have hf : f = T₀ φ := hall T₀ h₀

  have hNk : ∀ N : ℕ, 0 < N → (N : k) ≠ 0 := fun N hN h => by
    have h1 : prH p (N : D.host.E) = 0 := by rw [map_natCast]; exact h
    have h2 : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    exact h2 ((map_eq_zero (prH p)).1 h1)
  obtain ⟨N, hN, hinv, hsupp⟩ := hφ.2
  have hN0 := hNk N hN
  have hA := lat_compact p FS FT hS hT
  have hAo := lat_open p FS FT hS hT
  generalize hAd : ((latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True).comap (upH p FS FT) : AddSubgroup _) = A at hA hAo
  have memA : ∀ x, x ∈ A ↔ p.up FS FT x ∈ (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) := fun x => by
    rw [← hAd]; rfl
  have hup_smul : ∀ x : Matrix Y Y' k, p.up FS FT (N • x) = N • p.up FS FT x := fun x => map_nsmul (upH p FS FT) N x
  have hNx : ∀ x : Matrix Y Y' k, (N : k) • x = N • x := fun x => Nat.cast_smul_eq_nsmul k N x

  let g : Matrix Y Y' k → ℂ := fun x => φ (p.up FS FT x)
  have hlc : IsLocallyConstant g := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hU : IsOpen ((fun y : Matrix Y Y' k => (N : k)⁻¹ • (y - x)) ⁻¹' (A : Set (Matrix Y Y' k))) :=
      hAo.preimage ((continuous_const_smul ((N : k)⁻¹)).comp (continuous_id.sub continuous_const))
    have hx : x ∈ ((fun y : Matrix Y Y' k => (N : k)⁻¹ • (y - x)) ⁻¹' (A : Set (Matrix Y Y' k))) := by
      simp only [Set.mem_preimage, sub_self, smul_zero]; exact A.zero_mem
    filter_upwards [hU.mem_nhds hx] with y hy
    have hy' : (N : k)⁻¹ • (y - x) ∈ A := hy
    have e1 : y = x + N • ((N : k)⁻¹ • (y - x)) := by
      rw [← hNx, smul_smul, mul_inv_cancel₀ hN0, one_smul, add_sub_cancel]
    change φ (p.up FS FT y) = φ (p.up FS FT x)
    rw [e1, up_add, hup_smul]
    exact hinv _ ((memA _).1 hy') (up_half p FS FT _) _
  have hcs : HasCompactSupport g := by
    refine HasCompactSupport.intro (hA.image (continuous_const_smul (N : k)⁻¹)) fun x hx => ?_
    by_contra h
    apply hx
    have h1 := hsupp _ h
    rw [← hup_smul, ← memA] at h1
    refine ⟨N • x, h1, ?_⟩
    change (N : k)⁻¹ • (N • x) = x
    rw [← hNx, smul_smul, inv_mul_cancel₀ hN0, one_smul]
  let Φ : SB (Matrix Y Y' k) := ⟨g, hlc, hcs⟩

  have hext : ∀ Ψ : SB (Matrix Y Y' k), IsSBHalf p.e (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) (ext p FS FT Ψ) :=
    ext_sb p FS FT hS hT
  refine ⟨T₀.comp (ext p FS FT), ⟨fun Ψ => ?_, fun x Ψ Ψ' h => ?_, fun y hy Ψ Ψ' h => ?_⟩, fun O hO => ?_, Φ, fun x => rfl, ?_⟩
  · exact GlobalTheory.SchrTheta.isTheta_placeModel D ψ hψ S T _ _ hS hT p.e p.split.1 (GlobalTheory.PlaceCoord.infPart_split p.split)
      _ hf₀ T₀ h₀ _ (hext Ψ)
  · refine Eq.trans (congrArg T₀ ?_) (h₀.trans _ (hext Ψ) _ (up_half p FS FT x))
    funext t
    rw [ext_apply, ext_apply, down_add, down_up, h]
    exact if_congr (half_add (up_half p FS FT x)).symm rfl rfl
  · refine Eq.trans (congrArg T₀ ?_) (h₀.modul _ (hext Ψ) _ hy)
    funext t
    rw [ext_apply, ext_apply, h]
    split_ifs with ht
    · rw [up_down p FS FT ht]
    · rw [mul_zero]
  · have e1 : ext p FS FT O = (1 : ℂ) • halfInd p.e (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) := by
      funext t
      rw [one_smul, ext_apply, halfInd]
      by_cases ht : IsHalf p.e t
      · rw [if_pos ht, hO, Set.indicator_apply]
        refine if_congr ?_ rfl rfl
        rw [and_iff_left ht, ← up_down p FS FT ht, down_up, hlat]
        rfl
      · rw [if_neg ht, if_neg fun h => ht h.2]
    change T₀ (ext p FS FT O) = f₀
    rw [e1]
    exact h₀.vac
  · change T₀ (ext p FS FT Φ) = f
    rw [hf]
    congr 1
    funext t
    rw [ext_apply]
    split_ifs with ht
    · change φ (p.up FS FT (p.down FS FT t)) = φ t
      rw [up_down p FS FT ht]
    · by_contra h
      exact ht (hφ.1 t (Ne.symm h))

end GlobalTheory.LocMod.Witness
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstColumnTypeTwistDatumEqGivenFunction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FlipTop

theorem prodHalf_topFn_eq_givenFn : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (B : Frames G) {μ₀ : T}, L.Is μ₀ →
    ∀ (t : T) {e e' : AE D}, IsIdemSum e (locPl G t) → IsIdemSum e' (GlobalTheory.FlipTop.topPl L t) → (∀ w ∈ locPl G t, w ∉ GlobalTheory.FlipTop.topPl L t → ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧ ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1)) → ∀ (Φ : G.Datum) (j : ℕ) (hj : j < D.R.m),
    GlobalTheory.HalfProd.prodHalf e' (e - e') (halfInd (e - e') (latO (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (G.latS (.mu t 0 j) : Set _) (G.latT (.mu t 0 j) : Set _) fun _ => True)) (GlobalTheory.FlipTop.topFn B t e' j (GlobalTheory.FlipTop.rank_col G hj.le) (GlobalTheory.FlipTop.rank_col G hj)) =
      GlobalTheory.FlipStart.givenFn B t Φ e (.down t 0 j) := by
  intro D T L sc G B μ₀ hL t e e' he he' hAA Φ j hj
  classical
  have hsub : GlobalTheory.FlipTop.topPl L t ⊆ locPl G t := by
    intro w hw
    rcases Finset.mem_union.1 hw with h | h
    · exact Finset.mem_union_left _ (levelChainTypePlaces_subset_chosenPlaces G hL t h)
    · exact Finset.mem_union_right _ h
  obtain ⟨he₁, -⟩ := _root_.GlobalTheory.IdemSubDiff.isIdemSum_sdiff he he' hsub
  have h1 := GlobalTheory.PlaceDatum.idemSum_mul_self he'
  have h2 := GlobalTheory.PlaceDatum.idemSum_mul_self he₁
  obtain ⟨-, c1, c0⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he'
  obtain ⟨-, d1, -⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he₁
  have ha := GlobalTheory.FlipTop.rank_col G hj.le
  have hb := GlobalTheory.FlipTop.rank_col G hj
  funext x
  rw [GlobalTheory.HalfProd.prodHalf_apply, add_sub_cancel]
  unfold GlobalTheory.FlipStart.givenFn
  by_cases hx : IsHalf e x
  swap
  · rw [if_neg hx, if_neg hx, mul_zero]
  rw [if_pos hx, if_pos hx, mul_one]
  set N := GlobalTheory.FunObj.Comparison₂.fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D)) with hN
  have hfr : ∀ a : AE D, GlobalTheory.FunObj.Comparison₂.fr (B.β 0 (j + 1)) (B.β 0 j) ((a • x).map (toEAf D)) = toEAf D a • N := by
    intro a
    rw [hN, ← GlobalTheory.FunObj.Comparison₂.fr_smul]
    congr 1
    ext p q
    simp [Matrix.map_apply, Matrix.smul_apply, RingHom.map_mul]
  have hcomp : ∀ (a : AE D) (w : Pl D.host.E), cpt (D := D) w (toEAf D a) = 1 →
      (GlobalTheory.FunObj.Comparison₂.fr (B.β 0 (j + 1)) (B.β 0 j) ((a • x).map (toEAf D))).map (cpt (D := D) w) = N.map (cpt (D := D) w) := by
    intro a w hw
    rw [hfr]
    ext p q
    simp [Matrix.map_apply, Matrix.smul_apply, RingHom.map_mul, hw]

  have hsubm : ∀ w : Pl D.host.E, GlobalTheory.StepData.IntM ((N.map (cpt (D := D) w)).submatrix (GlobalTheory.FunObj.Comparison₂.ixOf G t w hb)
      (GlobalTheory.FunObj.Comparison₂.ixOf G t w ha)) ↔ GlobalTheory.StepData.IntM (N.map (cpt (D := D) w)) := fun w =>
    ⟨fun h i l => by simpa using h ((GlobalTheory.FunObj.Comparison₂.ixOf G t w hb).symm i) ((GlobalTheory.FunObj.Comparison₂.ixOf G t w ha).symm l),
      fun h i l => h _ _⟩
  have hR : ∀ w, givenDatum t w B Φ (edgeOf (.down t 0 j)) (locArg B t w (.down t 0 j) x) =
      stepFn L t w j ((N.map (cpt (D := D) w)).submatrix (GlobalTheory.FunObj.Comparison₂.ixOf G t w hb) (GlobalTheory.FunObj.Comparison₂.ixOf G t w ha)) := by
    intro w
    have hla : locArg B t w (.down t 0 j) x = B.coord t w (X := (0, j + 1)) (Y := (0, j)) ⟨Nat.zero_le _, hj⟩
        ⟨Nat.zero_le _, hj.le⟩ ((x.map (toEAf D)).map (cpt (D := D) w)) := by
      rw [Matrix.map_map]
      exact dif_pos ⟨Nat.zero_le _, hj⟩
    rw [hla]
    exact GlobalTheory.FunObj.Comparison₂.givenDatum_theta_coord B t w Φ hj ha hb (x.map (toEAf D))
  rw [Finset.prod_congr rfl fun w _ => hR w, ← Finset.prod_sdiff hsub]
  have hout : ∀ w ∈ locPl G t \ GlobalTheory.FlipTop.topPl L t, stepFn L t w j ((N.map (cpt (D := D) w)).submatrix
      (GlobalTheory.FunObj.Comparison₂.ixOf G t w hb) (GlobalTheory.FunObj.Comparison₂.ixOf G t w ha)) =
      if GlobalTheory.StepData.IntM (N.map (cpt (D := D) w)) then 1 else 0 := by
    intro w hw
    obtain ⟨-, hw2⟩ := Finset.mem_sdiff.1 hw
    have hP : w ∉ L.Pg := fun h => hw2 (Finset.mem_union_left _ h)
    have hQ : w ∉ L.Q t := fun h => hw2 (Finset.mem_union_right _ h)
    unfold stepFn
    rw [if_neg hP, if_neg hQ, Set.indicator_apply]
    exact if_congr (hsubm w) rfl rfl
  rw [Finset.prod_congr rfl hout, Finset.prod_boole]

  have hx1 : IsHalf (e - e') ((e - e') • x) := fun p q => by
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, h2]
  have hS : IsSelfDualC (G.pS (.mu t 0 j)) (G.latS (.mu t 0 j)) := (colY_isV D T L μ₀ hL j hj.le).sd
  have hT : IsSelfDualC (G.pT (.mu t 0 j)) (G.latT (.mu t 0 j)) := (colY_isV D T L μ₀ hL (j + 1) hj).sd
  have hAA' : ∀ w ∈ locPl G t \ GlobalTheory.FlipTop.topPl L t, ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧ ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1) := fun w hw =>
    hAA w (Finset.mem_sdiff.1 hw).1 (Finset.mem_sdiff.1 hw).2
  have hlat := GlobalTheory.T.mem_completedHomLattice_iff_integral_on_unit_half hS hT (B.isFrame_β hL (Nat.zero_le _) hj.le) (B.isFrame_β hL (Nat.zero_le _) hj) he₁ hAA'
    ((e - e') • x) hx1
  have k1 : halfInd (e - e') (latO (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (G.latS (.mu t 0 j) : Set _)
      (G.latT (.mu t 0 j) : Set _) fun _ => True) ((e - e') • x) =
      if ∀ w ∈ locPl G t \ GlobalTheory.FlipTop.topPl L t, GlobalTheory.StepData.IntM (N.map (cpt (D := D) w)) then 1 else 0 := by
    unfold halfInd
    refine if_congr ?_ rfl rfl
    rw [and_iff_left hx1, hlat]
    exact forall₂_congr fun w hw => by rw [hcomp _ w (d1 w hw)]

  have hint : IsIntM (toEAf D e' • N) ↔ ∀ w ∈ GlobalTheory.FlipTop.topPl L t, GlobalTheory.StepData.IntM (N.map (cpt (D := D) w)) := by
    constructor
    · intro h w hw i l
      have := (mem_OA_iff _).1 (h i l) w
      rw [Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, c1 w hw, one_mul] at this
      exact (GlobalTheory.FunObj.Comparison₂.vEq w).le_one_iff_le_one.2 this
    · intro h i l
      refine (mem_OA_iff _).2 fun w => ?_
      rw [Matrix.smul_apply, smul_eq_mul, RingHom.map_mul]
      by_cases hw : w ∈ GlobalTheory.FlipTop.topPl L t
      · rw [c1 w hw, one_mul]
        exact (GlobalTheory.FunObj.Comparison₂.vEq w).le_one_iff_le_one.1 (h w hw i l)
      · rw [c0 w hw, zero_mul]
        exact zero_mem _
  have hx0 : IsHalf e' (e' • x) := fun p q => by
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, h1]
  have k0 : GlobalTheory.FlipTop.topFn B t e' j ha hb (e' • x) = ∏ w ∈ GlobalTheory.FlipTop.topPl L t, stepFn L t w j
      ((N.map (cpt (D := D) w)).submatrix (GlobalTheory.FunObj.Comparison₂.ixOf G t w hb) (GlobalTheory.FunObj.Comparison₂.ixOf G t w ha)) := by
    unfold GlobalTheory.FlipTop.topFn
    rw [Finset.prod_congr rfl fun w hw => by rw [hcomp e' w (c1 w hw)]]
    by_cases H : ∀ w ∈ GlobalTheory.FlipTop.topPl L t, GlobalTheory.StepData.IntM (N.map (cpt (D := D) w))
    · rw [if_pos ⟨hx0, by rw [hfr]; exact hint.2 H⟩]
    · rw [if_neg fun h => H (by have h' := h.2; rw [hfr] at h'; exact hint.1 h')]
      push_neg at H
      obtain ⟨w, hw, hn⟩ := H
      refine (Finset.prod_eq_zero hw ?_).symm
      by_contra h0
      exact hn ((hsubm w).1 (GlobalTheory.FunObj.LocTest.intM_of_stepFn t w j h0))
  rw [k0, k1, mul_comm]

end GlobalTheory.FlipTop

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowGrpEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CellMass

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

def rowN (j : ℕ) : Subgroup (GA D (G.V (.grid D.R.m j))) :=
  if h : j + 2 * ((D.R.m - 1 - j) / 2) + 1 = D.R.m then GlobalTheory.MixPer.flagN (rowJac G j (by omega) ((D.R.m - 1 - j) / 2) (by omega))
  else if h' : j + 2 * ((D.R.m - 2 - j) / 2) + 2 = D.R.m then GlobalTheory.MixPer.flagN (besDecAt G j _ h') else ⊥

def rowEmb (j : ℕ) : GA D (G.V (.top j)) →* GA D (G.V (.grid D.R.m j)) :=
  if h : j + 2 * ((D.R.m - 1 - j) / 2) + 1 = D.R.m then (rowJac G j (by omega) ((D.R.m - 1 - j) / 2) (by omega)).emb0
  else if h' : j + 2 * ((D.R.m - 2 - j) / 2) + 2 = D.R.m then
    GlobalTheory.MixPer.embA (besDecAt G j _ h') (GlobalTheory.OrthSumExists.orthDecHsum D _ _) else 1

theorem rowGrp_eq (j : ℕ) : rowGrp G j = rowN G j ⊔ (rowEmb G j).range := by
  unfold rowGrp rowN rowEmb
  split_ifs
  · rfl
  · rfl
  · simp

def prSet (j : ℕ) (b : GfC (G.V (.grid D.R.m j))) : Set (GfC (G.V (.top j))) :=
  {g | ∃ n ∈ rowN G j, (b.1)⁻¹ * (n * rowEmb G j g.1) * b.1 ∈ latGrp G j}

end GlobalTheory.CellMass
end
end

