module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRangeSrcForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0001
public import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionGroupLocalGaloisIso
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0233
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionTraceNormContinuousStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicCompletion_trace_norm_continuous_alt : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (f : v.adicCompletion K →+* v'.adicCompletion L), Continuous f → letI := f.toAlgebra; FiniteDimensional (v.adicCompletion K) (v'.adicCompletion L) → Continuous (Algebra.trace (v.adicCompletion K) (v'.adicCompletion L)) ∧ Continuous (Algebra.norm (v.adicCompletion K) : v'.adicCompletion L → v.adicCompletion K) := by
  first | exact @GlobalTheory.adicCompletion_trace_norm_continuous | exact GlobalTheory.adicCompletion_trace_norm_continuous | (intros; apply GlobalTheory.adicCompletion_trace_norm_continuous <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionTraceNormOfBasisImageStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicCompletion_trace_norm_of_basis_image_alt : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (f : v.adicCompletion K →+* v'.adicCompletion L), (∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) → letI := f.toAlgebra; ∀ (n : ℕ) (b : Module.Basis (Fin n) K L) (b' : Module.Basis (Fin n) (v.adicCompletion K) (v'.adicCompletion L)), (∀ i, b' i = algebraMap L _ (b i)) → ∀ z : L, Algebra.trace (v.adicCompletion K) (v'.adicCompletion L) (algebraMap L _ z) = algebraMap K _ (Algebra.trace K L z) ∧ Algebra.norm (v.adicCompletion K) (algebraMap L (v'.adicCompletion L) z) = algebraMap K _ (Algebra.norm K z) := by
  first | exact @GlobalTheory.adicCompletion_trace_norm_of_basis_image | exact GlobalTheory.adicCompletion_trace_norm_of_basis_image | (intros; apply GlobalTheory.adicCompletion_trace_norm_of_basis_image <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineSpaceCoveredSmoothOfRelativeDimensionAddStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineSpaceCovered_smoothOfRelativeDimension_add : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (r d : ℕ), AffCover M M' φ f r → SmoothOfRelativeDimension d M.s → SmoothOfRelativeDimension (d + r) M'.s := by
  first | exact @GlobalTheory.FlagBundle.affCover_smooth | exact GlobalTheory.FlagBundle.affCover_smooth | (intros; apply GlobalTheory.FlagBundle.affCover_smooth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AvgLevel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.TopSpan


open Classical in
theorem avg_level (K : Type) [Field K] (V : Type) [AddCommGroup V] [Module K V] (G : Type) [Group G]
    (r : Representation K G V) (P : Subgroup G) [Fintype P] (ψ : P →* Kˣ) (f : V) (h : P) :
    r h ((Nat.card P : K)⁻¹ • ∑ p : P, ((ψ p⁻¹ : Kˣ) : K) • r p f) =
      ((ψ h : Kˣ) : K) • ((Nat.card P : K)⁻¹ • ∑ p : P, ((ψ p⁻¹ : Kˣ) : K) • r p f) := by
  have key : ∑ p : P, ((ψ p⁻¹ : Kˣ) : K) • r h (r p f) = ((ψ h : Kˣ) : K) • ∑ p : P, ((ψ p⁻¹ : Kˣ) : K) • r p f := by
    rw [Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun p => ?_
    simp only [Equiv.coe_mulLeft, smul_smul, ← Module.End.mul_apply, ← map_mul]
    congr 1
    rw [_root_.mul_inv_rev, map_mul, map_inv, map_inv, ← Units.val_mul]
    congr 1
    rw [mul_comm, mul_assoc, inv_mul_cancel, mul_one]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_smul, map_sum, smul_comm]
  simp only [map_smul]
  rw [key]


set_option maxHeartbeats 1000000 in
theorem jR_level : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (b : Bool) (t : T) (f : A.fam.amb.FR t), (∀ h : (F.lvl b).P, (A.fam.R t).r h f = (((F.lvl b).ψ h : D.what₂.LLˣ) : D.what₂.LL) • f) → ∀ (q : (levEnv D.sp.X' R.βX (R.datXt t)).Q) (hq : (R.B.R t).act_tie.red q ∈ (F.lvl b).P) (h : Bridge.Gf D.sp.X'), R.B.jR t f (h * q) = (((levEnv D.sp.X' R.βX (R.datXt t)).ch q : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hq⟩ : D.what₂.LLˣ) : D.what₂.LL)) • R.B.jR t f h := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F b t f hf q hq h
  have e : (R.B.R t).pres.extL (A.leftGroupActionRight t ((R.B.R t).act_tie.red q) f) =
      Bridge.g0Act (levEnv D.sp.X' R.βX (R.datXt t)).ch q ((R.B.R t).pres.extL f) :=
    (R.B.R t).act_tie.act_eq ((R.B.R t).act_tie.red q) q rfl f
  have hf' : A.leftGroupActionRight t ((R.B.R t).act_tie.red q) f = (((F.lvl b).ψ ⟨_, hq⟩ : D.what₂.LLˣ) : D.what₂.LL) • f := hf ⟨_, hq⟩
  have e3 := congrArg (R.B.R t).pres.extL hf'
  have e4 : (R.B.R t).pres.extL ((((F.lvl b).ψ ⟨_, hq⟩ : D.what₂.LLˣ) : D.what₂.LL) • f) =
      D.what₂.embLL (((F.lvl b).ψ ⟨_, hq⟩ : D.what₂.LLˣ) : D.what₂.LL) • (R.B.R t).pres.extL f :=
    map_smulₛₗ (R.B.R t).pres.extL _ f
  have e5 := congrFun ((e4.symm.trans e3.symm).trans e) h
  simp only [Bridge.g0Act, Pi.smul_apply] at e5
  have e7 := congrArg (fun w => (((levEnv D.sp.X' R.βX (R.datXt t)).ch q : ℂˣ) : ℂ) • w) e5
  simp only [smul_smul, Units.mul_inv, one_smul] at e7
  exact e7.symm

end GlobalTheory.TopSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLevelAdelicTypeImpliesLiftLaw
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.LevToQ
end GlobalTheory.LevToQ

namespace GlobalTheory.LevToQ
theorem units_map_inv_val {K : Type} [Field K] (σ : K →+* ℂ) (u : Kˣ) :
    (((Units.map σ.toMonoidHom u)⁻¹ : ℂˣ) : ℂ) = σ ((u⁻¹ : Kˣ) : K) := by
  simp
end GlobalTheory.LevToQ


set_option maxHeartbeats 800000 in
theorem GlobalTheory.LevToQ.levtoq : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.models_cV → R.grp_red_L → ∀ (i : Fin D.R.m) (t : T) (Φ : Bridge.Gf (Vc D i) → (R.cV i).W), (R.cV i).ext Φ ∈ levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (datVP R i t (R.levR F false))) (levChi _ (R.βV i) (datVP R i t (R.levR F false))) → ∀ (κ : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q) (hu : (R.B.L i t).act_tie.red κ ∈ F.P0) (h : Bridge.Gf (Vc D i)), Φ (h * κ) = (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch κ : ℂˣ) : ℂ) • D.what₂.embLL ((F.ψ0⁻¹ ⟨_, hu⟩ : D.what₂.LLˣ) : D.what₂.LL) • Φ h := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hcV hred i t Φ hΦ κ hu h
  have hl := GlobalTheory.DefiniteMult.exists_fin_lift (Vc D i) (κ : Bridge.Gf (Vc D i))
  obtain ⟨k, hkG, hk⟩ := hl
  have hl' := GlobalTheory.DefiniteMult.exists_fin_lift (Vc D i) h
  obtain ⟨g, hgG, hg⟩ := hl'
  have hfk : finE (Vc D i) k = Formalism.UG.bc (swapAE D) (((κ : Bridge.Gf (Vc D i)) : GL _ _)) := by
    rw [finE_eq, ← hk]
    rfl
  have hκQ := κ.2
  have hpar : finE (Vc D i) k ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t) := by
    rw [hfk]; exact hκQ.1
  have hrt : Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k) = R.eG ((R.B.L i t).act_tie.red κ) := by
    exact (congrArg (Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t)) hfk).trans (hred i t κ).symm
  have hmem : Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k) ∈ (R.levR F false).conj.H := by
    rw [hrt]
    show R.eG.symm (R.eG ((R.B.L i t).act_tie.red κ)) ∈ F.P0
    simpa using hu
  have hkS : k ∈ levS (Vc D i) (R.βV i) (datVP R i t (R.levR F false)) :=
    ⟨hkG, hpar, hmem⟩
  have hlaw := hΦ k hkS g
  have e1 : (R.cV i).ext Φ (g * k) = Φ (h * κ) := by
    show (R.cV i).ρ (g * k)⁻¹ (Φ ((finHom (Vc D i)).rangeRestrict (g * k))) = _
    have hrr : (finHom (Vc D i)).rangeRestrict (g * k) = h * (κ : Bridge.Gf (Vc D i)) := by
      rw [map_mul, hg]
      exact congrArg (h * ·) hk
    exact (LinearMap.congr_fun ((hcV i).1 _ ((GfC _).inv_mem ((GfC _).mul_mem hgG hkG))) _).trans
      ((Module.End.one_apply _).trans (congrArg Φ hrr))
  have e2 : (R.cV i).ext Φ g = Φ h := by
    show (R.cV i).ρ g⁻¹ (Φ ((finHom (Vc D i)).rangeRestrict g)) = _
    exact (LinearMap.congr_fun ((hcV i).1 _ ((GfC _).inv_mem hgG)) _).trans
      ((Module.End.one_apply _).trans (congrArg Φ hg))
  have hchi : levChi (Vc D i) (R.βV i) (datVP R i t (R.levR F false)) k =
      (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch κ : ℂˣ) : ℂ) *
        D.what₂.embLL ((F.ψ0⁻¹ ⟨_, hu⟩ : D.what₂.LLˣ) : D.what₂.LL) := by
    have hw : (⟨R.eG.symm (Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k)), hmem⟩ : F.P0) = ⟨_, hu⟩ :=
      Subtype.ext ((congrArg R.eG.symm hrt).trans (R.eG.symm_apply_apply _))
    have c1 : levChi (Vc D i) (R.βV i) (datVP R i t (R.levR F false)) k =
        ((Formalism.L2.DIV.levFn (R.βV i) (withP (R.datVt i t) (R.levR F false).conj) (finE (Vc D i) k) : ℂˣ) : ℂ) := rfl
    have c2 := levFn_withP (V := Vc D i) (β := R.βV i) (L := R.datVt i t) (R.levR F false).conj (finE (Vc D i) k)
    have c3 := Formalism.L2.DIV.extendOne_of_mem (R.levR F false).conj.chi hmem
    have c4 : Formalism.L2.DIV.levFn (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) k) = (levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch κ :=
      congrArg (Formalism.L2.DIV.levFn (R.βV i) (flagL (R.datVt i t))) hfk
    have c5 : (((R.levR F false).conj.chi ⟨_, hmem⟩ : ℂˣ) : ℂ) =
        D.what₂.embLL ((F.ψ0⁻¹ ⟨_, hu⟩ : D.what₂.LLˣ) : D.what₂.LL) := by
      have d1 : (R.levR F false).conj.chi ⟨_, hmem⟩ = ((R.levR F false).chi ⟨_, hmem⟩)⁻¹ := rfl
      have d2 : (R.levR F false).chi ⟨_, hmem⟩ = Units.map D.what₂.embLL.toMonoidHom
          (F.ψ0 ⟨R.eG.symm (Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k)), hmem⟩) := rfl
      have d3 : (((Units.map D.what₂.embLL.toMonoidHom (F.ψ0 ⟨_, hu⟩))⁻¹ : ℂˣ) : ℂ) =
          D.what₂.embLL ((F.ψ0⁻¹ ⟨_, hu⟩ : D.what₂.LLˣ) : D.what₂.LL) :=
        (GlobalTheory.LevToQ.units_map_inv_val D.what₂.embLL (F.ψ0 ⟨_, hu⟩)).trans
          (congrArg (fun u : D.what₂.LLˣ => D.what₂.embLL (u : D.what₂.LL)) (MonoidHom.inv_apply F.ψ0 _).symm)
      exact (congrArg (fun u : ℂˣ => (u : ℂ)) (d1.trans (congrArg (·⁻¹) (d2.trans (congrArg (Units.map D.what₂.embLL.toMonoidHom) (congrArg F.ψ0 hw)))))).trans d3
    have c6 := congrArg (fun u : ℂˣ => (u : ℂ)) (c2.trans (congrArg₂ (· * ·) c3 c4))
    refine c1.trans (c6.trans ?_)
    exact (Units.val_mul _ _).trans ((congrArg (· * (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch κ : ℂˣ) : ℂ)) c5).trans (mul_comm _ _))
  calc Φ (h * κ) = (R.cV i).ext Φ (g * k) := e1.symm
    _ = levChi (Vc D i) (R.βV i) (datVP R i t (R.levR F false)) k • (R.cV i).ext Φ g := hlaw
    _ = levChi (Vc D i) (R.βV i) (datVP R i t (R.levR F false)) k • Φ h := congrArg _ e2
    _ = ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch κ : ℂˣ) : ℂ) *
        D.what₂.embLL ((F.ψ0⁻¹ ⟨_, hu⟩ : D.what₂.LLˣ) : D.what₂.LL)) • Φ h := congrArg (· • Φ h) hchi
    _ = _ := mul_smul _ _ _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLevelFramesHermitianNeZeroOffPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

open scoped ComplexOrder

namespace GlobalTheory.Mem.FramePos

open Formalism.L2.DIV

theorem majAt_XQ_ne_zero {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
    {Pl0 : Type} {B : BlockDat K G Pl0} {ℓ : Lvl K G} {v0 : InfinitePlace K} {s : ℕ}
    (h : BlockHyp B ℓ v0 s) (Z : Submodule K B.S.Forms) (v : InfinitePlace K)
    (x : Fin (B.dZ ℓ Z) → K) (hx : x ≠ 0) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (B.XQ ℓ Z) v x x ≠ 0 := by
  have hP : Function.Surjective (B.Pq ℓ Z).mulVec := fun y =>
    ⟨(B.zE ℓ Z).mulVec y, by rw [Matrix.mulVec_mulVec, (BlockDat.lf_z_proj (Z := Z) h).1, Matrix.one_mulVec]⟩
  have hpos : (quotMetC ((B.Pq ℓ Z).map v.embedding) ((B.HV ℓ).map v.embedding)).PosDef :=
    (quotRestrPosDef _ _ _ (BlockDat.lf_HV_pos h v)).1 _ (map_surj _ _ hP)
  have hf := frameOfSpec _ _ hpos
  rw [majAt_eq]
  have e : B.XQ ℓ Z v = frameOf (quotMetC ((B.Pq ℓ Z).map v.embedding) ((B.HV ℓ).map v.embedding)) := rfl
  rw [e, hf.2]
  have hne : (fun i => v.embedding (x i)) ≠ 0 := by
    intro h0
    apply hx
    funext i
    have := congrFun h0 i
    simpa using this
  exact (hpos.dotProduct_mulVec_pos hne).ne'

end GlobalTheory.Mem.FramePos


open GlobalTheory.Mem.FramePos in
theorem GlobalTheory.Mem.R3.framesBase_majAt_ne_zero : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → GlobalTheory.CuspMult.MultEq R.toRealDat → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ (i : Fin D.R.m) (v : InfinitePlace D.what₂.LL), v ≠ A3.A.v0 → ∀ x : Fin ((lv (F.fc (R.toCx3 F).zs) false).dZ i A3.A.μ0) → D.what₂.LL, x ≠ 0 → Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) ((lv (F.fc (R.toCx3 F).zs) false).XT i A3.A.μ0) v x x ≠ 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG _ _ hH _ _ i v _ x hx
  have hok := hH.ok.ok2
  have hB : Formalism.L2.DIV.BlockHyp (A3.A.fam.L i A3.A.fam.μ0) (A3.A.fam.lvlA F.P0 F.ψ0) A3.A.fam.v0 1 :=
    ⟨hok.conj, hok.irr, hok.lifts i _⟩
  exact majAt_XQ_ne_zero hB _ v x hx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockGraph
section
set_option autoImplicit false

noncomputable section

open MvPolynomial

namespace GlobalTheory.CayleyBlock

def dList {σ : Type} [DecidableEq σ] (l : List σ) : Module.End ℂ (MvPolynomial σ ℂ) :=
  (l.map fun v => ((pderiv v : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) :
    MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ)).prod

def smallList {p q : ℕ} (τ : Fin q → Equiv.Perm (Fin p)) : List (Fin p × Fin p) :=
  (List.finRange q).flatMap fun b => (List.finRange p).map fun j => (τ b j, j)

def bigList {p q : ℕ} (τ : Fin q → Equiv.Perm (Fin p)) : List (Fin q × Fin p × Fin p) :=
  (List.finRange q).flatMap fun b => (List.finRange p).map fun j => (b, τ b j, j)

def blockGraph {p q : ℕ} (τ : Fin q → Equiv.Perm (Fin p)) : Fin q × Fin p × Fin p →₀ ℕ :=
  ∑ b, ∑ j, Finsupp.single (b, τ b j, j) 1

def sumMap (p q : ℕ) : MvPolynomial (Fin p × Fin p) ℂ →ₐ[ℂ] MvPolynomial (Fin q × Fin p × Fin p) ℂ :=
  aeval fun x => ∑ b, X (b, x.1, x.2)

def blockEmb {p q : ℕ} (h1 : Fintype.card (Unit × Fin p × Fin q) = p * q) :
    Fin q × Fin p × Fin p → Fin (p * q) × Fin (p * q) :=
  fun x => (Fintype.equivFinOfCardEq h1 ((), x.2.1, x.1), Fintype.equivFinOfCardEq h1 ((), x.2.2, x.1))

def sgnProd {p q : ℕ} (τ : Fin q → Equiv.Perm (Fin p)) : ℤ := ((∏ b, Equiv.Perm.sign (τ b) : ℤˣ) : ℤ)

end GlobalTheory.CayleyBlock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CastGAMemGFset
section
open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Lev Formalism.L2.Theta NumberField MeasureTheory GlobalTheory.Mem.SJ Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ.SchurMove

theorem castGA_mem_GFset {I I' : Formalism.MainNotions.S.AutInst} (e : I = I') (x : I.GA) :
    x ∈ I.GFset ↔ Formalism.L2.SG.RowsJoinPinned.castGA e x ∈ I'.GFset := by
  subst e; rfl

theorem schur_iotaX : ∀ (D : D7) (S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar) (M : DSModel (D.sp.Y 0) S) (E : Submodule ℂ (MMap M)) (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : St.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : Formalism.IndefR.Datum.InfFam D) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)), SchurAll D → (D.sp.Y 0).SigOK → IsInfFam θ → E ≤ Mult θ M J χ → (∀ T ∈ E, ∀ T' ∈ E, ∃ c : ℂ, ∀ v v' : M.Vec, ∫ x, star (T v ((Formalism.L2.SG.RowsJoinPinned.iotaX St h).symm x * t)) * T' v' ((Formalism.L2.SG.RowsJoinPinned.iotaX St h).symm x * t) ∂(muX St) = c * ∏ τ, ⟪(v τ : M.H τ), (v' τ : M.H τ)⟫_ℂ) := by
  intro D S M E St h θ J χ t hS hsig hθ hE T hT T' hT'
  haveI := St.B.haar
  haveI := St.B.sf
  have hι : ∀ g, g ∈ GQ (D.sp.Y 0) ↔ Formalism.L2.SG.RowsJoinPinned.iotaX St h g ∈ St.B.I.GFset := by
    intro g
    rw [Formalism.IndefR.RationalEmbedding.iota_rat]
    exact castGA_mem_GFset _ _
  exact GlobalTheory.Mem.SJ.HaarMove.schur_of_bridge M θ J χ (fun μ 𝓕 => hS _ hsig S θ M J χ μ 𝓕) hθ St.B.I St.B.μf
    St.B.fund St.B.fund_spec (Formalism.L2.SG.RowsJoinPinned.iotaX St h) hι t T (hE hT) T' (hE hT')

end GlobalTheory.Mem.SJ.SchurMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernCurvatureInvOneSubConjMulTransposeAtZero
section
open scoped Matrix

namespace GlobalTheory.HermFrame

open Matrix Filter Topology

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {m l : Type*} [Fintype m] [DecidableEq m] [Fintype l]

theorem curv_inv_one_sub_mul {P : E → Matrix m l ℂ} {Q : E → Matrix l m ℂ} {z ξ η : E}
    {C : Matrix l m ℂ} (hP : ∀ x, MContDiffAt 2 P x) (hQ : ∀ x, MContDiffAt 2 Q x)
    (hP0 : P z = 0) (hdP : ∀ x, mdel P x ξ = 0) (hdQ : ∀ x, mdel Q x ξ = C) :
    curv (fun x => (1 - P x * Q x)⁻¹) z ξ η = -(mdbar P z η * C)ᵀ := by
  have hK : ∀ x, MContDiffAt 2 (fun x => 1 - P x * Q x) x :=
    fun x => (mContDiffAt_const 1).sub ((hP x).mul (hQ x))
  have hK0 : (1 - P z * Q z) = 1 := by rw [hP0]; simp
  have hd : ∀ x, mdel (fun x => 1 - P x * Q x) x ξ = -(P x * C) := fun x => by
    have h1 := (hP x).of_le one_le_two
    have h2 := (hQ x).of_le one_le_two
    simp only [sub_eq_add_neg]
    rw [mdel_add (mContDiffAt_const 1) (h1.mul h2).neg, mdel_neg, mdel_mul h1 h2, hdP, hdQ]
    simp
  have hdd : mddbar (fun x => 1 - P x * Q x) z ξ η = -(mdbar P z η * C) := by
    rw [← mdbar_mdel (hK z)]
    simp only [hd]
    rw [mdbar_neg, mdbar_mul ((hP z).of_le one_le_two) (mContDiffAt_const C)]
    simp
  have hu : IsUnit (1 - P z * Q z)ᵀ.det := by rw [hK0]; simp
  have e : (fun x => (1 - P x * Q x)⁻¹) = fun x => dualGram (1 - P x * Q x)ᵀ := by
    funext x; rw [dualGram, transpose_nonsing_inv, transpose_transpose]
  rw [e, curv_dual (hK z).transpose hu, curv_eq (hK z).transpose hu,
    mdel_transpose (fun x => 1 - P x * Q x), hd,
    show mddbar (fun x => (1 - P x * Q x)ᵀ) z ξ η = (mddbar (fun x => 1 - P x * Q x) z ξ η)ᵀ from rfl,
    hdd, hK0, hP0]
  simp

end

section

variable {n : ℕ} {a b : Type*}

theorem mContDiffAt_coordMatrix (f : a → b → Fin n) (w : ReciprocityTheory.L2DbarEstimates.V n) :
    MContDiffAt 2 (fun u : ReciprocityTheory.L2DbarEstimates.V n => Matrix.of fun i j => u (f i j)) w := fun i j =>
  ((EuclideanSpace.proj (𝕜 := ℂ) (f i j)).restrictScalars ℝ).contDiff.contDiffAt

theorem mdel_coordMatrix (f : a → b → Fin n) (w ξ : ReciprocityTheory.L2DbarEstimates.V n) :
    mdel (fun u : ReciprocityTheory.L2DbarEstimates.V n => Matrix.of fun i j => u (f i j)) w ξ =
      Matrix.of fun i j => ξ (f i j) := by
  ext i j
  let L : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] ℂ := EuclideanSpace.proj (𝕜 := ℂ) (f i j)
  change del L w ξ = L ξ
  rw [del_eq_fderiv L.differentiableAt, L.fderiv]

theorem mdbar_coordMatrix (f : a → b → Fin n) (w ξ : ReciprocityTheory.L2DbarEstimates.V n) :
    mdbar (fun u : ReciprocityTheory.L2DbarEstimates.V n => Matrix.of fun i j => u (f i j)) w ξ = 0 := by
  have h := mdel_add_mdbar (fun u : ReciprocityTheory.L2DbarEstimates.V n => Matrix.of fun i j => u (f i j)) w ξ
  rw [mdel_coordMatrix] at h
  rw [← add_right_inj (Matrix.of fun i j => ξ (f i j)), h, add_zero]
  ext i j
  let L : ReciprocityTheory.L2DbarEstimates.V n →L[ℝ] ℂ := (EuclideanSpace.proj (𝕜 := ℂ) (f i j)).restrictScalars ℝ
  change fderiv ℝ L w ξ = L ξ
  rw [L.fderiv]

end

theorem curv_inv_one_sub_conj_mul_transpose_zero : ∀ {n r s : ℕ} (f g : Fin r → Fin s → Fin n) (ξ η : ReciprocityTheory.L2DbarEstimates.V n), GlobalTheory.HermFrame.curv (fun u : ReciprocityTheory.L2DbarEstimates.V n => (1 - (Matrix.of fun i j => u (f i j)).map (starRingEnd ℂ) * (Matrix.of fun i j => u (g i j))ᵀ)⁻¹) 0 ξ η = -((Matrix.of fun i j => ξ (g i j)) * (Matrix.of fun i j => η (f i j))ᴴ) := by
  intro n r s f g ξ η
  let Z : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin r) (Fin s) ℂ := fun u => Matrix.of fun i j => u (f i j)
  let W : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin r) (Fin s) ℂ := fun u => Matrix.of fun i j => u (g i j)
  have h := curv_inv_one_sub_mul (P := fun u => (Z u)ᴴᵀ) (Q := fun u => (W u)ᵀ) (z := 0) (ξ := ξ)
    (η := η) (C := (W ξ)ᵀ) (fun x => (mContDiffAt_coordMatrix f x).conjTranspose.transpose)
    (fun x => (mContDiffAt_coordMatrix g x).transpose) (by ext i j; simp [Z])
    (fun x => by
      rw [mdel_transpose (fun u => (Z u)ᴴ), mdel_conjTranspose, mdbar_coordMatrix]; simp)
    (fun x => by rw [mdel_transpose W, mdel_coordMatrix])
  rw [mdbar_transpose (fun u => (Z u)ᴴ), mdbar_conjTranspose, mdel_coordMatrix, ← transpose_mul,
    transpose_transpose] at h
  exact h

end GlobalTheory.HermFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernTopFormNegativePartEqZeroOfNonnegOnOpen
section
open AlgebraicGeometry CategoryTheory MvPolynomial MeasureTheory
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric

namespace GlobalTheory

theorem iSup_measure_apply_eq_zero {α κ : Type*} [MeasurableSpace α] (μ : κ → Measure α) {S : Set α}
    (hS : MeasurableSet S) (h : ∀ i, μ i S = 0) : (⨆ i, μ i) S = 0 := by
  have hle : (⨆ i, μ i) ≤ (⨆ i, μ i).restrict Sᶜ := by
    refine iSup_le fun i => ?_
    calc μ i = (μ i).restrict Sᶜ :=
          (Measure.restrict_eq_self_of_ae_mem (measure_eq_zero_iff_ae_notMem.1 (h i))).symm
      _ ≤ (⨆ i, μ i).restrict Sᶜ := Measure.restrict_mono subset_rfl (le_iSup μ i)
  refine le_antisymm ?_ (zero_le)
  calc (⨆ i, μ i) S ≤ (⨆ i, μ i).restrict Sᶜ S := Measure.le_iff'.1 hle S
    _ = 0 := by rw [Measure.restrict_apply hS, Set.inter_compl_self, measure_empty]

theorem chernTopPart_neg_eq_zero_of_nonneg {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {ι : Type} {m : ι → ℕ}
    (E : Fr (ratOf X) m 0) (O : X.X.Opens) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ)
    (R : MvPolynomial (ι × ℕ) ℝ)
    (h : ∀ y ∈ ptsIn X.str σ O, ∀ c : AlgChart X.str σ X.dim, y ∈ c.e.source → ∀ A ∈ E.S (under y),
      0 ≤ chernTop R (fun w => H A (c.e.symm w)) (c.e y)) :
    chernTopPart E H R (-1) (ptsIn X.str σ O) = 0 := by
  have hS : MeasurableSet (ptsIn X.str σ O) := (isOpen_ptsIn O).measurableSet
  unfold chernTopPart glueMeas
  refine iSup_measure_apply_eq_zero _ hS fun c => ?_
  rw [chartMeas_apply c.e _ hS]
  have hm : MeasurableSet (c.e '' (c.e.source ∩ ptsIn X.str σ O)) :=
    measurableSet_image c.e (c.e.open_source.measurableSet.inter hS) Set.inter_subset_left
  rw [setLIntegral_congr_fun hm (g := fun _ => 0) ?_, MeasureTheory.lintegral_zero]
  rintro _ ⟨y, ⟨hys, hyS⟩, rfl⟩
  have hz : c.e.symm (c.e y) ∈ c.e.source ∩ ptsIn X.str σ O := by
    rw [c.e.left_inv hys]; exact ⟨hys, hyS⟩
  beta_reduce
  generalize c.e.symm (c.e y) = z at hz ⊢
  apply ENNReal.ofReal_eq_zero.2
  have := h z hz.2 c hz.1 _ (E.nonempty (under z)).choose_spec
  push_cast
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionGroupLocalGaloisIsoStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decomposition_group_local_galois_iso : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (ι : Ω →ₐ[E] Kbar w), IsLocEmb A w ι → ∃ θ : Dec (F := E) A ≃* GalLoc w, Continuous θ ∧ Continuous θ.symm ∧ ∀ σ : Dec (F := E) A, Lifts ι (θ σ) (σ : G E Ω) := by
  first | exact @GlobalTheory.LocDec.decomposition_mulEquiv_galLoc | exact GlobalTheory.LocDec.decomposition_mulEquiv_galLoc | (intros; apply GlobalTheory.LocDec.decomposition_mulEquiv_galLoc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryAdmissibleFiniteMultiplicityStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitary_admissible_finiteMultiplicity : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n), (∀ K : Subgroup (finU (E := E) (n := n)), IsOpen (K : Set (finU (E := E) (n := n))) → FiniteDimensional ℂ (fixed (π.rep.comp (finU (E := E) (n := n)).subtype) K)) ∧ FiniteDimensional ℂ (π.rep.IntertwiningMap (autRep E n)) := by
  first | exact @GlobalTheory.DefU.admitted.admissible_finiteMult | exact GlobalTheory.DefU.admitted.admissible_finiteMult | (intros; apply GlobalTheory.DefU.admitted.admissible_finiteMult <;> assumption)
end

