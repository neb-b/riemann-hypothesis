module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0711
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0310
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0231
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulAntiOfUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveRationalInvariant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0008
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1220
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdSubConjEqNeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationSplitSupportProjectsVacuum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0294
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0329
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixCoeffRightTranslateDefiniteFormScalar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

noncomputable section

namespace GlobalTheory.Core.Rk.RealCoef

open scoped ComplexConjugate ComplexOrder

theorem petersson_conj {D : D7} {V : HSp D} (m : Measure (GA D V)) (φ ψ : GA D V → ℂ) :
    GlobalTheory.Cusp.petersson V m φ ψ = conj (GlobalTheory.Cusp.petersson V m ψ φ) := by
  simp only [GlobalTheory.Cusp.petersson, GlobalTheory.AutomorphicL2Unitary.pet]
  rw [← integral_conj]
  congr 1
  funext q
  simp [mul_comm]

theorem rcoef_of_fun {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) (m : Measure (GA D V)) (hm : m.IsHaarMeasure)
    (Y : GA D V → c.W) (hYc : Continuous Y) (hYi : ∀ γ ∈ GQ V, ∀ h, Y (γ * h) = Y h) {K : Set (GA D V)}
    (hK : IsCompact K) (hKc : ∀ h, ∃ γ ∈ GQ V, ∃ k ∈ K, h = γ * k)
    (hsh : ∀ b ∈ GinfC V, ∀ g, Y (g * b) = c.ρ b⁻¹ (Y g)) :
    ∃ z : ℂ, (∀ w : c.W, ∀ b ∈ GinfC V,
      GlobalTheory.Core.Rk.IP.rcoef m (fun g => ⟪w, Y g⟫_ℂ) (fun g => ⟪w, Y g⟫_ℂ) b = z * ⟪c.ρ b w, w⟫_ℂ) ∧ (Y ≠ 0 → z ≠ 0) := by
  haveI := hm
  haveI : m.IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds V m hm
  let φ : c.W → GA D V → ℂ := fun x g => ⟪x, Y g⟫_ℂ
  have hφL : ∀ x, GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) (φ x) := fun x γ hγ g => by
    simp only [φ, hYi γ hγ g]
  have hφc : ∀ x, Continuous (φ x) := fun x => continuous_const.inner hYc
  have hφ2 : ∀ x, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GQ V) m (φ x) := fun x => by
    obtain ⟨C, hCb⟩ := hK.exists_bound_of_continuousOn (hφc x).continuousOn
    refine GlobalTheory.Cusp.memL2_of_bounded_continuous_invariant (hφL x) (hφc x) (C := C) fun h => ?_
    obtain ⟨γ, hγ, k, hk, e⟩ := hKc h
    rw [e, hφL x γ hγ k]
    exact hCb k hk
  have hshift : ∀ b ∈ GinfC V, ∀ x, rTr V b (φ x) = φ (c.ρ b x) := by
    intro b hb x
    funext g
    show ⟪x, Y (g * b)⟫_ℂ = ⟪c.ρ b x, Y g⟫_ℂ
    rw [hsh b hb g, ← hc.2.1 b x (c.ρ b⁻¹ (Y g)), GlobalTheory.DefiniteEnd.rho_inv_cancel]
  have hadd : ∀ x x', φ (x + x') = φ x + φ x' := fun x x' => funext fun g => inner_add_left _ _ _
  have hsmul : ∀ (a : ℂ) x, φ (a • x) = (starRingEnd ℂ a) • φ x := fun a x => funext fun g => inner_smul_left _ _ _
  let B : c.W →ₗ⋆[ℂ] c.W →ₗ[ℂ] ℂ := LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun x x' => GlobalTheory.Cusp.petersson V m (φ x) (φ x'))
    (fun x x' y => by rw [hadd]; exact GlobalTheory.Cusp.petersson_add_left (hφ2 x) (hφ2 x') (hφ2 y))
    (fun a x y => by rw [hsmul]; exact GlobalTheory.Cusp.petersson_smul_left _ _ _)
    (fun x y y' => by
      rw [petersson_conj m (φ x) (φ (y + y')), hadd, GlobalTheory.Cusp.petersson_add_left (hφ2 y) (hφ2 y') (hφ2 x), map_add (f := _),
        ← petersson_conj m (φ x) (φ y), ← petersson_conj m (φ x) (φ y')])
    (fun a x y => by
      rw [petersson_conj m (φ x) (φ (a • y)), hsmul, GlobalTheory.Cusp.petersson_smul_left, map_mul,
        ← petersson_conj m (φ x) (φ y), Complex.conj_conj, RingHom.id_apply, smul_eq_mul])
  have hB : ∀ x x', B x x' = GlobalTheory.Cusp.petersson V m (φ x) (φ x') := fun _ _ => rfl
  have hinv : ∀ u ∈ GinfC V, ∀ x x', B (c.ρ u x) (c.ρ u x') = B x x' := by
    intro u hu x x'
    rw [hB, hB, ← hshift u hu, ← hshift u hu]
    exact GlobalTheory.Cusp.petersson_rTr (hφ2 x) (hφ2 x') u
  obtain ⟨z, hz⟩ := _root_.GlobalTheory.CoefRealSchur.form_eq_smul_inner D V c hc B hinv
  refine ⟨z, fun w b hb => ?_, fun hY hz0 => ?_⟩
  · show GlobalTheory.Cusp.petersson V m (rTr V b (φ w)) (φ w) = _
    rw [hshift b hb, ← hB]
    exact hz _ _
  · apply hY
    have h0 : ∀ x, φ x = 0 := by
      intro x
      by_contra hne
      have hpos := GlobalTheory.Cusp.petersson_self_pos (hφ2 x) (hφc x) hne
      have h1 : GlobalTheory.Cusp.petersson V m (φ x) (φ x) = 0 := by
        rw [← hB, hz x x, hz0, zero_mul]
      rw [h1, Complex.zero_re] at hpos
      exact lt_irrefl _ hpos
    funext g
    exact inner_self_eq_zero.1 (congrFun (h0 (Y g)) g)


set_option maxHeartbeats 1000000 in
theorem rcoef_scalar : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (m : Measure (GA D (Vc D i))), m.IsHaarMeasure → ∃ z : ℂ, (∀ (w : (R.cV i).W), ∀ b ∈ GinfC (Vc D i), GlobalTheory.Core.Rk.IP.rcoef m (fun g => ⟪w, R.extV i t y g⟫_ℂ) (fun g => ⟪w, R.extV i t y g⟫_ℂ) b = z * ⟪(R.cV i).ρ b w, w⟫_ℂ) ∧ (y ≠ 0 → z ≠ 0) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC i t y m hm
  have hmod := hC.models
  have hc : (R.cV i).Is := hmod.cV i
  have hx := (hmod.HV i t).2.1.le (LinearMap.mem_range_self _ y)
  have hp : (Vc D i).IsPosDef := hmod.vpos i
  have hpd : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ =>
    GlobalTheory.RepsObj.gramAt_posDef hp (D.sp.V_sig ((i : ℕ) + 1)) τ
  obtain ⟨K, hK, hKc⟩ := GlobalTheory.definite_unitary_cocompact (Vc D i) hpd
  have hYc : Continuous (R.extV i t y) := GlobalTheory.ThetaIntegrand.ext_continuous (R.cV i) hc (R.βV i) (R.datVt i t) hx
  have hYi : ∀ γ ∈ GQ (Vc D i), ∀ h, R.extV i t y (γ * h) = R.extV i t y h := GlobalTheory.ThetaIntegrand.ext_invariant (R.cV i) hx
  have hsh : ∀ b ∈ GinfC (Vc D i), ∀ g, R.extV i t y (g * b) = (R.cV i).ρ b⁻¹ (R.extV i t y g) :=
    fun b hb g => GlobalTheory.DownLift.DefiniteComp.extV_mul_inf R i t y hb g
  have key := rcoef_of_fun (R.cV i) hc m hm (R.extV i t y) hYc hYi hK hKc hsh
  refine ⟨key.choose, key.choose_spec.1, fun hy => key.choose_spec.2 fun hY0 => hy ?_⟩
  have hf0 : (R.HV i t).e y = 0 := by
    funext k
    obtain ⟨g, rfl⟩ := (finHom (Vc D i)).rangeRestrict_surjective k
    have e : (R.cV i).ρ g⁻¹ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict g)) = 0 := congrFun hY0 g
    have e2 := congrArg ((R.cV i).ρ g) e
    rw [GlobalTheory.DefiniteEnd.rho_inv_cancel] at e2
    exact e2.trans (LinearMap.map_zero _)
  exact (hmod.HV i t).1 (hf0.trans ((R.HV i t).e.map_zero).symm)

end GlobalTheory.Core.Rk.RealCoef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemCuspFormsIffAutomorphicCompact
section
noncomputable section

namespace GlobalTheory.Core.Rk.DownCompare

open scoped ComplexConjugate Matrix ComplexOrder Pointwise TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff)
open GlobalTheory.Core.Rk.IP (WRep up wcoef rcoef)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lattices

open Formalism.L2.DIV

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

end Lattices

variable {D : D7}

def latIn (V : HSp D) (L : Lat V) : Submodule (𝓞 D.host.E) V.V :=
  L.map (V.frame.equivFun.symm.toLinearMap.restrictScalars (𝓞 D.host.E))

theorem mem_latIn {V : HSp D} {L : Lat V} {x : V.V} : x ∈ latIn V L ↔ V.frame.equivFun x ∈ L :=
  ⟨by rintro ⟨y, hy, rfl⟩; exact (V.frame.equivFun.apply_symm_apply y).symm ▸ hy, fun h => ⟨_, h, V.frame.equivFun.symm_apply_apply x⟩⟩

theorem hT_eq (V : HSp D) (x y : V.V) :
    V.hT x y = ∑ i, ∑ j, star (V.frame.equivFun x i) * V.gram i j * V.frame.equivFun y j := by
  conv_lhs => rw [← V.frame.sum_equivFun x, ← V.frame.sum_equivFun y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, HSpace.gram,
    Finset.mul_sum, starRingEnd_apply, RingHom.id_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem latIn_lat {V : HSp D} {L : Lat V} (h : IsSelfDualC V L) : Submodule.IsLattice D.host.E (latIn V L) :=
  Submodule.IsLattice.of_fg D.host.E (h.1.fg.map _)

theorem latIn_unimod {V : HSp D} {L : Lat V} (h : IsSelfDualC V L) : Formalism.HermitianLatticesTheory.IsUnimodular V.hT (latIn V L) := by
  ext y
  rw [mem_latIn, h.2]
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, Submodule.mem_one,
    LinearMap.restrictScalars_apply]
  constructor
  · intro hy x hx
    obtain ⟨b, hb⟩ := hy _ (mem_latIn.2 (by rwa [LinearEquiv.apply_symm_apply] : V.frame.equivFun (V.frame.equivFun.symm x) ∈ L))
    exact ⟨b, by rw [hT_eq, LinearEquiv.apply_symm_apply] at hb; exact hb⟩
  · intro hy x hx
    obtain ⟨b, hb⟩ := hy _ (mem_latIn.1 hx)
    exact ⟨b, by rw [hT_eq]; exact hb⟩

def reset (V : HSp D) (L : Lat V) (h : IsSelfDualC V L) (s : (D.host.E →+* ℂ) → ℕ × ℕ) : HSp D :=
  { V with sig := s, L0 := latIn V L, standardTuple_isLattice := latIn_lat h, baseLattice_isUnimodular := latIn_unimod h }

theorem frameLat_reset (V : HSp D) (L : Lat V) (h : IsSelfDualC V L) (s : (D.host.E →+* ℂ) → ℕ × ℕ) :
    frameLat (reset V L h s) = L := by
  ext x
  exact (mem_latIn (V := V) (L := L) (x := V.frame.equivFun.symm x)).trans (by rw [V.frame.equivFun.apply_symm_apply x]; rfl)

section Transport

variable {ψ : AddChar (AF D.host.F) ℂ} {A W : HSp D} {LA : Lat A} {LW : Lat W} (hA : IsSelfDualC A LA) (hW : IsSelfDualC W LW)
  (sA sW : (D.host.E →+* ℂ) → ℕ × ℕ)

end Transport

end GlobalTheory.Core.Rk.DownCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedVacuumInvariantRationalFiniteParts
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.VacAllRat

theorem moveT_rat : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) vac, IsVacO ψ θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) vac → ∀ (a : I.ι) μ om, ChrEq μ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → IsWeilDatumO ψ _ _ μ μ om → ∀ c₀ g h, g ∈ GfC _ → h ∈ GfC _ → GlobalTheory.AdForm.VacAll.MoveT I l Z θ i hi c₀ μ om vac (g) (h) → ∀ r r', IsRatFin _ r → IsRatFin _ r' → GlobalTheory.AdForm.VacAll.MoveT I l Z θ i hi c₀ μ om vac (r * g) (r' * h) := by
  intro B X I hI hP l Z ψ θ hψ hθ i hi vac hvac a μ om hμ hom c₀ g h hg hh H r r' hr hr'
  have hp := (GlobalTheory.AdForm.StdStepsT.stdPair_steps_all I hI hP l Z ψ θ hψ hθ).1 i hi
  have htw := (GlobalTheory.Mem.ReadTwist.isTwist_of_reads B.R B.host _ B.embLL I.S (I.tup a) (I.xi a) (hI.xi_reads a)).1
  obtain ⟨n, hn, hord⟩ := htw.1
  choose e he using fun τ => (B.hc τ).e_int ⟨i, hi⟩
  have hinf := Formalism.L2.Host.HChar.HasInfQ.mul_triv (I.C.isMu0 ⟨i, hi⟩).inf
    (Formalism.L2.Host.HChar.inf_eq_one_of_order hn hord)
  have hexp := (GlobalTheory.HeckeInfExp.hasInfExp_iff_hasInfQ (I.rec7 l Z) _ _ _ hμ).2 hinf
  have hv := hvac.2
  exact GlobalTheory.AdForm.RatMove.move_rat _ _ hp hom (fun τ => -e τ) (fun τ => by
      have e1 : ((-e τ : ℤ) : ℚ) = -(B.hc τ).e ⟨i, hi⟩ := by rw [Int.cast_neg, ← he τ]
      exact e1 ▸ hexp τ) ⟨hv.theta, hv.fock⟩ (Th.VacIn.toRec (D := I.rec7 l Z) I.J.V)
    (GlobalTheory.AdForm.RatMove.curveIdeal_top _) hI.amb_ok.delta c₀ hg hh H hr hr'

end GlobalTheory.AdForm.VacAllRat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedVacuumInvariantUnderSingleSplitPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.AdForm.VacSplit

open Formalism.L2.Th1.H

theorem inter_ne_zero {V : Type} [AddCommGroup V] [Module ℂ V] {H : Sesq V} {α : V → ℂ} {A₁ A₂ : AddSubgroup V} {F : V → ℂ}
    (h : inter H α A₁ A₂ F ≠ 0) : relIdx A₁ A₂ ≠ 0 := by
  intro h0
  apply h
  funext z
  simp [inter, h0]

theorem inter_zero {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A₁ A₂ : AddSubgroup V) :
    inter H α A₁ A₂ 0 = 0 := by
  funext z
  simp [inter, opU]

theorem inter_const_mul {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A₁ A₂ : AddSubgroup V)
    (c : ℂ) (F : V → ℂ) (z : V) : inter H α A₁ A₂ (fun w => c * F w) z = c * inter H α A₁ A₂ F z := by
  unfold inter
  have e : ∀ q : A₂ ⧸ A₁.addSubgroupOf A₂, α ((Quotient.out q : A₂) : V) * opU H ((Quotient.out q : A₂) : V) (fun w => c * F w) z =
      c * (α ((Quotient.out q : A₂) : V) * opU H ((Quotient.out q : A₂) : V) F z) := fun q => by
    simp only [opU]; ring
  simp only [e]
  rw [← mul_finsum]
  ring

theorem mem_LamC_toHom {D : D7} (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ)
    (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E))
    (z : VCx D.what₂.Tau a b) (hz : z ∈ LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') :
    ∃ γ, z = embH (tauE D) δ (toHom S T hS hT γ) := by
  obtain ⟨x, -, rfl⟩ := hz
  refine ⟨(LinearMap.toMatrix' x).reindex (finCongr hT).symm (finCongr hS).symm, ?_⟩
  congr 1
  subst hS hT
  simp [toHom]

end GlobalTheory.AdForm.VacSplit

namespace GlobalTheory.AdForm.VacSplit

open GlobalTheory.ThetaMove Formalism.L2.Th1.H


set_option maxHeartbeats 1600000 in
theorem moveT_split : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) vac, IsVacO ψ θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) vac → ∀ (a : I.ι) μ om, ChrEq μ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → IsWeilDatumO ψ _ _ μ μ om → ∀ c₀ g h, g ∈ GfC _ → h ∈ GfC _ → GlobalTheory.AdForm.VacAll.MoveT I l Z θ i hi c₀ μ om vac (g) (h) → ∀ e, IsSplitIdem (I.rec7 l Z) e → ∀ s s', SuppAt e _ s → SuppAt e _ s' → GlobalTheory.AdForm.VacAll.MoveT I l Z θ i hi c₀ μ om vac (s * g) (s' * h) := by
  intro B X I hI hP l Z ψ θ hψ hθ i hi vac0 hvac _a μ om _hμ hW c₀ g h hg hh hmv e he s s' hs hs'
  intro N₁ N₁' hN₁ hN₁' x₁ y₁ hx₁ hy₁
  have hi0 : i ≤ B.R.m := Nat.le_of_succ_le hi
  obtain ⟨hstdAll, -, hemb, -, hroot⟩ := GlobalTheory.AdForm.StdStepsT.stdPair_steps_all I hI hP l Z ψ θ hψ hθ
  have hstd := hstdAll i hi
  have hAA : I.A.AA = ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) := I.A_AA
  have hSr := rankN (I.rec7 l Z) i hi0
  have hTr := rankN (I.rec7 l Z) (i + 1) hi
  obtain ⟨N, hN⟩ := (_root_.GlobalTheory.StdMove.std_moved_lattice _ _ _ hSr hstd.gS).1 g
  obtain ⟨N', hN'⟩ := (_root_.GlobalTheory.StdMove.std_moved_lattice _ _ _ hTr hstd.gT).1 h
  obtain ⟨x, hx⟩ := hroot _ g
  obtain ⟨y, hy⟩ := hroot _ h
  have key := hmv N N' hN hN' x y hx hy
  have hsG : s ∈ GfC _ := GlobalTheory.WeilProduct.mem_GfC_of_suppAt he hs
  have hs'G : s' ∈ GfC _ := GlobalTheory.WeilProduct.mem_GfC_of_suppAt he hs'
  have xv := fun g₀ (hg₀ : g₀ ∈ GfC _) h₀ (hh₀ : h₀ ∈ GfC _) M M' (hM : Moves _ hSr g₀ M) (hM' : Moves _ hTr h₀ M') =>
    _root_.GlobalTheory.MovedVac.vac_moved (I.rec7 l Z) ψ θ _ _ _ _ hSr hTr I.A.δ I.A.sc hstd (μ) (om) hW (vac0) hvac g₀ hg₀ h₀ hh₀ M M' hM hM'

  have hX := GlobalTheory.Mem.FieldsLaws.fields_ok B
  have hcc : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal (I.rec7 l Z) ⊤ := ⟨top_ne_bot, by simp⟩
  have hδ := ((I.J.ok_iff B (I.cols l) Z.W Z.V Z.S Z.N Z.G).1 hI.amb_ok).1
  have hχ := GlobalTheory.Mem.ChiIdeal.isChi_chiId (I.rec7 l Z) I.C.chiPsi I.C.isChi
  have hE := (GlobalTheory.Core.Ht2.family_laws I hI hX l Z).1
  have hfam := GlobalTheory.NatFamily.family (I.rec7 l Z) ⊤ I.J.δ (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi hcc hδ hχ
  have ha : Even (B.R.N i) := hSr ▸ hstd.rk.2.2.1
  have hb : Even (B.R.N (i + 1)) := hTr ▸ hstd.rk.2.2.2
  have hMv : GlobalTheory.ThetaMove.Moves I.A (B.R.N i) (B.R.N (i + 1)) := by
    show GlobalTheory.ThetaMove.Moves (I.J.amb B I.chi) _ _
    rw [AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G]
    exact GlobalTheory.ThetaMove.SeamMoves.moves_ambOf B.fields _ (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) ⊤ I.J.δ
      (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi I.J.cD _ _ hX (seamOf_ok B (I.cols l) Z.W Z.V Z.S Z.N Z.G) hcc hχ hE
      hfam.2.1 (hfam.2.2 _ _) ha hb
  have hemb' : B.fields.embC I.A.σ₀ = tauE (I.rec7 l Z) := funext hemb
  have hlam : ∀ M M', lam I.A (a := B.R.N i) (b := B.R.N (i + 1)) M M' =
      LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) M M' := by
    intro M M'
    show LamC (B.fields.embC I.A.σ₀) I.A.δ I.A.AA M M' = _
    rw [hemb', hAA]
    rfl
  have hvacT : ∀ M M', Formalism.L2.Col.IsSdLat M → Formalism.L2.Col.IsSdLat M' →
      vac I.A (a := B.R.N i) (b := B.R.N (i + 1)) M M' = I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) M M' := by
    intro M M' hM hM'
    funext z
    exact inv_mul_cancel_left₀ (hMv.2.2.2.2.1 M M' hM hM').1 _
  obtain ⟨hNsd, ΛS, hcS, hΛS⟩ := (_root_.GlobalTheory.StdMove.std_moved_lattice _ _ _ hSr hstd.gS).2 g N hN
  obtain ⟨hN'sd, ΛT, hcT, hΛT⟩ := (_root_.GlobalTheory.StdMove.std_moved_lattice _ _ _ hTr hstd.gT).2 h N' hN'
  obtain ⟨hN₁sd, ΛS₁, hcS₁, hΛS₁⟩ := (_root_.GlobalTheory.StdMove.std_moved_lattice _ _ _ hSr hstd.gS).2 (s * g) N₁ hN₁
  obtain ⟨hN₁'sd, ΛT₁, hcT₁, hΛT₁⟩ := (_root_.GlobalTheory.StdMove.std_moved_lattice _ _ _ hTr hstd.gT).2 (s' * h) N₁' hN₁'
  have v0 := xv g hg h hh N N' hN hN'
  have v1 := xv (s * g) (mul_mem hsG hg) h hh N₁ N' hN₁ hN'
  have v2 := xv (s * g) (mul_mem hsG hg) (s' * h) (mul_mem hs'G hh) N₁ N₁' hN₁ hN₁'
  have hc1 : om (s, 1) (om (g, h) (vac0)) = om (s * g, h) (vac0) := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
  have hc2 : om (1, s') (om (s * g, h) (vac0)) = om (s * g, s' * h) (vac0) := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
  have hth0 : I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N N' ≠ 0 := by
    intro h0
    apply v0.2.2
    refine key.trans (funext fun z => ?_)
    show _ = (0 : ℂ)
    rw [h0, Pi.zero_apply, mul_zero]
  have hv1 : I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N₁ N' ≠ 0 := by
    intro h0
    apply hth0
    rw [← hvacT N N' hNsd hN'sd, hMv.2.2.2.2.2.2 N₁ N N' hN₁sd hNsd hN'sd, hvacT N₁ N' hN₁sd hN'sd, h0, inter_zero]
  have hv2 : I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N₁ N₁' ≠ 0 := by
    intro h0
    apply hv1
    rw [← hvacT N₁ N' hN₁sd hN'sd, hMv.2.2.2.2.2.1 N₁ N₁' N' hN₁sd hN₁'sd hN'sd, hvacT N₁ N₁' hN₁sd hN₁'sd, h0, inter_zero]
  have hrel1 : relIdx (lam I.A (a := B.R.N i) (b := B.R.N (i + 1)) N N') (lam I.A N₁ N') ≠ 0 := by
    apply inter_ne_zero (H := HV I.A.sc) (α := alV I.A.d I.A.sc) (F := vac I.A (a := B.R.N i) (b := B.R.N (i + 1)) N N')
    rw [← hMv.2.2.2.2.2.2 N N₁ N' hNsd hN₁sd hN'sd, hvacT N₁ N' hN₁sd hN'sd]
    exact hv1
  have hrel2 : relIdx (lam I.A (a := B.R.N i) (b := B.R.N (i + 1)) N₁ N') (lam I.A N₁ N₁') ≠ 0 := by
    apply inter_ne_zero (H := HV I.A.sc) (α := alV I.A.d I.A.sc) (F := vac I.A (a := B.R.N i) (b := B.R.N (i + 1)) N₁ N')
    rw [← hMv.2.2.2.2.2.1 N₁ N' N₁' hN₁sd hN'sd hN₁'sd, hvacT N₁ N₁' hN₁sd hN₁'sd]
    exact hv2
  rw [hlam N N', hlam N₁ N'] at hrel1
  rw [hlam N₁ N', hlam N₁ N₁'] at hrel2
  have hfacts : ∀ (M : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin (B.R.N i) → (I.rec7 l Z).host.E)) (M' : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin (B.R.N (i + 1)) → (I.rec7 l Z).host.E)), Formalism.L2.Col.IsSdLat M → Formalism.L2.Col.IsSdLat M' →
      IsSelfDual (HV I.A.sc) (LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) M M') ∧
      IsSemiChar (HV I.A.sc) (LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) M M')
        (alV (I.rec7 l Z).host.d I.A.sc) := by
    intro M M' hM hM'
    have := (hMv.2.2.2.2.1 M M' hM hM').2.2
    rw [← hlam M M']
    exact this
  haveI : Nonempty (I.rec7 l Z).what₂.Tau := Fintype.card_pos_iff.1 hX.f_pos
  have hinj := GlobalTheory.ThetaMove.embH_injective (a := B.R.N i) (b := B.R.N (i + 1)) (tauE (I.rec7 l Z)) hstd.ne
  have memL : ∀ (M : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin (B.R.N i) → (I.rec7 l Z).host.E)) (M' : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin (B.R.N (i + 1)) → (I.rec7 l Z).host.E)) x, embH (tauE (I.rec7 l Z)) I.A.δ x ∈
      LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) M M' ↔
      x ∈ perO ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) M M' := by
    intro M M' x
    exact ⟨fun ⟨y, hy, e⟩ => hinj e ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.AdTh.SplitClass.exists_detAt _ he.1 s
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.AdTh.SplitClass.exists_detAt _ he.1 s'
  have st1 := GlobalTheory.T.splitPlacePair_moves_latticeVacuumReading (I.rec7 l Z) ψ θ _ _ _ _ hSr hTr I.A.δ I.A.sc hstd (μ) (om) hW ΛS ΛS₁ ΛT ΛT hΛS hΛS₁
    hΛT hΛT e he s 1 hs (GlobalTheory.LeviSplitChar.suppAt_one e _) x₀ 1 hx₀ (GlobalTheory.LeviSplitChar.isDetAt_one e _)
    (by rw [hcS, hcS₁, hcT]; exact _root_.GlobalTheory.LatPairMove.latO_move _ _ _ _ _ hSr hTr g s h 1 N N' N₁ N' hN hN' hN₁ (by rwa [one_mul]))
    _ _ (fun γ v hv => by rw [hcS, hcT]; exact (_root_.GlobalTheory.AdForm.RatLat.finOf_mem_iff _ ψ θ _ _ _ _ hSr hTr _ _ hstd ΛS ΛT N N' hcS hcT hΛS hΛT γ v hv).trans (memL N N' _).symm)
    (fun γ v hv => by rw [hcS₁, hcT]; exact (_root_.GlobalTheory.AdForm.RatLat.finOf_mem_iff _ ψ θ _ _ _ _ hSr hTr _ _ hstd ΛS₁ ΛT N₁ N' hcS₁ hcT hΛS₁ hΛT γ v hv).trans (memL N₁ N' _).symm)
    (mem_LamC_toHom _ _ hSr hTr _ N₁ N') (hfacts N₁ N' hN₁sd hN'sd).1 (hfacts N N' hNsd hN'sd).2 (hfacts N₁ N' hN₁sd hN'sd).2 hrel1
    (om (g, h) (vac0)) (by rw [hcS, hcT]; exact v0.1) v0.2.1.2 (by rw [hc1]; exact v1.2.1.2) (by rw [hc1]; exact v1.2.2)
  have mv1 : inter (HV I.A.sc) (alV (I.rec7 l Z).host.d I.A.sc)
      (LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) N N')
      (LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) N₁ N')
      (I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N N') = I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N₁ N' := by
    have c7 := hMv.2.2.2.2.2.2 N N₁ N' hNsd hN₁sd hN'sd
    rw [hvacT N N' hNsd hN'sd, hvacT N₁ N' hN₁sd hN'sd, hlam N N', hlam N₁ N'] at c7
    exact c7.symm
  have mv2 : inter (HV I.A.sc) (alV (I.rec7 l Z).host.d I.A.sc)
      (LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) N₁ N')
      (LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) N₁ N₁')
      (I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N₁ N') = I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N₁ N₁' := by
    have c6 := hMv.2.2.2.2.2.1 N₁ N' N₁' hN₁sd hN'sd hN₁'sd
    rw [hvacT N₁ N' hN₁sd hN'sd, hvacT N₁ N₁' hN₁sd hN₁'sd, hlam N₁ N', hlam N₁ N₁'] at c6
    exact c6.symm
  have e1 : xiN θ _ _ hSr hTr I.A.δ I.A.sc (om (s * g, h) (vac0)) = fun z =>
      ((μ x₀ : ℂ))⁻¹ * (c₀ * ((μ x : ℂ))⁻¹ * (μ y : ℂ)) * I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N₁ N' z := by
    rw [← hc1]
    refine st1.trans (funext fun z => ?_)
    rw [show xiN θ _ _ hSr hTr I.A.δ I.A.sc (om (g, h) (vac0)) = _ from key]
    erw [inter_const_mul]
    erw [mv1]
    simp only [map_one, Circle.coe_one, mul_one]
    ring
  have st2 := GlobalTheory.T.splitPlacePair_moves_latticeVacuumReading (I.rec7 l Z) ψ θ _ _ _ _ hSr hTr I.A.δ I.A.sc hstd (μ) (om) hW ΛS₁ ΛS₁ ΛT ΛT₁ hΛS₁ hΛS₁
    hΛT hΛT₁ e he 1 s' (GlobalTheory.LeviSplitChar.suppAt_one e _) hs' 1 y₀ (GlobalTheory.LeviSplitChar.isDetAt_one e _) hy₀
    (by rw [hcS₁, hcT, hcT₁]; exact _root_.GlobalTheory.LatPairMove.latO_move _ _ _ _ _ hSr hTr (s * g) 1 h s' N₁ N' N₁ N₁' hN₁ hN' (by rwa [one_mul]) hN₁')
    _ _ (fun γ v hv => by rw [hcS₁, hcT]; exact (_root_.GlobalTheory.AdForm.RatLat.finOf_mem_iff _ ψ θ _ _ _ _ hSr hTr _ _ hstd ΛS₁ ΛT N₁ N' hcS₁ hcT hΛS₁ hΛT γ v hv).trans (memL N₁ N' _).symm)
    (fun γ v hv => by rw [hcS₁, hcT₁]; exact (_root_.GlobalTheory.AdForm.RatLat.finOf_mem_iff _ ψ θ _ _ _ _ hSr hTr _ _ hstd ΛS₁ ΛT₁ N₁ N₁' hcS₁ hcT₁ hΛS₁ hΛT₁ γ v hv).trans (memL N₁ N₁' _).symm)
    (mem_LamC_toHom _ _ hSr hTr _ N₁ N₁') (hfacts N₁ N₁' hN₁sd hN₁'sd).1 (hfacts N₁ N' hN₁sd hN'sd).2
    (hfacts N₁ N₁' hN₁sd hN₁'sd).2 hrel2
    (om (s * g, h) (vac0)) (by rw [hcS₁, hcT]; exact v1.1) v1.2.1.2 (by rw [hc2]; exact v2.2.1.2) (by rw [hc2]; exact v2.2.2)
  have rx := _root_.GlobalTheory.SplitRootProd.mu_root_mul _ _ (μ) _ hstd.rk.2.2.1 hW.resS e he s g hs x₀ x x₁ hx₀ hx hx₁
  have ry := _root_.GlobalTheory.SplitRootProd.mu_root_mul _ _ (μ) _ hstd.rk.2.2.2 hW.resT e he s' h hs' y₀ y y₁ hy₀ hy hy₁
  rw [← hc2]
  refine st2.trans (funext fun z => ?_)
  rw [e1]
  erw [inter_const_mul]
  erw [mv2]
  rw [rx, ry]
  simp only [map_one, Circle.coe_one, inv_one, one_mul, Circle.coe_mul, mul_inv]
  ring

end GlobalTheory.AdForm.VacSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TorusEntryRatioIntegralAtUnramifiedPlaceStatement
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusEntryRatio_integral_at_unramified_place : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → UnrAt s v → ∀ 𝔉, IsFlatBF s (· = v) 𝔉 → ∀ f, Vac ψ B.V J.W LV LW (· = v) f → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → J.d.levi t ∈ grpAt J.W (· = v) → 𝔉 (s.om (1, J.d.levi t) f) ≠ 0 → ∀ i j : Fin ρ, j.1 = i.1 + 1 → t.1 i i * (t⁻¹).1 j j - 1 ∈ intAt D (· = v) := by
  first | exact @GlobalTheory.FinPl.RatioStep.ratio_int | exact GlobalTheory.FinPl.RatioStep.ratio_int | (intros; apply GlobalTheory.FinPl.RatioStep.ratio_int <;> assumption)
end
end

