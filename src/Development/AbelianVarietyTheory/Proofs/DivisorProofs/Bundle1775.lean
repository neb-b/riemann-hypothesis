module

public import Mathlib
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.CondSq
public import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubgroupIsUnit
public import Formalism.SharpRestriction.LevelLetterCocycles.CommutingEndomorphismPreservesInvariants
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1725
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1743
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1756
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1757
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1716
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0895
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1758

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiAtComp
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp

namespace GlobalTheory.BigOn.Exp.TwAdmProof

theorem not_mem_sq_of_eWL {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 E))
    (hv : (p : 𝓞 E) ∈ w.asIdeal) (he : eWL E w = 1) : (p : 𝓞 E) ∉ w.asIdeal ^ 2 := by
  obtain ⟨P, hP, hP0⟩ := w
  have he' : P.ramificationIdx ℤ = 1 := he
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 E)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) ≤ P := by
    rw [hmap, Ideal.span_le]; simpa using hv
  have : P.LiesOver (Ideal.span {(p : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.comap_ne_top _ hP.ne_top) (Ideal.map_le_iff_le_comap.mp hle)⟩
  have hb : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P hb] at he'
  intro h2
  refine (Ideal.ramificationIdx'_ne_one_iff hle).2 ?_ he'
  rw [hmap, Ideal.span_le]
  simpa using h2

end GlobalTheory.BigOn.Exp.TwAdmProof

namespace GlobalTheory.BigOn.Exp.TwAdmProof

variable {D : D7}

theorem not_mem_of_dvd (P : PlE D.host) (he : eWL D.host.E P = 1) {p : ℕ} (hp : p.Prime)
    (h : p ∣ D.host.QS * D.host.q * D.host.d) : (p : 𝓞 D.host.E) ∉ P.asIdeal := fun hv =>
  not_mem_sq_of_eWL hp P hv he (UpperTheory.Ram.mem_sq_of_dvd_condN D.host hp h _ P.isPrime hv)

theorem two_not_mem (P : PlE D.host) (he : eWL D.host.E P = 1) : ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal :=
  not_mem_of_dvd P he Nat.prime_two ((((dvd_pow_self 2 (by omega)).trans D.host.tower_dvd).mul_right _).mul_right _)

theorem d_not_mem (P : PlE D.host) (he : eWL D.host.E P = 1) : ((D.host.d : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal :=
  not_mem_of_dvd P he D.host.hyp.2.1 (dvd_mul_left _ _)

theorem q_not_mem (P : PlE D.host) (he : eWL D.host.E P = 1) : ((D.host.q : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal :=
  not_mem_of_dvd P he D.host.hyp.1 ((dvd_mul_left _ _).mul_right _)

end GlobalTheory.BigOn.Exp.TwAdmProof

namespace GlobalTheory.BigOn.Exp.TwAdmProof

variable {D : D7}

theorem exists_splitK_of (P : PlE D.host) (h1 : P.asIdeal.inertiaDeg ℤ = 1) (he : eWL D.host.E P = 1) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ D.host.cls p = .splitK ∧ ((p : 𝓞 D.host.E) ∈ P.asIdeal) := by
  have hp := GlobalTheory.TwistDet.prime_normV h1
  have hmem : ((Formalism.ConjugateSelfDual.normV P : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    have h2 : Ideal.absNorm P.asIdeal = Formalism.ConjugateSelfDual.normV P := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
    exact h2 ▸ Ideal.absNorm_mem P.asIdeal
  have hodd : Odd (Formalism.ConjugateSelfDual.normV P) := by
    refine hp.eq_two_or_odd'.resolve_left fun e => two_not_mem P he ?_
    rw [e] at hmem; exact hmem
  refine GlobalTheory.TwistDet.exists_splitK h1 he hodd (fun h => q_not_mem P he h) (fun h => d_not_mem P he h)

theorem psiAt_comp {Γ Γ' A : Type} [Group Γ] [Group Γ'] [CommGroup A] (b : Bool) (ψ : Γ →* A) (f : Γ' →* Γ) :
    (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b ψ).comp f = Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (ψ.comp f) := by
  cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.inv_comp]

end GlobalTheory.BigOn.Exp.TwAdmProof

end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunModel
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section RunModelSec

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

def RunModel (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r) (i : Fin D.R.m) {C : Type} [Finite C]
    [MulAction p.P.Gp C] (M : TwoLevels D.host.E D.R.r p.P.Gp C) (ka : Wt M.Ψ D.R.r) : Prop :=
  ∃ (v : HeightOneSpectrum (𝓞 D.what₂.LL))
    (e : C ≃ ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp),

    (∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)) ∧

    (∀ c τ (h1 : τ ∈ M.Ψ) (h2 : τ ∈ (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).Ψ) a,
      ka ⟨τ, h1⟩ a = laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) (e c) ⟨τ, h2⟩ a) ∧

    (∃ a : p.P.Gp → C → ℂˣ, ∀ (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) (g : p.P.Gp) (c : C)
      (x : Frame M.Ψ D.R.r), x ∈ M.dom →
      ∀ (h1 : M.Ψ = (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).Ψ)
        (h2 : M.Ψ = (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e (g • c))).Ψ),
        rdU ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀)
            (actLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (levFull (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (r.lev i g⁻¹) F.1)
            (e c) (castFrame h1 x) =
          (a g c : ℂ) * rdU ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀) F.1 (e (g • c))
            (castFrame h2 (lact (M.tr g c) x))) ∧

    (∀ c, ∀ γ ∈ (M.comp c).Γ, ∀ w ∈ (M.comp c).L',
      Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w - w ∈ p.T.Q.l.Mb • (M.comp c).L') ∧

    ∃ φ : ∀ c, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E]
        ((M.comp c).L' ⧸ (p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (M.comp c).L'))),
      ∀ (c : C) (u : p.P.Gp), u • c = c → ∃ n : ℤ, ∀ w : (M.comp c).L',
        ∃ hw : Matrix.mulVec (M.tr u c : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w ∈ (M.comp c).L',
          Submodule.Quotient.mk (p := p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (M.comp c).L')) ⟨_, hw⟩ =
            φ c ((r.lev i u ^ n) ((φ c).symm (Submodule.Quotient.mk w)))

end RunModelSec

end GlobalTheory.ShareOn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrArchPairAdeleJoin
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section
open MeasureTheory
namespace GlobalTheory.WeilL2Words
variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem adeleJoin_archPart (a : κ → AdeleRing (𝓞 F) F) :
    GlobalTheory.WeilCont.adeleJoin F (archPart F a) (fun i => (a i).2) = a := by
  funext i
  simp only [GlobalTheory.WeilCont.adeleJoin, archPart, RingEquiv.symm_apply_apply]
  rfl

theorem adeleJoin_add_arch (x v : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    GlobalTheory.WeilCont.adeleJoin F x y + arch F v = GlobalTheory.WeilCont.adeleJoin F (x + v) y := by
  funext i
  refine Prod.ext ?_ ?_
  · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i) + (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (v i) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i + v i)
    rw [map_add (f := _)]
  · exact add_zero (y i)

theorem adeleJoin_dot_arch (x u : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    GlobalTheory.WeilCont.adeleJoin F x y ⬝ᵥ arch F u = arch1 F (∑ i, x i * u i) := by
  rw [dotProduct, adeleOfMixedSpaceComponent_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [arch, mul_arch1']
  congr 2
  exact RingEquiv.apply_symm_apply _ _

theorem arch_dot_arch (v u : κ → mixedEmbedding.mixedSpace F) :
    arch F v ⬝ᵥ arch F u = arch1 F (∑ i, v i * u i) := by
  rw [dotProduct, adeleOfMixedSpaceComponent_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [arch, arch, mul_arch1']
  congr 2
  exact RingEquiv.apply_symm_apply _ _

theorem schA_exists_sum {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) :
    ∃ (n : ℕ) (f : Fin n → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : Fin n → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
      (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧ Φ = ∑ i, GlobalTheory.WeilM.pureA F (f i) (g i) := by
  rw [GlobalTheory.WeilM.schA, Submodule.mem_span_set'] at hΦ
  obtain ⟨n, c, s, rfl⟩ := hΦ
  choose f g hg hfg using fun i => (s i).2
  refine ⟨n, fun i => c i • f i, g, hg, Finset.sum_congr rfl fun i _ => ?_⟩
  rw [hfg i]
  ext a
  simp [GlobalTheory.WeilM.pureA, mul_assoc]

variable [Invertible (2 : AdeleRing (𝓞 F) F)]

theorem ell_half (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ) (z : mixedEmbedding.mixedSpace F) :
    ℓ (InfiniteAdeleRing.ringEquiv_mixedSpace F (⅟(2 : AdeleRing (𝓞 F) F)).1 * z) = ℓ z / 2 := by
  set c := InfiniteAdeleRing.ringEquiv_mixedSpace F (⅟(2 : AdeleRing (𝓞 F) F)).1
  have hc : c + c = 1 := by
    rw [← map_add (f := _)]
    have : (⅟(2 : AdeleRing (𝓞 F) F)).1 + (⅟(2 : AdeleRing (𝓞 F) F)).1 = (⅟(2 : AdeleRing (𝓞 F) F) + ⅟2).1 := rfl
    rw [this, invOf_two_add_invOf_two]
    exact map_one _
  have h2 : ℓ (c * z) + ℓ (c * z) = ℓ z := by rw [← map_add (f := _), ← add_mul, hc, one_mul]
  linarith

theorem schr_archPair_adeleJoin (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (hℓ : ∀ z, ψ (arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z))
    (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ)
    (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    GlobalTheory.WeilM.schr ψ (archPair F h) Φ (GlobalTheory.WeilCont.adeleJoin F x y) =
      Complex.exp (2 * Real.pi * Complex.I * ((ℓ (∑ i, x i * h.2 i) : ℂ) + (ℓ (∑ i, h.1 i * h.2 i) : ℂ) / 2)) *
        Φ (GlobalTheory.WeilCont.adeleJoin F (x + h.1) y) := by
  simp only [GlobalTheory.WeilM.schr, archPair]
  rw [adeleJoin_add_arch, adeleJoin_dot_arch, arch_dot_arch, mul_arch1', ← adeleOfMixedSpaceComponent_add, hℓ, map_add (f := _), ell_half]
  congr 2
  push_cast
  ring

theorem hasDerivAt_schr_pureA (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (hℓ : ∀ z, ψ (arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z))
    (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.schr ψ (archPair F (t • h)) (GlobalTheory.WeilM.pureA F f g) (GlobalTheory.WeilCont.adeleJoin F x y))
      ((2 * Real.pi * Complex.I * (ℓ (∑ i, x i * h.2 i) : ℂ) * f x + fderiv ℝ f x h.1) * g y) 0 := by
  set A : ℝ := ℓ (∑ i, x i * h.2 i)
  set B : ℝ := ℓ (∑ i, h.1 i * h.2 i) / 2
  have key : (fun t : ℝ => GlobalTheory.WeilM.schr ψ (archPair F (t • h)) (GlobalTheory.WeilM.pureA F f g) (GlobalTheory.WeilCont.adeleJoin F x y)) =
      fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((t * A + t ^ 2 * B : ℝ) : ℂ)) * (f (x + t • h.1) * g y) := by
    funext t
    rw [schr_archPair_adeleJoin F ψ ℓ hℓ, GlobalTheory.WeilCont.pureA_adeleJoin]
    congr 2
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, A, B]
    have e1 : ∑ i, x i * (t • h.2 i) = t • ∑ i, x i * h.2 i := by
      rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun i _ => mul_smul_comm _ _ _
    have e2 : ∑ i, (t • h.1 i) * (t • h.2 i) = (t ^ 2) • ∑ i, h.1 i * h.2 i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_mul_assoc, mul_smul_comm, smul_smul, pow_two]
    rw [e1, e2, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    push_cast
    ring
  rw [key]
  have hφ := ((((hasDerivAt_id (0:ℝ)).mul_const A).fun_add ((hasDerivAt_pow 2 (0:ℝ)).mul_const B)).ofReal_comp).const_mul
    (2 * (Real.pi : ℂ) * Complex.I)
  have hS := ((f.hasFDerivAt (x + (0:ℝ) • h.1)).comp_hasDerivAt (0:ℝ)
      (((hasDerivAt_id (0:ℝ)).smul_const h.1).const_add x)).mul_const (g y)
  have hT := hφ.cexp.fun_mul hS
  refine hT.congr_deriv ?_
  simp only [id, Function.comp, zero_smul, add_zero, one_smul, zero_mul, mul_zero, Complex.ofReal_zero, Complex.exp_zero,
    one_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_one, Complex.ofReal_pow]
  ring

omit [Invertible (2 : AdeleRing (𝓞 F) F)] in
theorem schr_sum' [Invertible (2 : AdeleRing (𝓞 F) F)] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) {n : ℕ} (Φ : Fin n → (κ → AdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.schr ψ w (∑ i, Φ i) = ∑ i, GlobalTheory.WeilM.schr ψ w (Φ i) := by
  funext x
  simp [GlobalTheory.WeilM.schr, Finset.sum_apply, Finset.mul_sum]

theorem hasDerivAt_schr_sum (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (hℓ : ∀ z, ψ (arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z))
    (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) {n : ℕ}
    (f : Fin n → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : Fin n → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.schr ψ (archPair F (t • h)) (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i))
        (GlobalTheory.WeilCont.adeleJoin F x y))
      (∑ i, (2 * Real.pi * Complex.I * (ℓ (∑ k, x k * h.2 k) : ℂ) * f i x + fderiv ℝ (f i) x h.1) * g i y) 0 := by
  have e : (fun t : ℝ => GlobalTheory.WeilM.schr ψ (archPair F (t • h)) (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i))
      (GlobalTheory.WeilCont.adeleJoin F x y)) = fun t => ∑ i, GlobalTheory.WeilM.schr ψ (archPair F (t • h)) (GlobalTheory.WeilM.pureA F (f i) (g i))
      (GlobalTheory.WeilCont.adeleJoin F x y) := by
    funext t
    rw [schr_sum', Finset.sum_apply]
  rw [e]
  exact HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hasDerivAt_schr_pureA F ψ ℓ hℓ h (f i) (g i) x y

theorem differentiableAt_schr {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsStdInf F ψ)
    (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ}
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) (a : κ → AdeleRing (𝓞 F) F) :
    DifferentiableAt ℝ (fun t : ℝ => GlobalTheory.WeilM.schr ψ (archPair F (t • h)) Φ a) 0 := by
  obtain ⟨ℓ, -, hℓ⟩ := hψ
  obtain ⟨n, f, g, -, rfl⟩ := schA_exists_sum F hΦ
  rw [← adeleJoin_archPart F a]
  exact (hasDerivAt_schr_sum F ψ ℓ hℓ h f g _ _).differentiableAt

theorem dS_sum_adeleJoin (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (hℓ : ∀ z, ψ (arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z))
    (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) {n : ℕ}
    (f : Fin n → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : Fin n → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    dS F ψ h (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) (GlobalTheory.WeilCont.adeleJoin F x y) =
      ∑ i, (2 * Real.pi * Complex.I * (ℓ (∑ k, x k * h.2 k) : ℂ) * f i x + fderiv ℝ (f i) x h.1) * g i y :=
  (hasDerivAt_schr_sum F ψ ℓ hℓ h f g x y).deriv

theorem dS_mem_schA {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsStdInf F ψ)
    (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ}
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) : dS F ψ h Φ ∈ GlobalTheory.WeilM.schA F κ := by
  obtain ⟨n, f, g, hg, rfl⟩ := schA_exists_sum F hΦ
  obtain ⟨f', hf'⟩ := dS_sum_pureA F κ ψ hψ n g f h
  rw [hf']
  exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f' i, g i, hg i, rfl⟩

end GlobalTheory.WeilL2Words
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergLawApplyStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergIntertwiner_eq_twisted_weilOperator : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' →
    ∀ (K : GL (Fin a') (Fv F Bs.v₁) →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V'.J),
    (∀ g, K g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.V' (evFin F Bs.v₁) ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = g.val ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp σ)) =
        (Γ.V'.J.map Bs.τ₁)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * Γ.V'.J.map Bs.τ₁) →
    ∀ (S : GL (Fin a') (Fv F Bs.v₁) → ((Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ) → (Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _, ∀ c : ℂ, S g (c • φ + φ') = c • S g φ + S g φ') →
    (∀ g g', ∀ φ ∈ GlobalTheory.WeilM.SB _, S (g * g') φ = S g (S g' φ)) →
    (∀ φ ∈ GlobalTheory.WeilM.SB _, S 1 φ = φ) →
    (∀ g (γ : Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F Bs.v₁) γ →
      ∀ φ ∈ GlobalTheory.WeilM.SB _,
        S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ) =
          GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁)
            (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (K g, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.W.J)) γ)) (S g φ)) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ μ : @Measure (Fin a' × Fin (a + a') → Fv F Bs.v₁) (borel _),
      @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∃ ν α : (Fv F Bs.v₁)ˣ →* ℂˣ, (∀ x, ‖(ν x : ℂ)‖ = 1) ∧
      ∀ ι, Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι → ∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g φ) = omB ν α g 1 (ι φ) := by
  first | exact @GlobalTheory.LinModelLocal.exists_omB_of_linBar | exact GlobalTheory.LinModelLocal.exists_omB_of_linBar | (intros; apply GlobalTheory.LinModelLocal.exists_omB_of_linBar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBoxTensorLeftFixedLinearApplyStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledStabilizer_generated_antidiag_splitPlace_V : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T → ∀ H : Subgroup (GlobalTheory.DblVac.UD σ G.V),
      (∀ p ∈ GlobalTheory.DblVac.KD σ G.V v, p ∈ GlobalTheory.DblVac.PDiag σ G.V → p ∈ H) →
      (∀ p ∈ GlobalTheory.DblVac.KD σ G.V v, p ∈ GlobalTheory.DblVac.PAnti σ G.V → p ∈ H) → ∀ g ∈ GlobalTheory.DblVac.KD σ G.V v, g ∈ H := by
  first | exact @GlobalTheory.DblGenV.mem_of_KD_diag_anti | exact GlobalTheory.DblGenV.mem_of_KD_diag_anti | (intros; apply GlobalTheory.DblGenV.mem_of_KD_diag_anti <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPartRealisationWithScalarsCharOfWeak
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn

theorem splitPartRealisationWithScalars_char_of_weak : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), p.R.toRealDat.ExAt → SingleIndexPlacesAreTwisted p → (R2 p).Char (F2 p) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hE hW
  have hc := Formalism.IndefR.Links.RealDat3.characterisation_of_weak p.charW hE
  exact GlobalTheory.BigOn.char_charOf D _ _ _ p.P.A3.A _ p.R.toRealDat (F2 p) hc.lev ⟨hc.grp.red_R, hc.grp.red_L, hc.grp.levels, hc.grp.record, hc.grp.chiW⟩ hc.fam hc.models hc.chain hc.thP
    ⟨_root_.GlobalTheory.BigOn.tupTw_of_w1Row D L hT Gi Gl Kc Y cX ex Csz p hW, hc.tup.mu_off, hc.tup.mu_used, hc.tup.mu_ne, hc.tup.mu_conj, hc.tup.mu_on⟩

end GlobalTheory.BigOn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFiringRowAtConcreteLifts
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaFireAssembly

theorem thetaFireRow_toLiftReal : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : RecTie.TopMultH R) (hinj : ∀ i t, Function.Injective (R.extV i t)), R.BaseW F → R.ExAt → A.v0 = InfinitePlace.mk D.what₂.embLL → ∀ IL : RecTie.LiftIds (RecTie.toLiftReal R F tupT hm hTop hinj), RecTie.ThetaFireRow (RecTie.toLiftReal R F tupT hm hTop hinj) IL := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F tupT hm hTop hinj h e hv IL
  have hP : R.IsThP := RealDat.thP_of_weak h.thP e
  refine ⟨fun μ _ i => GlobalTheory.ThetaPRead.isThetaP_toLiftReal R F tupT hm hTop hinj hP.thF μ i, ?_, ?_⟩
  · exact _root_.GlobalTheory.ThetaFireLift.thetaFireL R F tupT hm hTop hinj h.lev h.grp h.models hP hv IL
  · exact GlobalTheory.LiftResInj.resInjL_toLiftReal R F tupT hm hTop hinj h.models.inf

end GlobalTheory.ThetaFireAssembly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToRatHyp0
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie

namespace GlobalTheory.BigOn.Exp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}

structure RatHyp0 (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (F : Face D A3.A)
    (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
    (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)) (i : D.ntw.Tw) (j : Fin D.R.m) : Prop where
  size : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV
  host : HostHyp D
  std : VStd D j
  laws : LawsJ T
  core : GlobalTheory.Hk3.Core Rl.toRealDat F
  unif : Rl.toRealDat.LUnif
  fw : Nonempty (FWTie T Rl.toRealDat κ v₀)
  tieIn : TieIn T Rl.toRealDat κ v₀
  io : IoExt Rl.toRealDat
  guard : QGuard Rl.toRealDat
  fin : Finite T0
  pins : OMPins T Rl.toRealDat κ v₀ O j
  phase : PhaseTie T Rl.toRealDat κ v₀ O (fun j => cj (twAt D.what₂.embLL A3.A.v0) (Rl.phs j)) j
  galois : IsGalois ℚ D.LL0
  small : SmallHas D Rl.C
  inUse : D.ntw.NonzeroIndexPlace i
  low : ∀ P : Pl D.host.E, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK *
    (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → P ∈ D.ntw.S0 i

end GlobalTheory.BigOn.Exp
end
end

