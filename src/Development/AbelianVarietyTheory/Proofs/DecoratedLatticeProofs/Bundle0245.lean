module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiEqOfFinPart
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0146
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0240

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDerivAtHeisenbergThetaSeries
section
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

noncomputable section

namespace GlobalTheory.Core.Rk.OntoDer

theorem hasDerivAt_term {G : Type} [AddCommGroup G] (a : ℝ →+ G) (p : G →+ ℂ) (κ : ℂ) (hκ : ∀ t : ℝ, p (a t) = t * κ)
    (φ φ₁ : G → ℂ) (hφ : ∀ x, HasDerivAt (fun t : ℝ => φ (x + a t)) (φ₁ x) 0) (u : G) (s : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (t * p (a t) + t * p u + t * p u) * φ (u + a t))
      (Complex.exp (s * p (a s) + s * p u + s * p u) * ((p + p) (u + a s) * φ (u + a s) + φ₁ (u + a s))) s := by
  have h1 : HasDerivAt (fun t : ℝ => φ (u + a t)) (φ₁ (u + a s)) s := by
    have h := hφ (u + a s)
    rw [← sub_self s] at h
    have h' := HasDerivAt.comp_sub_const s s h
    refine h'.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    show φ (u + a t) = φ (u + a s + a (t - s))
    rw [map_sub, add_assoc, add_sub_cancel]
  have h0 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 s := Complex.ofRealCLM.hasDerivAt
  have h2 := (((h0.mul (h0.mul_const κ)).add (h0.mul_const (p u))).add (h0.mul_const (p u))).cexp
  have h3 := h2.mul h1
  simp only [hκ]
  refine h3.congr_deriv ?_
  simp only [AddMonoidHom.add_apply, map_add (f := _), hκ, Pi.add_apply, Pi.mul_apply]
  ring

variable {D : D7}

theorem two_halves (S T : HSp D) (x y : WO S T) : symplO S T x y = symplOH S T x y + symplOH S T x y := by
  unfold symplOH
  rw [← add_mul, ← map_add (f := _), add_halves, map_one, one_mul]

theorem phase_identity {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (x y a b ξ : Mx D T.rank ρ) :
    symplOH S T (d.extX T x + d.extY T y) (d.extX T a + d.extY T b) +
        (-(symplOH S T (d.extX T (x + a)) (d.extY T (y + b)))) + symplO S T (d.extX T (x + a + ξ)) (d.extY T (y + b)) =
      -(symplOH S T (d.extX T x) (d.extY T y)) + symplO S T (d.extX T (x + ξ)) (d.extY T y) +
        (symplOH S T (d.extX T a) (d.extY T b) + symplOH S T (d.extX T (x + ξ)) (d.extY T b) +
          symplOH S T (d.extX T (x + ξ)) (d.extY T b)) := by
  simp only [two_halves, map_add (f := _), GlobalTheory.WeilVacMove.symplOH_add_left, GlobalTheory.WeilVacMove.symplOH_add_right,
    HypDec.symplOH_extX_extX, HypDec.symplOH_extY_extY,
    GlobalTheory.WeilVacMove.symplOH_skew S T (d.extX T a) (d.extY T y)]
  ring

theorem eq_ext (A B : HSp D) (w : WO (dblSp A) B) :
    w = (dblDec A).extX B (HMul.hMul w (dblDec A).jX) + (dblDec A).extY B (HMul.hMul w (dblDec A).jY) := by
  have h0 : HMul.hMul (dblDec A).j0 (dblDec A).p0 = (0 : Mx D (dblSp A).rank (dblSp A).rank) := by
    ext i j
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun k _ => Fin.elim0 k
  have h := (dblDec A).sum_eq_one
  rw [h0, add_zero] at h
  rw [HypDec.extX_apply, HypDec.extY_apply, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_add, h, Matrix.mul_one]

def mulLine {m n k : ℕ} (M : ℝ →+ Mx D m n) (j : Mx D n k) : ℝ →+ Mx D m k where
  toFun t := HMul.hMul (M t) j
  map_zero' := by rw [map_zero, Matrix.zero_mul]
  map_add' s t := by rw [map_add (f := _), Matrix.add_mul]

theorem continuous_mulLine {m n k : ℕ} {M : ℝ →+ Mx D m n} (hM : Continuous M) (j : Mx D n k) :
    Continuous (mulLine M j) := hM.matrix_mul continuous_const

theorem map_mul_zero {m n k : ℕ} {R : Type} [CommRing R] (q : AE D →+* R) {u : Mx D m n} (hu : u.map q = 0)
    (j : Mx D n k) : (HMul.hMul u j : Mx D m k).map q = 0 := by
  rw [Matrix.map_mul, hu, Matrix.zero_mul]

theorem exists_summable_bound {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} {φ : Mx D m n → ℂ}
    (hφ : GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ) {Q : Set (Mx D m n)} (hQ : IsCompact Q) :
    ∃ b : Matrix (Fin m) (Fin n) D.host.E → ℝ, Summable b ∧ ∀ x ∈ Q, ∀ ξ, ‖φ (x + rat ξ)‖ ≤ b ξ := by
  obtain ⟨N, hN⟩ := _root_.GlobalTheory.Unf.MajLoc.summable_bound D θ hθ m n
  obtain ⟨-, K, hK, hC⟩ := _root_.GlobalTheory.SchwartzMaj.continuous_and_le_maj D θ hθ m n φ hφ
  obtain ⟨C, hC⟩ := hC N
  obtain ⟨b, hb, hb'⟩ := hN K Q hK hQ
  refine ⟨fun ξ => |C| * b ξ, hb.mul_left _, fun x hx ξ => (hC _).trans ?_⟩
  exact mul_le_mul (le_abs_self C) (hb' x hx ξ) (GlobalTheory.Unf.maj_nonneg _ _ _ _) (abs_nonneg C)


set_option maxHeartbeats 1600000 in
theorem hasDerivAt_heisO_thetaSeries : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (φ : Mx D B.rank A.rank → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ → ∀ f : WO (dblSp A) B → ℂ, (∀ w : WO (dblSp A) B, f w = ψ (-(symplOH (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY)))) * ∑' ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E, ψ (symplO (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX + rat ξ)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY))) * φ (HMul.hMul w (dblDec A).jX + rat ξ)) → ∀ M : ℝ →+ WO (dblSp A) B, Continuous M → (∀ t, (M t).map (finPart D) = 0) → ∃ φ' : Mx D B.rank A.rank → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ' ∧ ∀ f' : WO (dblSp A) B → ℂ, (∀ w : WO (dblSp A) B, f' w = ψ (-(symplOH (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY)))) * ∑' ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E, ψ (symplO (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX + rat ξ)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY))) * φ' (HMul.hMul w (dblDec A).jX + rat ξ)) → ∀ w, HasDerivAt (fun t : ℝ => heisO ψ (dblSp A) B (M t) f w) (f' w) 0 := by
  intro D ψ hψ A B φ hφ f hf M hM hM0
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨lam, hl, hlam⟩ := GlobalTheory.WeilVacMove.exists_log hψ
  have hn : ∀ z, ‖ψ z‖ = 1 := hψ.1.2.1
  haveI : IsTopologicalAddGroup (AE D) := IsTopologicalRing.to_topologicalAddGroup
  let d := dblDec A
  let a : ℝ →+ Mx D B.rank A.rank := mulLine M d.jX
  let b : ℝ →+ Mx D B.rank A.rank := mulLine M d.jY
  let L : ℝ →+ WO (dblSp A) B := mulLine b d.pY
  have ha : Continuous a := continuous_mulLine hM _
  have hL : Continuous L := continuous_mulLine (continuous_mulLine hM _) _
  have ha0 : ∀ t, (a t).map (finPart D) = 0 := fun t => map_mul_zero _ (hM0 t) _
  have hL0 : ∀ t, (L t).map (finPart D) = 0 := fun t => map_mul_zero _ (map_mul_zero _ (hM0 t) _) _
  let p : Mx D B.rank A.rank →+ ℂ := (GlobalTheory.WeilVacMove.phase lam (dblSp A) B (L 1)).comp (d.extX B)
  have hX : Continuous (d.extX B) := continuous_id.matrix_mul continuous_const
  have hp : Continuous p := hl.comp (GlobalTheory.WeilVacMove.continuous_symplOH (dblSp A) B hX continuous_const)
  have hp0 : ∀ u : Mx D B.rank A.rank, u.map (infPart D) = 0 → p u = 0 := fun u hu => by
    show lam (symplOH (dblSp A) B (d.extX B u) (L 1)) = 0
    rw [(GlobalTheory.WeilVacMove.symplOH_fin_real (dblSp A) B (d.extX B u) (L 1) (map_mul_zero _ hu _) (hL0 1)).1, map_zero]
  have hψp : ∀ (u : Mx D B.rank A.rank) (t : ℝ),
      ψ (symplOH (dblSp A) B (d.extX B u) (d.extY B (b t))) = Complex.exp (t * p u) := fun u t =>
    GlobalTheory.WeilVacMove.psi_sympl_line hl hlam hL hL0 (d.extX B u) t
  have hκ : ∀ t : ℝ, p (a t) = t * p (a 1) := fun t =>
    GlobalTheory.WeilVacMove.additive_real (p.comp a) (hp.comp ha) t
  obtain ⟨hd, hm, hadd⟩ := _root_.GlobalTheory.SchwartzDeriv.isSchwartzBruhat_closed D _ _ φ hφ
  obtain ⟨φ₁, hφ₁, hder⟩ := hd a ha ha0
  have hℓ := hm (p + p) (hp.add hp) fun u hu => by rw [AddMonoidHom.add_apply, hp0 u hu, add_zero]
  have hφ' := (_root_.GlobalTheory.SchwartzDeriv.isSchwartzBruhat_closed D _ _ _ hℓ).2.2 φ₁ hφ₁
  refine ⟨_, hφ', fun f' hf' w => ?_⟩
  set φ' : Mx D B.rank A.rank → ℂ := (fun x => (p + p) x * φ x) + φ₁ with hφ'def
  let x : Mx D B.rank A.rank := HMul.hMul w d.jX
  let y : Mx D B.rank A.rank := HMul.hMul w d.jY
  let c : Matrix (Fin B.rank) (Fin A.rank) D.host.E → ℂ := fun ξ =>
    ψ (symplO (dblSp A) B (d.extX B (x + rat ξ)) (d.extY B y))
  let e : Matrix (Fin B.rank) (Fin A.rank) D.host.E → ℝ → ℂ := fun ξ t =>
    Complex.exp (t * p (a t) + t * p (x + rat ξ) + t * p (x + rat ξ))
  have he : ∀ ξ t, e ξ t = ψ (symplOH (dblSp A) B (d.extX B (a t)) (d.extY B (b t)) +
      symplOH (dblSp A) B (d.extX B (x + rat ξ)) (d.extY B (b t)) +
      symplOH (dblSp A) B (d.extX B (x + rat ξ)) (d.extY B (b t))) := fun ξ t => by
    rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hψp, hψp, ← Complex.exp_add, ← Complex.exp_add]
  have he0 : ∀ ξ, e ξ 0 = 1 := fun ξ => by simp [e]
  have hform : ∀ t, heisO ψ (dblSp A) B (M t) f w =
      ψ (-(symplOH (dblSp A) B (d.extX B x) (d.extY B y))) * ∑' ξ, c ξ * (e ξ t * φ (x + rat ξ + a t)) := by
    intro t
    have e1 : HMul.hMul (w + M t) (dblDec A).jX = x + a t := Matrix.add_mul _ _ _
    have e2 : HMul.hMul (w + M t) (dblDec A).jY = y + b t := Matrix.add_mul _ _ _
    have e3 : symplOH (dblSp A) B w (M t) =
        symplOH (dblSp A) B (d.extX B x + d.extY B y) (d.extX B (a t) + d.extY B (b t)) :=
      congrArg₂ (symplOH (dblSp A) B) (eq_ext A B w) (eq_ext A B (M t))
    rw [heisO, hf, e1, e2, e3, ← mul_assoc, ← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr fun ξ => ?_
    rw [he, add_right_comm x (rat ξ) (a t), ← mul_assoc, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul,
      ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, phase_identity]
  have hQ : IsCompact ((fun t : ℝ => x + a t) '' Set.Icc (-1) 1) :=
    isCompact_Icc.image (continuous_const.add ha)
  obtain ⟨u, hu, hu'⟩ := exists_summable_bound hθ hφ' hQ
  obtain ⟨v, hv, hv'⟩ := exists_summable_bound hθ hφ (isCompact_singleton (x := x))
  have key := hasDerivAt_tsum_of_isPreconnected (t := Set.Ioo (-1 : ℝ) 1) (y₀ := (0 : ℝ)) (y := (0 : ℝ))
    (g := fun ξ t => c ξ * (e ξ t * φ (x + rat ξ + a t)))
    (g' := fun ξ t => c ξ * (e ξ t * φ' (x + rat ξ + a t))) hu isOpen_Ioo isPreconnected_Ioo
    (fun ξ t _ => (hasDerivAt_term a p _ hκ φ φ₁ hder (x + rat ξ) t).const_mul (c ξ))
    (fun ξ t ht => by
      rw [norm_mul, norm_mul, he, hn, hn, one_mul, one_mul, add_right_comm]
      exact hu' _ ⟨t, Set.Ioo_subset_Icc_self ht, rfl⟩ ξ)
    (by norm_num)
    (Summable.of_norm_bounded hv fun ξ => by
      rw [norm_mul, norm_mul, he, hn, hn, one_mul, one_mul, map_zero, add_zero]
      exact hv' x rfl ξ)
    (by norm_num)
  simp only [he0, map_zero, add_zero, one_mul] at key
  rw [hf', funext hform]
  exact key.const_mul _

end GlobalTheory.Core.Rk.OntoDer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertPlaceLocalTraceCharacterConductorIntegers
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.InertFrameLoc

section Rigid

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem ringHom_eq_id_of_int (f : w.adicCompletion E →+* w.adicCompletion E)
    (h1 : ∀ x : E, f (algebraMap E _ x) = algebraMap E _ x)
    (h2 : ∀ z, Valued.v z ≤ 1 → Valued.v (f z) ≤ 1) : f = RingHom.id _ := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  set t : w.adicCompletion E := algebraMap E _ (a : E) with ht
  have hft : f t = t := h1 _
  have ht1 : Valued.v t < 1 := by
    rw [ht, GlobalTheory.Idele.valued_algebraMap]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem w a).2 ha
  have htz : t ≠ 0 := by
    rw [ht, map_ne_zero, Ne, RingOfIntegers.coe_eq_zero_iff]
    exact ha0
  have key : ∀ (n : ℕ) z, Valued.v z ≤ Valued.v t ^ n → Valued.v (f z) ≤ Valued.v t ^ n := by
    intro n z hz
    have htn : t ^ n ≠ 0 := pow_ne_zero _ htz
    have hz' : z = t ^ n * (z / t ^ n) := by field_simp
    rw [hz', map_mul, map_pow, hft, Valuation.map_mul, Valuation.map_pow]
    refine mul_le_of_le_one_right' (h2 _ ?_)
    rw [map_div₀, map_pow]
    exact div_le_one_of_le₀ hz zero_le'
  have hcont : Continuous f := by
    refine continuous_of_continuousAt_zero f (Metric.tendsto_nhds.2 fun ε hε => ?_)
    have h1' : ‖t‖ < 1 := Valued.toNormedField.norm_lt_one_iff.2 ht1
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε h1'
    have hne : Valued.v t ^ m ≠ 0 := pow_ne_zero _ ((map_ne_zero _).2 htz)
    filter_upwards [(GlobalTheory.Idele.isOpen_valued_le (K := E) w (WithZero.log (Valued.v t ^ m))).mem_nhds
      (x := 0) (by simp)] with z hz
    rw [map_zero, dist_zero_right]
    refine (Valued.toNormedField.norm_le_iff.2 ?_).trans_lt ((norm_pow t m).trans_lt hm)
    rw [map_pow]
    refine key m z ?_
    have hz' : Valued.v z ≤ WithZero.exp (WithZero.log (Valued.v t ^ m)) := hz
    rwa [WithZero.exp_log hne] at hz'
  exact RingHom.coe_inj ((HeightOneSpectrum.denseRange_algebraMap E w).equalizer hcont continuous_id
    (funext fun x => h1 x))

end Rigid

end GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertFrameLoc

section Cond

open GlobalTheory.EmbChart

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}

theorem tensAt_mul_tensAt (y y' : Fv D.host.F v ⊗[D.host.F] D.host.E) :
    tensAt D.host.E v y * tensAt D.host.E v y' = tensAt D.host.E v (y * y') := by
  rw [tensAt_mul_right, compFin_tensAt]

theorem compFin_incA (x : D.host.E) :
    compFin D.host.F D.host.E v (incA D x) = (1 : Fv D.host.F v) ⊗ₜ[D.host.F] x := by
  show evFin D.host.F v 1 ⊗ₜ x = _
  rw [map_one]

theorem tensAt_one_mul_incA (x : D.host.E) :
    tensAt D.host.E v 1 * incA D x = tensAt D.host.E v ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] x) := by
  rw [tensAt_mul_right, one_mul, compFin_incA]

theorem secW_mul (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v)
    (z z' : w.adicCompletion D.host.E) : secW hw h (z * z') = secW hw h z * secW hw h z' := by
  show tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm (z * z')) =
    tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z) *
      tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z')
  rw [map_mul, tensAt_mul_tensAt]

theorem complEquiv_symm_algebraMap (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v)
    (x : D.host.E) : (GlobalTheory.LFun.InertChart.complEquiv hw h).symm (algebraMap D.host.E _ x) =
      (1 : Fv D.host.F v) ⊗ₜ[D.host.F] x := by
  rw [RingEquiv.symm_apply_eq]
  show _ = GlobalTheory.LFun.toCompl h ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] x)
  rw [GlobalTheory.LFun.toCompl_tmul, map_one, one_mul]

theorem isPrimeIdem_tensAt (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) :
    IsPrimeIdem w (tensAt D.host.E v 1) (tensAt D.host.E v 1) := by
  refine Or.inr ⟨rfl, ⟨v, atPlace v 1, ⟨GlobalTheory.AdelicU.singleFin v 1, rfl, GlobalTheory.AdelicU.evalV_singleFin_self v 1,
    fun u hu => GlobalTheory.AdelicU.evalV_singleFin_ne hu 1⟩, rfl⟩, fun x hx => ?_⟩
  rw [tensAt_one_mul_incA, finPart_tensAt_mem_iff, GlobalTheory.LFun.InertChart.mem_intLoc_iff hw h, GlobalTheory.LFun.toCompl_tmul,
    map_one, one_mul]
  show _ ↔ ¬ (Valued.v (algebraMap D.host.E (w.adicCompletion D.host.E) (x : D.host.E)⁻¹) ≤ 1)
  have h0 : w.valuation D.host.E (x : D.host.E) ≠ 0 := (map_ne_zero _).2 (RingOfIntegers.coe_ne_zero_iff.2 hx)
  rw [GlobalTheory.Idele.valued_algebraMap, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 h0),
    HeightOneSpectrum.valuation_lt_one_iff_mem]

end Cond

theorem thW_cond : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (ϖ : w.adicCompletion D.host.E) (k : w.adicCompletion D.host.E), IsStdChar D ψ (-1) → IsConjAt D.sp.cm.sig h c → IsUnramInv ϖ c (qV D.host.F v) → GlobalTheory.InertLoc.IsGen D w k → ∀ z, (∀ u ∈ Formalism.UG.intL (w.adicCompletion D.host.E), thW ψ hw h (k * c k) (z * u) = 1) ↔ z ∈ Formalism.UG.intL (w.adicCompletion D.host.E) := by
  intro D ψ v w hw h c ϖ k hψ hconj hU hk z
  have he := isPrimeIdem_tensAt (D := D) hw h
  obtain ⟨ϖ0, σ0, q0, π0, hU0, -, hch, hV⟩ := GlobalTheory.InertLoc.exists_chart (GlobalTheory.WeilAtPlace.conjPl_eq_of_inert hw h) he
  have hsec_e : ∀ y, GlobalTheory.EmbChart.tensAt D.host.E v 1 * secW hw h y = secW hw h y := fun y => by
    show GlobalTheory.EmbChart.tensAt D.host.E v 1 * GlobalTheory.EmbChart.tensAt D.host.E v _ = GlobalTheory.EmbChart.tensAt D.host.E v _
    rw [tensAt_mul_tensAt, one_mul]
  let f0 : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E :=
    { toFun := fun z => π0 (secW hw h z)
      map_one' := by
        show π0 (GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm 1)) = 1
        rw [map_one]
        exact hch.pi_idem
      map_mul' := fun z z' => by
        show π0 (secW hw h (z * z')) = π0 (secW hw h z) * π0 (secW hw h z')
        rw [secW_mul, map_mul]
      map_zero' := by
        show π0 (secW hw h 0) = 0
        rw [map_zero, map_zero]
      map_add' := fun z z' => by
        show π0 (secW hw h (z + z')) = π0 (secW hw h z) + π0 (secW hw h z')
        rw [map_add (f := _), map_add (f := _)] }
  have hf0 : f0 = RingHom.id _ := ringHom_eq_id_of_int w f0 (fun x => by
      show π0 (GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm (algebraMap D.host.E _ x))) = _
      rw [complEquiv_symm_algebraMap, ← tensAt_one_mul_incA, map_mul, hch.pi_idem, one_mul, hch.2.2.2.1])
    (fun z hz => by
      refine (hch.2.2.2.2.2 (secW hw h z)).1 ?_
      rw [hsec_e]
      show finPart D (GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z)) ∈ intAE D
      rw [GlobalTheory.EmbChart.finPart_tensAt_mem_iff, GlobalTheory.LFun.InertChart.mem_intLoc_iff hw h]
      show (GlobalTheory.LFun.InertChart.complEquiv hw h) ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z) ∈ Ov D.host.E w
      rw [RingEquiv.apply_symm_apply]
      exact hz)
  have hpi : ∀ z, π0 (secW hw h z) = z := fun z => RingHom.congr_fun hf0 z
  have hsec : ∀ z, hch.sec z = secW hw h z := fun z =>
    hch.ext (hch.mul_sec z) (hsec_e z) (by rw [hch.pi_sec, hpi])
  have hσc : ∀ x : D.host.E, σ0 (algebraMap D.host.E _ x) = c (algebraMap D.host.E _ x) := fun x => by
    calc σ0 (algebraMap D.host.E _ x) = σ0 (π0 (incA D x)) := by rw [hch.2.2.2.1]
      _ = π0 (cA D (incA D x)) := (hch.2.2.2.2.1 _).symm
      _ = algebraMap D.host.E _ (D.sp.cm.sig x) := hch.2.2.2.1 (D.sp.cm.sig x)
      _ = c (algebraMap D.host.E _ x) := (GlobalTheory.LFun.InertChart.conj_algebraMap hconj x).symm
  have hg := ringHom_eq_id_of_int w (c.comp σ0) (fun x => by
      rw [RingHom.comp_apply, hσc, hU.1])
    (fun z hz => by
      rw [RingHom.comp_apply, hU.2.1, hU0.2.1]
      exact hz)
  have hσ : ∀ z, σ0 z = c z := fun z => by
    have h1 : c (σ0 z) = z := RingHom.congr_fun hg z
    calc σ0 z = c (c (σ0 z)) := (hU.1 _).symm
      _ = c z := by rw [h1]
  have hth : ∀ z, GlobalTheory.InertLoc.th ψ hch k z = thW ψ hw h (k * c k) z := fun z => by
    rw [GlobalTheory.InertLoc.th_apply, thW_apply, hσ, hsec]
  obtain ⟨β, -, hβ, -⟩ := hV D.sp.X'
  have hi : 0 < D.sp.X'.rank := by
    have h1 := D.R.m_add_three_le_k
    rw [D.sp.X'_rank, Formalism.BasicNotions.Ranks.rankX', Formalism.BasicNotions.Ranks.r]
    omega
  have := GlobalTheory.InertLoc.th_cond hψ hch hU0.2.1 hβ ⟨0, hi⟩ hk z
  simpa only [hth] using this

end GlobalTheory.InertFrameLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrincipalCongruenceRealPointsIntegrationHeightOn
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.PrinMeas

variable {D : D7}

theorem proj_mem_stabLoc_of_mem_prinInf (A : HSp D) (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D))
    (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) (hfr : Formalism.L2.DIV.IsFrame β (frameLat A)) {g : GA D A}
    (hg : g ∈ prinInf A β Z) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    proj D.sp.cm.sig A.gram v g ∈ stabLoc D.sp.cm.sig A.gram (frameLat A) v :=
  (_root_.GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D A β (frameLat A) hfr g).1 (Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev hg)) v

theorem frameInv_eq_one {θ : InfFam D} {A : HSp D} {cA : CptF A} {a : GL (Fin A.rank) (AE D)} (h : Defin θ A cA a)
    (τ : D.what₂.Tau) : frameInv θ A a τ = 1 := by
  have h3 := h.maj_eq τ
  rw [Matrix.mul_one] at h3
  rw [frameInv, Matrix.mul_assoc]
  exact mul_eq_one_comm.1 h3

theorem prinInf_props : ∀ (D : D7) (θ : InfFam D) (A : HSp D) (cA : CptF A) (a : GL (Fin A.rank) (AE D)), Defin θ A cA a → ∀ (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)), Formalism.L2.DIV.IsFrame β (frameLat A) → ∀ m : Measure (GA D A), m.IsHaarMeasure → MeasurableSet (prinInf A β Z) ∧ prinInf A β Z ⊆ openOff A (frameLat A) (under Z) ∧ (∀ g ∈ prinInf A β Z, hgtL A (frameLat A) a g = 1) ∧ ∃ mR : Measure (GinfC A), mR.IsHaarMeasure ∧ ∀ F : GA D A → ℂ, Continuous F → (∀ (b : GinfC A), ∀ κ ∈ prin A β Z, F ((b : GA D A) * κ) = F b) → ∫ g in prinInf A β Z, F g ∂m = ∫ b : GinfC A, F b ∂mR := by
  intro D θ A cA a hD β Z hfr m hm
  haveI := hm
  set K := prin A β Z
  let S : Subgroup (GA D A) := (Formalism.L2.DIV.lev D.sp.cm A.gram β (prinDat A Z)).comap (Formalism.IndefR.Lev.finE A)
  have hSset : (S : Set (GA D A)) = prinInf A β Z := rfl
  have hstab : ∀ g ∈ S, ∀ v, proj D.sp.cm.sig A.gram v g ∈ stabLoc D.sp.cm.sig A.gram (frameLat A) v :=
    fun g hg v => proj_mem_stabLoc_of_mem_prinInf A β Z hfr hg v

  obtain ⟨U, hU, hUk⟩ := _root_.GlobalTheory.ChainOnto.LevelOpen.exists_open_princ D A β Z
  have hUS : U ≤ S := fun k hk => by
    refine Subgroup.mem_comap.2 (GlobalTheory.LevSplit.mem_lev_of_red D.sp.cm A.gram β (prinDat A Z) _
      (GlobalTheory.LevSplit.finE_mem_UA A k) (hUk k hk).1 fun PP hPP => ?_)
    rcases hPP with h | h
    · exact (hUk k hk).2 PP h
    · exact absurd h (Finset.notMem_empty PP)
  have hSopen : IsOpen (S : Set (GA D A)) := Subgroup.isOpen_mono hUS hU

  have hfinK : ∀ g ∈ S, (GlobalTheory.AutMult.toFin A g : GA D A) ∈ K := fun g hg =>
    ⟨(GlobalTheory.AutMult.toFin A g).2, Subgroup.mem_comap.2 (by
      rw [GlobalTheory.ChainOnto.HaarInf.finE_toFin]; exact Subgroup.mem_comap.1 hg)⟩
  have hker : {g : GA D A | g ∈ S ∧ GlobalTheory.AutMult.toInf A g = 1} = (K : Set (GA D A)) := by
    ext g
    simp only [Set.mem_setOf_eq, GlobalTheory.ChainOnto.HaarInf.toInf_eq_one_iff]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have hKc : IsCompact (K : Set (GA D A)) :=
    GlobalTheory.T.isCompact_finite_adelic_subgroup_integral_open D A (frameLat A) (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat A) K inf_le_left
      (fun k hk v => hstab k hk.2 v) ⟨U, hU, fun k hk hkf => ⟨hkf, hUS hk⟩⟩
  have hpi : ∀ b : GinfC A, GlobalTheory.AutMult.toInf A ((GinfC A).subtype b) = b := fun b => GlobalTheory.AutMult.toInf_coe b
  have hiS : ∀ b : GinfC A, (GinfC A).subtype b ∈ S := fun b => by
    refine Subgroup.mem_comap.2 ?_
    rw [Subgroup.subtype_apply, GlobalTheory.ChainOnto.HaarInf.finE_of_mem_ginfC A b.2]; exact one_mem _
  have hHaar : (Measure.map (GlobalTheory.AutMult.toInf A) (m.restrict (S : Set (GA D A)))).IsHaarMeasure :=
    _root_.GlobalTheory.ChainOnto.map_restrict_isHaar (GA D A) (GinfC A) m S (GinfC A).subtype (GlobalTheory.AutMult.toInf A) hSopen
      continuous_subtype_val (GlobalTheory.AutMult.continuous_toInf A) hpi hiS (hker ▸ hKc)
  refine ⟨hSopen.measurableSet, fun g hg v _ => hstab g hg v, fun g hg => ?_, _, hHaar, fun F hF hinv => ?_⟩
  ·
    have hK : g ∈ Kmax A a := by
      refine (hD.maj.mem_Kmax_iff hD.inf g).2 ⟨mem_levelOpen.2 (hstab g hg), fun τ => ?_⟩
      rw [frameInv_eq_one hD τ]
      exact Commute.one_right _
    have := hgt_mul A a 1 ((io_mem_Khat A a).2 ⟨hK, one_mem _⟩)
    change hgt A a (io A (g, 1)) = 1
    simpa using this
  · have hmeas : AEMeasurable (GlobalTheory.AutMult.toInf A) (m.restrict (S : Set (GA D A))) :=
      (GlobalTheory.AutMult.continuous_toInf A).measurable.aemeasurable
    have hFA : ∀ g ∈ (S : Set (GA D A)), F g = (fun b : GinfC A => F b) (GlobalTheory.AutMult.toInf A g) := fun g hg => by
      conv_lhs => rw [← GlobalTheory.AutMult.toInf_mul_toFin g]
      exact hinv _ _ (hfinK g hg)
    have hf : AEStronglyMeasurable (fun b : GinfC A => F b)
        (Measure.map (GlobalTheory.AutMult.toInf A) (m.restrict (S : Set (GA D A)))) :=
      (hF.comp continuous_subtype_val).aestronglyMeasurable
    rw [← hSset, setIntegral_congr_fun hSopen.measurableSet hFA, integral_map hmeas hf]

end GlobalTheory.Core.Rk.PrinMeas
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralSplitPlaceAdelicStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedDoublingIntegral_splitPlace_adelic : GlobalTheory.Published.UnramifiedDoublingGL → ∀ D : D7, LocalZetaOn D fun v => Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  first | exact @GlobalTheory.Core.Rk.IP.localZetaOn_split | exact GlobalTheory.Core.Rk.IP.localZetaOn_split | (intros; apply GlobalTheory.Core.Rk.IP.localZetaOn_split <;> assumption)
end

