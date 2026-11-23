module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0269
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.FundamentalContinuity.AdelicIsomorphismStatement
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0296
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerDualHalfDerivativeLinearForm
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn

theorem gramAt_conjTranspose {D : D7} (V : HSp D) (τ : D.what₂.Tau) : (gramAt D V τ)ᴴ = gramAt D V τ := by
  ext i j
  have hcm := D.host.isCMField_hostE
  have h1 : star (V.hT (V.frame j) (V.frame i)) = V.hT (V.frame i) (V.frame j) := V.herm.eq _ _
  simp only [Matrix.conjTranspose_apply, gramAt, Matrix.map_apply, HSpace.gram]
  rw [← h1]
  exact (NumberField.IsCMField.complexEmbedding_complexConj _ (tauE D τ) _).symm

theorem conj_complexPlace_traceZero_element (D : D7) (τ : D.what₂.Tau) : conj (tauE D τ D.host.xi0) = -tauE D τ D.host.xi0 := by
  have hcm := D.host.isCMField_hostE
  rw [← NumberField.IsCMField.complexEmbedding_complexConj _ (tauE D τ) _]
  have h := GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D
  change tauE D τ (star D.host.xi0) = _
  rw [h, map_neg]

theorem re_trace_swap {n m : ℕ} (c : ℂ) (hc : conj c = -c) (G : Matrix (Fin n) (Fin n) ℂ) (hG : Gᴴ = G)
    (X Y : Matrix (Fin n) (Fin m) ℂ) :
    (c * Matrix.trace (Xᴴ * G * Y)).re = -(c * Matrix.trace (Yᴴ * G * X)).re := by
  have ht : Matrix.trace (Xᴴ * G * Y) = conj (Matrix.trace (Yᴴ * G * X)) := by
    have h := Matrix.trace_conjTranspose (Yᴴ * G * X)
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG,
      ← Matrix.mul_assoc] at h
    exact h
  rw [ht]
  have hre : c.re = 0 := by
    have := congrArg Complex.re hc
    simp only [Complex.conj_re, Complex.neg_re] at this
    linarith
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, hre]
  ring

end GlobalTheory.StdUnn


open GlobalTheory.Unf in
theorem GlobalTheory.StdUnn.sch_dRho_dualHalf : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ (τ : D.what₂.Tau) (Y : Matrix (Fin B.rank) (Fin A.rank) ℂ) (x : Mx D B.rank A.rank), sch ψ A B ν 𝓨 (Formalism.IndefR.Datum.dRho (heisO ψ (dblSp A) B) θ τ (Y * (dblDec A).qY.map (tauE D τ)) f) x = -(2 * Real.pi * Complex.I) * ((2 * (tauE D τ D.host.xi0 * Matrix.trace (Yᴴ * gramAt D B τ * compAt θ τ x)).re : ℝ) : ℂ) * sch ψ A B ν 𝓨 f x := by
  intro D ψ hψ θ hθ A B ν 𝓨 hν f hf τ Y x
  let d := dblDec A
  let v : VolM D B.rank A.rank := ⟨ν, 𝓨, hν⟩
  have hL := GlobalTheory.OrientedHeis.isLineAt_lineAt (m := B.rank) (n := A.rank) hθ τ Y
  have hq : compAt θ τ d.pY = d.qY.map (tauE D τ) := by
    ext i j
    exact (hθ τ).1 _
  have hL' : IsLineAt θ τ (Y * compAt θ τ d.pY) ((d.extY B).comp (lineAt θ τ Y)) := by
    refine ⟨?_, fun t => ?_, fun t τ' => ?_⟩
    · exact hL.1.matrix_mul continuous_const
    · show ((lineAt θ τ Y t) * d.pY).map (finPart D) = 0
      rw [Matrix.map_mul, hL.2.1 t, Matrix.zero_mul]
    · show compAt θ τ' ((lineAt θ τ Y t) * d.pY) = _
      rw [GlobalTheory.OrientedHeis.compAt_mul, hL.2.2 t τ']
      split_ifs with h
      · subst h
        rw [Matrix.smul_mul]
      · rw [Matrix.zero_mul]
  have hline := GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ hL' (GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ _)
  have hline' : ∀ t, d.extY B (lineAt θ τ Y t) = lineAt θ τ (Y * compAt θ τ d.pY) t := fun t => by
    rw [← hline]; rfl
  have hder := GlobalTheory.Unf.hasDerivAt_mixS_extY D ψ hψ θ hθ (dblSp A) (zeroSp D) B A.rank d v f hf
    (lineAt θ τ Y) hL.1 hL.2.1 x 0
  have hfun : (fun p => deriv (fun t : ℝ => heisO ψ (dblSp A) B (d.extY B (lineAt θ τ Y t)) f p) 0) =
      dRho (heisO ψ (dblSp A) B) θ τ (Y * compAt θ τ d.pY) f := by
    funext p
    simp only [hline']
    rfl
  change HasDerivAt (fun t : ℝ => ψ (symplO (dblSp A) B (d.extX B x) (d.extY B (lineAt θ τ Y t))) * d.mixS B ψ v.μ v.𝓕 f x 0) (d.mixS B ψ v.μ v.𝓕 (fun p => deriv (fun t : ℝ => heisO ψ (dblSp A) B (d.extY B (lineAt θ τ Y t)) f p) 0) x 0) 0 at hder
  rw [hfun] at hder
  have hphase : ∀ t : ℝ, ψ (symplO (dblSp A) B (d.extX B x) (d.extY B (lineAt θ τ Y t))) =
      Complex.exp ((2 * Real.pi * Complex.I *
        (GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt (GlobalTheory.Size.posSp D A.rank) B τ Y (compAt θ τ x) : ℂ)) * t) := by
    intro t
    have e := GlobalTheory.ThetaDecay.psi_symplOH_lineAt hψ hθ (GlobalTheory.Size.posSp D A.rank) B x τ Y t
    have e2 : symplOH (dblSp A) B (d.extX B x) (d.extY B (lineAt θ τ Y t)) =
        symplOH (GlobalTheory.Size.posSp D A.rank) B x (lineAt θ τ Y t) := by
      rw [d.symplOH_extX_extY]
      exact (congrArg (trHalf D) (hO_posSp D B A.rank x _)).symm
    have e3 : ψ (symplOH (dblSp A) B (d.extX B x) (d.extY B (lineAt θ τ Y t))) =
        Complex.exp ((Real.pi * Complex.I) *
          ((t * GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt (GlobalTheory.Size.posSp D A.rank) B τ Y (compAt θ τ x) : ℝ) : ℂ)) := by
      rw [e2]; exact e
    rw [symplO_eq_two_half, AddChar.map_add_eq_mul, e3, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hfun2 : (fun t : ℝ => ψ (symplO (dblSp A) B (d.extX B x) (d.extY B (lineAt θ τ Y t))) *
      d.mixS B ψ v.μ v.𝓕 f x 0) =
      fun t : ℝ => Complex.exp ((2 * Real.pi * Complex.I *
        (GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt (GlobalTheory.Size.posSp D A.rank) B τ Y (compAt θ τ x) : ℂ)) * t) *
          d.mixS B ψ v.μ v.𝓕 f x 0 :=
    funext fun t => by rw [hphase]
  rw [hfun2] at hder
  set a : ℝ := GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt (GlobalTheory.Size.posSp D A.rank) B τ Y (compAt θ τ x) with ha_def
  set M := d.mixS B ψ v.μ v.𝓕 f x 0 with hM
  have hexp : HasDerivAt (fun t : ℝ => Complex.exp ((2 * Real.pi * Complex.I * (a : ℂ)) * t) * M)
      ((2 * Real.pi * Complex.I * (a : ℂ)) * M) 0 := by
    have h2 : HasDerivAt (fun u : ℂ => Complex.exp ((2 * Real.pi * Complex.I * (a : ℂ)) * u) * M)
        (Complex.exp ((2 * Real.pi * Complex.I * (a : ℂ)) * ((0:ℝ):ℂ)) * ((2 * Real.pi * Complex.I * (a : ℂ)) * 1) * M)
        ((0:ℝ):ℂ) :=
      (((hasDerivAt_id _).const_mul (2 * Real.pi * Complex.I * (a : ℂ))).cexp).mul_const M
    have h3 := h2.comp_ofReal
    refine h3.congr_deriv ?_
    simp
  have heq := hder.unique hexp
  have ha : a = -(2 * (tauE D τ D.host.xi0 * Matrix.trace (Yᴴ * gramAt D B τ * compAt θ τ x)).re) := by
    rw [ha_def]
    refine (GlobalTheory.Unf.symplAt_posSp D B A.rank τ Y (compAt θ τ x)).trans ?_
    rw [GlobalTheory.StdUnn.re_trace_swap _ (GlobalTheory.StdUnn.conj_complexPlace_traceZero_element D τ) _ (GlobalTheory.StdUnn.gramAt_conjTranspose B τ)]
    ring
  show d.mixS B ψ ν 𝓨 _ x 0 = _ * d.mixS B ψ ν 𝓨 f x 0
  rw [← hq]
  change d.mixS B ψ v.μ v.𝓕 _ x 0 = _ * M
  rw [heq, ha]
  push_cast
  ring

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondModelFinitePartFrameActionMatrix
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.AdBridge

namespace GlobalTheory.Core.Mi.FinFrame

theorem eq_self_of_rat_of_int (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ι : E ⊗[F] Formalism.MainNotions.S.Af F →+* E ⊗[F] Formalism.MainNotions.S.Af F)
    (hι : ∀ x, ι (Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) x) = Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) x)
    (hO : ∀ a ∈ IntAf F E, ι a ∈ IntAf F E) (a : E ⊗[F] Formalism.MainNotions.S.Af F) : ι a = a := by
  obtain ⟨-, hden, hzero, hdenom, -⟩ := GlobalTheory.St.G.IntAd.integral_adeles_properties F E
  have key : ∀ b ∈ IntAf F E, ι b = b := by
    intro b hb
    rw [← sub_eq_zero]
    refine hzero _ fun m hm => ?_
    obtain ⟨x, t, ht, rfl⟩ := hden b hb m hm
    refine ⟨ι t - t, (IntAf F E).sub_mem (hO _ ht) ht, ?_⟩
    simp only [map_add (f := _), map_mul, map_natCast, hι]
    ring
  obtain ⟨m, hm, hma⟩ := hdenom a
  have h := key _ hma
  simp only [map_mul, map_natCast] at h
  have hu : IsUnit (m : E ⊗[F] Formalism.MainNotions.S.Af F) := by
    have : IsUnit (m : F) := (Nat.cast_ne_zero.2 hm.ne').isUnit
    simpa using this.map (algebraMap F (E ⊗[F] Formalism.MainNotions.S.Af F))
  exact hu.mul_left_cancel h

theorem tauF_eq (D : D7) (z : AE D) : tauF (Formalism.L2.SG.InstExistsPf.instOf D) z = toEAf D z := by
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero (toEAf D)).symm
  | tmul a x => exact tauF_tmul (Formalism.L2.SG.InstExistsPf.instOf D) a x
  | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add (toEAf D) x y).symm)

theorem fmat_iota (D : D7) (g : GA D (D.sp.Y 0)) :
    (Formalism.L2.SG.InstExistsPf.instOf D).fmat (Formalism.IndefR.RationalEmbedding.iota D g).2 = (mt (D.sp.Y 0) g).map (toEAf D) := by
  have hb := Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D (Formalism.IndefR.RationalEmbedding.iota D g)
  have key : (Formalism.IndefR.RationalEmbedding.iota D).symm (Formalism.IndefR.RationalEmbedding.iota D g) = g :=
    (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply g
  refine (hb.2.trans (congrArg (fun q => ofHAFin (Formalism.IndefR.RationalEmbedding.inst D) q) key)).trans ?_
  ext i j
  exact tauF_eq D _

theorem toEAf_incA (D : D7) (y : D.host.E) :
    toEAf D (incA D y) = Formalism.UG.inclE (F := D.host.F) (Formalism.MainNotions.S.Af D.host.F) y :=
  (tauF_eq D _).symm.trans (tauF_tmul (Formalism.L2.SG.InstExistsPf.instOf D) 1 y)

theorem map_cols {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) {m n : ℕ} (M : Matrix (Fin m) (Fin m) A)
    (N : Matrix (Fin m) (Fin n) A) (P : Matrix (Fin n) (Fin n) A) (h : M * N = N * P) (j : Fin n) :
    M.map f *ᵥ (fun k => f (N k j)) = ∑ i, f (P i j) • fun k => f (N k i) := by
  funext k
  have h3 := congrArg f (congrFun (congrFun h k) j)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, map_sum, map_mul] at h3
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [h3]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem embA_cols {D : D7} {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (a : GA D A)
    (j : Fin A.rank) :
    (mt S (embA d o a)).map (toEAf D) *ᵥ
        (fun k => Formalism.UG.inclE (F := D.host.F) (Formalism.MainNotions.S.Af D.host.F) ((d.i₀ * o.iA) k j)) =
      ∑ i, toEAf D (mt A a i j) • fun k => Formalism.UG.inclE (F := D.host.F) (Formalism.MainNotions.S.Af D.host.F) ((d.i₀ * o.iA) k i) := by
  have h1 : mt S (embA d o a) ⬝ (d.j0 ⬝ o.jA) = (d.j0 ⬝ o.jA) ⬝ mt A a := by
    change mt S (d.emb0 (o.emb (a, 1))) ⬝ (d.j0 ⬝ o.jA) = _
    rw [← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, Matrix.mul_assoc, o.emb_jA, Matrix.mul_assoc]
  have h2 : d.j0 ⬝ o.jA = (d.i₀ * o.iA).map (incA D) := (Matrix.map_mul (f := incA D)).symm
  rw [h2] at h1
  have h3 := map_cols (toEAf D) _ _ _ h1 j
  simp only [Matrix.map_apply, toEAf_incA] at h3
  exact h3

theorem transport (D : D7) (I : AutInst) (ιE : I.E ≃+* D.host.E) (hId : ∀ y, HEq (ιE y) y)
    (hI : I = Formalism.L2.SG.InstExistsPf.instOf D) (hr : (D.sp.Y 0).rank = I.n)
    (ιA : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)
    (hrat : ∀ x : I.E, ιA (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) x) =
      Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (ιE x))
    (hint : ∀ a, a ∈ IntAf I.F I.E ↔ ιA a ∈ IntAf D.host.F D.host.E)
    {n : ℕ} (q : Fin n → Fin I.n → I.E) (g : GA D (D.sp.Y 0)) (c : Fin n → GlobalTheory.AdForm.EF D) (j : Fin n)
    (H : (mt (D.sp.Y 0) g).map (toEAf D) *ᵥ
        (fun k => Formalism.UG.inclE (F := D.host.F) (Formalism.MainNotions.S.Af D.host.F) (ιE (q j (Fin.cast hr k)))) =
      ∑ i, c i • fun k => Formalism.UG.inclE (F := D.host.F) (Formalism.MainNotions.S.Af D.host.F) (ιE (q i (Fin.cast hr k)))) :
    I.fmat (castGA hI.symm (Formalism.IndefR.RationalEmbedding.iota D g)).2 *ᵥ incl I (q j) = ∑ i, ιA.symm (c i) • incl I (q i) := by
  generalize hI.symm = e
  subst hI
  have hid : ∀ y, ιE y = y := fun y => eq_of_heq (hId y)
  have hA : ∀ a, ιA a = a := eq_self_of_rat_of_int (Formalism.L2.SG.InstExistsPf.instOf D).F (Formalism.L2.SG.InstExistsPf.instOf D).E ιA.toRingHom
    (fun x => (hrat x).trans (congrArg _ (hid x))) (fun a ha => (hint a).1 ha)
  have hA' : ∀ a, ιA.symm a = a := fun a => (hA _).symm.trans (ιA.apply_symm_apply a)
  simp only [hid] at H
  simp only [hA']
  change (Formalism.L2.SG.InstExistsPf.instOf D).fmat (Formalism.IndefR.RationalEmbedding.iota D g).2 *ᵥ _ = _
  rw [fmat_iota]
  exact H

theorem repM_toH : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (B : SBes X h u ψ (D.sp.X 0)) (F : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F), IdE X → B.Adapted tr.wt → ∀ a : GA D (D.sp.X 0), RepM X tr.wt tr.ιA ((B.toH a).2 : X.B.I.Gf) (GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a) := by
  intro D X h u ψ B F tr hId hAd a j
  have hn := Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)
  refine transport D X.B.I X.ιE hId h (rank_eq X h) tr.ιA tr.ιA_rat tr.ιA_int
    (fun i => X.crd (Formalism.L2.SG.ColDict.qFr tr.wt i)) (embA B.d B.o a)
    (fun i => GlobalTheory.AdForm.finM (D.sp.X 0) hn a i j) j ?_
  have H := embA_cols B.d B.o a (Fin.cast hn.symm j)
  simp only [hAd _ _] at H
  refine H.trans ?_
  exact Fintype.sum_equiv (finCongr hn) _ _ fun i => rfl

end GlobalTheory.Core.Mi.FinFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondModelRealPartMatrixFrame
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi.RealMat

variable {D : D7}

theorem psiT_incA (τ : D.what₂.Tau) (x : D.host.E) : Formalism.IndefR.Eqv.psiT D τ (incA D x) = tauE D τ x := by
  show Formalism.IndefR.Eqv.thetaC D τ ((fstA D.host.F 1) ⊗ₜ[D.host.F] x) = _
  rw [Formalism.IndefR.Eqv.thetaC_tmul]
  simp

theorem embA_cols {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (a : GA D A) :
    HMul.hMul (Formalism.L2.Theta.mt S (embA d o a)) (rat (d.i₀ * o.iA) : Matrix (Fin S.rank) (Fin A.rank) (AE D)) =
      HMul.hMul (rat (d.i₀ * o.iA) : Matrix (Fin S.rank) (Fin A.rank) (AE D)) (Formalism.L2.Theta.mt A a) := by
  have e : (rat (d.i₀ * o.iA) : Mx D S.rank A.rank) = HMul.hMul d.j0 o.jA := rat_mul _ _
  rw [e, GlobalTheory.MixPer.embA_apply d o a, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, Matrix.mul_assoc, o.emb_jA, Matrix.mul_assoc]

theorem embA_cols_at {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (a : GA D A) (τ : D.what₂.Tau) :
    (Formalism.L2.Theta.mt S (embA d o a)).map (Formalism.IndefR.Eqv.psiT D τ) * (d.i₀ * o.iA).map (tauE D τ) =
      (d.i₀ * o.iA).map (tauE D τ) * (Formalism.L2.Theta.mt A a).map (Formalism.IndefR.Eqv.psiT D τ) := by
  have e : (d.i₀ * o.iA).map (tauE D τ) =
      (rat (d.i₀ * o.iA) : Mx D S.rank A.rank).map (Formalism.IndefR.Eqv.psiT D τ) := by
    ext i j
    exact (psiT_incA τ _).symm
  rw [e, ← Matrix.map_mul, ← Matrix.map_mul, embA_cols]

theorem act_gen {I : Formalism.MainNotions.S.AutInst} (h : I = Formalism.L2.SG.InstExistsPf.instOf D)
    (ιE : I.E ≃+* D.host.E) (hιE : ∀ x : I.E, HEq (ιE x) x) (pl : InfinitePlace I.F ≃ D.what₂.Tau)
    (hφ : ∀ v (x : I.E), I.φ v x = embS D (pl v) (ιE x)) (hr : (D.sp.Y 0).rank = I.n) (k : GA D (D.sp.Y 0))
    (τ : D.what₂.Tau) {m : ℕ} (C : Matrix (Fin (D.sp.Y 0).rank) (Fin m) D.host.E) (M : Matrix (Fin m) (Fin m) ℂ)
    (x : Fin m → Fin I.n → I.E) (hx : ∀ i j, C i j = ιE (x j (Fin.cast hr i)))
    (hC : (Formalism.L2.Theta.mt (D.sp.Y 0) k).map (Formalism.IndefR.Eqv.psiT D τ) * C.map (tauE D τ) = C.map (tauE D τ) * M) (b : Fin m) :
    uMat (((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm) k).1 (pl.symm τ)) *ᵥ rv I (pl.symm τ) (x b) =
      ∑ i, M i b • rv I (pl.symm τ) (x i) := by
  subst h
  have hι : ∀ x, ιE x = x := fun x => eq_of_heq (hιE x)
  have key : ∀ τ τ' : D.what₂.Tau, embS D τ = embS D τ' → τ = τ' :=
    fun τ τ' e => D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 e))
  have hpl : pl = (Formalism.L2.Host.tauPl D).symm := Equiv.ext fun v => key _ _ (RingHom.ext fun x => by
    have e := hφ v x
    have e2 : embS D (pl v) (ιE x) = embS D (pl v) x := congrArg _ (hι x)
    exact (e2.symm.trans e.symm).trans (SeeReal.phi_inst v x))
  have hcol : ∀ j, (fun i => (Formalism.L2.SG.InstExistsPf.instOf D).φ (pl.symm τ) (x j i)) =
      fun i : Fin (D.sp.Y 0).rank => (C.map (tauE D τ)) i j := by
    intro j
    funext i
    rw [hφ, Equiv.apply_symm_apply]
    exact (congrArg (tauE D τ) (hx i j)).symm
  subst hpl
  have hT : ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA (rfl : Formalism.L2.SG.InstExistsPf.instOf D = _).symm)) k =
      Formalism.IndefR.RationalEmbedding.iota D k := rfl
  have hP := Formalism.L2.SG.EvalTIota.P_isUnit_det' (D := D) (Formalism.L2.Host.tauPl D τ)
  have hbr := Formalism.L2.SG.EvalTIota.infMat_brg_i (Formalism.IndefR.RationalEmbedding.iota D k) τ
  rw [ContinuousMulEquiv.symm_apply_apply, Formalism.IndefR.Eqv.infMat_thetaC] at hbr
  have hu := SeeReal.eq_of_conj hP hbr.symm
  have hrv : ∀ j, rv (Formalism.L2.SG.InstExistsPf.instOf D) ((Formalism.L2.Host.tauPl D).symm.symm τ) (x j) =
      (Formalism.L2.SG.EvalTIota.Pi (D := D) (Formalism.L2.Host.tauPl D τ))⁻¹ *ᵥ
        fun i : Fin (D.sp.Y 0).rank => (C.map (tauE D τ)) i j := by
    intro j
    rw [← hcol j]
    rfl
  have main : Formalism.L2.SG.EvalTIota.uM' (Formalism.IndefR.RationalEmbedding.iota D k) (Formalism.L2.Host.tauPl D τ) *ᵥ
      ((Formalism.L2.SG.EvalTIota.Pi (D := D) (Formalism.L2.Host.tauPl D τ))⁻¹ *ᵥ
        fun i : Fin (D.sp.Y 0).rank => (C.map (tauE D τ)) i b) =
      ∑ j, M j b • ((Formalism.L2.SG.EvalTIota.Pi (D := D) (Formalism.L2.Host.tauPl D τ))⁻¹ *ᵥ
        fun i : Fin (D.sp.Y 0).rank => (C.map (tauE D τ)) i j) := by
    rw [hu, Matrix.mulVec_mulVec, Matrix.mul_assoc _ (Formalism.L2.SG.EvalTIota.Pi _), Matrix.mul_nonsing_inv _ hP,
      Matrix.mul_one, ← Matrix.mulVec_mulVec]
    simp_rw [← Matrix.mulVec_smul]
    rw [← Matrix.mulVec_sum]
    congr 1
    funext i
    have e := congrFun (congrFun hC i) b
    simp only [Matrix.mul_apply] at e
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    exact e.trans (Finset.sum_congr rfl fun j _ => mul_comm _ _)
  refine (congrArg (fun w => Formalism.L2.SG.EvalTIota.uM' (Formalism.IndefR.RationalEmbedding.iota D k) (Formalism.L2.Host.tauPl D τ) *ᵥ w) (hrv b)).trans ?_
  exact main.trans (Finset.sum_congr rfl fun j _ => congrArg (fun w => M j b • w) (hrv j).symm)

theorem gramQ_isUnit (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hW : (∀ x y, (VS D).hT (wt x) (wt y) = (VS D).hT x y) ∧ (∀ a, wt (X.eX a) = D.sp.hypE a) ∧
      (∀ a, wt (X.fY a) = D.sp.hypF a) ∧ wt (X.zu u) = D.zmOf u) (v : InfinitePlace X.B.I.F) :
    IsUnit (Formalism.L2.SG.ColDict.gramQ X wt v).det := by
  obtain ⟨Q, Qi, G', hQQi, hQiQ, hQq, -, -, -, hG', hblk⟩ := GlobalTheory.St.qFrame_basis_gram D X u wt hW
  set φ := X.B.I.φ v with hφ
  set G := (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm with hGdef
  have hgram : Formalism.L2.SG.ColDict.gramQ X wt v = G.map φ := by
    ext a b
    have h1 := congrFun (congrFun hblk (Sum.inl a)) (Sum.inl b)
    rw [Matrix.fromBlocks_apply₁₁] at h1
    rw [Matrix.map_apply, ← h1]
    simp only [Formalism.L2.SG.ColDict.gramQ, Matrix.of_apply, Formalism.L2.SG.ColDict.rvV]
    have := PI.ScPiFrameW.hJ_rv X.B.I v (X.crd (Formalism.L2.SG.ColDict.qFr wt a)) (X.crd (Formalism.L2.SG.ColDict.qFr wt b))
    refine this.trans ?_
    congr 1
    simp only [Formalism.UG.hform, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, hQq, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hdetG : G.det ≠ 0 := by
    have hJu : IsUnit X.B.I.J.det := isUnit_iff_ne_zero.mpr X.B.I.J_det
    have hJinv : X.B.I.J * X.B.I.J⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJu
    have hR : Matrix.fromBlocks G 0 0 G' *
        (Qi * X.B.I.J⁻¹ * (Qi.map (starRingEnd X.B.I.E))ᵀ) = 1 := by
      rw [← hblk]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Q Qi, hQQi, Matrix.one_mul, ← Matrix.mul_assoc X.B.I.J, hJinv, Matrix.one_mul,
        ← Matrix.transpose_mul, ← Matrix.map_mul, hQiQ, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.transpose_one]
    have hd := congrArg Matrix.det hR
    rw [Matrix.det_mul, Matrix.det_one, Matrix.det_fromBlocks_zero₂₁] at hd
    exact left_ne_zero_of_mul (left_ne_zero_of_mul_eq_one hd)
  have hm : (G.map φ).det = φ G.det := (RingHom.map_det φ G).symm
  rw [hgram, hm, isUnit_iff_ne_zero, map_ne_zero]
  exact hdetG

end GlobalTheory.Core.Mi.RealMat


open GlobalTheory.Core.Mi.RealMat in
theorem GlobalTheory.Core.Mi.sTil_toH_eq_infM : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (B : SBes X h u ψ (D.sp.X 0)) (F : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F) (θ : InfFam D), IsInfFam θ → IdE X → B.Adapted tr.wt → ∀ (a : GA D (D.sp.X 0)) (τ : D.what₂.Tau), Formalism.L2.SG.ColDict.sTil X tr.wt ((B.toH a).1 : X.B.I.Ginf) τ = GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a τ := by
  intro D X h u ψ B F tr θ hθ hE hA a τ
  obtain rfl := Formalism.IndefR.Eqv.eq_thetaC D hθ
  have hdetQ := gramQ_isUnit X u tr.wt ⟨tr.wt_isom, tr.wt_e, tr.wt_f, tr.weight_z⟩ (X.pl.symm τ)
  have hn := Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)
  have hact := act_gen h X.ιE hE X.pl X.φ_eq (rank_eq X h) (embA B.d B.o a) τ (B.d.i₀ * B.o.iA) _
    (fun j => X.crd (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast hn j))) hA (embA_cols_at B.d B.o a τ)
  have hlin : ∀ b, uMat (((B.toH a).1 : X.B.I.Ginf) (X.pl.symm τ)) *ᵥ
      Formalism.L2.SG.ColDict.rvV X (X.pl.symm τ) (Formalism.L2.SG.ColDict.qFr tr.wt b) =
      ∑ i, GlobalTheory.AdForm.infM (Formalism.IndefR.Eqv.thetaC D) (D.sp.X 0) hn a τ i b •
        Formalism.L2.SG.ColDict.rvV X (X.pl.symm τ) (Formalism.L2.SG.ColDict.qFr tr.wt i) := by
    intro b
    refine (hact (Fin.cast hn.symm b)).trans ?_
    exact Fintype.sum_equiv (finCongr hn) _ _ fun i => rfl
  have hM : (Matrix.of fun a' b => hJ (X.B.I.ε (X.pl.symm τ))
      (Formalism.L2.SG.ColDict.rvV X (X.pl.symm τ) (Formalism.L2.SG.ColDict.qFr tr.wt a'))
      (uMat (((B.toH a).1 : X.B.I.Ginf) (X.pl.symm τ)) *ᵥ
        Formalism.L2.SG.ColDict.rvV X (X.pl.symm τ) (Formalism.L2.SG.ColDict.qFr tr.wt b))) =
      Formalism.L2.SG.ColDict.gramQ X tr.wt (X.pl.symm τ) * GlobalTheory.AdForm.infM (Formalism.IndefR.Eqv.thetaC D) (D.sp.X 0) hn a τ := by
    ext a' b
    rw [Matrix.of_apply, hlin, Matrix.mul_apply]
    simp only [hJ, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, Formalism.L2.SG.ColDict.gramQ,
      Matrix.of_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  show (Formalism.L2.SG.ColDict.gramQ X tr.wt (X.pl.symm τ))⁻¹ * _ = _
  rw [hM, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdetQ, Matrix.one_mul]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ShiftedAdditiveCharacterArchimedeanParameters
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn


set_option synthInstance.maxHeartbeats 400000 in
theorem shift_char_realPar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ μ : D.host.E, IsSkew μ → ∃ lam : D.host.F, algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ ∧ IsCharAF D.host.F (shift ψ lam) ∧ ∃ l : D.what₂.Tau → ℝ, HasRealPar (shift ψ lam) θ l ∧ ∀ τ, |l τ| = ‖tauE D τ D.host.xi0‖ / ‖tauE D τ μ‖ := by
  intro D ψ hψ θ hθ μ hμ
  have hstar : ∀ x : D.host.E, star x = IsCMField.complexConj D.host.E x := fun _ => rfl
  set y : D.host.E := -D.host.xi0 / μ with hy_def
  have hyc : IsCMField.complexConj D.host.E y = y := by
    rw [hy_def, map_div₀, map_neg, conj_xi0_alt, ← hstar μ, hμ.2, neg_neg, div_neg, neg_div]
  have hyF : y ∈ D.host.F := (IsCMField.complexConj_eq_self_iff D.host.E y).1 hyc
  have hy0 : y ≠ 0 := div_ne_zero (neg_ne_zero.2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)) hμ.1
  let lam : D.host.F := ⟨y, hyF⟩
  have hlam : algebraMap D.host.F D.host.E lam = y := rfl
  have hlam0 : lam ≠ 0 := fun h => hy0 (by rw [← hlam, h, map_zero])
  refine ⟨lam, hlam, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact hψ.1.1.comp (continuous_const.mul continuous_id)
    · intro x; exact hψ.1.2.1 _
    · intro a
      rw [shift, AddChar.mulShift_apply, ← map_mul]
      exact hψ.1.2.2.1 _
    · obtain ⟨x, hx⟩ := hψ.1.2.2.2
      refine ⟨algebraMap D.host.F (AF D.host.F) lam⁻¹ * x, ?_⟩
      rw [shift, AddChar.mulShift_apply, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hlam0, map_one, one_mul]
      exact hx
  ·
    have hreal : ∀ τ, (tauE D τ y).im = 0 := by
      intro τ
      have h := IsCMField.complexEmbedding_complexConj D.host.E (tauE D τ) y
      rw [hyc] at h
      have := congrArg Complex.im h
      rw [Complex.conj_im] at this
      linarith
    refine ⟨fun τ => -(tauE D τ y).re, ?_, ?_⟩
    · intro x
      have e1 : psiInf D.host.F (shift ψ lam) x =
          psiInf D.host.F ψ (algebraMap D.host.F (Ainf D.host.F) lam * x) := by
        simp only [psiInf, shift, AddChar.mulShift_apply]
        congr 1
        show (algebraMap D.host.F (Ainf D.host.F) lam * x, algebraMap D.host.F (Af D.host.F) lam * 0) = _
        rw [mul_zero]; rfl
      rw [e1, hψ.2.2 θ hθ]
      congr 1
      have e2 : ∀ ρ, θ ρ ((algebraMap D.host.F (Ainf D.host.F) lam * x) ⊗ₜ[D.host.F] (1 : D.host.E)) =
          θ ρ (x ⊗ₜ[D.host.F] (1 : D.host.E)) * tauE D ρ y := by
        intro ρ
        have e3 : (algebraMap D.host.F (Ainf D.host.F) lam * x) ⊗ₜ[D.host.F] (1 : D.host.E) =
            (x ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : Ainf D.host.F) ⊗ₜ[D.host.F] y) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← Algebra.smul_def, ← TensorProduct.smul_tmul',
            ← TensorProduct.tmul_smul, Algebra.smul_def, mul_one, hlam]
        rw [e3, map_mul, (hθ ρ).1]
      simp only [e2]
      have e4 : ∀ ρ, (((-(tauE D ρ y).re : ℝ)) : ℂ) = -tauE D ρ y := by
        intro ρ
        apply Complex.ext <;> simp [hreal ρ]
      simp only [e4, Finset.mul_sum]
      push_cast
      refine Finset.sum_congr rfl fun ρ _ => ?_
      ring
    · intro τ
      have h1 : |(tauE D τ y).re| = ‖tauE D τ y‖ := by
        rw [← Complex.abs_re_eq_norm.2 (hreal τ)]
      rw [abs_neg, h1, hy_def, map_div₀, map_neg, norm_div, norm_neg]

end GlobalTheory.StdUnn
end

