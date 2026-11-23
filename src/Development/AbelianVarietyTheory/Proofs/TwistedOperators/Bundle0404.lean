module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0244
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0042
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0011
public import GroundTheory.GlobalFields.TateThesis.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0396
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0377

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsGlueBaseDataOfIsAdelicGlueVector
section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdIsom.GlueBase

open GlobalTheory.IdemSupport (cP)

section Alg

variable {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]

theorem split_prime {e a t t' : A} (ht : t' * t = 1) {y f : M} (hy : e • y = y) :
    y = e • (y - a • f) + (a * (e * t')) • (t • f) := by
  have key : a * (e * t') * t = e * a := by linear_combination (a * e) * ht
  rw [smul_sub, hy, smul_smul, smul_smul, key, sub_add_cancel]

theorem mem_of_mul_sub (S : Subring A) {b h t : A} (hb : b ∈ S) (h1 : b * h ∈ S) (h2 : h - t ∈ S) : b * t ∈ S := by
  have hd := S.sub_mem h1 (S.mul_mem hb h2)
  rwa [mul_sub, sub_sub_cancel] at hd

theorem mem_of_sub (S : Subring A) {a b : A} (ha : a ∈ S) (h : a - b ∈ S) : b ∈ S := by
  have hd := S.sub_mem ha h
  rwa [sub_sub_cancel] at hd

theorem idem_smul_smul {e : A} (he : e * e = e) (x : M) : e • e • x = e • x := by
  rw [smul_smul, he]

end Alg

variable {D : D7}

theorem inc_inv_mul (u : D.what₂.Word) : inc D (Tu D u)⁻¹ * inc D (Tu D u) = 1 := by
  rw [← map_mul, inv_mul_cancel₀ (Tu_ne_zero u), map_one]

theorem cjA_inc_inv (u : D.what₂.Word) : cjA D (inc D (Tu D u)⁻¹) = inc D (Tu D u)⁻¹ := by
  rw [cjA_inc]
  congr 1
  simp [Tu, star_inv₀]

theorem hA_idem {X : HSp D} {e : EAf D} {y : Fin X.rank → EAf D} (hy : cjA D e • y = y) (x : Fin X.rank → EAf D) :
    hA X x y = hA X (e • x) y := by
  conv_lhs => rw [← hy]
  rw [hA_smul_right, hA_smul_left, cjA_cjA]

theorem isBasePair_of_isGlueVec (D : D7) (u : D.what₂.Word) (π : 𝓞 D.host.E) (hπ : IsPi u π) (X : HSp D) (L₀ : Lat X)
    (f : Fin X.rank → EAf D) (hL : Submodule.IsFullLattice D.host.E L₀) (hf : IsGlueVec X u L₀ f) :
    IsBasePair X u π L₀ fun w => idem w • f := by
  have ht : inc D (Tu D u)⁻¹ * inc D (Tu D u) = 1 := inc_inv_mul u
  have := hL
  unfold IsBasePair
  refine ⟨by infer_instance, fun w e he hT y => ?_, fun w e he hπw => ?_⟩
  ·
    obtain rfl := eq_idem he
    have hinv : idem w * inc D (Tu D u)⁻¹ ∈ OA D := (idem_mul_inv_mem_iff u w).2 hT
    simp only [InCmp]
    constructor
    · rintro ⟨hy, hey⟩
      exact ⟨(mem_hat_dualL_iff hL y).2 fun x hx => hf.int x hx y hy, hey⟩
    · rintro ⟨hy, hey⟩
      obtain ⟨a, ha, hya⟩ := hf.dual y ((mem_hat_dualL_iff hL y).1 hy)
      refine ⟨?_, hey⟩
      rw [split_prime (a := a) (f := f) ht hey]
      exact add_mem_hat (smul_mem_hat (idem_mem w) hya) (smul_mem_hat ((OA D).mul_mem ha hinv) hf.mul_mem)
  ·
    obtain rfl := eq_idem he
    have hTw : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
      rw [← pi_mul_cO hπ]
      exact w.asIdeal.mul_mem_right _ hπw
    have hnot : idem w * inc D (Tu D u)⁻¹ ∉ OA D := fun h => (idem_mul_inv_mem_iff u w).1 h hTw
    have hff : hA X f f - inc D (Tu D u)⁻¹ ∈ OA D := hf.norm
    refine ⟨idem_smul_smul (idem_mul_self w) f, ?_, ?_, ?_⟩
    · show inc D (Tu D u) • (idem w • f) ∈ hat L₀
      rw [smul_smul, mul_comm, ← smul_smul]
      exact smul_mem_hat (idem_mem w) hf.mul_mem
    ·
      intro hmem
      apply hnot
      refine mem_of_mul_sub (OA D) (idem_mem w) ?_ hff
      rw [← hA_smul_left, ← cjA_hA]
      exact cjA_mem (hf.pair _ hmem)
    · intro y
      simp only [InCmp]
      constructor
      · rintro ⟨hy, hey⟩
        refine ⟨hey, fun x hx => hf.int x hx.1 y hy, ?_⟩
        rw [hA_smul_left]
        exact (OA D).mul_mem (idem_mem w) (hf.pair y hy)
      · rintro ⟨hey, hx, hfy⟩
        have hdual : ∀ x ∈ hat L₀, hA X x y ∈ OA D := by
          intro x hx'
          rw [hA_idem hey]
          exact hx _ ⟨smul_mem_hat (idem_mem w) hx', idem_smul_smul (idem_mul_self w) x⟩
        obtain ⟨a, ha, hya⟩ := hf.dual y hdual
        refine ⟨?_, hey⟩
        have h1 : cjA D a * idem w * hA X f f ∈ OA D := by
          have hp : hA X (idem w • f) (a • f) ∈ OA D := by
            refine mem_of_sub (OA D) hfy ?_
            rw [← hA_sub_right, hA_smul_left]
            exact (OA D).mul_mem (idem_mem w) (hf.pair _ hya)
          rwa [hA_smul_left, hA_smul_right, ← mul_assoc, mul_comm (idem w)] at hp
        have h2 : cjA D a * idem w * inc D (Tu D u)⁻¹ ∈ OA D :=
          mem_of_mul_sub (OA D) ((OA D).mul_mem (cjA_mem ha) (idem_mem w)) h1 hff
        have h3 : a * (cjA D (idem w) * inc D (Tu D u)⁻¹) ∈ OA D := by
          have hc := cjA_mem h2
          rwa [map_mul, map_mul, cjA_cjA, cjA_inc_inv, mul_assoc] at hc
        rw [split_prime (a := a) (f := f) ht hey]
        exact add_mem_hat (smul_mem_hat (cjA_mem (idem_mem w)) hya) (smul_mem_hat h3 hf.mul_mem)

end GlobalTheory.AdIsom.GlueBase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JEvExistsAndJEvBar
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjReading

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))

private theorem tieIn_of_fwTie' (fw : FWTie T R κ v₀) : TieIn T R κ v₀ :=
  ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩

private theorem pb_eq_of_omPins (hL : R.toLevCh.Is A.μ0) (fw : FWTie T R κ v₀) (i : Fin D.R.m)
    (hOi : OMPins T R κ v₀ O i) : T.pb = R.C.P.pb :=
  GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore R fw.laws.toLawsM hL (hOi.2.tuple ()).half

private theorem jEvExists_and_jEvBar_of_isEmpty (hm : IsEmpty (Fin D.R.m)) : JEvExists T R κ v₀ ∧ JEvBar T R κ := by
  constructor
  · intro i
    exact hm.elim i
  · intro i
    exact hm.elim i

theorem jEvExists_and_jEvBar (hL : R.toLevCh.Is A.μ0) (hM : R.IsModels) (fw : FWTie T R κ v₀)
    (hO : ∀ i, OMPins T R κ v₀ O i) : JEvExists T R κ v₀ ∧ JEvBar T R κ := by
  rcases isEmpty_or_nonempty (Fin D.R.m) with hm | hne
  · exact jEvExists_and_jEvBar_of_isEmpty T R κ v₀ hm
  · obtain ⟨i⟩ := hne
    have htie := tieIn_of_fwTie' T R κ v₀ fw
    have hpb := pb_eq_of_omPins T R κ v₀ O hL fw i (hO i)
    exact GlobalTheory.CuspValues.jEvExists_and_jEvBar _ _ _ _ _ T R κ v₀ hL hM htie hpb

theorem jEvExists (hL : R.toLevCh.Is A.μ0) (hM : R.IsModels) (fw : FWTie T R κ v₀)
    (hO : ∀ i, OMPins T R κ v₀ O i) : JEvExists T R κ v₀ := by
  obtain ⟨hJ, -⟩ := jEvExists_and_jEvBar T R κ v₀ O hL hM fw hO
  exact hJ

theorem jEvBar : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), R.toLevCh.Is A.μ0 → R.IsModels → FWTie T R κ v₀ → (∀ i, OMPins T R κ v₀ O i) → JEvBar T R κ := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O hL hM fw hO
  obtain ⟨-, hB⟩ := jEvExists_and_jEvBar T R κ v₀ O hL hM fw hO
  exact hB

end GlobalTheory.ConjReading
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiActionUnipotentLaws
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc GlobalTheory.Unf.FB GlobalTheory.Unf.FB.ThLaws

noncomputable section

namespace GlobalTheory.Unf.FB.ThLawsL

variable {D : D7}

theorem zEll_rat {σ : ℕ} (B : BesL D σ) :
    ∃ z0 : Matrix (Fin B.L.rank) (Fin (σ + 1)) D.host.E, zEll B.L (σ + 1) B.ζ = rat z0 := by
  refine ⟨Matrix.vecMulVec B.ζ (fun i : Fin (σ + 1) => if i.1 + 1 = σ + 1 then (1 : D.host.E) else 0), ?_⟩
  funext i j
  simp only [zEll, rat, Matrix.map_apply, Matrix.vecMulVec_apply, ell, map_mul, ratV]
  congr 1
  split_ifs <;> simp

theorem th_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (y : WO J.W₀ B.L → ℂ), GlobalTheory.Unf.FB.Quasi ψ J.W₀ B.L y → Continuous (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) ∧ (∃ M : ℝ, (∀ w, ‖y w‖ ≤ M) ∧ ∀ n, ‖(fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) n‖ ≤ M) ∧ (∀ γ ∈ flagN J.d, γ ∈ GQ J.W → ∀ n ∈ flagN J.d, (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (γ * n) = (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) n) ∧ (∀ c, ∀ n ∈ flagN J.d, (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (J.d.nC c * n) = star (ψ (J.d.qS B.L c (zEll B.L (σ + 1) B.ζ))) * (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) n) ∧ (∀ n ∈ flagN J.d, ∀ u ∈ UX D (σ + 1), (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (n * J.d.levi u) = (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) n * star (psiUni ψ u)) ∧ ∀ b, ∀ u ∈ UX D (σ + 1), (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (J.d.nB b * J.d.levi u) = star (psiUni ψ u) * star (y (zEll B.L (σ + 1) B.ζ ⬝ b)) := by
  intro D ψ hψs σ J B y hy
  have hψ : IsCharAF D.host.F ψ := hψs.1
  have hx : ∀ u ∈ UX D (σ + 1), zEll B.L (σ + 1) B.ζ ⬝ u.1 = zEll B.L (σ + 1) B.ζ := fun u hu => zEll_mul B.L B.ζ hu
  obtain ⟨hcen, hmul, hlevi, -⟩ := GlobalTheory.JacHom.jacS_hom D ψ J.W J.W₀ B.L (σ + 1) J.d (zEll B.L (σ + 1) B.ζ) hx
  obtain ⟨M, hM⟩ := exists_bound_quasi hψ hy
  have hval : ∀ n, star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n) =
      star (ψ (cenS J.d B.L (zEll B.L (σ + 1) B.ζ) n) * y (ptS J.d B.L (zEll B.L (σ + 1) B.ζ) n)) * star (psiFlag ψ J.d n) := fun n => by
    rw [jacS_zero_apply]
  have hnorm : ∀ a, ‖ψ a‖ = 1 := hψ.2.1
  have hflag1 : ∀ n, ‖psiFlag ψ J.d n‖ = 1 := fun n => hnorm _
  refine ⟨?_, ⟨M, hM, fun n => ?_⟩, ?_, ?_, ?_, ?_⟩
  · have e : (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) = fun n =>
        star (ψ (cenS J.d B.L (zEll B.L (σ + 1) B.ζ) n) * y (ptS J.d B.L (zEll B.L (σ + 1) B.ζ) n)) * star (psiFlag ψ J.d n) := funext hval
    rw [e]
    exact (((hψ.1.comp (continuous_cenS _ _ _)).mul (hy.2.comp (continuous_ptS _ _ _))).star).mul
      (continuous_psiFlag hψ.1 _).star
  · show ‖star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)‖ ≤ M
    rw [hval, norm_mul, norm_star, norm_star, norm_mul, hnorm, hflag1, one_mul, mul_one]
    exact hM _
  · intro γ hγN hγQ n hn
    obtain ⟨z0, hz0⟩ := zEll_rat B
    have hp := hmul γ hγN n hn
    obtain ⟨g0, hg0⟩ := ptS_rat J.d B.L z0 hγQ
    rw [← hz0] at hg0
    have hc : ψ (cenS J.d B.L (zEll B.L (σ + 1) B.ζ) γ) = 1 := by rw [hz0]; exact psi_cenS_rat hψ J.d B.L z0 hγQ
    show star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) (γ * n) y 0) * star (psiFlag ψ J.d (γ * n)) =
      star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)
    rw [hval, hval, hp.1, hp.2.1, psiFlag_mul J.d ψ hγN hn, psiFlag_rat hψ J.d hγQ, one_mul, hg0, hy.1 g0]
    congr 2
    rw [← mul_assoc, ← AddChar.map_add_eq_mul, add_neg_cancel_right, AddChar.map_add_eq_mul, hc, one_mul]
  · intro c n hn
    have hc : J.d.nC c ∈ flagN J.d := J.d.nC_mem_NFlag c
    show star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) (J.d.nC c * n) y 0) * star (psiFlag ψ J.d (J.d.nC c * n)) =
      _ * (star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n))
    rw [(hmul _ hc n hn).2.2, psiFlag_mul J.d ψ hc hn, psiFlag_nC, jacS_nC]
    simp only [Pi.smul_apply, smul_eq_mul, star_mul', one_mul, star_one]
    ring
  · intro n hn u hu
    have hl : J.d.levi u ∈ flagN J.d := J.d.levi_mem_NFlag hu
    show star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) (n * J.d.levi u) y 0) * star (psiFlag ψ J.d (n * J.d.levi u)) =
      star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n) * _
    rw [hlevi n hn u hu, psiFlag_mul J.d ψ hn hl, psiFlag_levi, star_mul', mul_assoc]
  · intro b u hu
    have hb : J.d.nB b ∈ flagN J.d := J.d.nB_mem_NFlag b
    have hl : J.d.levi u ∈ flagN J.d := J.d.levi_mem_NFlag hu
    have hp : ptS J.d B.L (zEll B.L (σ + 1) B.ζ) (J.d.nB b) = zEll B.L (σ + 1) B.ζ ⬝ b := by
      have := ptS_nB_mul_nC J.d B.L (zEll B.L (σ + 1) B.ζ) b 0
      rwa [J.d.nC_zero, mul_one] at this
    have hc : cenS J.d B.L (zEll B.L (σ + 1) B.ζ) (J.d.nB b) = 0 := by
      have := hcen b 0
      rw [J.d.nC_zero, mul_one] at this
      rw [this, HypDec.qS]
      simp [GlobalTheory.MixModel.symplOH_zero_right]
    show star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) (J.d.nB b * J.d.levi u) y 0) * star (psiFlag ψ J.d (J.d.nB b * J.d.levi u)) = _
    rw [hlevi _ hb u hu, psiFlag_mul J.d ψ hb hl, jacS_zero_apply, hp, hc, AddChar.map_zero_eq_one, one_mul,
      psiFlag_nB, one_mul, psiFlag_levi]
    ring

end GlobalTheory.Unf.FB.ThLawsL

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalLatticeEqIffIdempotentComponentsOver
section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocHat

open GlobalTheory.StdFrames (cpt cpt_ext toAd_spec)

variable {D : D7} {n : ℕ}

theorem mem_hat_iff_locL {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : Λ.FG) (y : Fin n → EAf D) :
    y ∈ hat Λ ↔ ∀ v : HeightOneSpectrum (𝓞 D.host.F),
      (fun i => Formalism.UG.prV (E := D.host.E) v (y i)) ∈ Formalism.L2.Herm.locL v Λ := by
  haveI : Module.Finite (𝓞 D.host.E) Λ := Module.Finite.iff_fg.mpr h
  rw [mem_hat]
  exact GlobalTheory.LatticeStabLocal.mem_latS_adele_iff Λ y

theorem prV_eq_zero_iff_cpt (v : HeightOneSpectrum (𝓞 D.host.F)) (z : EAf D) :
    Formalism.UG.prV (E := D.host.E) v z = 0 ↔ ∀ Q : Pl D.host.E, Q.under (𝓞 D.host.F) = v → cpt Q z = 0 := by
  refine (GlobalTheory.AdeleBaseChange.prV_eq_zero_iff (toAd_spec D) v z).trans ?_
  exact Iff.rfl

theorem mem_hat_iff_of_supp {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : Λ.FG)
    (v : HeightOneSpectrum (𝓞 D.host.F)) {y : Fin n → EAf D}
    (hy : ∀ w, w ≠ v → ∀ i, Formalism.UG.prV (E := D.host.E) w (y i) = 0) :
    y ∈ hat Λ ↔ (fun i => Formalism.UG.prV (E := D.host.E) v (y i)) ∈ Formalism.L2.Herm.locL v Λ := by
  rw [mem_hat_iff_locL h]
  refine ⟨fun H => H v, fun H w => ?_⟩
  by_cases hwv : w = v
  · subst hwv
    exact H
  · have hz : (fun i => Formalism.UG.prV (E := D.host.E) w (y i)) = 0 := by
      ext i
      exact hy w hwv i
    rw [hz]
    exact Submodule.zero_mem _

set_option maxHeartbeats 800000 in
theorem locL_le {Λ Λ' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : Λ.FG) (h' : Λ'.FG)
    (v : HeightOneSpectrum (𝓞 D.host.F))
    (H : ∀ Q : Pl D.host.E, Q.under (𝓞 D.host.F) = v → ∀ y : Fin n → EAf D, idem Q • y ∈ hat Λ → idem Q • y ∈ hat Λ') :
    Formalism.L2.Herm.locL v Λ ≤ Formalism.L2.Herm.locL v Λ' := by
  obtain ⟨e, -, -, he1, he0⟩ :=
    GlobalTheory.StdFrames.exists_idem (D := D) {Q : Pl D.host.E | Q.under (𝓞 D.host.F) = v}

  have hpe : Formalism.UG.prV (E := D.host.E) v e = 1 := by
    have h0 : Formalism.UG.prV (E := D.host.E) v (e - 1) = 0 := by
      rw [prV_eq_zero_iff_cpt]
      intro Q hQ
      rw [map_sub, map_one, he1 Q hQ, sub_self]
    rwa [map_sub, map_one, sub_eq_zero] at h0

  have key : ∀ x ∈ Λ, (e • fun i => inc D (x i)) ∈ hat Λ' := by
    intro x hx
    refine mem_hat_of_idem h' fun w => ?_
    rw [smul_smul]
    by_cases hw : w.under (𝓞 D.host.F) = v
    · have hwe : idem w * e = idem w := by
        refine cpt_ext fun Q => ?_
        rw [map_mul]
        by_cases hQ : Q = w
        · subst hQ
          rw [cpt_idem_self, he1 Q hw, one_mul]
        · rw [cpt_idem_ne hQ, zero_mul]
      rw [hwe]
      exact H w hw _ (smul_mem_hat (idem_mem w) (inc_mem_hat hx))
    · have hwe : idem w * e = 0 := by
        refine cpt_ext fun Q => ?_
        rw [map_mul, map_zero]
        by_cases hQ : Q = w
        · subst hQ
          rw [he0 Q hw, mul_zero]
        · rw [cpt_idem_ne hQ, zero_mul]
      rw [hwe, zero_smul]
      exact zero_mem_hat

  unfold Formalism.L2.Herm.locL Formalism.UG.latS
  rw [Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  have hm := (mem_hat_iff_locL h' _).mp (key x hx) v
  have hxe : (fun i => Formalism.UG.prV (E := D.host.E) v ((e • fun i => inc D (x i)) i)) =
      fun i => Formalism.UG.inclE (F := D.host.F) (v.adicCompletion D.host.F) (x i) := by
    funext i
    rw [Pi.smul_apply, smul_eq_mul, map_mul, hpe, one_mul]
    rw [Formalism.UG.P.afsplit_prV_inclE]
  rw [hxe] at hm
  exact hm

theorem prV_idem_smul {v : HeightOneSpectrum (𝓞 D.host.F)} {Q : Pl D.host.E} (hQ : Q.under (𝓞 D.host.F) = v)
    (y : Fin n → EAf D) : ∀ w, w ≠ v → ∀ i, Formalism.UG.prV (E := D.host.E) w ((idem Q • y) i) = 0 := by
  intro w hw i
  have hQw : Formalism.UG.prV (E := D.host.E) w (idem Q) = 0 := by
    rw [prV_eq_zero_iff_cpt]
    intro Q' hQ'
    apply cpt_idem_ne
    intro hEq
    subst hEq
    exact hw (hQ'.symm.trans hQ)
  rw [Pi.smul_apply, smul_eq_mul, map_mul, hQw, zero_mul]

theorem locL_eq_iff_idem : ∀ (D : D7) (n : ℕ) (Λ Λ' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), Λ.FG → Λ'.FG → ∀ v : HeightOneSpectrum (𝓞 D.host.F), Formalism.L2.Herm.locL v Λ = Formalism.L2.Herm.locL v Λ' ↔ ∀ Q : Pl D.host.E, Q.under (𝓞 D.host.F) = v → ∀ y : Fin n → EAf D, idem Q • y ∈ hat Λ ↔ idem Q • y ∈ hat Λ' := by
  intro D n Λ Λ' h h' v
  constructor
  · intro heq Q hQ y
    rw [mem_hat_iff_of_supp h v (prV_idem_smul hQ y), mem_hat_iff_of_supp h' v (prV_idem_smul hQ y), heq]
  · intro H
    exact le_antisymm (locL_le h h' v fun Q hQ y => (H Q hQ y).mp)
      (locL_le h' h v fun Q hQ y => (H Q hQ y).mpr)

end GlobalTheory.LocHat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParamIsometryFamiliesDifferByCharacter
section
open GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap Matrix

namespace GlobalTheory

theorem famChar_hasDerivAt : ∀ (l : Type) [Fintype l] (B : ℝ → (l ⊕ l → ℝ) → (l ⊕ l → ℝ)) (T U : ℝ → Sch l →ₗ[ℂ] Sch l) (Q : Sch l → EuclideanSpace ℝ l → ℂ), (∀ s t f, T (s + t) f = T s (T t f)) → (∀ f, T 0 f = f) → (∀ s t f, U (s + t) f = U s (U t f)) → (∀ f, U 0 f = f) → (∀ s t w, B (s + t) w = B s (B t w)) → (∀ w, B 0 w = w) → (∀ t w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(T t f₁) = rhoFun (B t w) ⇑(T t f)) → (∀ t w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(U t f₁) = rhoFun (B t w) ⇑(U t f)) → (∀ t f, ∫ x, ‖T t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) → (∀ t f, ∫ x, ‖U t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) → (∀ f y, Continuous fun t => T t f y) → (∀ f y, HasDerivAt (fun t => U t f y) (Q f y) 0) → ∃ c : ℂ, ∀ f y, HasDerivAt (fun t => T t f y) (Q f y + c * f y) 0 := by
  intro l _ B T U Q hT hT0 hU hU0 hB hB0 hTρ hUρ hTi hUi hTc hUd
  have hUinv : ∀ t f, U (-t) (U t f) = f := fun t f => by rw [← hU, neg_add_cancel, hU0]
  have hUinv' : ∀ t f, U t (U (-t) f) = f := fun t f => by rw [← hU, add_neg_cancel, hU0]

  have key : ∀ t, ∃ c : ℂ, ∀ f, T t f = c • U t f := by
    intro t
    obtain ⟨c, hc⟩ := _root_.GlobalTheory.RealWeil.exists_eq_smul_of_commute_rhoFun l ((T t).comp (U (-t)))
      (fun f => by simp only [LinearMap.comp_apply]; rw [hTi, hUi])
      (fun w f f₁ h => by
        simp only [LinearMap.comp_apply]
        rw [hTρ t (B (-t) w) (U (-t) f) (U (-t) f₁) (hUρ (-t) w f f₁ h), ← hB, add_neg_cancel, hB0])
    refine ⟨c, fun f => ?_⟩
    have := hc (U t f)
    simp only [LinearMap.comp_apply, hUinv] at this
    exact this
  choose lam hlam using key
  set f₀ : Sch l := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l)
  have hf₀ : f₀ 0 ≠ 0 := by simp [f₀]

  have hl0 : lam 0 = 1 := by
    have h := hlam 0 f₀
    rw [hT0, hU0] at h
    have h2 := congrArg (fun g : Sch l => g 0) h
    simp only [SchwartzMap.smul_apply, smul_eq_mul] at h2
    have : (lam 0 - 1) * f₀ 0 = 0 := by linear_combination -h2
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hf₀)
  have hlmul : ∀ s t, lam (s + t) = lam s * lam t := by
    intro s t
    have h1 := hlam (s + t) (U (-(s + t)) f₀)
    rw [hUinv', hT, hlam t, map_smul, hlam s, ← hU, hUinv', smul_smul] at h1
    have h2 := congrArg (fun g : Sch l => g 0) h1
    simp only [SchwartzMap.smul_apply, smul_eq_mul] at h2
    have : (lam s * lam t - lam (s + t)) * f₀ 0 = 0 := by linear_combination h2
    exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hf₀)).symm

  have hd : ContinuousAt (fun t => U t f₀ 0) 0 := (hUd f₀ 0).continuousAt
  have hd0 : U 0 f₀ 0 ≠ 0 := by rw [hU0]; exact hf₀
  have hlc : ContinuousAt lam 0 := by
    have hq : ContinuousAt (fun t => T t f₀ 0 / U t f₀ 0) 0 :=
      ((hTc f₀ 0).continuousAt).div hd hd0
    refine hq.congr ?_
    filter_upwards [hd.eventually_ne hd0] with t ht
    rw [hlam t f₀, SchwartzMap.smul_apply, smul_eq_mul, mul_div_assoc, div_self ht, mul_one]

  obtain ⟨c, hc⟩ := _root_.GlobalTheory.multiplicative_hasDerivAt_zero lam hl0 hlmul hlc
  refine ⟨c, fun f y => ?_⟩
  have hfun : (fun t => T t f y) = fun t => lam t * U t f y := by
    funext t; rw [hlam t f, SchwartzMap.smul_apply, smul_eq_mul]
  rw [hfun]
  have h := hc.mul (hUd f y)
  rw [hl0, hU0, one_mul, add_comm] at h
  exact h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryArchimedeanCoordinateActionLinearMulStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_archimedean_coordinate_action_linear_mul : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W),
    (∀ (h : UA σ W.J) (v v' : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
      archAct M h (v + v') = archAct M h v + archAct M h v') ∧
    (∀ (h : UA σ W.J) (c : ℝ) (v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
      archAct M h (c • v) = c • archAct M h v) ∧
    (∀ (h h' : UA σ W.J) (v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
      archAct M (h * h') v = archAct M h (archAct M h' v)) := by
  intro F E _ _ _ _ _ σ n d X W M
  exact GlobalTheory.ArchLine.archAct_linear_mul M
end

