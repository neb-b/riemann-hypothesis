module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1245
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Formalism.HarderNarasimhan.StatementPl
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0053
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniqueIsConnOfLift
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1448
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1454
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0251
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeSupLatticeComponentEq
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

section General

variable {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]

theorem finrank_eq_two_mul_nPl : Module.finrank ℚ K = 2 * Formalism.HN.nPl K := by
  rw [IsTotallyComplex.finrank, Formalism.HN.nPl, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]

theorem rkK_mul_muDef [StarRing K] {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) {L : Submodule (𝓞 K) V} (hL : L.FG)
    (hr : Formalism.HN.rkK L ≠ 0) :
    (Formalism.HN.rkK L : ℝ) * (Formalism.HN.muDef b X L / 2) = -Real.log (Formalism.HN.ht b X L) / (2 * (Formalism.HN.nPl K : ℝ)) := by
  obtain ⟨-, hrk, hht⟩ := Formalism.HN.plLat K V ι b X hX L hL
  have hd : (0 : ℝ) < |(NumberField.discr K : ℝ)| := abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero K)
  have hf : (0 : ℝ) < (Formalism.HN.nPl K : ℝ) := by
    have : 0 < Formalism.HN.nPl K := Fintype.card_pos
    exact_mod_cast this
  have hj : (0 : ℝ) < (Formalism.HN.rkK L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hr
  have e₁ : Formalism.HN.ht b X L = (2 : ℝ) ^ (Formalism.HN.nPl K * Formalism.HN.rkK L) *
      |(NumberField.discr K : ℝ)| ^ (-(Formalism.HN.rkK L : ℝ) / 2) *
      Formalism.F.covol (Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize b X) L) := rfl
  have hC : 0 < Formalism.F.covol (Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize b X) L) := by
    rw [e₁] at hht
    exact pos_of_mul_pos_right hht (by positivity)
  have hlog : Real.log (Formalism.HN.ht b X L) = ((Formalism.HN.nPl K : ℝ) * Formalism.HN.rkK L) * Real.log 2 +
      (-(Formalism.HN.rkK L : ℝ) / 2) * Real.log |(NumberField.discr K : ℝ)| +
      Real.log (Formalism.F.covol (Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize b X) L)) := by
    rw [e₁, Real.log_mul (by positivity) hC.ne', Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Real.log_rpow hd]
    push_cast; ring
  have hrk' : (Formalism.F.rk (Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize b X) L) : ℝ) =
      2 * (Formalism.HN.nPl K : ℝ) * Formalism.HN.rkK L := by
    have : Formalism.F.rk (Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize b X) L) = Module.finrank ℚ K * Formalism.HN.rkK L := hrk
    rw [this, finrank_eq_two_mul_nPl]; push_cast; ring
  have hmu : Formalism.HN.muDef b X L = 2 * (-Real.log (Formalism.F.covol (Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize b X) L)) /
      (2 * (Formalism.HN.nPl K : ℝ) * Formalism.HN.rkK L)) - Real.log 2 +
      Real.log |(NumberField.discr K : ℝ)| / (2 * (Formalism.HN.nPl K : ℝ)) := by
    rw [Formalism.HN.muDef, Formalism.HN.slope, Formalism.F.slope, Formalism.F.deg, hrk', Formalism.HN.logDisc, finrank_eq_two_mul_nPl]
    push_cast; ring
  rw [hmu, hlog]
  field_simp
  ring

theorem pgeoDeg_eq_deg {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K V) (hinv : h.IsConjInv) {N : (K →+* ℂ) → V → ℝ} (hN : ∀ σ x, h.nrm σ x = N σ x)
    (hg : AllWt.HasGram N) {L : Submodule (𝓞 K) V} (hL : L.FG) : ReciprocityTheory.GeometryOfNumbersTheory.deg h L = AllWt.deg N L := by
  by_cases h0 : L = ⊥
  · subst h0
    have hv : ReciprocityTheory.GeometryOfNumbersTheory.IsFrame K (⊥ : Submodule (𝓞 K) V) (Fin.elim0 : Fin 0 → V) :=
      ⟨fun i => i.elim0, linearIndependent_empty_type, by simp⟩
    rw [AllWt.deg_bot, ReciprocityTheory.GeometryOfNumbersTheory.arakelovDegree_eq_degreeOfFamily h hL hv]
    simp [ReciprocityTheory.GeometryOfNumbersTheory.degreeOfFamily, ReciprocityTheory.GeometryOfNumbersTheory.HermFam.gram]
  letI : StarRing K := starRingOfComm
  obtain ⟨n, ⟨b, X⟩, hG⟩ := hg.some
  haveI : FiniteDimensional K V := Module.Basis.finiteDimensional_of_finite b
  have hr : Formalism.HN.rkK L ≠ 0 := by
    intro hr
    apply h0
    rw [Formalism.HN.rkK, Submodule.finrank_eq_zero] at hr
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ Submodule.span K (L : Set V) := Submodule.subset_span hx
    rw [hr, Submodule.mem_bot] at hx'
    rw [hx']
    exact zero_mem _
  rw [_root_.GlobalTheory.FrameDeg.deg_eq_neg_log_ht K V h hinv (Fin n) b X (fun v => (hG v).1) (fun v x => ((hG v).2 x).trans (hN _ x).symm) L hL,
    AllWt.deg, AllWt.slope, AllWt.slope_sq_eq hG hL, rkK_mul_muDef b X (fun v => (hG v).1) hL hr]

end General

theorem isTotallyComplex_coeff {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}
    (c : Coeff l) : IsTotallyComplex c.F :=
  ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => CompHt.conj_comp_ne (c := c) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩

theorem Ready.degM_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw) (R : Choice X Z U P) (ω : CanId R.toModif) (x : ℝ) (D : Formalism.BasicNotions.D7) (V : (c.F →+* ℂ) → Formalism.BasicNotions.TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : Ready R ω x V dict) (f₁ : CuspFrame Z U x V dict P.u₁) (f₂ : CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : Consts), ∀ j ≤ P.T, (h.data f₁ f₂ th k).degM j = GlobalTheory.AllWt.degOn U x V dict Z (GlobalTheory.AllWt.wtOf Dw (P.wt j) 0) := by
  intro E _ _ _ H Dw l Xo c Y X Z r U P R ω x D V dict h f₁ f₂ th k j hj
  haveI : IsTotallyComplex c.F := isTotallyComplex_coeff c
  have hM : (h.data f₁ f₂ th k).M j = (GlobalTheory.AllWt.latOn U Z (GlobalTheory.AllWt.wtOf Dw (P.wt j) 0)).map
      ((h.equivV f₁ f₂ th k hj).toLinearMap.restrictScalars (𝓞 c.F)) := by
    ext y
    constructor
    · intro hy
      refine ⟨(h.equivV f₁ f₂ th k hj).symm y, ?_, (h.equivV f₁ f₂ th k hj).apply_symm_apply y⟩
      refine (h.equivV_mem f₁ f₂ th k hj _).1 ?_
      rw [LinearEquiv.apply_symm_apply]
      exact hy
    · rintro ⟨g, hg, rfl⟩
      exact (h.equivV_mem f₁ f₂ th k hj g).2 hg
  rw [HilbertSamuel.Data.degM, hM, ← FibIndep.deg_map_of_isometry
    (HermTools.comap ((h.data f₁ f₂ th k).nm j) (h.equivV f₁ f₂ th k hj).toLinearMap
      (h.equivV f₁ f₂ th k hj).injective) _ (h.equivV f₁ f₂ th k hj).toLinearMap (fun _ _ _ => rfl)
    (h.good j hj).2.1]
  exact pgeoDeg_eq_deg _ (HermTools.isConjInv_comap ((h.data f₁ f₂ th k).conjInv j) _ _)
    (fun σ x => h.nrm_equivV f₁ f₂ th k hj σ x) (h.good j hj).1 (h.good j hj).2.1

end GlobalTheory.CompHS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerLinEMulE
section
set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.CrysConn

namespace GlobalTheory.PDA

variable {B : Type} [CommRing B]

def PDPoly.derVal (Q : PDPoly B) : ℕ → Q.P
  | 0 => 0
  | n + 1 => Q.e n

def PDPoly.derLin (Q : PDPoly B) : Q.P →ₗ[B] Q.P := Q.e.constr B Q.derVal

theorem PDPoly.derLin_e (Q : PDPoly B) (n : ℕ) : Q.derLin (Q.e n) = Q.derVal n := by
  simp [PDPoly.derLin, Module.Basis.constr_basis]

theorem PDPoly.derLin_e_succ (Q : PDPoly B) (n : ℕ) : Q.derLin (Q.e (n + 1)) = Q.e n := Q.derLin_e (n + 1)

theorem PDPoly.derLin_e_zero (Q : PDPoly B) : Q.derLin (Q.e 0) = 0 := Q.derLin_e 0

theorem PDPoly.derLin_e_mul_e (Q : PDPoly B) (m n : ℕ) :
    Q.derLin (Q.e m * Q.e n) = Q.e m * Q.derLin (Q.e n) + Q.e n * Q.derLin (Q.e m) := by
  rcases m with _ | a
  · rw [Q.derLin_e_zero, Q.e_zero]; simp
  rcases n with _ | b
  · rw [Q.derLin_e_zero, Q.e_zero]; simp
  rw [Q.derLin_e_succ, Q.derLin_e_succ, Q.e_mul, Q.e_mul, Q.e_mul, ← nsmul_eq_mul, map_nsmul,
    show a + 1 + (b + 1) = (a + b + 1) + 1 by omega, Q.derLin_e_succ, show a + 1 + b = a + b + 1 by omega,
    show b + 1 + a = a + b + 1 by omega, Nat.choose_succ_succ' (a + b + 1) a,
    Nat.choose_symm_of_eq_add (show a + b + 1 = (b + 1) + a by omega)]
  push_cast
  rw [nsmul_eq_mul]
  push_cast
  ring

theorem PDPoly.derLin_mul (Q : PDPoly B) (x y : Q.P) :
    Q.derLin (x * y) = x * Q.derLin y + y * Q.derLin x := by
  have h2 : ∀ x n, Q.derLin (x * Q.e n) = x * Q.derLin (Q.e n) + Q.e n * Q.derLin x := fun x n ↦ by
    have := Q.e.ext (f₁ := Q.derLin ∘ₗ LinearMap.mulRight B (Q.e n))
      (f₂ := LinearMap.mulRight B (Q.derLin (Q.e n)) + LinearMap.mulLeft B (Q.e n) ∘ₗ Q.derLin)
      (fun m ↦ by simpa using Q.derLin_e_mul_e m n)
    simpa using LinearMap.congr_fun this x
  have := Q.e.ext (f₁ := Q.derLin ∘ₗ LinearMap.mulLeft B x)
    (f₂ := LinearMap.mulLeft B x ∘ₗ Q.derLin + LinearMap.mulRight B (Q.derLin x))
    (fun n ↦ by simpa using h2 x n)
  simpa using LinearMap.congr_fun this y

def PDPoly.der (Q : PDPoly B) : Derivation B Q.P Q.P :=
  Derivation.mk' Q.derLin fun x y ↦ by simpa [smul_eq_mul] using Q.derLin_mul x y

theorem PDPoly.der_apply (Q : PDPoly B) (x : Q.P) : Q.der x = Q.derLin x := rfl

end GlobalTheory.PDA

namespace GlobalTheory.PDA

variable {B : Type} [CommRing B]

theorem PDPoly.der_dpow_succ {J : Ideal B} (δ : DividedPowers J) (Q : PDPoly B) (η : DividedPowers (Q.ext J))
    (h : Q.IsStd δ η) (n : ℕ) {a : Q.P} (ha : a ∈ Q.ext J) :
    Q.der (η.dpow (n + 1) a) = η.dpow n a * Q.der a := by
  set D := Q.der
  let P : Q.P → Prop := fun a ↦ ∀ n, D (η.dpow n a) = dpPred η n a • D a
  have hzero : P 0 := fun n ↦ by
    cases n with
    | zero => simp [η.dpow_zero (Q.ext J).zero_mem]
    | succ n => simp [dpow_eval_zero _ n.succ_ne_zero]
  have hadd : ∀ a ∈ Q.ext J, ∀ b ∈ Q.ext J, P a → P b → P (a + b) := fun a ha b hb iha ihb n ↦ by
    have iha : ∀ n, D (η.dpow n a) = dpPred η n a • D a := iha
    have ihb : ∀ n, D (η.dpow n b) = dpPred η n b • D b := ihb
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [η.dpow_add ha hb, map_sum, D.leibniz, iha, ihb, smul_smul, Finset.sum_add_distrib,
      ← Finset.sum_smul, sum_dpow_mul_dpPred η ha hb, sum_dpow_mul_dpPred' η ha hb, map_add, smul_add]
    exact add_comm _ _
  have hmul : ∀ r, ∀ a ∈ Q.ext J, P a → P (r * a) := fun r a ha hP n ↦ by
    cases n with
    | zero => simp [η.dpow_zero (Ideal.mul_mem_left _ r ha), dpPred]
    | succ m =>
      have hm := hP (m + 1)
      have hs := dpPred_mul_self η ha (m + 1)
      simp only [dpPred, smul_eq_mul] at hm hs ⊢
      rw [η.dpow_mul ha, η.dpow_mul ha, D.leibniz, D.leibniz, D.leibniz_pow, hm]
      simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
      push_cast at hs ⊢
      linear_combination (-(r ^ m * D r)) * hs
  have hspan : ∀ s : Set Q.P, s ⊆ Q.ext J → (∀ x ∈ s, P x) → ∀ a ∈ Ideal.span s, P a := by
    intro s hs hP a ha
    have hle : Ideal.span s ≤ Q.ext J := Ideal.span_le.2 hs
    induction ha using Submodule.span_induction with
    | mem x hx => exact hP x hx
    | zero => exact hzero
    | add x y hx hy ihx ihy => exact hadd x (hle hx) y (hle hy) ihx ihy
    | smul r x hx ih => exact hmul r x (hle hx) ih
  have hJ : ∀ x ∈ J.map (algebraMap B Q.P), P x := by
    refine hspan _ ?_ ?_
    · rintro _ ⟨j, hj, rfl⟩; exact Q.algebraMap_mem_ext hj
    · rintro _ ⟨j, hj, rfl⟩ n
      rw [h.dp.2 j hj, Derivation.map_algebraMap, Derivation.map_algebraMap, smul_zero]
  have he1 := Q.e_one_mem_ext J
  have hA : ∀ x ∈ Q.aug, P x := by
    refine hspan _ ?_ ?_
    · rintro _ ⟨k, rfl⟩; exact Ideal.mem_sup_right (Q.e_succ_mem_aug k)
    · rintro _ ⟨k, rfl⟩ n
      cases n with
      | zero => simp [η.dpow_zero (Ideal.mem_sup_right (Q.e_succ_mem_aug k)), dpPred]
      | succ m =>
        have c1 : η.dpow (m + 1) (Q.e (k + 1)) =
            (Nat.uniformBell (m + 1) (k + 1) : Q.P) * Q.e ((m * (k + 1) + k) + 1) := by
          rw [← h.var (k + 1), η.dpow_comp (by omega) he1, h.var, show (m + 1) * (k + 1) = m * (k + 1) + k + 1 by ring]
        have c2 : dpPred η (m + 1) (Q.e (k + 1)) * Q.e k =
            (Nat.uniformBell (m + 1) (k + 1) : Q.P) * Q.e (m * (k + 1) + k) := by
          have := dpPred_dpow η he1 (m + 1) (n := k + 1) (by omega)
          rw [h.var, show dpPred η (k + 1) (Q.e 1) = Q.e k from h.var k,
            show (m + 1) * (k + 1) = m * (k + 1) + k + 1 by ring,
            show dpPred η (m * (k + 1) + k + 1) (Q.e 1) = Q.e (m * (k + 1) + k) from h.var _] at this
          exact this
        rw [c1, D.leibniz, D.map_natCast, smul_zero, add_zero, smul_eq_mul, smul_eq_mul, Q.der_apply,
          Q.der_apply, Q.derLin_e_succ, Q.derLin_e_succ, c2]
  have hall : ∀ x ∈ Q.ext J, P x := fun x hx ↦ by
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    exact hadd y (Ideal.mem_sup_left hy) z (Ideal.mem_sup_right hz) (hJ y hy) (hA z hz)
  simpa [dpPred, smul_eq_mul] using hall a ha (n + 1)

theorem PDPoly.exists_der (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B)
    (δ : DividedPowers J) (Q : PDPoly B) [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J)) :
    Q.IsStd δ η → ∃ D : Derivation R Q.P Q.P, (∀ b, D (algebraMap B Q.P b) = 0) ∧
      (∀ n, D (Q.e (n + 1)) = Q.e n) ∧ ∀ n, ∀ a ∈ Q.ext J, D (η.dpow (n + 1) a) = η.dpow n a * D a := by
  intro h
  refine ⟨Q.der.restrictScalars R, fun b ↦ ?_, fun n ↦ ?_, fun n a ha ↦ ?_⟩
  · rw [Derivation.restrictScalars_apply, Derivation.map_algebraMap]
  · rw [Derivation.restrictScalars_apply, Q.der_apply, Q.derLin_e_succ]
  · simp only [Derivation.restrictScalars_apply]
    exact Q.der_dpow_succ δ η h n ha

end GlobalTheory.PDA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetPowSectionRationalGenericPoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef.SecRat

theorem isIntegral_of_isGenOver (k K : Type) [Field k] [Field K] [Algebra k K] (C : Scheme.{0})
    [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C) (hx : IsGenOver k x) : IsIntegral C := by
  have : SmoothOfRelativeDimension 1 (strHom k (X := C)) := hx.1.1
  have : Smooth (strHom k (X := C)) := SmoothOfRelativeDimension.smooth 1 _
  have hred : IsReduced C := isReduced_of_smooth_of_isReduced (strHom k C)
  have hd : IsDominant x := hx.2.1.1
  have hden : DenseRange x.base := hd.denseRange
  have hcl : closure {x.base default} = (Set.univ : Set C) := by
    have hr : Set.range x.base = {x.base default} := by
      ext y; constructor
      · rintro ⟨p, rfl⟩; rw [Subsingleton.elim p default]; rfl
      · rintro rfl; exact ⟨_, rfl⟩
    rw [← hr]; exact hden.closure_range
  have hirr : IsIrreducible (Set.univ : Set C) := hcl ▸ isIrreducible_singleton.closure
  have : IrreducibleSpace C := { isPreirreducible_univ := hirr.2, toNonempty := ⟨x.base default⟩ }
  exact (isIntegral_iff_irreducibleSpace_and_isReduced C).2 ⟨this, hred⟩

theorem not_isUnit_evAt {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (b : Sp R ⟶ X)
    {U : X.Opens} (h : ⊤ ≤ b ⁻¹ᵁ U) (f : Γ(X, U)) (hf : b (IsLocalRing.closedPoint R) ∉ X.basicOpen f) :
    ¬ IsUnit (evAt b h f) := by
  intro hu
  apply hf
  have h1 : (b.appLE U ⊤ h).hom f = (Scheme.ΓSpecIso (.of R)).inv.hom (evAt b h f) := by
    simp [evAt]
  have h2 : (Sp R).basicOpen ((b.appLE U ⊤ h).hom f) = ⊤ ⊓ (Sp R).basicOpen ((b.app U).hom f) := by
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply, Scheme.basicOpen_res]
  have h3 : IsLocalRing.closedPoint R ∈ (Sp R).basicOpen ((b.appLE U ⊤ h).hom f) := by
    rw [h1, basicOpen_eq_of_affine]
    exact (PrimeSpectrum.mem_basicOpen _ _).2 fun hm => (IsLocalRing.mem_maximalIdeal _).1 hm hu
  rw [h2, ← Scheme.preimage_basicOpen] at h3
  exact h3.2

theorem evAt_coord {R : Type} [CommRing R] {C : Scheme.{0}} (x : Sp R ⟶ C) {W : C.Modules} {r m : ℕ}
    (σ : (lbPow (det W r) m).Sec) (c₀ c : Chart W r) (V' : C.Opens) (h₀ : V' ≤ c₀.U) (h₁ : V' ≤ c.U)
    (hx' : ⊤ ≤ x ⁻¹ᵁ V') (M : Matrix (Fin r) (Fin r) Γ(C, V'))
    (hM : ∀ j, resM W h₀ (c₀.e j) = ∑ i, M i j • resM W h₁ (c.e i))
    (h0 : ⊤ ≤ x ⁻¹ᵁ (lbPow (det W r) m).U (fun _ => c₀)) (h1 : ⊤ ≤ x ⁻¹ᵁ (lbPow (det W r) m).U (fun _ => c)) :
    evAt x h1 (σ.f (fun _ => c)) = (M.map (evAt x hx')).det ^ m * evAt x h0 (σ.f (fun _ => c₀)) := by
  have hV : V' ≤ (lbPow (det W r) m).U (fun _ => c) ⊓ (lbPow (det W r) m).U (fun _ => c₀) :=
    fun y hy => ⟨Set.mem_iInter.2 fun _ => h₁ hy, Set.mem_iInter.2 fun _ => h₀ hy⟩
  have hxV : ⊤ ≤ x ⁻¹ᵁ ((lbPow (det W r) m).U (fun _ => c) ⊓ (lbPow (det W r) m).U (fun _ => c₀)) :=
    hx'.trans (x.preimage_mono hV)
  have hcc : ⊤ ≤ x ⁻¹ᵁ (c.U ⊓ c₀.U) := hx'.trans (x.preimage_mono (le_inf h₁ h₀))
  have e := congrArg (evAt x hxV) (σ.compat (fun _ => c) (fun _ => c₀))
  rw [(_root_.GlobalTheory.Nef.evAt_calculus).2.2.1 R C x _ _ _ h1 hxV, map_mul, (_root_.GlobalTheory.Nef.evAt_calculus).2.2.1 R C x _ _ _ h0 hxV] at e
  rw [e]
  congr 1
  have hd : evAt x hcc (c.isFrame.detUnit c₀.isFrame (inf_le_left : c.U ⊓ c₀.U ≤ c.U) inf_le_right).val =
      (M.map (evAt x hx')).det := by
    rw [← (_root_.GlobalTheory.Nef.evAt_calculus).2.2.1 R C x _ _ (le_inf h₁ h₀) hcc hx']
    have hr := IsFrame.res_detUnit c.isFrame c₀.isFrame (inf_le_left : c.U ⊓ c₀.U ≤ c.U) inf_le_right (le_inf h₁ h₀)
    refine (congrArg (evAt x hx') (congrArg Units.val hr)).trans ?_
    rw [IsFrame.val_detUnit, Module.Basis.det_apply, RingHom.map_det]
    congr 1
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply, Module.Basis.toMatrix_apply, hM]
    simp only [← IsFrame.basis_apply c.isFrame h₁]
    rw [Module.Basis.repr_sum_self]
  rw [← hd, ← map_pow, ← (_root_.GlobalTheory.Nef.evAt_calculus).2.2.1 R C x _ _ (fun y hy => ⟨Set.mem_iInter.1 hy.1 PUnit.unit, Set.mem_iInter.1 hy.2 PUnit.unit⟩ : (lbPow (det W r) m).U (fun _ => c) ⊓ (lbPow (det W r) m).U (fun _ => c₀) ≤ c.U ⊓ c₀.U) hcc hxV]
  congr 1
  dsimp only [lbPow, LB.LinComb]
  rw [Fintype.prod_unique, zpow_natCast, Units.val_pow_eq_pow_val]
  erw [map_pow]
  congr 1

theorem val_lt_one {k K : Type} [Field k] [Field K] [Algebra k K] (v : Place k K) (a : v.O) (ha : ¬ IsUnit a) :
    v.1 (a : K) < 1 := by
  have h1 : v.1 (a : K) ≤ 1 := (Valuation.mem_valuationSubring_iff _ _).1 a.2
  refine lt_of_le_of_ne h1 fun h => ha ?_
  have h0 : (a : K) ≠ 0 := fun h0 => by rw [h0, map_zero] at h; exact zero_ne_one h
  have hi : (a : K)⁻¹ ∈ v.O := (Valuation.mem_valuationSubring_iff _ _).2 (by rw [map_inv₀, h, inv_one])
  exact isUnit_iff_exists_inv.2 ⟨⟨_, hi⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩

theorem sec_eq_zero {X : Scheme.{0}} {L : LB X} (σ : L.Sec) (h : ∀ j, σ.f j = 0) : σ = 0 := by
  obtain ⟨f, hc⟩ := σ
  have : f = fun _ => 0 := funext h
  subst this
  rfl

end GlobalTheory.Nef.SecRat


open GlobalTheory.Nef.SecRat in
theorem GlobalTheory.Nef.sec_detPow_rational : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (W : C.Modules) (r : ℕ), IsVB W r → ∀ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)), (V₀ : Set C).Nonempty → IsFrame s → ∀ (m : ℕ) (σ : (lbPow (det W r) m).Sec), σ ≠ 0 → ∃ f : K, f ≠ 0 ∧ ∀ (v : Place k K) (g : Matrix (Fin r) (Fin r) K), LocFrame x s v g → v.1 (f * g.det ^ m) ≤ 1 ∧ ∀ b : Sp v.O ⟶ C, spMap v.O.subtype ≫ b = x → b (IsLocalRing.closedPoint v.O) ∉ Out.nonzeroLocus σ → v.1 (f * g.det ^ m) < 1 := by
  intro k K _ _ _ _ _ C _ x hx W r hW V₀ s hV₀ hs m σ hσ
  haveI := isIntegral_of_isGenOver k K C x hx
  let c₀ : Chart W r := ⟨V₀, s, hs⟩
  have hUeq : ∀ c : Chart W r, (((lbPow (det W r) m).U (fun _ => c) : C.Opens) : Set C) = c.U := fun c =>
    Set.ext fun y => ⟨fun hy => Set.mem_iInter.1 hy PUnit.unit, fun hy => Set.mem_iInter.2 fun _ => hy⟩
  have hle : ∀ c : Chart W r, c.U ≤ (lbPow (det W r) m).U (fun _ => c) := fun c y hy =>
    Set.mem_iInter.2 fun _ => hy
  obtain ⟨hx0, hinj0, -⟩ := _root_.GlobalTheory.Nef.isGen_evAt_frac K C x hx.2.1 ((lbPow (det W r) m).U fun _ => c₀)
    (by rw [hUeq]; exact hV₀)
  refine ⟨evAt x hx0 (σ.f fun _ => c₀), ?_, ?_⟩
  · intro hf
    apply hσ
    have h0 : σ.f (fun _ => c₀) = 0 := hinj0 (by rw [hf, map_zero])
    refine sec_eq_zero σ fun j => ?_
    have hj : j = fun _ => j PUnit.unit := funext fun _ => rfl
    rw [hj]
    generalize j PUnit.unit = c
    by_cases hne : (((lbPow (det W r) m).U fun _ => c : C.Opens) : Set C).Nonempty
    · have hne2 : ((((lbPow (det W r) m).U fun _ => c) ⊓ (lbPow (det W r) m).U (fun _ => c₀) :
          C.Opens) : Set C).Nonempty :=
        nonempty_preirreducible_inter (Opens.isOpen _) (Opens.isOpen _) hne (by rw [hUeq]; exact hV₀)
      obtain ⟨hxj, hinjj, -⟩ := _root_.GlobalTheory.Nef.isGen_evAt_frac K C x hx.2.1 _ hne
      obtain ⟨hx2, -, -⟩ := _root_.GlobalTheory.Nef.isGen_evAt_frac K C x hx.2.1 _ hne2
      apply hinjj
      have e := congrArg (evAt x hx2) (σ.compat (fun _ => c) (fun _ => c₀))
      rw [(_root_.GlobalTheory.Nef.evAt_calculus).2.2.1 K C x _ _ _ hxj hx2, map_mul, (_root_.GlobalTheory.Nef.evAt_calculus).2.2.1 K C x _ _ _ hx0 hx2, h0,
        map_zero, mul_zero] at e
      rw [e, map_zero]
    · exact eq_zero_of_basicOpen_eq_bot _ (eq_bot_iff.2 fun y hy => hne ⟨y, C.basicOpen_le _ hy⟩)
  · rintro v g ⟨b, V, t, V', h₀, h₁, hx', M, hb, hbV, ht, hM, rfl⟩
    let c : Chart W r := ⟨V, t, ht⟩
    have hbj : ⊤ ≤ b ⁻¹ᵁ (lbPow (det W r) m).U (fun _ => c) := hbV.trans (b.preimage_mono (hle c))
    have hxj : ⊤ ≤ x ⁻¹ᵁ (lbPow (det W r) m).U (fun _ => c) := hx'.trans (x.preimage_mono (h₁.trans (hle c)))
    have key := evAt_coord x σ c₀ c V' h₀ h₁ hx' M hM hx0 hxj
    have hval : v.1 (evAt x hx0 (σ.f fun _ => c₀) * (M.map (evAt x hx')).det ^ m) =
        v.1 ((evAt b hbj (σ.f fun _ => c) : v.O) : K) := by
      rw [mul_comm, ← key]
      congr 1
      subst hb
      exact (_root_.GlobalTheory.Nef.evAt_calculus).1 v.O K C v.O.subtype b _ hbj hxj _
    refine ⟨?_, ?_⟩
    · rw [hval]
      exact (Valuation.mem_valuationSubring_iff _ _).1 (evAt b hbj _).2
    · intro b' hb' hout
      have e : spMap (algebraMap K K) ≫ x = x := by
        rw [Algebra.algebraMap_self, spMap, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
      obtain ⟨b₀, -, huniq⟩ := _root_.GlobalTheory.Nef.existsUnique_centre k K K C x hx v
      have hbb : b' = b := (huniq b' (hb'.trans e.symm)).trans (huniq b (hb.trans e.symm)).symm
      subst hbb
      have hnu := not_isUnit_evAt b' hbj (σ.f fun _ => c) (fun hm => hout (Opens.mem_iSup.2 ⟨_, hm⟩))
      rw [hval]
      exact val_lt_one v _ hnu
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilDatumFirstFactorOnDoublingTensor
section
namespace DoublingFirstFactorDivisor
section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.DoublingFirstFactor

theorem doubled_first_factor : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ)),
      Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
    ∀ ωd : GA D (GlobalTheory.Doubling.dblSp S) × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO (GlobalTheory.Doubling.dblSp S) T → ℂ),
      Formalism.IndefR.Datum.IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd →
    ∀ (g : GA D S) (f₁ f₂ : Formalism.IndefR.Datum.WO S T → ℂ),
      Formalism.IndefR.Datum.IsThetaFunO ψ S T f₁ → Formalism.IndefR.Datum.IsThetaFunO ψ S T f₂ →
      ωd (GlobalTheory.Doubling.io S (g, 1), 1) (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T f₁ f₂) =
        GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T (ω (g, 1) f₁) f₂ := by
  intro D ψ _ S T χS χT ω hω ωd hωd g f₁ f₂ h₁ h₂
  have key := ((GlobalTheory.DoublingTheta.thetaClause D ψ S T χS χT ω ωd hω hωd f₁ f₂ h₁ h₂).2 g 1 1).1
  have e : ω ((1 : GA D S), (1 : GA D T)) = 1 := map_one ω
  rw [key, e, map_one, map_one, inv_one, Circle.coe_one, one_smul]
  rfl

end GlobalTheory.CompanionTheory.DoublingFirstFactor

end

end DoublingFirstFactorDivisor
section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.Adopt.doubledWeilDatum_firstFactor_on_doublingTensor : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ)),
      Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
    ∀ ωd : GA D (GlobalTheory.Doubling.dblSp S) × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO (GlobalTheory.Doubling.dblSp S) T → ℂ),
      Formalism.IndefR.Datum.IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd →
    ∀ (g : GA D S) (f₁ f₂ : Formalism.IndefR.Datum.WO S T → ℂ),
      Formalism.IndefR.Datum.IsThetaFunO ψ S T f₁ → Formalism.IndefR.Datum.IsThetaFunO ψ S T f₂ →
      ωd (GlobalTheory.Doubling.io S (g, 1), 1) (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T f₁ f₂) =
        GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T (ω (g, 1) f₁) f₂ := by
  first | exact @DoublingFirstFactorDivisor.GlobalTheory.CompanionTheory.DoublingFirstFactor.doubled_first_factor | exact DoublingFirstFactorDivisor.GlobalTheory.CompanionTheory.DoublingFirstFactor.doubled_first_factor | (intros; apply DoublingFirstFactorDivisor.GlobalTheory.CompanionTheory.DoublingFirstFactor.doubled_first_factor <;> assumption)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSphericalCuspFormWhittakerNeZeroStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spherical_cuspForm_whittaker_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) → ∀ (π : CuspSub E (m + 1)) (α : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ), (∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) → ∃ φ ∈ π.V, (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), act (.fin (locGL E (m + 1) w k)) φ = φ) ∧ ∃ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit φ.1 x ≠ 0 := by
  first | exact @GlobalTheory.JSW.NzSph.exists_sph_whit_ne_zero | exact GlobalTheory.JSW.NzSph.exists_sph_whit_ne_zero | (intros; apply GlobalTheory.JSW.NzSph.exists_sph_whit_ne_zero <;> assumption)
end

