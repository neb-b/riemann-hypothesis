module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0607
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelAlgebraicExpansion
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionStandardPairSecond
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0582

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.BotFourierSnd

open GlobalTheory.PlaceModel GlobalTheory.AlgWave GlobalTheory.BotFourier GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle

variable {D : D7}

theorem unitChar_mem {ν : (AE D)ˣ →* Circle} (hν : Continuous ν) {e : AE D} {S : Finset (Pl D.host.E)}
    (he : IsIdemSum e S) {k : ℕ} {N : Matrix (Fin k) (Fin k) (Lev.EAf D)} (hN : IsIntM N) : unitChar ν e N ∈ Qb := by
  obtain ⟨-, -, -, m, hm, hord⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D ν hν
  unfold unitChar
  split_ifs with hu
  · obtain ⟨h1, h2, h3⟩ := hu.choose_spec
    have hdet : N.det ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      let B : Matrix (Fin k) (Fin k) (Formalism.L2.Herm.intAf D.host.F D.host.E) := fun a b => ⟨_, hN a b⟩
      have hB : N = (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype.mapMatrix B := rfl
      rw [hB, ← RingHom.map_det]
      exact (B.det).2
    have hE := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_mem he
    have hfu : Formalism.L2.Pj.FinUnit hu.choose := ⟨h1, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (by
      rw [h2]; exact add_mem (sub_mem (one_mem _) hE) (mul_mem hE hdet)), GlobalTheory.PlaceDatum.finPart_mem_of_toEAf h3⟩
    have hpow := hord _ hfu
    refine mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (n := m) hm ?_)
    have e1 : (((ν hu.choose)⁻¹ : Circle) : ℂ) ^ m = Circle.coeHom (((ν hu.choose) ^ m)⁻¹) := by
      rw [← inv_pow, map_pow]; rfl
    rw [e1, hpow, inv_one, map_one]
    exact isAlgebraic_one
  · exact zero_mem _

theorem stdSnd_mem {ν : (AE D)ˣ →* Circle} (hν : Continuous ν) {e : AE D} {S : Finset (Pl D.host.E)}
    (he : IsIdemSum e S) (I : Ideal (𝓞 D.host.E)) (a : ℕ) (A' WW : HSp D) (βA : GL (Fin A'.rank) (Lev.EAf D))
    (βW : GL (Fin WW.rank) (Lev.EAf D)) (x : WO A' WW) : stdSnd ν e I a A' WW βA βW x ∈ Qb := by
  unfold stdSnd
  split_ifs with hc
  · exact unitChar_mem hν he (GlobalTheory.CompanionTheory.StdSndTheta.isIntM_rightBlock hc.2.1)
  · exact zero_mem _


set_option maxHeartbeats 2000000 in
theorem isAlgComb_of_isThetaAt {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S WW : HSp D}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)}
    (hSd : IsSelfDualC S ΛS) (hWd : IsSelfDualC WW ΛT) {e : AE D} (hee : e * e = e) (hinf : infPart D e = 0)
    {vac Φ f : WO S WW → ℂ} (hSB : IsSBHalf e (latO S WW ΛS ΛT fun _ => True) Φ) (hΦ : ∀ x, Φ x ∈ Qb)
    (hth : IsThetaAt ψ (symplO S WW) (heisO ψ S WW) e (latO S WW ΛS ΛT fun _ => True) 1 vac Φ f) :
    GlobalTheory.MovedAlg.IsAlgComb ψ S WW vac f := by
  classical
  have hinf' := GlobalTheory.PlaceDatum.infPart_cA hinf
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hth
  rw [hall Tm hTm]
  set Λ : AddSubgroup (WO S WW) := latO S WW ΛS ΛT fun _ => True with hΛ

  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S WW ΛS ΛT hψ hSd hWd).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S WW _ _ hSd.1.fg hWd.1.fg fun _ => True
  have he' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, hee]
  have hsm : ∀ a : AE D, a * a = a → ∀ u ∈ Λ, a • u ∈ Λ ⊓ half S WW a := fun a ha u hu =>
    AddSubgroup.mem_inf.2 ⟨GlobalTheory.LatticeStable.smul_mem_latO D S WW _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu, by rw [mem_half, smul_smul, ha]⟩
  have finX : ∀ x ∈ half S WW e, x.map (infPart D) = 0 := fun x hx =>
    GlobalTheory.PlaceDatum.infPart_of_half hinf ((isHalf_iff S WW).2 hx)
  have finY : ∀ y ∈ half S WW (cA D e), y.map (infPart D) = 0 := fun y hy =>
    GlobalTheory.PlaceDatum.infPart_of_half hinf' ((isHalf_iff S WW).2 hy)
  have tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S WW => k • t := fun k hk a b hab => by
    rw [← inv_smul_nsmul S WW hk a, ← inv_smul_nsmul S WW hk b]
    exact congrArg _ hab
  have hb : IsBichar (fun x y : WO S WW => ψ (symplO S WW x y)) := by
    have hl (a b y : WO S WW) : symplO S WW (a + b) y = symplO S WW a y + symplO S WW b y := by
      unfold symplO hO
      simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]
    have hr (x a b : WO S WW) : symplO S WW x (a + b) = symplO S WW x a + symplO S WW x b := by
      unfold symplO hO
      simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, map_add (f := _)]
    have hz₁ (y : WO S WW) : symplO S WW 0 y = 0 := by simpa using hl 0 0 y
    have hz₂ (y : WO S WW) : symplO S WW y 0 = 0 := by simpa using hr y 0 0
    exact ⟨fun a b y => by rw [hl, AddChar.map_add_eq_mul],
      fun a b y => by rw [hr, AddChar.map_add_eq_mul],
      fun y => by rw [hz₁, AddChar.map_zero_eq_one],
      fun y => by rw [hz₂, AddChar.map_zero_eq_one]⟩

  obtain ⟨h1, k, hk, h2, h3⟩ := hSB
  have hmem := mem_algSpan (χ := fun x y : WO S WW => ψ (symplO S WW x y)) (X := half S WW e)
    (Y := half S WW (cA D e)) (L := Λ ⊓ half S WW e) (L' := Λ ⊓ half S WW (cA D e)) hb
    (fun x hx y hy => psi_mem hψ hSd hWd (finX x hx) (finY y hy)) inf_le_right inf_le_right
    (fun u hu y hy => (hdual u (finX u hu.2)).1 hu.1 y hy.1)
    (fun x hx h => ⟨(hdual x (finX x hx)).2 fun u hu => by
      have := h _ (hsm _ he' u hu)
      rwa [← symplO_smul, (mem_half S WW).1 hx] at this, hx⟩)
    (half_div S WW e) (half_div S WW _) tf
    (fun k hk => by
      obtain ⟨R, hR, h⟩ := hfin k hk
      refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
      obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
      refine ⟨_, ⟨r, hr, rfl⟩, e • u, hsm e hee u hu, ?_⟩
      have := (mem_half S WW).1 ht.2
      rw [← this, htr, smul_add, smul_comm e k u])
    _ hΦ (fun t ht => (isHalf_iff S WW).1 (h1 t ht)) k hk
    (fun u hu => h2 u hu.1 ((isHalf_iff S WW).2 hu.2))
    (fun t ht => ⟨h3 t ht, (half S WW e).nsmul_mem ((isHalf_iff S WW).1 (h1 t ht)) _⟩)

  set V : Submodule Qb (WO S WW → ℂ) := Submodule.span Qb
    {F | ∃ w : WO S WW, w.map (infPart D) = 0 ∧ F = heisO ψ S WW w vac} with hV
  have hvac : Tm (halfInd e Λ) = vac := by simpa using hTm.vac
  have s0 := GlobalTheory.isSBHalf_halfInd e Λ
  have hT : ∀ Ψ ∈ algSpan (fun x y : WO S WW => ψ (symplO S WW x y)) (half S WW e) (half S WW (cA D e))
      (Λ ⊓ half S WW e), Tm Ψ ∈ V := by
    intro Ψ hΨ
    induction hΨ using Submodule.span_induction with
    | mem _ hh =>
      obtain ⟨x, hx, y, hy, rfl⟩ := hh
      have s1 : IsSBHalf e Λ fun t => ψ (symplO S WW t y) * halfInd e Λ t := by
        obtain ⟨k, hk, hk'⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO' (S := S) (T := WW)
          (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hSd)
          (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hWd) y (finY y hy)
        obtain ⟨a1, k', hk1, a2, a3⟩ := s0
        refine ⟨fun t ht => a1 t (right_ne_zero_of_mul ht), k * k', Nat.mul_pos hk hk1, fun u hu hh t => ?_,
          fun t ht => ?_⟩
        · have e1 : halfInd e Λ (t + (k * k') • u) = halfInd e Λ t := by
            rw [mul_nsmul]
            exact a2 _ (nsmul_mem hu k) ((isHalf_iff S WW).2 (nsmul_mem ((isHalf_iff S WW).1 hh) k)) t
          have e2 : ψ (symplO S WW ((k * k') • u) y) = 1 := by
            rw [mul_nsmul']
            refine (hb.nsmul k _ y).trans ((hdual _ (finX _ (nsmul_mem ((isHalf_iff S WW).1 hh) k'))).1
              (nsmul_mem hu k') _ hk')
          simp only [e1, symplO_add_left, AddChar.map_add_eq_mul, e2, mul_one]
        · rw [mul_nsmul']
          exact nsmul_mem (a3 t (right_ne_zero_of_mul ht)) k
      have e1 : wave (fun x y : WO S WW => ψ (symplO S WW x y)) (Λ ⊓ half S WW e) x y =
          fun t => (fun t => ψ (symplO S WW t y) * halfInd e Λ t) (t + x) := by
        rw [halfInd_eq_ind]; rfl
      rw [e1, hTm.trans _ s1 x ((isHalf_iff S WW).2 hx), hTm.modul _ s0 y ((isHalf_iff S WW).2 hy), hvac]
      have e2 : heisO ψ S WW x (heisO ψ S WW y vac) =
          ψ (symplOH S WW x y) • heisO ψ S WW (x + y) vac := heisL_heisL S WW ψ x y vac
      rw [e2]
      refine smul_mem_of_mem (psiH_mem hψ hSd hWd (finX x hx) (finY y hy)) (Submodule.subset_span ⟨x + y, ?_, rfl⟩)
      refine Matrix.ext fun a b => ?_
      have q1 : infPart D (x a b) = 0 := congrFun (congrFun (finX x hx) a) b
      have q2 : infPart D (y a b) = 0 := congrFun (congrFun (finY y hy) a) b
      change infPart D (x a b + y a b) = 0
      rw [RingHom.map_add (f := _), q1, q2, add_zero]
    | zero => rw [map_zero]; exact zero_mem _
    | add f g _ _ hf hg => rw [map_add]; exact add_mem hf hg
    | smul c f _ hf =>
      change Tm ((c : ℂ) • f) ∈ V
      rw [map_smul]
      exact V.smul_mem c hf
  obtain ⟨n, f, g, hfg⟩ := (Submodule.mem_span_set').1 (hT _ hmem)
  choose w hw hgw using fun p => (g p).2
  refine ⟨n, fun p => (f p : ℂ), w, fun p => mem_algebraicClosure_iff.1 (f p).2, hw, ?_⟩
  rw [← hfg]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← hgw p]
  rfl

theorem frMapAdj_nsmul (A' WW : HSp D) (βA' : GL (Fin A'.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D)) (k : ℕ)
    (x : WO A' WW) : frMapAdj A' WW βA' βW (k • x) = k • frMapAdj A' WW βA' βW x :=
  map_nsmul (AddMonoidHom.mk' (frMapAdj A' WW βA' βW) (GlobalTheory.PlaceVec.frMapAdj_add A' WW βA' βW)) k x

theorem dualCoord_apply (A' WW : HSp D) (βA' : GL (Fin A'.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D)) (x : WO A' WW)
    (i j) : dualCoord A' WW βA' βW x i j = eToEAf D D.host.xi0 * frMapAdj A' WW βA' βW x i j := rfl

theorem dualCoord_add (A' WW : HSp D) (βA' : GL (Fin A'.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D)) (x y : WO A' WW) :
    dualCoord A' WW βA' βW (x + y) = dualCoord A' WW βA' βW x + dualCoord A' WW βA' βW y := by
  ext i j
  rw [Matrix.add_apply, dualCoord_apply, dualCoord_apply, dualCoord_apply, GlobalTheory.PlaceVec.frMapAdj_add, Matrix.add_apply,
    mul_add]

theorem dualCoord_nsmul (A' WW : HSp D) (βA' : GL (Fin A'.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D)) (k : ℕ)
    (x : WO A' WW) : dualCoord A' WW βA' βW (k • x) = k • dualCoord A' WW βA' βW x :=
  map_nsmul (AddMonoidHom.mk' (dualCoord A' WW βA' βW) (dualCoord_add A' WW βA' βW)) k x

theorem exists_den_dualCoord {A' WW : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)} (hS : ΛS.FG) (hT : ΛT.FG) (βA' : GL (Fin A'.rank) (EAf D))
    (βW : GL (Fin WW.rank) (EAf D)) : ∃ M : ℕ, 0 < M ∧
      ∀ u ∈ latO A' WW (ΛS : Set (Fin A'.rank → D.host.E)) (ΛT : Set (Fin WW.rank → D.host.E)) (fun _ => True),
        ∀ i j, (M : EAf D) * dualCoord A' WW βA' βW u i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨k₃, hk₃, h₃⟩ := GlobalTheory.PlaceVec.exists_nsmul_latO_int (S := A') (T := WW) hS hT
  obtain ⟨k₁, hk₁, h₁⟩ := GlobalTheory.PlaceVec.frMapAdj_up A' WW βA' βW
  obtain ⟨d, hd, hξ⟩ := GlobalTheory.PlaceVec.exists_nsmul_mem_int (eToEAf D D.host.xi0)
  refine ⟨d * k₁ * k₃, by positivity, fun u hu i j => ?_⟩
  have h1 := h₁ (k₃ • u) (by rw [GlobalTheory.PlaceVec.map_toEAf_nsmul]; exact h₃ u hu) i j
  have e : ((d * k₁ * k₃ : ℕ) : EAf D) * dualCoord A' WW βA' βW u i j =
      (d • eToEAf D D.host.xi0) * (k₁ • frMapAdj A' WW βA' βW (k₃ • u)) i j := by
    rw [frMapAdj_nsmul, dualCoord_apply, Matrix.smul_apply, Matrix.smul_apply, nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  rw [e]
  exact mul_mem hξ h1

theorem exists_mul_dualCoord {A' WW : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)} (hS : Submodule.IsFullLattice D.host.E ΛS)
    (hT : Submodule.IsFullLattice D.host.E ΛT) {a : AE D} (hinf : infPart D a = 0) (βA' : GL (Fin A'.rank) (EAf D))
    (βW : GL (Fin WW.rank) (EAf D)) : ∃ K : ℕ, 0 < K ∧ ∀ t : WO A' WW, IsHalf a t → IsIntM (dualCoord A' WW βA' βW t) →
      K • t ∈ latO A' WW (ΛS : Set (Fin A'.rank → D.host.E)) (ΛT : Set (Fin WW.rank → D.host.E)) (fun _ => True) := by
  obtain ⟨m, hm, hξ⟩ := GlobalTheory.PlaceVec.exists_nsmul_mem_int (eToEAf D D.host.xi0⁻¹)
  obtain ⟨k₂, hk₂, h₂⟩ := GlobalTheory.PlaceVec.frMapAdj_down A' WW βA' βW
  obtain ⟨k₄, hk₄, h₄⟩ := GlobalTheory.PlaceVec.exists_nsmul_int_mem_latO hS hT (S := A') (T := WW)
  refine ⟨k₄ * (k₂ * m), by positivity, fun t ht hi => ?_⟩
  have hF : IsIntM (frMapAdj A' WW βA' βW (m • t)) := fun i j => by
    have e : frMapAdj A' WW βA' βW (m • t) i j = (m • eToEAf D D.host.xi0⁻¹) * dualCoord A' WW βA' βW t i j := by
      rw [frMapAdj_nsmul, dualCoord_apply, Matrix.smul_apply, nsmul_eq_mul, nsmul_eq_mul, mul_assoc, ← mul_assoc (eToEAf D _),
        ← RingHom.map_mul, inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), RingHom.map_one, one_mul]
    rw [e]
    exact mul_mem hξ (hi i j)
  have h3 := h₄ (k₂ • m • t)
    (GlobalTheory.PlaceVec.half_infPart hinf (nsmul_mem (nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff A' WW).1 ht) _) _))
    (by rw [GlobalTheory.PlaceVec.map_toEAf_nsmul]; exact h₂ _ hF)
  rwa [smul_smul, smul_smul, mul_assoc] at h3

theorem isIntM_rightBlock {k d a : ℕ} {Y : Matrix (Fin k) (Fin d) (EAf D)} (h : IsIntM Y) : IsIntM (rightBlock a Y) :=
  fun i j => by
    unfold rightBlock
    split_ifs
    · exact h _ _
    · exact zero_mem _

theorem rightBlock_shift {k d a : ℕ} {Y Y' W : Matrix (Fin k) (Fin d) (EAf D)} {c : EAf D}
    (h : ∀ i j, Y' i j = Y i j + c * W i j) (i j : Fin k) :
    rightBlock a Y' i j = rightBlock a Y i j + c * rightBlock a W i j := by
  unfold rightBlock
  split_ifs
  · exact h _ _
  · rw [mul_zero, add_zero]


set_option maxHeartbeats 1000000 in
theorem stdSnd_shift {ν : (AE D)ˣ →* Circle} {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S)
    {I : Ideal (𝓞 D.host.E)} {n₀ n c : ℕ} (hn₀ : ((n₀ : ℕ) : 𝓞 D.host.E) ∈ I)
    (hl : ∀ x, Formalism.L2.Pj.FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = n • y) → ν x = 1)
    (hc : ∀ P ∈ S, ((c : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) (a : ℕ) (A' WW : HSp D) (βA' : GL (Fin A'.rank) (EAf D))
    (βW : GL (Fin WW.rank) (EAf D)) {t t' : WO A' WW} (hh : IsHalf (cA D e) t' ↔ IsHalf (cA D e) t)
    {W : Matrix (Fin A'.rank) (Fin WW.rank) (EAf D)} (hW : IsIntM W)
    (h : ∀ i j, dualCoord A' WW βA' βW t' i j = dualCoord A' WW βA' βW t i j + ((n₀ * (n * c) : ℕ) : EAf D) * W i j) :
    stdSnd ν e I a A' WW βA' βW t' = stdSnd ν e I a A' WW βA' βW t := by
  have hW1 : ∀ i j, ((n * c : ℕ) : EAf D) * W i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun i j => mul_mem (natCast_mem _ _) (hW i j)
  have hW2 : ∀ i j, (n₀ : EAf D) * (((n * c : ℕ) : EAf D) * W i j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun i j => mul_mem (natCast_mem _ _) (hW1 i j)
  have ha : ∀ i j, dualCoord A' WW βA' βW t' i j =
      dualCoord A' WW βA' βW t i j + (n₀ : EAf D) * (((n * c : ℕ) : EAf D) * W i j) := fun i j => by
    rw [h, Nat.cast_mul n₀, mul_assoc]
  have hb : ∀ i j, dualCoord A' WW βA' βW t i j =
      dualCoord A' WW βA' βW t' i j + (n₀ : EAf D) * (-(((n * c : ℕ) : EAf D) * W i j)) := fun i j => by
    rw [ha, mul_neg, add_neg_cancel_right]
  have hint : IsIntM (dualCoord A' WW βA' βW t') ↔ IsIntM (dualCoord A' WW βA' βW t) :=
    forall_congr' fun i => forall_congr' fun j => by
      rw [ha]
      exact add_mem_cancel_right (hW2 i j)
  have hid : (∀ i j, j.1 < a → InId I (dualCoord A' WW βA' βW t' i j)) ↔
      ∀ i j, j.1 < a → InId I (dualCoord A' WW βA' βW t i j) :=
    ⟨fun H i j hj => StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.inId_shift hn₀ (neg_mem (hW1 i j)) (hb i j) (H i j hj),
      fun H i j hj => StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.inId_shift hn₀ (hW1 i j) (ha i j) (H i j hj)⟩
  unfold stdSnd
  by_cases hcnd : IsHalf (cA D e) t ∧ IsIntM (dualCoord A' WW βA' βW t) ∧
      ∀ i j, j.1 < a → InId I (dualCoord A' WW βA' βW t i j)
  · rw [if_pos hcnd, if_pos ⟨hh.2 hcnd.1, hint.2 hcnd.2.1, hid.2 hcnd.2.2⟩]
    refine (StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.unitChar_congr he hl hc (isIntM_rightBlock hcnd.2.1)
      (Z := rightBlock a fun i j => (n₀ : EAf D) * W i j) (isIntM_rightBlock fun i j => mul_mem (natCast_mem _ _) (hW i j))
      (rightBlock_shift (c := ((n * c : ℕ) : EAf D)) fun i j => ?_)).symm
    rw [h, Nat.cast_mul n₀]
    ring
  · rw [if_neg hcnd, if_neg fun h' => hcnd ⟨hh.1 h'.1, hint.1 h'.2.1, hid.1 h'.2.2⟩]


set_option maxHeartbeats 1000000 in
theorem stdSnd_isSB {ν : (AE D)ˣ →* Circle} (hν : Continuous ν) {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S)
    {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊥) (a : ℕ) (A' WW : HSp D) (βA' : GL (Fin A'.rank) (EAf D))
    (βW : GL (Fin WW.rank) (EAf D)) (Λ : AddSubgroup (WO A' WW))
    (hB : ∃ M : ℕ, 0 < M ∧ ∀ u ∈ Λ, ∀ i j, (M : EAf D) * dualCoord A' WW βA' βW u i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hC : ∃ K : ℕ, 0 < K ∧ ∀ t : WO A' WW, IsHalf (cA D e) t → IsIntM (dualCoord A' WW βA' βW t) → K • t ∈ Λ) :
    IsSBHalf (cA D e) Λ (stdSnd ν e I a A' WW βA' βW) := by
  obtain ⟨M, hM, hB⟩ := hB
  obtain ⟨K, hK, hC⟩ := hC
  obtain ⟨n, hn, hl, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D ν hν
  obtain ⟨n₀, hn₀, hnI⟩ : ∃ n₀ : ℕ, 0 < n₀ ∧ ((n₀ : ℕ) : 𝓞 D.host.E) ∈ I :=
    ⟨_, Nat.pos_of_ne_zero fun h => hI (Ideal.absNorm_eq_zero_iff.1 h), Ideal.absNorm_mem I⟩
  obtain ⟨c, hc, hcS⟩ := GlobalTheory.PlaceVec.exists_nat_mem_places S
  refine ⟨fun t ht => ?_, K * ((n₀ * (n * c)) * M), Nat.mul_pos hK (Nat.mul_pos (Nat.mul_pos hn₀ (Nat.mul_pos hn hc)) hM),
    fun u hu hh t => ?_, fun t ht => ?_⟩
  · unfold stdSnd at ht
    by_contra h
    exact ht (if_neg fun h' => h h'.1)
  · refine stdSnd_shift he hnI hl hcS a A' WW βA' βW
      (W := fun i j => (K : EAf D) * ((M : EAf D) * dualCoord A' WW βA' βW u i j))
      ?_ (fun i j => mul_mem (natCast_mem _ _) (hB u hu i j)) fun i j => ?_
    · rw [GlobalTheory.PlaceModel.isHalf_iff A' WW, GlobalTheory.PlaceModel.isHalf_iff A' WW]
      exact AddSubgroup.add_mem_cancel_right _ (nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff A' WW).1 hh) _)
    · rw [dualCoord_add, dualCoord_nsmul, Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul]
      push_cast
      ring
  · have h : IsHalf (cA D e) t ∧ IsIntM (dualCoord A' WW βA' βW t) := by
      unfold stdSnd at ht
      by_contra h
      exact ht (if_neg fun h' => h ⟨h'.1, h'.2.1⟩)
    rw [mul_nsmul]
    exact nsmul_mem (hC t h.1 h.2) _

theorem finDatum'_isAlgComb : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X →
    ∀ t : T, GlobalTheory.MovedAlg.IsAlgComb W.ψ A' WW X.vac' (X.f' t) := by
  intro D T L sc G W i j A A' WW X hX t
  have hI := hX.is
  have hν := (hI.weil' t).hecT
  have he := hI.idem t
  have hee := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hinf := GlobalTheory.PlaceDatum.infPart_cA (GlobalTheory.PlaceDatum.infPart_idemSum he)
  have hSd : IsSelfDualC A' X.rA'.Λ := hI.rigA'.1
  have hWd : IsSelfDualC WW X.rW.Λ := hI.rigW.1
  exact isAlgComb_of_isThetaAt hI.isVac'.1 hSd hWd (by rw [← RingHom.map_mul, hee]) hinf
    (stdSnd_isSB hν.1 he (GlobalTheory.ConstRatio.ideal_ne_bot X (locPl G) t) _ A' WW X.rA'.β X.rW.β _
      (exists_den_dualCoord hSd.1.fg hWd.1.fg X.rA'.β X.rW.β)
      (exists_mul_dualCoord (GlobalTheory.ProjXCols.selfDual_isFullLattice A' _ hSd)
        (GlobalTheory.ProjXCols.selfDual_isFullLattice WW _ hWd) hinf X.rA'.β X.rW.β))
    (fun x => stdSnd_mem hν.1 he _ _ A' WW X.rA'.β X.rW.β x) (hI.snd t)

end GlobalTheory.BotFourierSnd

end
