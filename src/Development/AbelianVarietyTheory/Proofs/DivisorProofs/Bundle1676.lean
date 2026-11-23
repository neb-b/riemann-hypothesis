module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0918
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1657
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrientedHermitianFormQuadSumEqTrace
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformFixedBySmallFiniteHeisenberg
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaLevel

theorem uniform_locConst {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [NonarchimedeanAddGroup X] (g : X → ℂ) (hg : IsLocallyConstant g) (hc : HasCompactSupport g) :
    ∃ H : OpenAddSubgroup X, ∀ z, ∀ a ∈ H, g (z + a) = g z :=
  _root_.GlobalTheory.locallyConstant_compactSupport_invariant_openAddSubgroup g hg hc

theorem char_dot_compact {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    [NonarchimedeanAddGroup K] (χ : AddChar K ℂ) (hχ : Continuous χ) (κ : Type) [Fintype κ] (C : Set (κ → K))
    (hC : IsCompact C) : ∃ H : OpenAddSubgroup (κ → K), ∀ z ∈ C, ∀ a ∈ H, ∀ b ∈ H, χ (z ⬝ᵥ b + a ⬝ᵥ b) = 1 :=
  _root_.GlobalTheory.CharDotKill.charDot_kill χ hχ κ C hC

end GlobalTheory.ThetaLevel

namespace GlobalTheory.ThetaLevel

open Matrix

section Heis

variable {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]

theorem schr_add (a b : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) (x : κ → R) :
    GlobalTheory.WeilM.schr ψ (a + b) φ x =
      ψ (-(⅟(2 : R) * (a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2))) * GlobalTheory.WeilM.schr ψ a (GlobalTheory.WeilM.schr ψ b φ) x := by
  simp only [GlobalTheory.WeilM.schr, Prod.fst_add, Prod.snd_add]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc x a.1 b.1]
  congr 2
  simp only [dotProduct_add, add_dotProduct]
  linear_combination (a.1 ⬝ᵥ b.2) * (invOf_two_add_invOf_two : ⅟(2 : R) + ⅟(2 : R) = 1)

end Heis

theorem symp_eq_symplO (D : D7) (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E)
    (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (hA : JA = T.gramᵀ)
    (hB : ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹)) (x y : Formalism.IndefR.Datum.WO S T) :
    GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB) x y =
      Formalism.IndefR.Datum.symplO S T x y := by
  have hB' : ∀ a b, ξ * incM D.host.F JB a b = incA (D := D) D.host.xi0 * incA (D := D) (S.gram⁻¹ a b) := by
    intro a b
    have h := congrFun (congrFun hB a) b
    rw [Matrix.smul_apply, smul_eq_mul] at h
    rw [h]
    show incA (D := D) (D.host.xi0 * S.gram⁻¹ a b) = _
    rw [map_mul]
  unfold GlobalTheory.WeilM.symp GlobalTheory.WeilM.hTens Formalism.IndefR.Datum.symplO Formalism.IndefR.Datum.hO
  congr 1
  simp only [Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, k]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  subst hA
  have hT : incM D.host.F T.gramᵀ i k = incA (D := D) (T.gram k i) := rfl
  rw [hT]
  have hc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig (y k l) = Formalism.L2.Theta.cA D (y k l) := rfl
  rw [hc]
  linear_combination (x i j * incA (D := D) (T.gram k i) * Formalism.L2.Theta.cA D (y k l)) * hB' j l

end GlobalTheory.ThetaLevel

namespace GlobalTheory.ThetaLevel

open Matrix

def infIncl (F : Type) [Field F] [NumberField F] : Ainf F →ₗ[F] AF F where
  toFun x := pairA F x 0
  map_add' _ _ := Prod.ext rfl (add_zero 0).symm
  map_smul' c _ := Prod.ext rfl (smul_zero c).symm


set_option maxHeartbeats 2000000 in
theorem infIdem_smul (D : D7) (z : AE D) :
    pairA D.host.F 1 0 • z = TensorProduct.map (infIncl D.host.F) LinearMap.id
      (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    rw [TensorProduct.smul_tmul']
    rw [Algebra.TensorProduct.map_tmul, TensorProduct.map_tmul]
    congr 1
    exact Prod.ext (one_mul _) (zero_mul _)
  | add z z' hz hz' =>
    rw [smul_add (pairA D.host.F 1 0) z z', hz, hz', map_add (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)) z z',
      map_add]

theorem finIdem_smul (D : D7) (z : AE D) (hz : infPart D z = 0) : pairA D.host.F 0 1 • z = z := by
  have h1 : pairA D.host.F 0 1 + pairA D.host.F 1 0 = 1 := Prod.ext (zero_add 1) (add_zero 1)
  have h2 := infIdem_smul D z
  rw [show Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) z = 0 from hz, map_zero] at h2
  calc pairA D.host.F 0 1 • z = pairA D.host.F 0 1 • z + pairA D.host.F 1 0 • z := by rw [h2, add_zero]
    _ = z := by rw [← add_smul, h1, one_smul]

theorem e_eq_fin (D : D7) (S T : HSp D) {B : Formalism.IndefR.Datum.WO S T → Formalism.IndefR.Datum.WO S T → AF D.host.F}
    {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (u : Formalism.IndefR.Datum.WO S T)
    (hu : u.map (infPart D) = 0) :
    co.e u = ((fun i => pairA D.host.F 0 ((co.e u).1 i).2), (fun i => pairA D.host.F 0 ((co.e u).2 i).2)) := by
  have hu' : pairA D.host.F 0 1 • u = u := by
    ext a b
    exact finIdem_smul D (u a b) (congrFun (congrFun hu a) b)
  have h2 := congrArg co.e hu'
  rw [LinearEquiv.map_smul] at h2
  conv_lhs => rw [← h2]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · exact Prod.ext (zero_mul _) (one_mul _)
  · exact Prod.ext (zero_mul _) (one_mul _)

theorem schr_fin_fix (F : Type) [Field F] [NumberField F] [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ)
    (hψ : Continuous ψ) {κ : Type} [Fintype κ] (Φ : (κ → AF F) → ℂ) (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) :
    ∃ K : OpenAddSubgroup (κ → Af F), ∀ a ∈ K, ∀ b ∈ K,
      GlobalTheory.WeilM.schr ψ ((fun i => pairA F 0 (a i)), (fun i => pairA F 0 (b i))) Φ = Φ := by
  haveI := GlobalTheory.HeisSchA.nonarch_finiteAdeleRing (F := F)
  haveI : NonarchimedeanAddGroup (κ → Af F) := GlobalTheory.HeisSchA.nonarch_pi
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    obtain ⟨H1, hH1⟩ := uniform_locConst g hg.1 hg.2
    obtain ⟨H2, hH2⟩ := char_dot_compact (GlobalTheory.HeisSchA.finChar ψ)
      (hψ.comp (continuous_const.prodMk continuous_id)) κ (tsupport g) hg.2
    let c : Af F := (⅟(2 : AF F)).2
    let m : (κ → Af F) →+ (κ → Af F) := DistribSMul.toAddMonoidHom _ c
    have hm : Continuous m := continuous_const_smul c
    refine ⟨H1 ⊓ H2 ⊓ H2.comap m hm, fun a ha b hb => funext fun x => ?_⟩
    obtain ⟨⟨ha1, -⟩, ha3⟩ := ha
    obtain ⟨⟨-, hb2⟩, -⟩ := hb
    let z : κ → Af F := fun i => (x i).2
    have hpa1 : GlobalTheory.WeilM.pureA F f g (x + fun i => pairA F 0 (a i)) =
        f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) * g (z + a) := by
      simp only [GlobalTheory.WeilM.pureA]
      congr 2
      funext i
      show InfiniteAdeleRing.ringEquiv_mixedSpace F ((x i).1 + 0) = _
      rw [add_zero]
    have hpa0 : GlobalTheory.WeilM.pureA F f g x = f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) * g z := rfl
    have harg : x ⬝ᵥ (fun i => pairA F 0 (b i)) + ⅟(2 : AF F) * ((fun i => pairA F 0 (a i)) ⬝ᵥ (fun i => pairA F 0 (b i)))
        = pairA F 0 (z ⬝ᵥ b + (c • a) ⬝ᵥ b) := by
      have e1 : GlobalTheory.HeisSchA.p1 (F := F) (x ⬝ᵥ (fun i => pairA F 0 (b i)) + ⅟(2 : AF F) *
          ((fun i => pairA F 0 (a i)) ⬝ᵥ (fun i => pairA F 0 (b i)))) = 0 := by
        rw [map_add (f := _), map_mul, RingHom.map_dotProduct, RingHom.map_dotProduct]
        have e0 : (fun i => GlobalTheory.HeisSchA.p1 (F := F) (pairA F 0 (b i))) = 0 := funext fun i => rfl
        simp only [Function.comp_def, e0, dotProduct_zero, mul_zero, add_zero]
      have e2 : GlobalTheory.HeisSchA.p2 (F := F) (x ⬝ᵥ (fun i => pairA F 0 (b i)) + ⅟(2 : AF F) *
          ((fun i => pairA F 0 (a i)) ⬝ᵥ (fun i => pairA F 0 (b i)))) = z ⬝ᵥ b + (c • a) ⬝ᵥ b := by
        rw [map_add (f := _), map_mul, RingHom.map_dotProduct, RingHom.map_dotProduct, smul_dotProduct, smul_eq_mul]
        rfl
      exact Prod.ext e1 e2
    show ψ (x ⬝ᵥ (fun i => pairA F 0 (b i)) + ⅟(2 : AF F) * ((fun i => pairA F 0 (a i)) ⬝ᵥ
      (fun i => pairA F 0 (b i)))) * GlobalTheory.WeilM.pureA F f g (x + fun i => pairA F 0 (a i)) = GlobalTheory.WeilM.pureA F f g x
    rw [harg, hpa1, hpa0, hH1 z a ha1]
    by_cases hz : g z = 0
    · rw [hz, mul_zero, mul_zero]
    · have h3 : GlobalTheory.HeisSchA.finChar ψ (z ⬝ᵥ b + (c • a) ⬝ᵥ b) = 1 := hH2 z (subset_tsupport _ hz) _ ha3 b hb2
      rw [show ψ (pairA F 0 (z ⬝ᵥ b + (c • a) ⬝ᵥ b)) = 1 from h3, one_mul]
  | zero => exact ⟨⊤, fun a _ b _ => funext fun x => mul_zero _⟩
  | add Φ₁ Φ₂ _ _ h1 h2 =>
    obtain ⟨K1, hK1⟩ := h1
    obtain ⟨K2, hK2⟩ := h2
    refine ⟨K1 ⊓ K2, fun a ha b hb => funext fun x => ?_⟩
    have e1 := congrFun (hK1 a ha.1 b hb.1) x
    have e2 := congrFun (hK2 a ha.2 b hb.2) x
    simp only [GlobalTheory.WeilM.schr] at e1 e2 ⊢
    rw [Pi.add_apply, Pi.add_apply, mul_add, e1, e2]
  | smul r Φ₁ _ h1 =>
    obtain ⟨K1, hK1⟩ := h1
    refine ⟨K1, fun a ha b hb => funext fun x => ?_⟩
    have e1 := congrFun (hK1 a ha b hb) x
    simp only [GlobalTheory.WeilM.schr] at e1 ⊢
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, e1]

end GlobalTheory.ThetaLevel

namespace GlobalTheory.ThetaLevel

open Matrix


set_option maxHeartbeats 1000000 in
theorem thetaTr_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
      ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
        (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
          co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
        ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∃ U : AddSubgroup (Formalism.IndefR.Datum.WO S T), IsOpen (U : Set (Formalism.IndefR.Datum.WO S T)) ∧
          ∀ u ∈ U, u.map (infPart D) = 0 → Formalism.IndefR.Datum.heisO ψ S T u (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) = GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ := by
  intro D ψ hψ S T JA JB ξ hA hB κ _ co _ Φ hΦ
  haveI : IsModuleTopology (AF D.host.F) (Formalism.IndefR.Datum.WO S T) :=
    inferInstanceAs (IsModuleTopology (AF D.host.F) (Fin T.rank → Fin S.rank → AE D))
  obtain ⟨K, hK⟩ := schr_fin_fix D.host.F ψ hψ.1.1 Φ hΦ
  have hcont : Continuous co.e := IsModuleTopology.continuous_of_linearMap co.e.toLinearMap
  let f1 : Formalism.IndefR.Datum.WO S T →+ (κ → Af D.host.F) :=
    AddMonoidHom.mk' (fun u i => ((co.e u).1 i).2) (fun u v => by funext i; rw [map_add (f := _)]; rfl)
  let f2 : Formalism.IndefR.Datum.WO S T →+ (κ → Af D.host.F) :=
    AddMonoidHom.mk' (fun u i => ((co.e u).2 i).2) (fun u v => by funext i; rw [map_add (f := _)]; rfl)
  have hf1 : Continuous f1 :=
    continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp (continuous_fst.comp hcont))
  have hf2 : Continuous f2 :=
    continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp (continuous_snd.comp hcont))
  let U : OpenAddSubgroup (Formalism.IndefR.Datum.WO S T) := K.comap f1 hf1 ⊓ K.comap f2 hf2
  refine ⟨(U : AddSubgroup _), U.isOpen, fun u hu hinf => funext fun w => ?_⟩
  have hfix : GlobalTheory.WeilM.schr ψ (co.e u) Φ = Φ := by
    rw [e_eq_fin D S T co u hinf]
    exact hK _ hu.1 _ hu.2
  show ψ (Formalism.IndefR.Datum.symplOH S T w u) * GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ (co.e (w + u)) Φ) =
    GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ (co.e w) Φ)
  rw [map_add (f := _)]
  have h1 : GlobalTheory.WeilM.schr ψ (co.e w + co.e u) Φ = fun x =>
      ψ (-(⅟(2 : AF D.host.F) * ((co.e w).1 ⬝ᵥ (co.e u).2 - (co.e u).1 ⬝ᵥ (co.e w).2))) *
        GlobalTheory.WeilM.schr ψ (co.e w) (GlobalTheory.WeilM.schr ψ (co.e u) Φ) x :=
    funext (schr_add ψ _ _ Φ)
  rw [h1, hfix]
  simp only [GlobalTheory.WeilM.thetaSum]
  rw [tsum_mul_left, ← mul_assoc, ← AddChar.map_add_eq_mul]
  have h2 : Formalism.IndefR.Datum.symplOH S T w u =
      ⅟(2 : AF D.host.F) * ((co.e w).1 ⬝ᵥ (co.e u).2 - (co.e u).1 ⬝ᵥ (co.e w).2) := by
    rw [← co.form, symp_eq_symplO D S T JA JB ξ hA hB, Formalism.IndefR.Datum.symplOH]
    congr 1
    refine (invOf_eq_right_inv ?_).symm
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
    norm_num
  rw [h2, add_neg_cancel, AddChar.map_zero_eq_one, one_mul]

end GlobalTheory.ThetaLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSecondPos
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RouteCoordsW

open GlobalTheory.RouteCoords GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation

theorem trace_second_pos {A : Type} [CommRing A] (c : A →+* A) {n b : ℕ} (hc : ∀ z, c (c z) = z) (ξ : A) (hξ : c ξ = -ξ)
    (g : Matrix (Fin n) (Fin n) A) (p pi : Matrix (Fin b) (Fin b) A) (hg : (g.map c)ᵀ = g) (hp : (p.map c)ᵀ = p)
    (hpi : pi * p = 1) (Z Z' : Matrix (Fin n) (Fin b) A) :
    c (ξ * (pi * ((-(Z'.map c * p)).map c)ᵀ * g * (-(Z.map c * p))).trace) =
      -(ξ * (Z * pᵀ * (Z'.map c)ᵀ * gᵀ).trace) := by
  rw [← trace_second c hc ξ hξ g p pi hg hp hpi Z Z', ← map_neg, ← mul_neg, ← trace_neg]
  congr 3
  simp only [Matrix.neg_mul, neg_neg]

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.RouteCoordsW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLatticeInvariantSchwartzGlobal
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Classical

open scoped GlobalTheory.VacAny
open Topology

noncomputable section
namespace GlobalTheory.VacAvg

def schrL {K : Type} [CommRing K] [Invertible (2 : K)] (ψ : AddChar K ℂ) {κ : Type} [Fintype κ]
    (z : (κ → K) × (κ → K)) : Module.End ℂ ((κ → K) → ℂ) where
  toFun := schr ψ z
  map_add' f g := by funext x; simp only [schr, Pi.add_apply, mul_add]
  map_smul' r f := by funext x; simp only [schr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem schrL_apply {K : Type} [CommRing K] [Invertible (2 : K)] (ψ : AddChar K ℂ) {κ : Type} [Fintype κ]
    (z : (κ → K) × (κ → K)) (f : (κ → K) → ℂ) : schrL ψ z f = schr ψ z f := rfl

theorem ops_schrL {K : Type} [CommRing K] [Invertible (2 : K)] (ψ : AddChar K ℂ) {κ : Type} [Fintype κ] :
    GlobalTheory.Published.SvN.Ops (fun z z' : (κ → K) × (κ → K) => ψ (⅟(2 : K) * (z.1 ⬝ᵥ z'.2 - z'.1 ⬝ᵥ z.2))) (schrL ψ) := by
  constructor
  · intro v
    funext x
    simp [schrL_apply, schr]
  · intro x y v
    simp only [schrL_apply]
    exact schr_schr ψ x y v

theorem addChar_ne_zero {A : Type} [AddGroup A] (ψ : AddChar A ℂ) (t : A) : ψ t ≠ 0 := by
  intro h
  have := ψ.map_add_eq_mul t (-t)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

theorem eventually_schr_fix {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) (ψ : AddChar (Fv F v) ℂ)
    (hψ : Continuous ψ) {κ : Type} [Fintype κ] {f : (κ → Fv F v) → ℂ} (hf : f ∈ SB (κ → Fv F v)) :
    ∀ᶠ z in 𝓝 (0 : (κ → Fv F v) × (κ → Fv F v)), schr ψ z f = f := by
  obtain ⟨U₀, hU₀⟩ := GlobalTheory.HeisLatVac.lc_exists_open_ker ψ hψ
  obtain ⟨K, hK⟩ := GlobalTheory.WeilM.HaarUniq.exists_invariant hf
  have hc : Continuous fun z : ((κ → Fv F v) × (κ → Fv F v)) × (κ → Fv F v) =>
      z.2 ⬝ᵥ z.1.2 + ⅟(2 : Fv F v) * (z.1.1 ⬝ᵥ z.1.2) :=
    (continuous_snd.dotProduct continuous_fst.snd).add
      (continuous_const.mul (continuous_fst.fst.dotProduct continuous_fst.snd))
  have h1 : ∀ᶠ z : (κ → Fv F v) × (κ → Fv F v) in 𝓝 0, ∀ x ∈ tsupport f,
      x ⬝ᵥ z.2 + ⅟(2 : Fv F v) * (z.1 ⬝ᵥ z.2) ∈ (U₀ : Set (Fv F v)) := by
    refine IsCompact.eventually_forall_of_forall_eventually hf.2
      (P := fun (z : (κ → Fv F v) × (κ → Fv F v)) (x : κ → Fv F v) =>
        x ⬝ᵥ z.2 + ⅟(2 : Fv F v) * (z.1 ⬝ᵥ z.2) ∈ (U₀ : Set (Fv F v))) fun x _ => ?_
    refine (U₀.isOpen.preimage hc).mem_nhds ?_
    simpa using U₀.zero_mem
  have h2 : ∀ᶠ z : (κ → Fv F v) × (κ → Fv F v) in 𝓝 0, z.1 ∈ (K : Set (κ → Fv F v)) :=
    (K.isOpen.preimage continuous_fst).mem_nhds K.zero_mem
  filter_upwards [h1, h2] with z hz1 hz2
  funext x
  show ψ (x ⬝ᵥ z.2 + ⅟(2 : Fv F v) * (z.1 ⬝ᵥ z.2)) * f (x + z.1) = f x
  rw [hK z.1 hz2 x]
  by_cases hx : x ∈ tsupport f
  · rw [hU₀ _ (hz1 x hx), one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

theorem tens_sum {F : Type} [Field F] [NumberField F] {R κ ι : Type} (ev : AF F → R) (s : Finset ι) (c : ι → ℂ)
    (g : ι → (κ → R) → ℂ) (r : (κ → AF F) → ℂ) :
    tens ev (∑ q ∈ s, c q • g q) r = ∑ q ∈ s, c q • tens ev (g q) r := by
  funext x
  simp only [tens, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, mul_assoc]

theorem tens_smul {F : Type} [Field F] [NumberField F] {R κ : Type} (ev : AF F → R) (c : ℂ) (g : (κ → R) → ℂ)
    (r : (κ → AF F) → ℂ) : tens ev (c • g) r = c • tens ev g r := by
  funext x
  simp only [tens, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem rho_sum {R : Type} [CommRing R] [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W]
    {B : W → W → R} {κ ι : Type} [Fintype κ] (d : Darboux B κ) (ψ : AddChar R ℂ) (γ : W) (s : Finset ι)
    (Φ : ι → (κ → R) → ℂ) : d.rho ψ γ (∑ q ∈ s, Φ q) = ∑ q ∈ s, d.rho ψ γ (Φ q) := by
  funext x
  simp only [Darboux.rho, schr, Finset.sum_apply, Finset.mul_sum]

theorem avg_eigen : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (w : Pl (F := F)) (Ψ : (Fin a' × Fin (a + a') → AF F) → ℂ), Ψ ∈ schA F (Fin a' × Fin (a + a')) →
    (∀ γ ∈ latAtV G.V' G.W w, ∀ c : ℂ, Acts (evFin F w) (G.M'.co.rho B.ψ γ) (G.M'.vac w) (c • G.M'.vac w) →
      G.M'.co.rho B.ψ γ Ψ = c • Ψ) →
    ∀ (m : ℕ) (f : Fin m → SInf F (Fin a' × Fin (a + a'))) (φ : Fin m → ∀ v : Pl (F := F), (Fin a' × Fin (a + a') → Fv F v) → ℂ),
    (∀ i v, φ i v ∈ SB (Fin a' × Fin (a + a') → Fv F v)) →
    (∀ i, ∀ᶠ v in Filter.cofinite, φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1) →
    Ψ = ∑ i, pure (f i) (φ i) →
    ∃ g : Fin m → (Fin a' × Fin (a + a') → Fv F w) → ℂ, (∀ i, g i ∈ SB (Fin a' × Fin (a + a') → Fv F w)) ∧
      (∀ i, ∀ γ ∈ latAtV G.V' G.W w, ∀ c : ℂ, Acts (evFin F w) (G.M'.co.rho B.ψ γ) (G.M'.vac w) (c • G.M'.vac w) →
        Acts (evFin F w) (G.M'.co.rho B.ψ γ) (g i) (c • g i)) ∧
      Ψ = ∑ i, pure (f i) (Function.update (φ i) w (g i)) := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hT w Ψ _ hyp m f φ hSB hstd hsum
  classical
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ w) := GlobalTheory.SchrSB.continuous_psiAt B.ψ hT.base.std.1 w
  obtain ⟨hvSB, hv0, θ, -, hθ⟩ := hT.geo.hM'.vac w
  have hat : ∀ γ ∈ latAtV G.V' G.W w, At (evFin F w) γ := (GlobalTheory.LatVac.latAtV_at_stable G.V' G.W w).1
  set L := schrL (κ := Fin a' × Fin (a + a')) (GlobalTheory.LatVac.psiAt B.ψ w) with hL
  set vac := G.M'.vac w with hvac
  set Λ := (latAtV G.V' G.W w).map (GlobalTheory.LatVac.locCo G.M'.co w) with hΛ
  obtain ⟨-, hΛc⟩ := GlobalTheory.LatOpenCpt.main σ B G.V' G.W _ _ _ _ hT.geo.hV' hT.geo.hW G.M' hT.geo.hM'.rat w
  have hAct : ∀ γ ∈ latAtV G.V' G.W w, ∀ φ₀ : (Fin a' × Fin (a + a') → Fv F w) → ℂ,
      Acts (evFin F w) (G.M'.co.rho B.ψ γ) φ₀ (L (GlobalTheory.LatVac.locCo G.M'.co w γ) φ₀) :=
    fun γ hγ φ₀ => GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ w γ (hat γ hγ) φ₀
  have huniq : ∀ γ ∈ latAtV G.V' G.W w, ∀ c₀ : ℂ, Acts (evFin F w) (G.M'.co.rho B.ψ γ) vac (c₀ • vac) →
      L (GlobalTheory.LatVac.locCo G.M'.co w γ) vac = c₀ • vac := fun γ hγ c₀ h =>
    GlobalTheory.TensUniq.eq_of_tens_eq w vac _ _ hvSB fun r hr => (hAct γ hγ vac r hr).symm.trans (h r hr)
  have hinj : ∀ e e' : ℂ, e • vac = e' • vac → e = e' := fun e e' h => smul_left_injective ℂ hv0 h
  have hex : ∀ z ∈ Λ, ∃ e : ℂ, L z vac = e • vac := by
    rintro _ ⟨γ, hγ, rfl⟩
    exact ⟨_, huniq γ hγ _ (hθ γ hγ)⟩
  let α : (Fin a' × Fin (a + a') → Fv F w) × (Fin a' × Fin (a + a') → Fv F w) → ℂ :=
    fun z => if h : ∃ e : ℂ, L z vac = e • vac then h.choose else 1
  have hαspec : ∀ z, (∃ e : ℂ, L z vac = e • vac) → L z vac = α z • vac := fun z h => by
    show _ = (if h : ∃ e : ℂ, L z vac = e • vac then h.choose else 1) • vac
    rw [dite_eq_left h]
    exact h.choose_spec
  let c : (Fin a' × Fin (a + a') → Fv F w) × (Fin a' × Fin (a + a') → Fv F w) →
      (Fin a' × Fin (a + a') → Fv F w) × (Fin a' × Fin (a + a') → Fv F w) → ℂ :=
    fun z z' => GlobalTheory.LatVac.psiAt B.ψ w (⅟(2 : Fv F w) * (z.1 ⬝ᵥ z'.2 - z'.1 ⬝ᵥ z.2))
  have hops : GlobalTheory.Published.SvN.Ops c L := ops_schrL _
  have hαne : ∀ z ∈ Λ, α z ≠ 0 := by
    intro z hz h0
    have h1 := hops.mul (-z) z vac
    rw [hαspec z (hex z hz), h0, zero_smul, map_zero, neg_add_cancel, hops.zero] at h1
    exact hv0 ((smul_eq_zero.1 h1.symm).resolve_left (addChar_ne_zero _ _))
  have hsplit : GlobalTheory.Published.SvN.Splits c Λ α := by
    refine ⟨hαne, fun x hx y hy => hinj _ _ ?_⟩
    have h1 := hops.mul x y vac
    rw [hαspec y (hex y hy), map_smul, hαspec x (hex x hx), hαspec (x + y) (hex _ (Λ.add_mem hx hy)), smul_smul,
      smul_smul] at h1
    rw [mul_comm (α x)]
    exact h1
  have hfix : ∀ᶠ z in 𝓝 (0 : (Fin a' × Fin (a + a') → Fv F w) × (Fin a' × Fin (a + a') → Fv F w)),
      L z vac = vac ∧ ∀ i, L z (φ i w) = φ i w :=
    (eventually_schr_fix w _ hψc hvSB).and (Filter.eventually_all.2 fun i => eventually_schr_fix w _ hψc (hSB i w))
  obtain ⟨U, hU⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hfix
  have hUα : ∀ u ∈ U.toAddSubgroup, α u = 1 := fun u hu =>
    hinj _ _ (by rw [← hαspec u ⟨1, by rw [one_smul]; exact (hU hu).1⟩, one_smul]; exact (hU hu).1)
  have hfin : Finite (Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ) :=
    GlobalTheory.Published.SvN.finite_quot Λ U.toAddSubgroup U.mem_nhds_zero hΛc subset_rfl
  letI := Fintype.ofFinite (Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ)
  obtain ⟨avg, havg⟩ : ∃ avg : Fin m → (Fin a' × Fin (a + a') → Fv F w) → ℂ, ∀ i,
      avg i = ∑ q : Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ, (α q.out.1)⁻¹ • L q.out.1 (φ i w) := ⟨_, fun _ => rfl⟩
  have heig : ∀ i, ∀ z ∈ Λ, L z (avg i) = α z • avg i := fun i z hz => by
    rw [havg i]
    exact GlobalTheory.Published.SvN.average hops hsplit U.toAddSubgroup hUα (φ i w) (fun u hu => (hU hu).2 i) z hz
  set N := Fintype.card (Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ) with hN
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  choose γq hγq hγqe using fun q : Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ => AddSubgroup.mem_map.1 q.out.2
  choose r hr1 hr2 using fun i => GlobalTheory.PureFactor.exists_rest_factor w (f i) (φ i) (hstd i)
  have hpure : ∀ i, pure (f i) (φ i) = tens (evFin F w) (φ i w) (r i) := fun i => by
    rw [hr2, Function.update_eq_self]
  have hRest : ∀ i, Rest (evFin F w) (φ i w) (r i) := fun i =>
    ⟨hr1 i, hpure i ▸ GlobalTheory.TensUniq.pure_mem_schA (f i) (φ i) (hSB i) (hstd i)⟩
  have hΨ' : Ψ = ∑ i, tens (evFin F w) (φ i w) (r i) := by
    rw [hsum]; exact Finset.sum_congr rfl fun i _ => hpure i
  have hqΨ : ∀ q : Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ, G.M'.co.rho B.ψ (γq q) Ψ = α q.out.1 • Ψ := fun q =>
    hyp _ (hγq q) _ (by
      have := hAct _ (hγq q) vac
      rwa [hγqe q, hαspec _ (hex _ q.out.2)] at this)
  have hqΨ2 : ∀ q : Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ,
      G.M'.co.rho B.ψ (γq q) Ψ = ∑ i, tens (evFin F w) (L q.out.1 (φ i w)) (r i) := fun q => by
    rw [hΨ', rho_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hAct _ (hγq q) (φ i w) (r i) (hRest i), hγqe q]
  have e1 : ∑ q : Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ, (α q.out.1)⁻¹ • G.M'.co.rho B.ψ (γq q) Ψ = (N : ℂ) • Ψ := by
    calc ∑ q : Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ, (α q.out.1)⁻¹ • G.M'.co.rho B.ψ (γq q) Ψ
          = ∑ q : Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ, Ψ :=
          Finset.sum_congr rfl fun q _ => by rw [hqΨ q, smul_smul, inv_mul_cancel₀ (hαne _ q.out.2), one_smul]
      _ = (N : ℂ) • Ψ := by rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  have e2 : ∑ q : Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ, (α q.out.1)⁻¹ • G.M'.co.rho B.ψ (γq q) Ψ =
      ∑ i, tens (evFin F w) (avg i) (r i) := by
    simp only [hqΨ2, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [havg i, tens_sum]
  have hgSB : ∀ i, (N : ℂ)⁻¹ • avg i ∈ SB (Fin a' × Fin (a + a') → Fv F w) := fun i => by
    rw [havg i]
    exact (SB _).smul_mem _ (Submodule.sum_mem _ fun q _ => (SB _).smul_mem _
      (GlobalTheory.SchrSB.schr_mem_SB B.ψ hT.base.std.1 w _ _ (hSB i w)))
  refine ⟨fun i => (N : ℂ)⁻¹ • avg i, hgSB, fun i γ hγ c₀ hc => ?_, ?_⟩
  · have hz : GlobalTheory.LatVac.locCo G.M'.co w γ ∈ Λ := AddSubgroup.mem_map_of_mem _ hγ
    have e := huniq γ hγ c₀ hc
    rw [hαspec _ (hex _ hz)] at e
    have hc₀ := hinj _ _ e
    have := hAct γ hγ ((N : ℂ)⁻¹ • avg i)
    rwa [map_smul, heig i _ hz, hc₀, smul_comm] at this
  · calc Ψ = (N : ℂ)⁻¹ • ((N : ℂ) • Ψ) := by rw [smul_smul, inv_mul_cancel₀ hN0, one_smul]
      _ = _ := by
        rw [← e1, e2, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← tens_smul, hr2]

end GlobalTheory.VacAvg
end
end

