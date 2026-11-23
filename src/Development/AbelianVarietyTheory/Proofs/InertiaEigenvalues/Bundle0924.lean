module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0821
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0912
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0918
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0797
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0913
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumsSpanCuspFormsBaseTupleSecondField
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0012
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1602
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0963
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentSumSelfDualFramesBound
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0919
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0615
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitarySphericalSatakeMultisetMapInv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0800
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0770
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLevelDatumReferenceTupleSmallField
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.RefDatumLev

variable {D : D7}

theorem q_base_empty {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0) :
    R.Q A.μ0 = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun PP hPP => ?_
  have h := (hL.Q_ram A.μ0 PP).2 (Or.inl hPP)
  rw [hL.xi_base] at h
  exact h fun x _ => rfl

open Classical in
theorem isIdemSum_conjPl {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (h : IsIdemSum e P) :
    IsIdemSum (cA D e) (P.image Formalism.L2.DIV.conjPl) := by
  classical
  obtain ⟨⟨es, hes, he⟩, hc⟩ := h
  refine ⟨⟨fun Q => cA D (es (Formalism.L2.DIV.conjPl Q)), ?_, ?_⟩, ?_⟩
  · intro Q hQ
    obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hQ
    show Formalism.L2.NTheta.IsIdemAt (cA D (es (Formalism.L2.DIV.conjPl (Formalism.L2.DIV.conjPl PP)))) (Formalism.L2.DIV.conjPl PP)
    rw [Formalism.L2.DIV.conjPl_conjPl]
    exact GlobalTheory.MovedIdem.isIdemAt_conj (hes PP hPP) fun x => Iff.rfl
  · rw [Finset.sum_image (fun a _ b _ (hab : Formalism.L2.DIV.conjPl a = Formalism.L2.DIV.conjPl b) => by
      rw [← Formalism.L2.DIV.conjPl_conjPl a, hab, Formalism.L2.DIV.conjPl_conjPl b])]
    simp only [Formalism.L2.DIV.conjPl_conjPl]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [he, map_sum]
  · rw [GlobalTheory.MovedIdem.cA_cA, mul_comm]; exact hc

theorem frMapAdj_add' (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (x y : WO S T) :
    frMapAdj S T βS βT (x + y) = frMapAdj S T βS βT x + frMapAdj S T βS βT y := by
  unfold frMapAdj
  rw [Matrix.map_add (cA D) (fun a b => (cA D).map_add a b), Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul,
    Matrix.map_add (toEAf D) (fun a b => (toEAf D).map_add a b), Matrix.mul_add, Matrix.add_mul]

theorem frMapAdj_nsmul' (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (k : ℕ) (x : WO S T) :
    frMapAdj S T βS βT (k • x) = k • frMapAdj S T βS βT x := by
  induction k with
  | zero =>
    rw [zero_smul, zero_smul]
    unfold frMapAdj
    rw [Matrix.map_zero (cA D) (cA D).map_zero, Matrix.transpose_zero, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.map_zero (toEAf D) (toEAf D).map_zero, Matrix.mul_zero, Matrix.zero_mul]
  | succ n ih => rw [succ_nsmul, succ_nsmul, frMapAdj_add', ih]

theorem natM_mem_Mb (T : CoreJ D) : ((T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ T.Q.l.Mb := by
  have hle : T.Q.l.Mb * T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ T.Q.l.Mb := Ideal.mul_le_left
  rw [T.Q.l.prod] at hle
  exact hle (Ideal.mem_span_singleton_self _)

theorem isIntM_add_nsmul_iff {b a : ℕ} {N N' : Matrix (Fin b) (Fin a) (EAf D)} (hN' : IsIntM N') (k : ℕ) :
    IsIntM (N + k • N') ↔ IsIntM N := by
  constructor
  · intro h i j
    have := sub_mem (h i j) (nsmul_mem (hN' i j) k)
    rwa [Matrix.add_apply, Matrix.smul_apply, add_sub_cancel_right] at this
  · intro h i j
    rw [Matrix.add_apply, Matrix.smul_apply]
    exact add_mem (h i j) (nsmul_mem (hN' i j) k)

theorem redM_add_nsmul (PP : Formalism.L2.DIV.Pl D.host.E) {b a : ℕ} {N N' : Matrix (Fin b) (Fin a) (EAf D)} (hN : IsIntM N)
    (hN' : IsIntM N') (k : ℕ) (hk : ((k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) : redM PP (N + k • N') = redM PP N := by
  have hk0 : ((k : ℕ) : Formalism.L2.DIV.kP PP) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hk
  ext i j
  have h1 : (N + k • N') i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := (isIntM_add_nsmul_iff hN' _).2 hN i j
  unfold redM
  rw [dite_eq_left h1, dite_eq_left (hN i j)]
  have h2 : (⟨(N + k • N') i j, h1⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) =
      ⟨N i j, hN i j⟩ + ((k : ℕ) : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨N' i j, hN' i j⟩ := by
    apply Subtype.ext
    simp [Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h2, map_add (f := _), map_mul, map_natCast, hk0, zero_mul, add_zero]

theorem omegaK_congr {a b : ℕ} (Pg : Finset (Formalism.L2.DIV.Pl D.host.E))
    {y y' : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)}
    (h : ∀ PP ∈ Pg, y PP = y' PP) : omegaK Pg y = omegaK Pg y' := by
  unfold omegaK
  have : (∀ PP ∈ Pg, LowZero a (y PP) ∧ topL a (y PP) = 1) ↔ (∀ PP ∈ Pg, LowZero a (y' PP) ∧ topL a (y' PP) = 1) :=
    ⟨fun hy PP hPP => h PP hPP ▸ hy PP hPP, fun hy PP hPP => (h PP hPP).symm ▸ hy PP hPP⟩
  by_cases hc : ∀ PP ∈ Pg, LowZero a (y PP) ∧ topL a (y PP) = 1
  · rw [if_pos hc, if_pos (this.1 hc)]
  · rw [if_neg hc, if_neg (fun h' => hc (this.2 h'))]

theorem omegaK_mem {a b : ℕ} (Pg : Finset (Formalism.L2.DIV.Pl D.host.E))
    (y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)) (k : Subfield ℂ) :
    omegaK Pg y ∈ k := by
  unfold omegaK
  split_ifs
  exacts [k.one_mem, k.zero_mem]

theorem omegaQ_empty {a b : ℕ} (r : ℕ) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (k : ℤ)
    (y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)) : omegaQ ∅ r ξ k y = 1 := by
  unfold omegaQ
  rw [dite_eq_left (fun PP h => absurd h (Finset.notMem_empty PP))]
  simp

theorem isLevDatum_ref : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m), GlobalTheory.NT.RayField → ∀ (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)), LawsJ T → GlobalTheory.Hk3.Core Rl.toRealDat F → Nonempty (FWTie T Rl.toRealDat κ v₀) → TieIn T Rl.toRealDat κ v₀ → IoExt Rl.toRealDat → QGuard Rl.toRealDat → IsGalois ℚ D.LL0 → Formalism.L2.Host.ValLL0 D Rl.C → RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → ∀ (j : Fin D.R.m) (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j), OMPins T Rl.toRealDat κ v₀ O j → GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T Rl.toRealDat j T.σ₀ hV → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.IsLevDatum Rl.toRealDat.ψ (Vc D j) (Wc D j) (Rl.toRealDat.ΛV j) (Rl.toRealDat.ΛW j) T.Q.l.M (embLL0 D).fieldRange (Rl.toRealDat.vacP j) (Rl.toRealDat.vP j A3.A.μ0) := by
  intro D Γ _ _ Pl0 I0 T0 A3 hRF T _ Rl cG S YS F κ v₀ O hT hcore hfw hti hio hQ hgal hval hray hroots j hV hpins hfp
  classical
  have hQ0 : Rl.toRealDat.Q A3.A.μ0 = ∅ := q_base_empty Rl.toRealDat hcore.lev
  obtain ⟨-, e, he, hth⟩ := hcore.thP.vP j A3.A.μ0
  rw [hQ0, Finset.union_empty] at he
  simp only [hQ0, omegaQ_empty, mul_one] at hth
  obtain ⟨cV, hbV⟩ := hcore.lev.βV j
  obtain ⟨cW, hbW⟩ := hcore.lev.βW j
  have hsV := GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hbV
  have hsW := GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hbW
  have hfV := hbV.1
  have hfW := hbW.1
  have hhalf := (hpins.2.tuple ()).half
  have hP2 : ∀ PP ∈ Rl.toRealDat.Pg,
      ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal :=
    fun PP hPP => hhalf.2.2 PP (Or.inl hPP)
  have hMPg : ∀ PP ∈ Rl.toRealDat.Pg, ((T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    intro PP hPP
    have h1 : ((T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ T.Q.l.Mb := natM_mem_Mb T
    have h2 : T.Q.l.Mb ≤ PP.asIdeal := by
      rw [hhalf.1]
      exact Ideal.prod_le_inf.trans (Finset.inf_le hPP)
    exact h2 h1
  refine ⟨Rl.toRealDat.Pg.image Formalism.L2.DIV.conjPl, cA D e, _, isIdemSum_conjPl he, ?_, ?_, ?_, ?_, hth⟩
  · intro PP hPP
    obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.1 hPP
    show Formalism.L2.DIV.starOHom ((T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ P0.asIdeal
    rw [map_natCast]
    exact hMPg P0 hP0
  · intro t ht
    by_cases hc : IsHalf (cA D e) t ∧ IsIntM (frMapAdj (Vc D j) (Wc D j) (Rl.toRealDat.βV j) (Rl.toRealDat.βW j) t)
    · exact ⟨_root_.GlobalTheory.HalfAdjLattice.mem_latO_of_adj_int D _ _ _ _ _ _ hsV hsW hfV hfW _ e he hP2 t hc.1 hc.2, hc.1⟩
    · exact absurd (if_neg hc) ht
  · intro u hu hue t
    have hN' := _root_.GlobalTheory.HalfAdjInt.frMapAdj_int_of_half D _ _ _ _ _ _ hsV hsW hfV hfW _ e he hP2 u hu hue
    have hfr : frMapAdj (Vc D j) (Wc D j) (Rl.toRealDat.βV j) (Rl.toRealDat.βW j) (t + T.Q.l.M • u) =
        frMapAdj (Vc D j) (Wc D j) (Rl.toRealDat.βV j) (Rl.toRealDat.βW j) t +
          T.Q.l.M • frMapAdj (Vc D j) (Wc D j) (Rl.toRealDat.βV j) (Rl.toRealDat.βW j) u := by
      rw [frMapAdj_add', frMapAdj_nsmul']
    have hKu : IsHalf (cA D e) (T.Q.l.M • u) := fun a b => by
      rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hue a b]
    have hhalf' : IsHalf (cA D e) (t + T.Q.l.M • u) ↔ IsHalf (cA D e) t := by
      constructor
      · intro h a b
        have := h a b
        rw [Matrix.add_apply, mul_add, hKu a b] at this
        exact add_right_cancel this
      · intro h a b
        rw [Matrix.add_apply, mul_add, h a b, hKu a b]
    show (if _ then _ else _) = (if _ then _ else _)
    rw [hfr]
    by_cases hc : IsHalf (cA D e) t ∧ IsIntM (frMapAdj (Vc D j) (Wc D j) (Rl.toRealDat.βV j) (Rl.toRealDat.βW j) t)
    · rw [if_pos ⟨hhalf'.2 hc.1, (isIntM_add_nsmul_iff hN' _).2 hc.2⟩, if_pos hc]
      exact omegaK_congr _ fun PP hPP => redM_add_nsmul PP hc.2 hN' _ (hMPg PP hPP)
    · rw [if_neg, if_neg hc]
      intro h'
      exact hc ⟨hhalf'.1 h'.1, (isIntM_add_nsmul_iff hN' _).1 h'.2⟩
  · intro t
    show (if _ then _ else _) ∈ _
    split_ifs
    · exact omegaK_mem _ _ _
    · exact Subfield.zero_mem _

end GlobalTheory.RefDatumLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarisableOfIsLocS
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowSphSmall

open GlobalTheory.CuspRep.ParLaws GlobalTheory.LocLanglands

end GlobalTheory.RowSphSmall

section FormSec
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open Formalism.IndefR.principalLevelFrame Formalism.IndefR.Mult

namespace GlobalTheory.RowSphSmall


set_option maxHeartbeats 1000000 in
theorem exists_form_rowRepR (hH : GlobalTheory.Published.HarishChandraFinite) (hC : GlobalTheory.Published.CuspRapidDecay) (D : D7) (G : Type) [Group G]
    [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D)
    (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (hP : Pins R F cG) (σ : D.what₂.FT) :
    ∃ B : (principalLevelFrame.rowRepR R.θ (Y.eFT σ)).S → (principalLevelFrame.rowRepR R.θ (Y.eFT σ)).S → ℂ,
      (∀ x y z (c : ℂ), B x (y + c • z) = B x y + c * B x z) ∧ (∀ x y, B x y = starRingEnd ℂ (B y x)) ∧
      (∀ x, x ≠ 0 → 0 < (B x x).re) ∧
      ∀ h (x y x' y' : (principalLevelFrame.rowRepR R.θ (Y.eFT σ)).S), (x' : GAf D.host.E D.R.r → ℂ) = NG.rt D.host.E D.R.r h x →
        (y' : GAf D.host.E D.R.r → ℂ) = NG.rt D.host.E D.R.r h y → B x' y' = B x y := by
  obtain ⟨b, hb⟩ := principalLevelFrame.rowRepR_occ R.θ (Y.eFT σ)
  set π := principalLevelFrame.rowRepR R.θ (Y.eFT σ) with hπ
  have hne : isotIn (D := D) (actM Y.PY (R.MY 0)) (Minf R.θ Y.PY (R.MY 0)) (FinTyp.conjT π) ≠ ⊥ := by
    intro h
    apply hb
    unfold isotE isotL
    rw [h, inf_bot_eq]
  have hM := hP.char.base.models
  have hθ : IsInfFam R.θ := hM.inf
  have hSig : (Yc D 0).SigOK := D.sp.Y_sig 0
  have hcc := _root_.GlobalTheory.CongConjugate.congConj D.host.E D.R.r
  have hfd : ∀ j, j < D.R.m → (R.νY A3.A.μ0 j).IsHaarMeasure ∧
      IsFundamentalDomain (GQ (Yc D j)) (R.fdY A3.A.μ0 j) (R.νY A3.A.μ0 j) := by
    intro j hj
    by_cases h : j + 1 < D.R.m
    · have := hM.νY A3.A.μ0 j h
      exact ⟨this.1.1, this.2⟩
    · obtain rfl : j = D.R.m - 1 := by omega
      have := hM.νY' A3.A.μ0
      exact ⟨this.1.1, this.2⟩
  obtain ⟨hHaar, hFD⟩ := hfd 0 Y.hm
  have hSA : SchurAll D := fun V _ S θ M J χ μ 𝓕 =>
    (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ μ 𝓕).2
  obtain ⟨hlin, hherm, hpos⟩ := GlobalTheory.FinTypesRows.minf_sesq (M := R.MY 0) (θ := R.θ) (R.νY A3.A.μ0 0)
    (R.fdY A3.A.μ0 0) Y.PY hSA hSig hθ hHaar hFD
  obtain ⟨B', h1, h2, h3, h4⟩ := GlobalTheory.finTyp_invariant_form_of_isotIn D D.R.r _ (actM Y.PY (R.MY 0))
    (Minf R.θ Y.PY (R.MY 0)) (ipM (R.MY 0) (R.νY A3.A.μ0 0) (R.fdY A3.A.μ0 0)) hlin hherm hpos
    (fun h x hx => GlobalTheory.FinTypesRows.minf_stable Y.PY hcc h hx)
    (fun h x hx y hy => _root_.GlobalTheory.SchurPairingInvariant.ipM_actM D (Yc D 0) _ R.θ (R.MY 0) D.R.r Y.PY (R.νY A3.A.μ0 0) (R.fdY A3.A.μ0 0) hSA hSig hθ
      hHaar hFD h x hx y hy) (FinTyp.conjT π) hne
  exact GlobalTheory.RowLocalRows.form_of_conjT π B' h1 h2 h3 h4

end GlobalTheory.RowSphSmall
end FormSec

namespace GlobalTheory.RowSphSmall

theorem isUnitarisable_of_isLocS {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (π : NG.FinTyp L n)
    (B : π.S → π.S → ℂ) (hlin : ∀ x y z (c : ℂ), B x (y + c • z) = B x y + c * B x z)
    (hherm : ∀ x y, B x y = starRingEnd ℂ (B y x)) (hpos : ∀ x, x ≠ 0 → 0 < (B x x).re)
    (hinv : ∀ h (x y x' y' : π.S), (x' : Formalism.AUTREP.GAf L n → ℂ) = NG.rt L n h x →
      (y' : Formalism.AUTREP.GAf L n → ℂ) = NG.rt L n h y → B x' y' = B x y)
    (s : ReciprocityTheory.Aut.SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))) (hτ : IsLocS π.S s τ) :
    GlobalTheory.SmGL.IsUnitarisable τ.ρ := by
  obtain ⟨i, T, -, -, hTi, hTm, hTe⟩ := hτ
  obtain ⟨e, he1, he2⟩ := GlobalTheory.SplitEmb.exists_hom_trivOutside_loc L n s
  let t : τ.V → π.S := fun v => ⟨T v, hTm v⟩
  have tadd : ∀ v w, t (v + w) = t v + t w := fun v w => Subtype.ext (map_add T v w)
  have tsmul : ∀ (c : ℂ) v, t (c • v) = c • t v := fun c v => Subtype.ext (map_smul T c v)
  have hlin2 : ∀ y z : π.S, ∀ c : ℂ, B (y + c • z) = fun x => B y x + starRingEnd ℂ c * B z x := by
    intro y z c
    funext x
    rw [hherm, hlin, map_add (f := _), map_mul, ← hherm, ← hherm]
  have hadd1 : ∀ y z x : π.S, B (y + z) x = B y x + B z x := by
    intro y z x
    have := congrFun (hlin2 y z 1) x
    simpa using this
  have hsm1 : ∀ (c : ℂ) (z x : π.S), B (c • z) x = starRingEnd ℂ c * B z x := by
    intro c z x
    have h1 := congrFun (hlin2 0 z c) x
    have h0 : B 0 x = 0 := by
      have := hadd1 0 0 x
      simp only [add_zero] at this
      linear_combination -this
    simpa [h0] using h1
  have hadd2 : ∀ x y z : π.S, B x (y + z) = B x y + B x z := by
    intro x y z
    simpa using hlin x y z 1
  have hsm2 : ∀ (c : ℂ) (x z : π.S), B x (c • z) = c * B x z := by
    intro c x z
    have h1 := hlin x 0 z c
    have h0 : B x 0 = 0 := by
      have := hadd2 x 0 0
      simp only [add_zero] at this
      linear_combination -this
    simpa [h0] using h1
  let Bf : τ.V →ₗ[ℂ] τ.V →ₛₗ[starRingEnd ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v w => B (t w) (t v))
      (fun v v' w => by rw [tadd, hadd2])
      (fun c v w => by rw [tsmul, hsm2]; rfl)
      (fun v w w' => by rw [tadd, hadd1])
      (fun c v w => by rw [tsmul, hsm1]; rfl)
  refine ⟨Bf, ?_, ?_, ?_⟩
  · intro v w
    show B (t v) (t w) = starRingEnd ℂ (B (t w) (t v))
    exact hherm _ _
  · intro v hv
    show 0 < (B (t v) (t v)).re
    apply hpos
    intro h0
    apply hv
    apply hTi
    rw [map_zero]
    exact congrArg Subtype.val h0
  · intro g v w
    show B (t (τ.ρ g w)) (t (τ.ρ g v)) = B (t w) (t v)
    let g' := Matrix.GeneralLinearGroup.map i.symm.toRingHom g
    have hg : Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n (e g')) = g := by
      rw [he2]
      ext a b
      simp [g']
    have hx : ∀ a, T (τ.ρ g a) = NG.rt L n (e g') (T a) := by
      intro a
      rw [← hg]
      exact hTe (e g') (he1 g') a
    exact hinv (e g') (t w) (t v) (t (τ.ρ g w)) (t (τ.ρ g v)) (hx w) (hx v)

end GlobalTheory.RowSphSmall
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeConjugateHalfIffDual
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

noncomputable section

namespace GlobalTheory.ConjHalfDual

open Formalism.IndefR.Fin.LevelGroupLemmas.Lat

variable {D : D7}

theorem cA_cA_self (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a x =>
    show a ⊗ₜ[D.host.F] D.sp.cm.sig (D.sp.cm.sig x) = a ⊗ₜ[D.host.F] x
    congr 1
    exact star_star x
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem infPart_cA_of_zero {z : AE D} (h : infPart D z = 0) : infPart D (cA D z) = 0 := by
  have key : ∀ w : AE D, infPart D (cA D w) =
      Algebra.TensorProduct.map (AlgHom.id D.host.F (Ainf D.host.F)) D.sp.cm.sig (infPart D w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rfl
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]
  rw [key, h, map_zero]

theorem symplO_add_right' (S T : HSp D) (x y y' : WO S T) :
    symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  unfold symplO; rw [hO_add_right, mul_add, map_add (f := _)]

theorem hO_eq_zero_of {f g : AE D} (hfg : cA D g * f = 0) {S T : HSp D} {x y' : WO S T} (hx : IsHalf f x) :
    hO S T x (g • y') = 0 := by
  unfold hO
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
    Finset.sum_eq_zero fun d _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, ← hx d a, map_mul]
  calc incA D (S.gram⁻¹ a b) * (cA D g * cA D (y' c b)) * incA D (T.gram c d) * (f * x d a)
      = (cA D g * f) * (incA D (S.gram⁻¹ a b) * cA D (y' c b) * incA D (T.gram c d) * x d a) := by ring
    _ = 0 := by rw [hfg, zero_mul]

theorem symplO_eq_zero_of {f g : AE D} (hfg : cA D g * f = 0) {S T : HSp D} {x y' : WO S T} (hx : IsHalf f x) :
    symplO S T x (g • y') = 0 := by
  unfold symplO; rw [hO_eq_zero_of hfg hx, mul_zero, map_zero]

theorem mem_latO_iff_of_conjHalf : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ e : AE D, e * e = e → e * cA D e = 0 → infPart D e = 0 → finPart D e ∈ intAE D → ∀ u : WO S T, IsHalf (cA D e) u → (u ∈ latO S T ΛS ΛT (fun _ => True) ↔ ∀ l ∈ latO S T ΛS ΛT (fun _ => True), IsHalf e l → ψ (symplO S T l u) = 1) := by
  intro D ψ S T ΛS ΛT hψ hS hT e he hec hinf hfin u hu
  have key := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT).1
  have hcc : cA D (cA D e) = e := cA_cA_self e
  have hcidem : cA D e * cA D e = cA D e := by rw [← map_mul, he]
  have hcinf : infPart D (cA D e) = 0 := infPart_cA_of_zero hinf
  constructor
  · intro hmem l hl _
    have hl0 : l.map (infPart D) = 0 := by
      ext i j; exact latAll_infPart hl i j
    exact (key l hl0).1 hl u hmem
  · intro h
    have hu0 : u.map (infPart D) = 0 := by
      ext i j
      rw [Matrix.map_apply, Matrix.zero_apply, ← hu i j, map_mul, hcinf, zero_mul]
    refine (key u hu0).2 fun u' hu' => ?_
    have hdec : u' = e • u' + (cA D e • u' + (1 - e - cA D e) • u') := by
      ext i j; simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
    have m1 : e • u' ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) :=
      smul_mem_latAll hfin hu'
    have hh1 : IsHalf e (e • u') := fun i j => by
      rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, he]
    have t1 : ψ (symplO S T u (e • u')) = 1 := by
      rw [GlobalTheory.SplitScalar.symplO_skew, AddChar.map_neg_eq_inv, h _ m1 hh1, inv_one]
    have t2 : symplO S T u (cA D e • u') = 0 :=
      symplO_eq_zero_of (f := cA D e) (by rw [hcc]; exact hec) hu
    have t3 : symplO S T u ((1 - e - cA D e) • u') = 0 :=
      symplO_eq_zero_of (f := cA D e) (by
        rw [map_sub, map_sub, map_one, hcc]
        linear_combination (-1 : AE D) * hcidem - hec) hu
    rw [hdec, symplO_add_right', symplO_add_right', t2, t3, add_zero, add_zero, t1]

end GlobalTheory.ConjHalfDual

end
end

