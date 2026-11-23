module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0584
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0587
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DependenceFixed
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0422
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0588
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0438
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridParameterRegularCardEqRankFormula
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0598
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0597
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosureUnitary
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0333
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0596
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CommutantDepthLatticePermutesCosetVectors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.CosShift

variable {D : D7} {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
  {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {𝔪 : Ideal (𝓞 D.host.E)}

theorem isHalf_sub' {e : AE D} {x y : Mx D m n} (hx : IsHalf e x) (hy : IsHalf e y) : IsHalf e (x - y) := fun i j => by
  simp only [Matrix.sub_apply, mul_sub, hx i j, hy i j]

theorem isHalf_add' {e : AE D} {x y : Mx D m n} (hx : IsHalf e x) (hy : IsHalf e y) : IsHalf e (x + y) := fun i j => by
  simp only [Matrix.add_apply, mul_add, hx i j, hy i j]

theorem map_smul_sub (e : AE D) (a b : homLat Λ Λ') : e • ((a - b : homLat Λ Λ') : Matrix (Fin m) (Fin n) D.host.E).map (incA D) =
    e • (a : Matrix (Fin m) (Fin n) D.host.E).map (incA D) - e • (b : Matrix (Fin m) (Fin n) D.host.E).map (incA D) := by
  rw [Submodule.coe_sub, Matrix.map_sub _ (incA D).map_sub, smul_sub]

theorem map_smul_add (e : AE D) (a b : homLat Λ Λ') : e • ((a + b : homLat Λ Λ') : Matrix (Fin m) (Fin n) D.host.E).map (incA D) =
    e • (a : Matrix (Fin m) (Fin n) D.host.E).map (incA D) + e • (b : Matrix (Fin m) (Fin n) D.host.E).map (incA D) := by
  ext i j
  simp only [Submodule.coe_add, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    (incA D).map_add, smul_add]

theorem mk_sub' (a b : homLat Λ Λ') : Cos.mk 𝔪 (a - b) = (Submodule.Quotient.mk a - Submodule.Quotient.mk b :
    homLat Λ Λ' ⧸ (𝔪 • ⊤ : Submodule (𝓞 D.host.E) (homLat Λ Λ'))) :=
  Submodule.Quotient.mk_sub _

theorem mk_add' (a b : homLat Λ Λ') : Cos.mk 𝔪 (a + b) = (Submodule.Quotient.mk a + Submodule.Quotient.mk b :
    homLat Λ Λ' ⧸ (𝔪 • ⊤ : Submodule (𝓞 D.host.E) (homLat Λ Λ'))) :=
  Submodule.Quotient.mk_add _

theorem mem_cosSet_add {e : AE D} {z : Mx D m n} (hz : IsHalf e z) (x₀ x₁ : homLat Λ Λ')
    (hx₁ : z - e • (x₁ : Matrix (Fin m) (Fin n) D.host.E).map (incA D) ∈ hatMx (𝔪 • homLat Λ Λ')) (t : Mx D m n) :
    t + z ∈ cosSet e (Cos.mk 𝔪 x₀) ↔ t ∈ cosSet e (Cos.mk 𝔪 (x₀ - x₁)) := by
  constructor
  · rintro ⟨ht, y, hy, hm⟩
    refine ⟨?_, y - x₁, ?_, ?_⟩
    · have := isHalf_sub' ht hz
      rwa [add_sub_cancel_right] at this
    · rw [mk_sub', mk_sub']
      exact congrArg (· - _) hy
    · rw [map_smul_sub]
      have h2 := sub_mem hm hx₁
      have e2 : t + z - e • (y : Matrix (Fin m) (Fin n) D.host.E).map (incA D) -
          (z - e • (x₁ : Matrix (Fin m) (Fin n) D.host.E).map (incA D)) =
          t - (e • (y : Matrix (Fin m) (Fin n) D.host.E).map (incA D) - e • (x₁ : Matrix (Fin m) (Fin n) D.host.E).map (incA D)) := by
        abel
      rwa [e2] at h2
  · rintro ⟨ht, y, hy, hm⟩
    refine ⟨isHalf_add' ht hz, y + x₁, ?_, ?_⟩
    · rw [mk_add']
      rw [mk_sub'] at hy
      have hy' : (Submodule.Quotient.mk y : homLat Λ Λ' ⧸ (𝔪 • ⊤ : Submodule (𝓞 D.host.E) (homLat Λ Λ'))) =
          Submodule.Quotient.mk x₀ - Submodule.Quotient.mk x₁ := hy
      rw [hy', sub_add_cancel]
      rfl
    · rw [map_smul_add]
      have h2 := add_mem hm hx₁
      have e2 : t - e • (y : Matrix (Fin m) (Fin n) D.host.E).map (incA D) +
          (z - e • (x₁ : Matrix (Fin m) (Fin n) D.host.E).map (incA D)) =
          t + z - (e • (y : Matrix (Fin m) (Fin n) D.host.E).map (incA D) + e • (x₁ : Matrix (Fin m) (Fin n) D.host.E).map (incA D)) := by
        abel
      rwa [e2] at h2

theorem cosInd_add {e : AE D} {z : Mx D m n} (hz : IsHalf e z) (x₁ : homLat Λ Λ')
    (hx₁ : z - e • (x₁ : Matrix (Fin m) (Fin n) D.host.E).map (incA D) ∈ hatMx (𝔪 • homLat Λ Λ')) (κ : Cos Λ Λ' 𝔪) :
    ∃ κ' : Cos Λ Λ' 𝔪, (fun t => cosInd e κ (t + z)) = cosInd e κ' := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, Cos.mk 𝔪 x₀ = κ := Submodule.Quotient.mk_surjective _ κ
  refine ⟨Cos.mk 𝔪 (x₀ - x₁), funext fun t => ?_⟩
  have key := mem_cosSet_add hz x₀ x₁ hx₁ t
  rw [hx₀] at key
  show Set.indicator (cosSet e κ) 1 (t + z) = Set.indicator (cosSet e (Cos.mk 𝔪 (x₀ - x₁))) 1 t
  classical
  simp only [Set.indicator_apply, key, Pi.one_apply]

end GlobalTheory.CosShift

private theorem GlobalTheory.CosShift.selfDual_full {D : D7} : ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    IsSelfDualC V Λ → Submodule.IsFullLattice D.host.E Λ := by
  intro V Λ hΛ
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
  refine ⟨?_⟩
  obtain ⟨s, hs⟩ := hΛ.1.fg
  apply eq_top_iff.mpr
  intro y _
  let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
    ∑ i, ∑ j, star (x i) * V.gram i j * y j
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
  have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
    exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
  let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
    carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
    zero_mem' := by refine ⟨0, ?_⟩; simp [f]
    add_mem' := by
      rintro x z ⟨b, hb⟩ ⟨c, hc⟩
      refine ⟨b + c, ?_⟩
      change (b : D.host.E) + c = _
      rw [hb, hc]
      simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
    smul_mem' := by
      rintro c x ⟨b, hb⟩
      refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
      simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change star (c : D.host.E) * _ = _
      ring }
  have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
    intro x hx
    obtain ⟨b, hb⟩ := ha x hx
    exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
  have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
    apply (hΛ.2 _).2
    intro x hx
    have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
    obtain ⟨b, hb⟩ := hxP
    refine ⟨b, ?_⟩
    rw [hb]
    dsimp only [f, Pi.smul_apply]
    simp only [smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
    Submodule.subset_span hy
  have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
    (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
  change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
    ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
  rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
  exact this


theorem GlobalTheory.CosShift.mem_hatMx_of_latO {D : D7} (hq : OffQ D) {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}
    (hL : L.Is μ₀) (G : GridData L sc) {i : ℕ} (hi : i < D.R.m) {e : AE D} (he : IsIdemSum e G.pl.W0)
    {z : WO (G.pS (.chi i 0)) (G.pT (.chi i 0))} (hz : IsHalf e z)
    (hm : z ∈ latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _) fun _ => True) :
    z ∈ hatMx (homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0))) := by
  have hSD := GlobalTheory.CosetRow.selfDual_chi hL G i hi
  obtain ⟨βS, hβS⟩ := Formalism.L2.DIV.frame_exists_alt D.host.F D.host.E _ (G.latS (.chi i 0)) (GlobalTheory.CosShift.selfDual_full _ _ hSD.1)
  obtain ⟨βT, hβT⟩ := Formalism.L2.DIV.frame_exists_alt D.host.F D.host.E _ (G.latT (.chi i 0)) (GlobalTheory.CosShift.selfDual_full _ _ hSD.2)
  exact GlobalTheory.RowLatChi.mem_hatMx_of_int hβS hβT he hz fun w hw a b =>
    GlobalTheory.RowLatChi.int_of_mem_latO hSD.1 hβS hβT w (GlobalTheory.DepthFix.aa_int hL hq G hw) hm a b


set_option maxHeartbeats 1000000 in
open GlobalTheory.CosShift in
theorem GlobalTheory.CosShift.epart : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → (∀ κ, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) e (latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd e κ) (W.cosVec i κ)) → ∀ w ∈ Ann W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (depLat G (.chi i 0)), w.map (infPart D) = 0 → ∀ κ, ∃ κ', heisO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (e • w) (W.cosVec i κ) = W.cosVec i κ' := by
  intro D hq T L μ₀ hL sc G W M hM i hi e he hθ w hw hwinf κ
  obtain ⟨⟨T₀, hT₀⟩, -⟩ := hθ κ
  have hv : ∀ κ, W.cosVec i κ = T₀ (cosInd e κ) := fun κ => (hθ κ).2 T₀ hT₀
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hSD := GlobalTheory.CosetRow.selfDual_chi hL G i hi
  have hz : IsHalf e (e • w) := fun a b => by
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hee]
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0)),
      e • w - e • (x₁ : Matrix _ _ D.host.E).map (incA D) ∈
        hatMx (G.modul • homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0))) :=
    (by
      apply _root_.GlobalTheory.CosRatApprox.exists_rat_approx (G.pl.modul_ne_bot sc)
      · with_unfolding_all exact selfDual_full (G.pS (.chi i 0)) (G.latS (.chi i 0)) hSD.1
      · with_unfolding_all exact selfDual_full (G.pT (.chi i 0)) (G.latT (.chi i 0)) hSD.2
      · exact he
      · exact hz
      · exact mem_hatMx_of_latO hq hL G hi he hz (_root_.GlobalTheory.AnnPart.part_mem_latO hL G W.ψ W.ψ_std i hi e he w hw hwinf))
  obtain ⟨κ', hκ'⟩ := cosInd_add hz x₁ hx₁ κ
  refine ⟨κ', ?_⟩
  rw [hv κ, hv κ', ← hκ']
  exact (hT₀.trans (cosInd e κ) (GlobalTheory.GridWeil.isSBHalf_cosInd hSD.1 hSD.2 (G.pl.modul_ne_bot sc) hee
    (GlobalTheory.PlaceDatum.infPart_idemSum he) κ) (e • w) hz).symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalAlongRightGridArrows
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RightArrowCusp

theorem vert_par : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}, GlobalTheory.Hk3.Core R F → ∀ G : GlobalTheory.Grid.GridPre R, G.Is → ∀ i j : ℕ, i ≤ D.R.m → j ≤ D.R.m → (G.V i j).S = GlobalTheory.Grid.parV D i j := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R F _ G hG i j hi hj
  cases i with
  | zero =>
    rw [GlobalTheory.Grid.parV_zero D hj]
    rcases j with _ | j
    · rfl
    · show (if j + 1 < D.R.m then GlobalTheory.Grid.nodeY R (j + 1) else GlobalTheory.Grid.nodeX R).S = _
      split_ifs with h
      · simp [Nat.min_eq_left hj]
      · have : j + 1 = D.R.m := by omega
        rw [this]
  | succ i => exact (hG.spaces.vert i j hi hj).par

theorem meas_haar_fund : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}, GlobalTheory.Hk3.Core R F → ∀ G : GlobalTheory.Grid.GridPre R, G.Is → ∀ (t : T) (i j : ℕ), i ≤ D.R.m → j ≤ D.R.m → (G.meas t i j).ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ (G.V i j).V) (G.meas t i j).fd (G.meas t i j).ν := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R F hC G hG t i j hi hj
  have aux : ∀ {N : GlobalTheory.Grid.Node D} (m : N.MeasDat) (df : Prop) K, m.Is df K →
      m.ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ N.V) m.fd m.ν := by
    intro N m df K h
    by_cases hd : df
    · exact ⟨(h.1 hd).1.1, (h.1 hd).2⟩
    · exact ⟨(h.2 hd).1.1, (h.2 hd).2⟩
  have cst : ∀ {S S' : GlobalTheory.Grid.Node D} (e : S = S') (m : S.MeasDat),
      m.ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ S.V) m.fd m.ν →
      (GlobalTheory.Grid.Node.MeasDat.cast e m).ν.IsHaarMeasure ∧
        IsFundamentalDomain (GQ S'.V) (GlobalTheory.Grid.Node.MeasDat.cast e m).fd (GlobalTheory.Grid.Node.MeasDat.cast e m).ν := by
    intro S S' e m h
    subst e
    exact h
  rcases i with _ | i
  · rcases j with _ | j
    · exact aux _ _ _ (hG.meas.col 0 (Nat.zero_le _))
    · show (GlobalTheory.Grid.meas0 R t j).ν.IsHaarMeasure ∧
        IsFundamentalDomain (GQ (GlobalTheory.Grid.row0 R (j + 1)).V) (GlobalTheory.Grid.meas0 R t j).fd (GlobalTheory.Grid.meas0 R t j).ν
      unfold GlobalTheory.Grid.meas0
      split_ifs with h
      · apply cst
        by_cases h2 : j + 1 + 1 < D.R.m
        · have := hC.models.νY t (j + 1) h2
          exact ⟨this.1.1, this.2⟩
        · have := hC.models.νY' t
          have e : D.R.m - 1 = j + 1 := by omega
          rw [e] at this
          exact ⟨this.1.1, this.2⟩
      · apply cst
        have := hC.models.νX t
        exact ⟨this.1.1, this.2⟩
  · rcases j with _ | j
    · exact aux _ _ _ (hG.meas.col (i + 1) hi)
    · exact aux _ _ _ (hG.meas.vert i j hi hj)

theorem thetaKO_eq_kerA : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts} {G' : GridData R.toLevCh sc} (W : G'.Weil) (i j : ℕ) (Ls : Submodule (𝓞 D.host.E) (G'.V (.grid i j)).V) (hs1 : Submodule.IsLattice D.host.E Ls) (hs2 : Formalism.HermitianLatticesTheory.IsUnimodular (G'.V (.grid i j)).hT Ls) (Lt : Submodule (𝓞 D.host.E) (G'.V (.grid (i + 1) j)).V) (ht1 : Submodule.IsLattice D.host.E Lt) (ht2 : Formalism.HermitianLatticesTheory.IsUnimodular (G'.V (.grid (i + 1) j)).hT Lt) (ω : GlobalTheory.Grid.WRep (GlobalTheory.VolRatioCompare.reLat (G'.V (.grid (i + 1) j)) Lt ht1 ht2) (GlobalTheory.VolRatioCompare.reLat (G'.V (.grid i j)) Ls hs1 hs2)), HEq (ω.toSgn true) (W.om (.chi i j)) → ∀ (Φ : Sch G' (.right i j)) (g : GA D (G'.V (.grid i j))) (h : GA D (G'.V (.grid (i + 1) j))), thetaKO ω h g Φ = W.kerA (.right i j) Φ g h := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc G' W i j Ls hs1 hs2 Lt ht1 ht2 ω hω Φ g h
  have e : ω.toSgn true = W.om (.chi i j) := eq_of_heq hω
  show (ω (h, g)) Φ 0 = (W.om (.chi i j) (negGA _ h, g)) Φ 0
  rw [← e]
  rfl

theorem isThetaFunO_neg_reLat : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S U : HSp D) (L : Submodule (𝓞 D.host.E) S.V) (h1 : Submodule.IsLattice D.host.E L) (h2 : Formalism.HermitianLatticesTheory.IsUnimodular S.hT L) (L' : Submodule (𝓞 D.host.E) U.V) (h1' : Submodule.IsLattice D.host.E L') (h2' : Formalism.HermitianLatticesTheory.IsUnimodular U.hT L') (Φ : WO (negSp S) U → ℂ), IsThetaFunO ψ (negSp S) U Φ → IsThetaFunO ψ (GlobalTheory.Grid.neg (GlobalTheory.VolRatioCompare.reLat S L h1 h2)) (GlobalTheory.VolRatioCompare.reLat U L' h1' h2') Φ := by
  intro D ψ S U L h1 h2 L' h1' h2' Φ h
  exact ⟨h.1, h.2, h.3, h.4⟩

theorem isCuspListed_smul : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (θ : InfFam D) (X : Node) (c : ℂ) (F : Fn G X), IsCuspListed θ X F → IsCuspListed θ X (c • F) := by
  intro D T L sc G θ X c F ⟨h1, h2, h3⟩
  refine ⟨Formalism.IndefR.Mult.isAutFunSm_smul _ _ h1 c, Formalism.IndefR.Mult.isCuspFun_smul _ h2 c, ?_⟩
  rcases X with ⟨i, j⟩ | i | j
  · intro τ
    have e : (fun g => star ((c • F) g)) = star c • fun g => star (F g) := by
      funext g; simp [Pi.smul_apply, smul_eq_mul, star_mul', mul_comm]
    show IsTypeAt _ _ _ _ fun g => star ((c • F) g)
    rw [e]
    exact GlobalTheory.Mem.Th.isTypeAt_smul _ (h3 τ)
  · intro τ; exact GlobalTheory.Mem.Th.isTypeAt_smul c (h3 τ)
  · intro τ; exact GlobalTheory.Mem.Th.isTypeAt_smul c (h3 τ)

theorem kerA_mul_left_invariant : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts} {G' : GridData R.toLevCh sc} (W : G'.Weil) (i j : ℕ), i < D.R.m → j ≤ D.R.m → ∀ Φ : Sch G' (.right i j), IsThetaFunO W.ψ (G'.pS (.chi i j)) (G'.pT (.chi i j)) Φ → ∀ F : Fn G' (.grid i j), IsCuspListed W.θ (.grid i j) F → ∀ h, ∀ γ ∈ GQ (G'.V (.grid i j)), ∀ g, W.kerA (.right i j) Φ (γ * g) h * F (γ * g) = W.kerA (.right i j) Φ g h * F g := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc G' W i j hi hj Φ hΦ F hF h γ hγ g
  have hω := W.om_is (.chi i j) (by first | exact ⟨hi, hj⟩ | exact ⟨hj, hi⟩ | simpa using ⟨hi, hj⟩)
  show thetaKO (W.om (.chi i j)) (negGA _ h) (γ * g) Φ * F (γ * g) = thetaKO (W.om (.chi i j)) (negGA _ h) g Φ * F g
  rw [GlobalTheory.UpArrowConv.thetaKO_left_snd hω hΦ _ γ hγ g, hF.1.left γ hγ g]

theorem isAutFunSm_reLat_iff : ∀ {D : D7} (θ : InfFam D) (V : HSp D) (L : Submodule (𝓞 D.host.E) V.V) (h1 : Submodule.IsLattice D.host.E L) (h2 : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L) (φ : GA D V → ℂ), IsAutFunSm θ (GlobalTheory.VolRatioCompare.reLat V L h1 h2) φ ↔ IsAutFunSm θ V φ := by
  intro D θ V L h1 h2 φ
  exact ⟨fun h => ⟨⟨h.left, h.level, h.cont⟩, h.smooth, h.zfin, h.growth⟩,
    fun h => ⟨⟨h.left, h.level, h.cont⟩, h.smooth, h.zfin, h.growth⟩⟩

theorem isCuspOfType_iff_isCuspListed : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts}, sc.cGap = 1 → ∀ {G' : GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ (i j : ℕ), i ≤ D.R.m → j ≤ D.R.m → ∀ (L : Submodule (𝓞 D.host.E) (G'.V (.grid i j)).V) (h1 : Submodule.IsLattice D.host.E L) (h2 : Formalism.HermitianLatticesTheory.IsUnimodular (G'.V (.grid i j)).hT L) (Mo : Formalism.IndefR.Mult.DSModel (GlobalTheory.VolRatioCompare.reLat (G'.V (.grid i j)) L h1 h2) (GlobalTheory.Grid.parV D i j)) (Λ : Submodule (𝓞 D.host.E) (Fin (GlobalTheory.VolRatioCompare.reLat (G'.V (.grid i j)) L h1 h2).rank → D.host.E)) (β : GL (Fin (GlobalTheory.VolRatioCompare.reLat (G'.V (.grid i j)) L h1 h2).rank) (Lev.EAf D)) (φ : Fn G' (.grid i j)), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ ⟨GlobalTheory.VolRatioCompare.reLat (G'.V (.grid i j)) L h1 h2, GlobalTheory.Grid.parV D i j, Mo, Λ, β⟩ φ ↔ IsCuspListed W.θ (.grid i j) φ := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc hsc G' W hW i j hi hj L h1 h2 Mo Λ β φ
  rw [hW.θ]
  refine and_congr (isAutFunSm_reLat_iff R.θ _ L h1 h2 φ) (and_congr Iff.rfl ?_)
  show (∀ τ, IsTypeAt R.θ (GlobalTheory.VolRatioCompare.reLat (G'.V (.grid i j)) L h1 h2) τ (GlobalTheory.Grid.parV D i j τ) φ) ↔
    ∀ τ, IsTypeAt R.θ (G'.V (.grid i j)) τ (Node.par D sc.cGap (.grid i j) τ) fun g => star (φ g)
  refine forall_congr' fun τ => ?_
  rw [hsc]
  have hp : GlobalTheory.Grid.parV D i j τ = Formalism.IndefR.Mult.dualPar (GlobalTheory.ChiGrid.parV D 1 i j τ) := by
    unfold GlobalTheory.Grid.parV GlobalTheory.ChiGrid.parV
    rw [GlobalTheory.GridParDCount.grid_eq_num D τ]
  rw [hp]
  exact _root_.GlobalTheory.TypeConj.isTypeAt_dualPar_iff R.θ (G'.V (.grid i j)) τ _ φ


open GlobalTheory.GridJoin in
theorem lift_right_of_smooth {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts} (hsc : sc.cGap = 1) {G' : GridData R.toLevCh sc} (W : G'.Weil)
    (hW : W.Over R) (ρ : RealMatch W) (hρ : RealMatch.Over R ρ) (M : Vol G') (t : T) (hM : M.Is t) (i j : ℕ) (hi : i < D.R.m)
    (hj : j ≤ D.R.m) (Ns Nt : GlobalTheory.Grid.Node D) (hs : SameSp (G'.V (.grid i j)) Ns.V) (ht : SameSp (G'.V (.grid (i + 1) j)) Nt.V)
    (hSs : Ns.S = GlobalTheory.Grid.parV D i j) (hSt : Nt.S = GlobalTheory.Grid.parV D (i + 1) j) (m : Ns.MeasDat) (hm1 : m.ν.IsHaarMeasure)
    (hm2 : IsFundamentalDomain (GQ Ns.V) m.fd m.ν) (ω : GlobalTheory.Grid.WRep Nt.V Ns.V) (hω : HEq (ω.toSgn true) (W.om (.chi i j)))
    (H : ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg Nt.V) Ns.V Φ →
      GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsSmooth R.θ (A := Ns) (B := Nt) m fun h g => thetaKO ω h g Φ) :
    ∀ e, IsIdemSum e (locPl G' t) → ∀ φ f, IsLocVec W (.chi i j) e (vacOf ρ (.right i j)) φ f →
      ∀ (Q : PolF D (G'.pT (.chi i j)).rank (G'.pS (.chi i j)).rank) (F : Fn G' (.grid i j)), IsCuspListed W.θ (.grid i j) F →
        LiftConv W M (.right i j) (W.fock (.chi i j) f Q) F ∧
          IsCuspListed W.θ (.grid (i + 1) j) (liftA W M (.right i j) (W.fock (.chi i j) f Q) F) := by
  obtain ⟨Vs, Ss, Ms, Λs, βs⟩ := Ns
  obtain ⟨Vt, St, Mt, Λt, βt⟩ := Nt
  obtain ⟨Ls, hs1, hs2, rfl⟩ := hs
  obtain ⟨Lt, ht1, ht2, rfl⟩ := ht
  dsimp only at hSs hSt
  subst hSs hSt
  intro e he φ f hf Q F hF
  have hΦ0 := _root_.GlobalTheory.RowFock.isThetaFunO_fock_right hW ρ hρ t i j hi hj e he φ f hf Q
  have hΦ : IsThetaFunO R.ψ (GlobalTheory.Grid.neg (GlobalTheory.VolRatioCompare.reLat (G'.V (.grid (i + 1) j)) Lt ht1 ht2))
      (GlobalTheory.VolRatioCompare.reLat (G'.V (.grid i j)) Ls hs1 hs2) (W.fock (.chi i j) f Q) :=
    hW.ψ ▸ isThetaFunO_neg_reLat W.ψ _ _ Lt ht1 ht2 Ls hs1 hs2 _ hΦ0
  have hK := thetaKO_eq_kerA W i j Ls hs1 hs2 Lt ht1 ht2 ω hω (W.fock (.chi i j) f Q)
  have hFs := (isCuspOfType_iff_isCuspListed hsc W hW i j hi.le hj Ls hs1 hs2 Ms Λs βs F).2 hF
  obtain ⟨hI, hT⟩ := H _ hΦ F hFs
  have hMX := (hM.vtx (.grid i j) ⟨hi.le, hj⟩).haar_fund
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.HaarFundDom.setIntegral_eq_const_mul (M.ν (.grid i j)) m.ν (M.fd (.grid i j)) m.fd hMX.1 hm1 hMX.2 hm2
  have key := fun h => hc (fun g => W.kerA (.right i j) (W.fock (.chi i j) f Q) g h * F g) (kerA_mul_left_invariant W i j hi hj _ hΦ0 F hF h)
  have e2 : ∀ h, (fun g => thetaKO ω h g (W.fock (.chi i j) f Q) * F g) =
      fun g => W.kerA (.right i j) (W.fock (.chi i j) f Q) g h * F g := fun h => funext fun g => by rw [hK g h]
  refine ⟨fun h => (key h).1.2 (e2 h ▸ hI h), ?_⟩
  have e : liftA W M (.right i j) (W.fock (.chi i j) f Q) F =
      c • fun h => ∫ g in m.fd, thetaKO ω h g (W.fock (.chi i j) f Q) * F g ∂m.ν := by
    funext h
    rw [liftA_apply, (key h).2]
    exact congrArg (c * ·) (congrArg (fun φ : GA D (G'.V (.grid i j)) → ℂ => ∫ g in m.fd, φ g ∂m.ν) (e2 h).symm)
  rw [e]
  exact isCuspListed_smul _ _ c _ ((isCuspOfType_iff_isCuspListed hsc W hW (i + 1) j hi hj Lt ht1 ht2 Mt Λt βt _).1 hT)

end GlobalTheory.RightArrowCusp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DenseUnitaryRealPointsAlgebraicEntries
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.RealAlgDense

theorem dense_alg : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ V : HSp D, Dense {g : GinfC V | ∀ τ a b, IsAlgebraic ℚ (compAt θ τ (Formalism.L2.Theta.mt V g.1) a b)} := by
  intro D θ hθ V
  obtain ⟨e, he⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  have hfin : ∀ h : GA D V, h ∈ GinfC V ↔ (e h).2 = 1 := fun h =>
    ⟨fun H => Subtype.ext (Units.ext ((he h).1.trans (congrArg Units.val (MonoidHom.mem_ker.1 H)))),
      fun H => MonoidHom.mem_ker.2 (Units.ext ((he h).1.symm.trans (by rw [H]; rfl)))⟩
  have hne : ∃ z, D.sp.cm.sig z ≠ z := by
    by_contra h
    push Not at h
    have hs : Function.Surjective (algebraMap D.host.F D.host.E) := fun z => (D.sp.cm.fixed z).1 (h z)
    have h1 : Module.finrank D.host.F D.host.E = 1 :=
      Algebra.finrank_eq_one_iff_bijective_algebraMap.2 ⟨(algebraMap D.host.F D.host.E).injective, hs⟩
    have h2 := D.sp.cm.deg2
    omega
  have hd := GlobalTheory.RealApprox.dense_inf D.host.F D.host.E D.sp.cm.sig (fun x => star_star x) hne V.gram
    (GlobalTheory.AutFunCounterexample.gram_herm V) (GlobalTheory.AutFunCounterexample.gram_det_ne V)
  let Φ : HA (Ainf D.host.F) D.sp.cm.sig V.gram → GinfC V := fun x =>
    ⟨e.symm (x, 1), (hfin _).2 (by rw [e.apply_symm_apply])⟩
  have hΦc : Continuous Φ :=
    Continuous.subtype_mk (e.symm.continuous.comp (continuous_id.prodMk continuous_const)) _
  have hΦs : Function.Surjective Φ := by
    intro g
    refine ⟨(e g.1).1, Subtype.ext ?_⟩
    change e.symm ((e g.1).1, 1) = g.1
    rw [← (hfin g.1).1 g.2]
    exact e.symm_apply_apply g.1
  refine Dense.mono ?_ (hΦs.denseRange.dense_image hΦc hd)
  rintro _ ⟨x, ⟨γ₀, hγ₀, hx⟩, rfl⟩ τ a b
  have hm := (he (e.symm (x, 1))).2
  rw [e.apply_symm_apply] at hm
  have key : compAt θ τ (Formalism.L2.Theta.mt V (Φ x).1) a b = tauE D τ (γ₀.1 a b) := by
    change infMat D.sp.cm.sig V.gram (θ τ) (e.symm (x, 1)) a b = _
    unfold infMat
    rw [← hm, ← hx]
    exact (hθ τ).1 _
  rw [key]
  have h0 : IsAlgebraic ℚ (γ₀.1 a b) := Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (γ₀.1 a b)
  first
    | exact h0.algHom (tauE D τ).toRatAlgHom
    | exact IsAlgebraic.map (tauE D τ).toRatAlgHom h0
    | exact (isAlgebraic_algHom_iff (tauE D τ).toRatAlgHom (tauE D τ).injective).2 h0

end GlobalTheory.RealAlgDense
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowDataHaveDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.FirstRowDepth

theorem datumDep : GlobalTheory.SepRows.DatumDep := by
  intro D hq T L μ0 hL sc G W M hM ρ Φ i
  obtain ⟨-, ⟨hth, hlat⟩, -⟩ := _root_.GlobalTheory.CosDep.cosVec_dep D hq T L μ0 hL sc G W M hM i.1 i.2 (Φ i)
  have hthP : ∀ P, IsThetaFunO W.ψ (G.pS (.chi i.1 0)) (G.pT (.chi i.1 0))
      (W.fock (.chi i.1 0) (W.cosVec i (Φ i)) P) := fun P =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ hth P
  refine ⟨hthP (ρ i), fun u hu => ?_, fun e he u hu hh => ?_⟩
  · exact GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite W.ψ W.θ _ _ W.θ_is _ _ _ _ _ hthP (2 • u)
      (GlobalTheory.VacGood.infPart_latO (AddSubgroup.nsmul_mem _ hu 2).1) (hlat.1 u hu) (ρ i)
  · exact GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite W.ψ W.θ _ _ W.θ_is _ _ _ _ _ hthP u
      (GlobalTheory.VacGood.infPart_latO hu.1) (hlat.2 e he u hu hh) (ρ i)

end GlobalTheory.FirstRowDepth

end
end

