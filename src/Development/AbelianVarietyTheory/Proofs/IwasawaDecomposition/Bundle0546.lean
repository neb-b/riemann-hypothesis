module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqZeroOfForallExistsLsumETwoPi
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0191
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0533
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0258
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0524
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0174
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0366
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelGroupWithCharacterAtTypePlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsClosedEmbeddingOfAffine

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NomePowerSeriesDvdOfSumBounded
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

namespace GlobalTheory

theorem powerSeries_dvd_of_sum_bounded : ∀ (G H : PowerSeries ℂ) (T C : ℝ) (g h : ℂ → ℂ), H ≠ 0 →
    (∀ w : ℂ, T < w.im → SumsAt G w (g w) ∧ SumsAt H w (h w) ∧ (h w ≠ 0 → ‖g w‖ ≤ C * ‖h w‖)) →
    H ∣ G := by
  intro G H T C g h hH hyp
  set m : ℕ := H.order.toNat with hm
  set T₀ : ℝ := max T 0 + 1 with hT₀
  have hT₀T : T < T₀ := by have := le_max_left T 0; linarith
  set w₁ : ℂ := Complex.I * (T₀ : ℂ) with hw₁
  have hw₁im : w₁.im = T₀ := by simp [hw₁]
  set q₁ := eTwoPi w₁ with hq₁
  set ρ₁ : ℝ := GlobalTheory.Conv.cuspRadius T₀ with hρ₁
  have hρ₁pos : 0 < ρ₁ := GlobalTheory.Conv.cuspRadius_pos T₀
  have hq₁n : ‖q₁‖ = ρ₁ := by rw [hq₁, GlobalTheory.Conv.norm_eTwoPi, hw₁im]
  have hH₁ : HasSum (fun j : ℕ => PowerSeries.coeff j H * q₁ ^ j) (h w₁) :=
    (hyp w₁ (by rw [hw₁im]; exact hT₀T)).2.1
  have hS₁ : Summable (fun j : ℕ => ‖PowerSeries.coeff j H * q₁ ^ j‖) := hH₁.summable.norm
  set S₁ := ∑' j : ℕ, ‖PowerSeries.coeff j H * q₁ ^ j‖ with hS₁def

  have hbnd : ∀ w : ℂ, T₀ ≤ w.im → ‖h w‖ ≤ (‖eTwoPi w‖ / ρ₁) ^ m * S₁ := by
    intro w hw
    have hHw : HasSum (fun j : ℕ => PowerSeries.coeff j H * eTwoPi w ^ j) (h w) :=
      (hyp w (lt_of_lt_of_le hT₀T hw)).2.1
    set ρ := ‖eTwoPi w‖ with hρ
    have hρ0 : 0 ≤ ρ := norm_nonneg _
    have hρle : ρ ≤ ρ₁ := by
      rw [hρ, GlobalTheory.Conv.norm_eTwoPi]; exact GlobalTheory.Conv.cuspRadius_strictAnti.antitone hw
    have hterm : ∀ j : ℕ, ‖PowerSeries.coeff j H * eTwoPi w ^ j‖ ≤
        (ρ / ρ₁) ^ m * ‖PowerSeries.coeff j H * q₁ ^ j‖ := by
      intro j
      by_cases hj : j < m
      · rw [PowerSeries.coeff_of_lt_order_toNat j hj]; simp
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hj)
        rw [norm_mul, norm_mul, norm_pow, norm_pow, ← hρ, hq₁n, div_pow, pow_add, pow_add]
        have hc := norm_nonneg (PowerSeries.coeff (m + d) H)
        have hpow : ρ ^ d ≤ ρ₁ ^ d := pow_le_pow_left₀ hρ0 hρle d
        have hρ₁m : 0 < ρ₁ ^ m := pow_pos hρ₁pos m
        calc ‖PowerSeries.coeff (m + d) H‖ * (ρ ^ m * ρ ^ d)
            ≤ ‖PowerSeries.coeff (m + d) H‖ * (ρ ^ m * ρ₁ ^ d) := by gcongr
          _ = ρ ^ m / ρ₁ ^ m * (‖PowerSeries.coeff (m + d) H‖ * (ρ₁ ^ m * ρ₁ ^ d)) := by
            field_simp
    rw [← hHw.tsum_eq]
    exact tsum_of_norm_bounded (hS₁.hasSum.mul_left _) hterm

  have hconv : (H : ℂ⸨X⸩) ∈ GlobalTheory.Conv.convLaurent :=
    GlobalTheory.Conv.halfRing_le_convLaurent T (GlobalTheory.Conv.coe_mem_halfRing.2 fun w hw => ⟨_, (hyp w hw).2.1⟩)
  have hH' : (H : ℂ⸨X⸩) ≠ 0 := fun h0 => hH ((map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective).1 h0)
  obtain ⟨T₂, hT₂⟩ := GlobalTheory.Conv.exists_lsum_eTwoPi_ne_zero hconv hH'
  have hne : ∀ w : ℂ, T < w.im → T₂ < w.im → h w ≠ 0 := by
    intro w hw hw2
    have := hT₂ w hw2
    rwa [GlobalTheory.Conv.lsum_coe, GlobalTheory.Conv.sum, (hyp w hw).2.1.tsum_eq] at this

  set F : ℂ⸨X⸩ := HahnSeries.single (-(m : ℤ)) (1 : ℂ) * (G : ℂ⸨X⸩) with hF
  have hFb := GlobalTheory.laurent_coeff_neg_eq_zero_of_bounded F (max T₀ T₂) (max C 0 * (S₁ / ρ₁ ^ m))
    (by
      intro w hw
      have hw0 : T₀ < w.im := lt_of_le_of_lt (le_max_left _ _) hw
      have hw2 : T₂ < w.im := lt_of_le_of_lt (le_max_right _ _) hw
      have hwT : T < w.im := hT₀T.trans hw0
      have hq0 : eTwoPi w ≠ 0 := GlobalTheory.Conv.eTwoPi_ne_zero w
      refine ⟨eTwoPi w ^ (-(m : ℤ)) * g w,
        GlobalTheory.Conv.hasSum_single_mul hq0 (-(m : ℤ)) (GlobalTheory.Conv.sumsAt_iff.1 (hyp w hwT).1), ?_⟩
      have hρpos : 0 < ‖eTwoPi w‖ := norm_pos_iff.2 hq0
      have hg := (hyp w hwT).2.2 (hne w hwT hw2)
      have hb := hbnd w hw0.le
      have hS₁0 : 0 ≤ S₁ := tsum_nonneg fun _ => norm_nonneg _
      have hρm : 0 < ‖eTwoPi w‖ ^ m := pow_pos hρpos m
      have hρ₁m : 0 < ρ₁ ^ m := pow_pos hρ₁pos m
      rw [norm_mul, norm_zpow, zpow_neg, zpow_natCast]
      have h1 : ‖g w‖ ≤ max C 0 * ((‖eTwoPi w‖ / ρ₁) ^ m * S₁) :=
        hg.trans ((mul_le_mul_of_nonneg_right (le_max_left C 0) (norm_nonneg _)).trans
          (mul_le_mul_of_nonneg_left hb (le_max_right C 0)))
      rw [div_pow] at h1
      rw [inv_mul_le_iff₀ hρm]
      calc ‖g w‖ ≤ max C 0 * (‖eTwoPi w‖ ^ m / ρ₁ ^ m * S₁) := h1
        _ = ‖eTwoPi w‖ ^ m * (max C 0 * (S₁ / ρ₁ ^ m)) := by ring)
  have hcoeff : ∀ i < m, PowerSeries.coeff i G = 0 := by
    intro i hi
    have := hFb ((i : ℤ) + -(m : ℤ)) (by omega)
    rw [hF, HahnSeries.coeff_single_mul_add, one_mul] at this
    simpa using this
  have hXG : (PowerSeries.X : PowerSeries ℂ) ^ m ∣ G := PowerSeries.X_pow_dvd_iff.2 hcoeff
  obtain ⟨u, hu⟩ := PowerSeries.isUnit_divided_by_X_pow_order hH
  have hHe : H = PowerSeries.X ^ m * (u : PowerSeries ℂ) := by
    rw [hu, hm, PowerSeries.X_pow_order_mul_divXPowOrder]
  have hHX : H ∣ (PowerSeries.X : PowerSeries ℂ) ^ m :=
    ⟨(u⁻¹ : (PowerSeries ℂ)ˣ), by rw [hHe, mul_assoc, Units.mul_inv, mul_one]⟩
  exact hHX.trans hXG

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NumbersEqConcreteNumbersAtBaseLevel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.ReadIndexNumerics

theorem ijIdx_eq (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup)
    (eMt : ∀ (i : Fin D.R.m) (t : T), (Fin (lDim D A P0 ψ0 i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1))
    (S0 : IndefData (A.side P0 ψ0 Zs)) (Xd : DivX D)
    (jW : ∀ i : Fin D.R.m, (Fin (S0.dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1))
    (i : Fin D.R.m) (t : T) (eW : (Fin (S0.dW i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Xd.MjH ((i : ℕ) + 1)).V)
    (hP : Formalism.DivisionValues.IsOrthProj (lH D A P0 ψ0 i t) (lZ0 D A P0 ψ0 Zs i t) (lPrj D A P0 ψ0 Zs i t))
    (hθ : ∀ x, D.what₂.thetaP (tup t) ((i : ℕ) + 1) (D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t x)) =
      jW i ((S0.θ i t).mulVec ((lPrj D A P0 ψ0 Zs i t).mulVec x)))
    (hj : ∀ x, Xd.jM ((i : ℕ) + 1) (eW x) = jW i x)
    (hl : (Xd.MjH ((i : ℕ) + 1)).L = (S0.M i).map ((eW : (Fin (S0.dW i) → D.what₂.LL) →ₗ[D.what₂.LL] (Xd.MjH ((i : ℕ) + 1)).V).restrictScalars (𝓞 D.what₂.LL)))
    (hT : Idx.TjL D (tup t) ((i : ℕ) + 1) = (Formalism.DivisionValues.matLat (lZ0 D A P0 ψ0 Zs i t) ((A.side P0 ψ0 Zs).Tl i t)).map
      ((eMt i t).toLinearMap.restrictScalars (𝓞 D.what₂.LL)))
    (w : D.what₂.places.Pl) :
    Idx.IjIdx Xd (tup t) ((i : ℕ) + 1) w = S0.Iw i t (D.plEq w) := by
  have hPE : ∀ z, lPrj D A P0 ψ0 Zs i t *ᵥ (lZ0 D A P0 ψ0 Zs i t *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec]; erw [hP.1]; exact Matrix.one_mulVec z
  have hth : Idx.thTj Xd (tup t) ((i : ℕ) + 1) = (Formalism.DivisionValues.matLat (S0.θ i t) ((A.side P0 ψ0 Zs).Tl i t)).map
      ((eW : (Fin (S0.dW i) → D.what₂.LL) →ₗ[D.what₂.LL] (Xd.MjH ((i : ℕ) + 1)).V).restrictScalars (𝓞 D.what₂.LL)) := by
    ext y
    have key : y ∈ Idx.thTj Xd (tup t) ((i : ℕ) + 1) ↔ ∃ x ∈ Idx.TjL D (tup t) ((i : ℕ) + 1),
        Xd.jM ((i : ℕ) + 1) y = D.what₂.thetaP (tup t) ((i : ℕ) + 1) (D.what₂.jMt (tup t) ((i : ℕ) + 1) x) := Iff.rfl
    rw [key, hT]
    constructor
    · rintro ⟨x, hx, hxy⟩
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 hx
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hu
      refine Submodule.mem_map.2 ⟨S0.θ i t *ᵥ z, Submodule.mem_map.2 ⟨z, hz, rfl⟩, ?_⟩
      apply Idx.jM_inj Xd
      have h1 := hθ (lZ0 D A P0 ψ0 Zs i t *ᵥ z)
      erw [hPE] at h1
      refine (hj _).trans ?_
      rw [hxy]
      exact h1.symm
    · intro hy
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 hy
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hu
      refine ⟨eMt i t (lZ0 D A P0 ψ0 Zs i t *ᵥ z), Submodule.mem_map.2 ⟨lZ0 D A P0 ψ0 Zs i t *ᵥ z,
        Submodule.mem_map.2 ⟨z, hz, rfl⟩, rfl⟩, ?_⟩
      have h1 := hθ (lZ0 D A P0 ψ0 Zs i t *ᵥ z)
      erw [hPE] at h1
      refine (hj _).trans ?_
      exact h1.symm
  unfold Idx.IjIdx
  rw [hth, hl, SkeletonIndexLemmas.lidx_map _ _ eW.injective]
  rfl

theorem numTie_of_read : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (Xd : DivX D) (JM : MjHIds D A3.A Xd (A3.indefDown (s0Of R F))), Pins R F cG → Holds R F → MjHTie D A3.A Xd (A3.indefDown (s0Of R F)) Z.jW JM → IdxDefs D Xd → NumTie D A3.A (A3.indefDown (s0Of R F)) Y.tup := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z Xd JM hP hH hM hI
  obtain ⟨-, hθ⟩ := GlobalTheory.T.liftCuspFormSpace_thetaMap_eq_data D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
  have hZ0 := GlobalTheory.T.zeroSubspace_spanned_by_dataZeroSubspace_lifts D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
  have hok := hH.ok.ok2
  have hB : ∀ i t, BlockHyp (A3.A.fam.L i t) (A3.A.fam.lvlA F.P0 F.ψ0) A3.A.fam.v0 1 :=
    fun i t => ⟨hok.conj, hok.irr, hok.lifts i t⟩
  have hOP : ∀ i t, Formalism.DivisionValues.IsOrthProj (lH D A3.A F.P0 F.ψ0 i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t)
      (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t) :=
    fun i t => BlockDat.lf_l_proj (Z := (A3.fam3.toSub2 (zsOf R F)).Zl i t) (hB i t)
  have hT := fun i t => _root_.GlobalTheory.Mem.LiftForms.TjL_eq_map_matLat D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) Y.tup Y.eMt i t (hOP i t) (Y.formsL i t) (Y.latL i t)
    (hZ0 i t) (fun x => by
      have e : ∀ v, lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ v) = v :=
        fun v => by rw [Matrix.mulVec_mulVec]; erw [(hOP i t).1]; exact Matrix.one_mulVec v
      have h2 := hθ i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ x))
      erw [e] at h2
      exact (hθ i t x).trans h2.symm)
  refine ⟨fun i t w => ?_, fun i t w => ?_, fun i w => ?_⟩
  · rw [hI.Ij_def _ _ _ (by omega) (by omega)]
    exact ijIdx_eq D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) Y.tup Y.eMt (A3.indefDown (s0Of R F)) Xd Z.jW i t (JM.eW i)
      (hOP i t) (hθ i t) (hM.j_eq i) (hM.hlat i).lat (hT i t) w
  · rw [hI.jw_def _ _ _ (by omega) (by omega)]
    refine _root_.GlobalTheory.Mem.JwLift.jwIdx_eq_jw D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) Y.tup Y.eMt i t (hOP i t) (Y.formsL i t)
      (BlockDat.lf_lE_form (hB i t)) ?_ (hT i t) w
    classical
    let K := D.what₂.LL
    let B := A3.A.fam.L i t
    let S := B.S
    let ℓ := A3.A.fam.lvlA F.P0 F.ψ0
    let Zl := (A3.fam3.toSub2 (zsOf R F)).Zl i t
    have hGood := (hB i t).ok.good
    change Submodule.span K (↑(B.Tl ℓ Zl) : Set (Fin (B.dZ ℓ Zl) → K)) = ⊤
    apply top_unique
    intro z _
    let x := (B.fE ℓ Zl).mulVec z
    have hdenom (c : S.Cl) : ∃ d : 𝓞 K, d ≠ 0 ∧ d • S.I x c ∈ S.Nab c := by
      obtain ⟨g, hg⟩ := (hGood.nab_lat c).fg
      obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 K)) g
        (fun y => S.pair y (S.I x c))
      refine ⟨d, nonZeroDivisors.coe_ne_zero d, ?_⟩
      have hdual : (d : 𝓞 K) • S.I x c ∈ Formalism.HermitianLatticesTheory.dual S.pair (S.Nab c) := by
        rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
        intro y hy
        refine Submodule.span_induction
          (p := fun y _ => S.pair y ((d : 𝓞 K) • S.I x c) ∈ (1 : Submodule (𝓞 K) K))
          ?_ ?_ ?_ ?_ (hg.symm ▸ hy)
        · intro y hy
          rw [LinearMap.map_smul_of_tower, Submodule.mem_one]
          exact hd y hy
        · simp
        · intro y y' _ _ hy hy'
          rw [map_add, LinearMap.add_apply]
          exact add_mem hy hy'
        · intro a y _ hy
          obtain ⟨a', ha'⟩ := Formalism.DivisionValues.exponent_index_lattice.hstar (K := K) a
          rw [← algebraMap_smul K a y, LinearMap.map_smulₛₗ, LinearMap.smul_apply]
          change star (algebraMap (𝓞 K) K a) • _ ∈ (1 : Submodule (𝓞 K) K)
          rw [← ha', algebraMap_smul]
          exact Submodule.smul_mem _ _ hy
      exact hGood.del_le c (by simpa using hGood.dual_le c _ hdual)
    choose d hd0 hd using hdenom
    let a := ∏ c, d c
    have ha : a ≠ 0 := Finset.prod_ne_zero_iff.mpr fun c _ => hd0 c
    have hax : a • x ∈ S.nabLat := by
      apply (Formalism.DivisionValues.ValuationLatticeField.mem_valLatF S.I S.Nab _).2
      intro c
      rw [LinearMap.map_smul_of_tower, Pi.smul_apply]
      obtain ⟨b, hb⟩ := Finset.dvd_prod_of_mem d (Finset.mem_univ c)
      rw [show a = d c * b from hb, mul_comm, mul_smul]
      exact (S.Nab c).smul_mem b (hd c)
    have haz : a • z ∈ B.Tl ℓ Zl := by
      apply BlockDat.lf_cutZ_le (hB i t)
      change (B.fE ℓ Zl).mulVec (a • z) ∈ S.nabLat
      rwa [Matrix.mulVec_smul]
    have haK : (a : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr ha
    have hmem : (a : K) • z ∈ Submodule.span K (↑(B.Tl ℓ Zl) : Set _) := by
      rw [algebraMap_smul K a z]
      exact Submodule.subset_span haz
    exact inv_smul_smul₀ haK z ▸ (Submodule.span K _).smul_mem (a : K)⁻¹ hmem
  · rw [Z.etaJ]
    by_cases h : D.plEq w ∈ R.twPl
    · rw [if_pos h, if_pos (show D.plEq w ∈ (A3.indefDown (s0Of R F)).Tw from h)]; rfl
    · rw [if_neg h, if_neg (show D.plEq w ∉ (A3.indefDown (s0Of R F)).Tw from h)]

end GlobalTheory.Mem.ReadIndexNumerics

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodQuadFormExtendsHolomorphicPunctPolydisc
section
open GlobalTheory.ShFam.Hor

namespace GlobalTheory

theorem periodVec_im_dot {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (v : Fin g → ℤ) :
    (dotProduct (fun i => (v i : ℂ)) (M.mulVec (fun i => (v i : ℂ)))).im
      = dotProduct (fun i => (v i : ℝ)) ((M.map Complex.im).mulVec (fun i => (v i : ℝ))) := by
  simp [dotProduct, Matrix.mulVec, Complex.im_sum, Finset.mul_sum, Complex.mul_im]

theorem periodVec_norm_exp_le {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (hM : (M.map Complex.im).PosDef)
    (v : Fin g → ℤ) :
    ‖Complex.exp (2 * Real.pi * Complex.I *
      dotProduct (fun i => (v i : ℂ)) (M.mulVec (fun i => (v i : ℂ))))‖ ≤ 1 := by
  have h1 : 0 ≤ dotProduct (fun i => (v i : ℝ)) ((M.map Complex.im).mulVec (fun i => (v i : ℝ))) := by
    have := hM.posSemidef.dotProduct_mulVec_nonneg (fun i => (v i : ℝ))
    simpa using this
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  have : (2 * Real.pi * Complex.I *
      dotProduct (fun i => (v i : ℂ)) (M.mulVec (fun i => (v i : ℂ)))).re
      = -(2 * Real.pi) * (dotProduct (fun i => (v i : ℂ)) (M.mulVec (fun i => (v i : ℂ)))).im := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this, periodVec_im_dot]
  have := Real.pi_pos
  nlinarith

end GlobalTheory

namespace GlobalTheory

theorem periodVec_extends : ∀ (n a g : ℕ) (ha : a ≤ n) (ρ₁ : ℝ) (τ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℤ), 0 < ρ₁ → ρ₁ ≤ 1 → (∀ i j, DifferentiableOn ℂ (fun s => τ s i j) {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁}) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).IsSymm ∧ ((τ s).map Complex.im).PosDef) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → ∀ k : Fin a, τ (s + Pi.single (Fin.castLE ha k) (2 * Real.pi * Complex.I)) = τ s + (B k).map (Int.cast : ℤ → ℂ)) → (∀ k, 0 ≤ dotProduct v ((B k).mulVec v)) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F (Metric.ball 0 ρ₁) ∧ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → dotProduct (fun i => (v i : ℂ)) ((τ s).mulVec (fun i => (v i : ℂ))) - ∑ k, s (Fin.castLE ha k) * ((dotProduct v ((B k).mulVec v) : ℤ) : ℂ) / (2 * Real.pi * Complex.I) = F (logExp a s) := by
  intro n a g ha ρ₁ τ B v hρ0 hρ1 hdiff hpos hmono hm
  let vC : Fin g → ℂ := fun i => (v i : ℂ)
  let m : Fin a → ℤ := fun k => dotProduct v ((B k).mulVec v)
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hcd : ∀ x : ℂ, 2 * Real.pi * Complex.I * (x / (2 * Real.pi * Complex.I)) = x := fun x => by
    field_simp
  let h : (Fin n → ℂ) → ℂ := fun s => dotProduct vC ((τ s).mulVec vC) -
    ∑ k, s (Fin.castLE ha k) * ((m k : ℤ) : ℂ) / (2 * Real.pi * Complex.I)
  have hdh : DifferentiableOn ℂ h
      {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁} := by
    apply DifferentiableOn.sub
    · simp only [dotProduct, Matrix.mulVec]
      apply DifferentiableOn.fun_sum; intro i _
      apply DifferentiableOn.mul (differentiableOn_const _)
      apply DifferentiableOn.fun_sum; intro j _
      exact (hdiff i j).mul (differentiableOn_const _)
    · apply DifferentiableOn.fun_sum; intro k _
      simp only [div_eq_mul_inv]
      apply DifferentiableOn.mul_const
      apply DifferentiableOn.mul_const
      exact differentiableOn_pi.mp differentiableOn_id (Fin.castLE ha k)
  have hQ : ∀ k : Fin a, dotProduct vC (((B k).map (Int.cast : ℤ → ℂ)).mulVec vC) = ((m k : ℤ) : ℂ) := by
    intro k
    simp [vC, m, dotProduct, Matrix.mulVec, Int.cast_sum, Int.cast_mul]
  have hinv : ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ →
      ∀ k : Fin n, (k : ℕ) < a → h (s + Pi.single k (2 * Real.pi * Complex.I)) = h s := by
    intro s hs hb k hk
    obtain ⟨k', rfl⟩ : ∃ k' : Fin a, Fin.castLE ha k' = k := ⟨⟨k, hk⟩, Fin.ext rfl⟩
    have hτ := hmono s hs hb k'
    simp only [h]
    rw [hτ, Matrix.add_mulVec, dotProduct_add, hQ k']
    have hsum : ∑ j, (s + Pi.single (Fin.castLE ha k') (2 * Real.pi * Complex.I) : Fin n → ℂ) (Fin.castLE ha j)
        * ((m j : ℤ) : ℂ) / (2 * Real.pi * Complex.I)
        = ∑ j, s (Fin.castLE ha j) * ((m j : ℤ) : ℂ) / (2 * Real.pi * Complex.I) + ((m k' : ℤ) : ℂ) := by
      simp only [Pi.add_apply, add_mul, add_div, Finset.sum_add_distrib]
      congr 1
      simp only [Pi.single_apply, (Fin.castLE_injective ha).eq_iff, ite_mul, zero_mul, ite_div, zero_div,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      field_simp
    rw [hsum]; ring
  obtain ⟨H, hHd, hHe⟩ := _root_.GlobalTheory.LogDescent.descent n a ρ₁ h hρ0 hρ1 hdh hinv
  let m' : Fin n → ℕ := fun j => if hj : (j : ℕ) < a then (m ⟨j, hj⟩).toNat else 0
  have hm0 : ∀ k, (((m k).toNat : ℕ) : ℂ) = ((m k : ℤ) : ℂ) := fun k => by
    have := Int.toNat_of_nonneg (hm k)
    exact_mod_cast this
  have hbound : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ₁, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) →
      ‖Complex.exp (2 * Real.pi * Complex.I * H z)‖ * ∏ k, ‖z k‖ ^ m' k ≤ 1 := by
    intro z hz hz0
    let s : Fin n → ℂ := fun j => if (j : ℕ) < a then Complex.log (z j) else z j
    have hzj : ∀ j, ‖z j‖ < ρ₁ := fun j =>
      lt_of_le_of_lt (norm_le_pi_norm z j) (by simpa using hz)
    have hls : logExp a s = z := by
      funext j; simp only [logExp, s]; split_ifs with hj
      · exact Complex.exp_log (hz0 j hj)
      · rfl
    have hsD : s ∈ logDom n a := by
      simp only [logDom, Set.mem_setOf_eq]
      intro j; simp only [s]; split_ifs with hj
      · rw [Complex.log_re]
        exact Real.log_neg (norm_pos_iff.2 (hz0 j hj)) (lt_of_lt_of_le (hzj j) hρ1)
      · exact lt_of_lt_of_le (hzj j) hρ1
    have hb' : logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ := by rw [hls]; exact hz
    have hHz : h s = H z := by rw [hHe s hsD hb', hls]
    have hprod : ∏ j, (z j) ^ m' j = ∏ k : Fin a, (z (Fin.castLE ha k)) ^ (m k).toNat := by
      symm
      apply Finset.prod_of_injOn (Fin.castLE ha)
      · intro x _ y _ hxy; exact Fin.castLE_injective ha hxy
      · intro x _; simp
      · intro j _ hj
        have : ¬ (j : ℕ) < a := by
          intro hlt; apply hj; exact ⟨⟨j, hlt⟩, by simp, Fin.ext rfl⟩
        simp [m', this]
      · intro k _; simp [m', Fin.coe_castLE, k.isLt]
    have hexp : ∀ k : Fin a, (z (Fin.castLE ha k)) ^ (m k).toNat
        = Complex.exp (s (Fin.castLE ha k) * ((m k : ℤ) : ℂ)) := by
      intro k
      have hk : ((Fin.castLE ha k : Fin n) : ℕ) < a := by simp
      rw [mul_comm, ← hm0 k, Complex.exp_nat_mul]
      congr 1
      simp only [s, if_pos hk]; exact (Complex.exp_log (hz0 _ hk)).symm
    calc ‖Complex.exp (2 * Real.pi * Complex.I * H z)‖ * ∏ k, ‖z k‖ ^ m' k
        = ‖Complex.exp (2 * Real.pi * Complex.I * h s) * ∏ k, z k ^ m' k‖ := by
          rw [norm_mul, norm_prod, hHz]; simp only [norm_pow]
      _ = ‖Complex.exp (2 * Real.pi * Complex.I * dotProduct vC ((τ s).mulVec vC))‖ := by
          rw [hprod, Finset.prod_congr rfl (fun k _ => hexp k), ← Complex.exp_sum, ← Complex.exp_add]
          congr 2
          simp only [h]
          rw [mul_sub, Finset.mul_sum, Finset.sum_congr rfl (fun k _ => hcd _)]
          ring
      _ ≤ 1 := periodVec_norm_exp_le _ (hpos s hsD hb').2 v
  obtain ⟨F, hFd, hFe⟩ := _root_.GlobalTheory.HyperplaneExt.extension_across_coordinate_hyperplanes n a ρ₁ H m' hρ0 hHd hbound
  refine ⟨F, hFd, fun s hs hb => ?_⟩
  rw [hFe _ hb (fun k hk => by simp [logExp, hk, Complex.exp_ne_zero])]
  exact hHe s hs hb

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlacesOverRealSubfieldSplit
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LevForms

theorem typeSpF_finiteDimensional : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (K : Type) [Field K] {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (ρ : Representation K (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* Kˣ),
    (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) →
    FiniteDimensional K ↥(NX.TypeSpF L n K ρ J χ) := by
  intro L _ _ _ n K _ W _ _ _ ρ J χ hJ
  classical
  obtain ⟨N, hN, hNJ⟩ := hJ
  obtain ⟨T, hT⟩ := _root_.GlobalTheory.DefiniteClassFinite.exists_finset_double_cosets_Umax L n
  obtain ⟨Jc, hJc⟩ := GlobalTheory.AlgFormsFin.exists_cover L n hN
  let Φ : ↥(NX.TypeSpF L n K ρ J χ) →ₗ[K] (↥(T ×ˢ Jc) → W) :=
    { toFun := fun f p => (f : GAf L n → W) (p.1.1 * p.1.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective Φ ((injective_iff_map_eq_zero Φ).2 fun f hf => ?_)
  refine Subtype.ext (funext fun g => ?_)
  obtain ⟨γ, t, u, ht, hu, rfl⟩ := hT g
  obtain ⟨j, hj, κ, hκ, rfl⟩ := hJc u hu
  have h0 : (f : GAf L n → W) (t * j) = 0 :=
    congrFun hf ⟨(t, j), Finset.mem_product.2 ⟨ht, hj⟩⟩
  obtain ⟨hκJ, hκ1⟩ := hNJ κ hκ
  have e : (γ : GAf L n) * t * (j * κ) = ((γ : GAf L n) * (t * j)) * κ := by simp only [mul_assoc]
  show (f : GAf L n → W) _ = 0
  rw [e, f.2.2 ⟨κ, hκJ⟩, hκ1, f.2.1 γ, h0, map_zero, Units.val_one, one_smul]

end GlobalTheory.LevForms
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreModelChartFrame
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.Points

namespace GlobalTheory.FlagEmb.QuotLine

section Pull

variable {X Z : Scheme.{0}} (f : Z ⟶ X) (L : LB X)

variable {f L} {W V : Z.Opens} {i j k : L.ι}

end Pull

section Three

variable {X X₀ X₁ Z : Scheme.{0}} (f : Z ⟶ X) (f₀ : Z ⟶ X₀) (f₁ : Z ⟶ X₁) (L : LB X) (L₀ : LB X₀) (L₁ : LB X₁)
  {I : Type} (a : I → L.ι) (b : I → L₀.ι) (c : I → L₁.ι)

variable {f f₀ f₁ L L₀ L₁ a b c}

end Three

section Val

variable {Z : Scheme.{0}} {U W : Z.Opens} (hU : IsAffineOpen U)

theorem valR_chart {C : Type} [CommRing C] (φ : Γ(Z, U) →+* C) (s : Γ(Z, U)) : valR (spMap φ ≫ hU.fromSpec) U s = φ s := by
  have h := le_preimage_specMap_fromSpec hU (CommRingCat.ofHom φ)
  exact (valR_eq _ U h s).trans (congrArg (fun t => t.hom s) (valMap_specMap_fromSpec hU (CommRingCat.ofHom φ) h))

end Val

end GlobalTheory.FlagEmb.QuotLine
end
end

