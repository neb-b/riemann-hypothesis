module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1491
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0414
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0382
public import ReciprocityTheory.DualLattices.Bundle0004
public import ReciprocityTheory.DualLattices.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1500
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerChainMatricesWithNormBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0741
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0745
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0779
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0737
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1508
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastMapNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0818
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0861
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastSideLogBound
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1498
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1482

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeUNuInvEqOneOfCong
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.SqNum.NuCond

open GlobalTheory.Mem.Col2.SplitChar GlobalTheory.Mem.Chr

theorem levelLe_mono {K : Type} [Field K] [NumberField K] {χ : Formalism.L2.Host.HChar K} {v : HeightOneSpectrum (𝓞 K)} {a b : ℕ}
    (h : χ.LevelLe v a) (hab : a ≤ b) : χ.LevelLe v b :=
  fun x hx hle => h x hx (hle.trans (WithZero.exp_le_exp.2 (neg_le_neg (Nat.cast_le.2 hab))))

variable {D : D7}

theorem val_le_of_mem_pow {v : HeightOneSpectrum (𝓞 D.host.E)} {n : ℕ} {b : 𝓞 D.host.E} (hb : b ∈ v.asIdeal ^ n) :
    v.valuation D.host.E (b : D.host.E) ≤ WithZero.exp (-(n : ℤ)) := by
  show v.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E b) ≤ _
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_dvd, Ideal.dvd_iff_le,
    Ideal.span_singleton_le_iff_mem]
  exact hb

theorem vl_le_of_mem_hatId {𝔪 : Ideal (𝓞 D.host.E)} {v : HeightOneSpectrum (𝓞 D.host.E)} {n : ℕ}
    (h𝔪 : ∀ b ∈ 𝔪, v.valuation D.host.E (b : D.host.E) ≤ WithZero.exp (-(n : ℤ))) {y : AE D} (hy : y ∈ hatId D 𝔪) :
    vl D v y ≤ WithZero.exp (-(n : ℤ)) := by
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hx
    rw [map_mul, vl_inc]
    exact (mul_le_of_le_one_right' (vl_le hs v)).trans (h𝔪 b hb)
  | zero => rw [map_zero]; exact zero_le'
  | add x y _ _ hx hy => exact (Valuation.map_add _ _ _).trans (max_le hx hy)
  | neg x _ hx => rwa [Valuation.map_neg]

theorem condE_le {T : Type} {L : LevCh D T} (P : Places L) {s : HeightOneSpectrum (𝓞 D.host.F)} (hs : s ∈ P.S0) :
    condE P ≤ (P.w s).asIdeal ^ condExp P s :=
  Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hs)

end GlobalTheory.FunObj.SqNum.NuCond


open GlobalTheory.FunObj.SqNum.NuCond GlobalTheory.Mem.Col2.SplitChar in
theorem GlobalTheory.FunObj.SqNum.heckeU_nuInv_eq_one_of_cong : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (i j : Fin D.R.m) {N : ℕ} (χν : HeckeU D N), (∀ x, χν.f x = (nuH G μ₀ i j)⁻¹.1 (finIdl D x)) → ∀ u, IntU D u → (u : AE D) - 1 ∈ hatId D (condE G.pl * D.host.conj • condE G.pl) → χν.f u = 1 := by
  classical
  intro D T L sc μ₀ hL G i j N χν hχ u hu hm
  rw [hχ]
  have k1 : 1 ≤ D.R.m - (i : ℕ) := by omega
  have k2 : D.R.m - (i : ℕ) ≤ D.R.m := by omega
  obtain ⟨c, hc, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  obtain ⟨n, hn⟩ : ∃ n : HeightOneSpectrum (𝓞 D.host.E) → ℕ, ∀ v, n v =
      if v.under (𝓞 D.host.F) ∈ G.pl.S0 then condExp G.pl (v.under (𝓞 D.host.F)) else 0 := ⟨_, fun _ => rfl⟩
  have hlev : ∀ v, (nuH G μ₀ i j).LevelLe v (n v) := by
    intro v
    have hμ := L.C.isMu0 j
    rw [show nuH G μ₀ i j = L.C.mu0 j * L.xiH μ₀ / G.ch.chiH (D.R.m - i) from rfl, hL.xi_base, mul_one, div_eq_mul_inv]
    refine Formalism.L2.Host.HChar.LevelLe.mul ?_ (Formalism.L2.Host.HChar.LevelLe.inv ?_)
    · by_cases h : v.under (𝓞 D.host.F) ∈ G.pl.S0
      · refine levelLe_mono (hμ.tame v) ?_
        rw [hn v, if_pos h, condExp]
        split_ifs <;> omega
      · refine Formalism.L2.Host.HChar.UnrAt.levelLe (hμ.unr v fun k hk => h ?_) _
        rw [G.pl.mem_S0_of_sum_eq]
        right
        rw [S1_mem_OmF]
        have hk' : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (v.under (𝓞 D.host.F)).asIdeal := by
          show _ ∈ v.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
          rw [Ideal.mem_comap, map_natCast]
          exact hk
        fin_cases k
        · exact Or.inl hk'
        · exact Or.inr (Or.inl hk')
    · by_cases h : v.under (𝓞 D.host.F) ∈ G.pl.S0
      · by_cases h0 : v.under (𝓞 D.host.F) = G.pl.v0
        · rw [hn v, if_pos h, condExp, if_pos h0]
          exact (G.ch.lev0 _ k1 k2 v h0).1
        · have h1 := (G.pl.mem_S0_of_sum_eq.1 h).resolve_left h0
          rw [hn v, if_pos h, condExp, if_neg h0]
          exact (G.ch.lev1 _ k1 k2 v h1).1
      · rw [hn v, if_neg h]
        exact Formalism.L2.Host.HChar.UnrAt.levelLe (G.ch.unr _ k1 k2 v h) 0
  have hval : ∀ v, vl D v ((u : AE D) - 1) ≤ WithZero.exp (-(n v : ℤ)) := by
    intro v
    by_cases h : v.under (𝓞 D.host.F) ∈ G.pl.S0
    · rw [hn v, if_pos h]
      refine vl_le_of_mem_hatId (fun b hb => ?_) hm
      have hw : (G.pl.w (v.under (𝓞 D.host.F))).under (𝓞 D.host.F) = v.under (𝓞 D.host.F) := G.pl.w_over _ h
      rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl c hcm.rank hcm.ne (G.pl.w (v.under (𝓞 D.host.F))) v).1 hw.symm with e | e
      · have hb1 : b ∈ condE G.pl := Ideal.mul_le_left hb
        have hb2 := condE_le G.pl h hb1
        rw [← e] at hb2
        exact val_le_of_mem_pow hb2
      · have hb1 : b ∈ D.host.conj • condE G.pl := Ideal.mul_le_right hb
        rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hb1
        have hb2 := val_le_of_mem_pow (condE_le G.pl h hb1)
        have e2 := e (((D.host.conj⁻¹ • b : 𝓞 D.host.E)) : D.host.E)
        have e3 : c.toRingEquiv (((D.host.conj⁻¹ • b : 𝓞 D.host.E)) : D.host.E) = (b : D.host.E) := by
          show c _ = _
          rw [hc]
          show D.host.conj (D.host.conj⁻¹ (b : D.host.E)) = _
          exact AlgEquiv.apply_symm_apply _ _
        rw [e3] at e2
        rw [e2]
        exact hb2
    · rw [hn v, if_neg h, Nat.cast_zero, neg_zero, WithZero.exp_zero]
      exact vl_le (sub_mem hu.1 (one_mem _)) v
  have hU := finIdl_unit hu
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local D.host.E _ (nuH G μ₀ i j)⁻¹.2.1 (finIdl D u) hU
    (fun w => by rw [finIdl_fst]; rfl) (fun v x hx => ?_)
  have hxu : Formalism.L2.Host.IsUnitAt v x := by
    show Valued.v (x : v.adicCompletion D.host.E) = 1
    rw [hx]
    exact hU v
  refine (hlev v).inv x hxu ?_
  rw [hx, vl_sub_one]
  exact hval v

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSeparatesDualLieGhostComponent
section
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.LieHodgeTate

theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, HasDatum hε G → (∀ x : G.dual.Lie, (∀ t, x (hodgeTate G t) = 0) → x = 0) ∧ (∀ x : G.dual.Lie, ∃ y : latt G, ∀ t, WittVector.fontaineTheta O p (y.1 t) = x (hodgeTate G t)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G hG
  obtain ⟨D, e, fil, lie, hal, -⟩ := hG
  have hprim : IsPrimitiveRoot (root ε).untilt p := by
    have := hε 1
    simpa [zeta] using this
  obtain ⟨-, hle, -, hfil, -, -⟩ := HodgeTateBound.bound p C v O hv ε hprim ℤ_[p] G.height D
  obtain ⟨-, -, -, hsurj, hν, -, -⟩ := _root_.GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε hprim
  have hsingle : ∀ i, toO e (e.symm (Pi.single i 1)) = Pi.single i 1 := by
    intro i
    funext j
    simp only [toO, LinearEquiv.apply_symm_apply]
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_eq_of_ne hj]
  refine ⟨fun x hx => ?_, fun x => ?_⟩
  · let φ : (Fin G.height → O) →ₗ[O] O :=
      x ∘ₗ fil.symm.toLinearMap ∘ₗ (LinearMap.codRestrict D.Fil D.al fun u => hle ⟨u, rfl⟩)
    have hφ : φ = 0 := by
      apply (Pi.basisFun O (Fin G.height)).ext
      intro i
      rw [Pi.basisFun_apply, LinearMap.zero_apply, ← hsingle i]
      have h1 : (⟨D.al (toO e (e.symm (Pi.single i 1))), hle ⟨_, rfl⟩⟩ : D.Fil) =
          fil (hodgeTate G (e.symm (Pi.single i 1))) := Subtype.ext (hal _)
      change x (fil.symm ⟨D.al _, _⟩) = 0
      rw [h1, LinearEquiv.symm_apply_apply]
      exact hx _
    ext w
    obtain ⟨u, hu⟩ := hfil _ (fil w).2
    have h1 : WittVector.fontaineTheta O p (nu ε) • fil w = ⟨D.al u, hle ⟨u, rfl⟩⟩ :=
      Subtype.ext hu.symm
    have h2 : WittVector.fontaineTheta O p (nu ε) * x w = 0 := by
      rw [← smul_eq_mul, ← map_smul, ← fil.symm_apply_apply (WittVector.fontaineTheta O p (nu ε) • w),
        map_smul fil, h1]
      exact LinearMap.congr_fun hφ u
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hν
    · simpa using h
  · haveI : ValuationRing O := ValuationRing.of_integers v hv
    haveI : Module.Free O ((Fin G.height → O) ⧸ LinearMap.ker D.bb) := by
      haveI : Module.Free O (LinearMap.range D.bb) :=
        GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing O _
      exact Module.Free.of_equiv (D.bb.quotKerEquivRange).symm
    haveI : Module.Free O ((Fin G.height → O) ⧸ D.Fil) := by
      change Module.Free O ((Fin G.height → O) ⧸ LinearMap.ker D.bb); infer_instance
    obtain ⟨N', hN'⟩ := GlobalTheory.exists_isCompl_of_projective_quotient D.Fil
    let ρ : (Fin G.height → O) →ₗ[O] O :=
      x ∘ₗ fil.symm.toLinearMap ∘ₗ D.Fil.projectionOnto N' hN'
    choose r hr using fun i => hsurj (ρ (Pi.single i 1))
    obtain ⟨L, hL⟩ := _root_.GlobalTheory.PDivLat.RowSpace.latt_eq_rowSpace p C v O hv ε hε G G.height D e fil hal
    refine ⟨L r, fun t => ?_⟩
    rw [hL]
    have hρ : ∀ w, ρ w = ∑ i, WittVector.fontaineTheta O p (r i) * w i := by
      intro w
      rw [LinearMap.pi_apply_eq_sum_univ ρ w]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hr, smul_eq_mul, mul_comm]
      congr 2
      funext j
      simp [Pi.single_apply, eq_comm]
    have hθ : WittVector.fontaineTheta O p (r ⬝ᵥ (D.F *ᵥ fun i => ofPadic p O (e t i))) =
        ρ (D.al (toO e t)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hρ, dotProduct, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, RingHom.map_mulVec]
      rfl
    rw [hθ]
    have h3 : D.Fil.projectionOnto N' hN' (D.al (toO e t)) = fil (hodgeTate G t) := by
      rw [show D.al (toO e t) = ((fil (hodgeTate G t) : D.Fil) : Fin _ → O) from hal t,
        Submodule.projectionOnto_apply_left]
    change x (fil.symm (D.Fil.projectionOnto N' hN' (D.al (toO e t)))) = _
    rw [h3, LinearEquiv.symm_apply_apply]

end GlobalTheory.LieHodgeTate
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HorizGenZpowMulMemSS
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCore.HorizMul

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem pnorm_zpow (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (m : ℤ) (x : Frame X.Ψ r) :
    X.pnorm (m • la) (fun y => P y ^ m) x = X.pnorm la P x ^ m := by
  unfold Data.pnorm
  rw [mul_zpow, norm_zpow, ← Finset.prod_zpow]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Real.rpow_intCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem differentiable_matDet {Ψ : Finset (E →+* ℂ)} (τ : Ψ) :
    Differentiable ℂ fun y : Frame Ψ r => (mat y τ).det := by
  simp only [Matrix.det_apply', mat, Matrix.of_apply]
  fun_prop

theorem horizGen_rmul' {Ψ : Finset (E →+* ℂ)} (τ : Ψ) (x b : Frame Ψ r) :
    horizGen τ (rmul x b) = horizGen τ x * horizGen τ b := by
  show (mat x τ * mat b τ).det⁻¹ = _
  rw [Matrix.det_mul, mul_inv]
  rfl

theorem horizGen_lact' {Ψ : Finset (E →+* ℂ)} (τ : Ψ) (γ : GL (Fin r) E) (x : Frame Ψ r) :
    horizGen τ (lact γ x) = (τ.1 γ.1.det)⁻¹ * horizGen τ x := by
  show (γ.1.map τ.1 * mat x τ).det⁻¹ = _
  rw [Matrix.det_mul, mul_inv, RingHom.map_det]
  rfl

theorem bchar_zsmul_modelFlat {Ψ : Finset (E →+* ℂ)} (τ : Ψ) (m : ℤ) {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) :
    bchar (m • modelFlat r τ) b = horizGen τ b ^ m := by
  classical
  have hd : (mat b τ).det = ∏ i, b τ i i :=
    Matrix.det_of_upperTriangular (M := mat b τ) fun a c h => (hb τ).2 a c h
  unfold bchar
  rw [Finset.prod_eq_single τ (fun τ' _ h => by simp [modelFlat, h]) (by simp)]
  simp only [Pi.smul_apply, modelFlat, if_true, smul_eq_mul, mul_neg, mul_one]
  rw [Finset.prod_zpow, horizGen, hd, inv_zpow', zpow_neg]

theorem isBddSec_horizGen_zpow (X : Data E r) (τ : X.Ψ) (m : ℤ)
    (hdet : ∀ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E).det = 1) (hχ : ∀ γ ∈ X.Γ, X.χ (m • modelFlat r τ) γ = 1) :
    X.IsBddSec (m • modelFlat r τ) fun y => horizGen τ y ^ m := by
  refine ⟨⟨fun y hy => ?_, fun x _ b hb => ?_, fun γ hγ x _ => ?_⟩, Real.sqrt ‖τ.1 X.Gm.det‖ ^ m, fun y hy => ?_⟩
  · have hne : (mat y τ).det ≠ 0 := (hy τ).1
    exact (((differentiable_matDet τ y).inv hne).zpow (Or.inl (inv_ne_zero hne))).differentiableWithinAt
  · beta_reduce
    rw [horizGen_rmul', mul_zpow, bchar_zsmul_modelFlat τ m hb, mul_comm]
  · beta_reduce
    rw [horizGen_lact', hdet γ hγ, map_one, inv_one, one_mul, hχ γ hγ, one_mul]
  · rw [pnorm_zpow, pnorm_horizGen X τ hy]

theorem chi_zsmul_modelFlat (X : Data E r) (τ : X.Ψ) (la : Wt X.Ψ r) (m : ℤ)
    (hχ : ∀ γ ∈ X.Γ, X.χ (la + m • modelFlat r τ) γ = X.χ la γ) : ∀ γ ∈ X.Γ, X.χ (m • modelFlat r τ) γ = 1 := by
  intro γ hγ
  obtain ⟨n, hn, h⟩ := X.χ_fin la
  have h0 : X.χ la γ ≠ 0 := fun h0 => by
    have := h γ hγ
    rw [h0, zero_pow hn.ne'] at this
    exact zero_ne_one this
  have h1 := (X.χ_add la (m • modelFlat r τ) γ hγ).symm.trans (hχ γ hγ)
  exact mul_left_cancel₀ h0 (h1.trans (mul_one _).symm)

theorem horizGen_zpow_mul_mem_SS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (τ : X.Ψ)
    (la : Wt X.Ψ r) (m : ℤ), (∀ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E).det = 1) →
    (∀ γ ∈ X.Γ, X.χ (la + m • modelFlat r τ) γ = X.χ la γ) →
    ∀ P ∈ X.SS la, (fun y => horizGen τ y ^ m * P y) ∈ X.SS (la + m • modelFlat r τ) := by
  intro E _ _ _ r X τ la m hdet hχ P hP
  have hQ := isBddSec_horizGen_zpow X τ m hdet (chi_zsmul_modelFlat X τ la m hχ)
  obtain ⟨hb, hfj⟩ := GlobalTheory.bddSec_mul_and_constTerm_mul E r X la _ P _ hP.1 hQ
  have e : (fun y => horizGen τ y ^ m * P y) = P * fun y => horizGen τ y ^ m := funext fun y => mul_comm _ _
  rw [e]
  refine ⟨hb, fun ξ hξ x hx => ?_⟩
  rw [hfj ξ hξ x hx, hP.2 ξ hξ x hx, zero_mul]

end GlobalTheory.FlatCore.HorizMul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IpAtNonnegOfDatFramed
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
open scoped ComplexOrder

namespace GlobalTheory.ColRowsTop


open GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum GlobalTheory.ColNorms GlobalTheory.PeriodClassSum GlobalTheory.LastPeriod in
theorem periodFun_le (hL : LastMapNorm) {X : Fields} (hX : X.Ok) {Pr : Primes X} (hPr : Pr.Ok) {R : Ranks} (W : Wts X Pr.Word R)
    (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ)
    (P : LevFam X.E X.K R.r Pr.vGs) (u : Pr.Word) (hI : ∀ τ, Br.Interlace (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ))
    (hS : ∀ τ, Br.SameShift (W.lamTrue u R.m τ) (W.sgTrue τ)) (s : X.K →+* ℂ)
    (ψ : RowPt Pr R sel (mu0 X.F X.E X.K Sg) → Formalism.L2.DIV.VV X.K (W.lamTrue u R.m))
    (F : RowPt Pr R sel (mu0 X.F X.E X.K Sg) → Formalism.L2.DIV.VV X.K W.sgTrue) :
    ‖s (PtilFF W Ch sel (mu0 X.F X.E X.K Sg) P (mtildeOk W Ch sel (mu0 X.F X.E X.K Sg) hX P) u ψ F)‖ ^ 2 ≤
      Real.exp (lastLog W u) *
        GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.normSqAt (evGSD W Ch sel (mu0 X.F X.E X.K Sg) P u) (GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.evOk W Ch sel Sg hX hPr P u) s ψ *
        GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.normSqAt (mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P) (mtildeOk W Ch sel (mu0 X.F X.E X.K Sg) hX P) s F := by
  have hT : (0 : ℝ) < (Pr.T u : ℝ) := Nat.cast_pos.2 (hPr.T_prime u).pos
  have ht : ∀ τ, star (s (X.emb τ (star ((Pr.piT u : 𝓞 X.E) : X.E)))) * s (X.emb τ (star ((Pr.piT u : 𝓞 X.E) : X.E))) =
      ((Pr.T u : ℝ) : ℂ) := fun τ => by
    have h1 := hX.conjE (s.comp (X.emb τ)) (star ((Pr.piT u : 𝓞 X.E) : X.E))
    rw [star_star, RingHom.comp_apply, RingHom.comp_apply, starRingEnd_apply] at h1
    have h2 : ((Pr.piT u : 𝓞 X.E) : X.E) * star ((Pr.piT u : 𝓞 X.E) : X.E) = (Pr.T u : X.E) := by
      have := congrArg (fun z : 𝓞 X.E => (z : X.E)) (hPr.piT_norm u)
      simp only [map_mul, map_natCast] at this
      exact this
    rw [← h1, ← map_mul, ← map_mul, h2]
    simp
  have hB := coefOpLe_brAt hL s (N_m_succ R) (W.lamTrue u R.m) W.sgTrue hI hS _ hT _ ht
  set hM := mtildeOk W Ch sel (mu0 X.F X.E X.K Sg) hX P
  set hE := GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.evOk W Ch sel Sg hX hPr P u
  let _ := hM.fintypeCl
  have h := sum_pair_le s _ _ _ _ hB ((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).toCSD hM).wt
    (fun c => ψ ((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).outSec.rep c))
    (fun c => F ((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).outSec.rep c))
  have e0 : PtilFF W Ch sel (mu0 X.F X.E X.K Sg) P hM u ψ F =
      ∑ c, ((((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).toCSD hM).wt c : ℕ) : X.K)⁻¹ *
        pairBK W.sgTrue (brC W u (ψ ((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).outSec.rep c)))
          (F ((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).outSec.rep c)) := by
    unfold PtilFF GSD.csOf
    exact (LinearMap.congr_fun (LinearMap.sum_apply _ _ _) _).trans (LinearMap.sum_apply _ _ _)
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.normSqAt (evGSD W Ch sel (mu0 X.F X.E X.K Sg) P u) hE s ψ =
      ∑ c, ((((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).toCSD hM).wt c : ℕ) : ℝ)⁻¹ *
        sqAt s (W.lamTrue u R.m) (ψ ((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).outSec.rep c)) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.normSqAt GSD.ipAt
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    exact (re_inv_mul _ _).trans
      (congrArg₂ (· * ·) rfl ((gram_posSemidef_and_sqAt X.E X.K X.Tau X.emb _ (W.lamTrue u R.m) s).2 _))
  have e2 : GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.normSqAt (mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P) hM s F =
      ∑ c, ((((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).toCSD hM).wt c : ℕ) : ℝ)⁻¹ *
        sqAt s W.sgTrue (F ((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).outSec.rep c)) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.normSqAt GSD.ipAt
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hg := (gram_posSemidef_and_sqAt X.E X.K X.Tau X.emb _ W.sgTrue s).2
    simp only [pairVr_one_eq, pairK_one_basis] at hg
    refine (re_inv_mul _ _).trans (congrArg₂ (· * ·) rfl (Eq.trans ?_ (hg _)))
    unfold GSD.pairAt
    rw [row_gramV]
    rfl
  rw [e0, e1, e2]
  refine h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ ?_) ?_)
  · rw [lastLog, Real.exp_add, mul_comm (-_ : ℝ), ← Real.rpow_def_of_pos hT, ← Int.cast_neg, Real.rpow_intCast]
    exact mul_le_mul_of_nonneg_left (Real.le_exp_log _) (by positivity)
  · exact Finset.sum_nonneg fun c _ => mul_nonneg (by positivity) (sqAt_nonneg _ _ _)
  · exact Finset.sum_nonneg fun c _ => mul_nonneg (by positivity) (sqAt_nonneg _ _ _)

theorem period_le (hL : GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.LastMapNorm) {X : Fields} (hX : X.Ok) {Pr : Primes X} (hPr : Pr.Ok) {R : Ranks}
    (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ} (mu : Tup X.F X.E X.K Sg) (hmu : mu = 1)
    (P : LevFam X.E X.K R.r Pr.vGs) (u : Pr.Word) (hI : ∀ τ, Br.Interlace (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ))
    (hS : ∀ τ, Br.SameShift (W.lamTrue u R.m τ) (W.sgTrue τ))
    (hP : (mtildeGSD W Ch sel mu P).Ok) (hE : (evGSD W Ch sel mu P u).Ok) (v : InfinitePlace X.K)
    (ψ : RowPt Pr R sel mu → Formalism.L2.DIV.VV X.K (W.lamTrue u R.m)) (F : RowPt Pr R sel mu → Formalism.L2.DIV.VV X.K W.sgTrue) :
    v (PtilFF W Ch sel mu P hP u ψ F) ^ 2 ≤
      Real.exp (lastLog W u) * ((evGSD W Ch sel mu P u).ipAt hE v ψ ψ).re * ((mtildeGSD W Ch sel mu P).ipAt hP v F F).re := by
  subst hmu
  have h := periodFun_le hL hX hPr W Ch sel Sg P u hI hS v.embedding ψ F
  rw [InfinitePlace.norm_embedding_eq] at h
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.normSqAt, InfinitePlace.mk_embedding] at h
  exact h

theorem ipAt_nonneg_of_datFramed {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K} {h : S.Ok} (hS : DatFramed S h)
    (v : InfinitePlace K) (ψ : S.EqFun) : 0 ≤ (S.ipAt h v ψ ψ).re := by
  obtain ⟨n, e, X, -, hX⟩ := hS
  obtain ⟨y, rfl⟩ := e.surjective ψ
  rw [← hX v y, Complex.ofReal_re]
  positivity

end GlobalTheory.ColRowsTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdLatEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotFrames

variable {D : D7} {T : Type} {A A' WW : HSp D}

def reRig (Y : Tri T A A' WW) (rA : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig A) (rA' : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig A') (rW : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig WW)
    (f : T → WO A WW → ℂ) (f' : T → WO A' WW → ℂ) : Tri T A A' WW :=
  { Y with rA := rA, rA' := rA', rW := rW, f := f, f' := f' }

abbrev botAlpha (L : LevCh D T) (i j : Fin D.R.m) (t : T) : (AE D)ˣ →* Circle :=
  L.mu t (j + 1) * L.eta ^ (rankV D i j % 2)

abbrev botBeta {L : LevCh D T} {sc : Consts} (G : GridData L sc) (i j : Fin D.R.m) : (AE D)ˣ →* Circle :=
  G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)

theorem isStd_lat_eq {V : HSp D} {r r' : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V} (h : r.IsStd) (h' : r'.IsStd) : r.Λ = r'.Λ := by
  ext y
  rw [h.2.1, h'.2.1]

theorem isStd_s_eq {V : HSp D} {r r' : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V} (h : r.IsStd) (h' : r'.IsStd) : r.s = r'.s :=
  funext fun τ => (h.2.2 τ).1.trans (h'.2.2 τ).1.symm

theorem isStd_B_eq {V : HSp D} {r r' : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V} (h : r.IsStd) (h' : r'.IsStd) : r.B = r'.B :=
  funext fun τ => (h.2.2 τ).2.trans (h'.2.2 τ).2.symm

end GlobalTheory.BotFrames

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialGoodReductionOfNeronOggShafarevich
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem potentialGoodReduction_of_neronOggShafarevich :
    GlobalTheory.Published.NeronOggShafarevichSt → GlobalTheory.Published.PotentialGoodReductionSt := by
  intro h R K Ω _ _ _ _ _ _ _ _ _ _ V hV A _ _ hA l _ hl
  exact ⟨_root_.GlobalTheory.finite_image_inertia_of_potentialGoodReduction h R K Ω V hV A hA l hl, _root_.GlobalTheory.hasPotentialGoodReduction_of_finite_image_inertia h R K Ω V hV A hA l hl⟩

end GlobalTheory
end

