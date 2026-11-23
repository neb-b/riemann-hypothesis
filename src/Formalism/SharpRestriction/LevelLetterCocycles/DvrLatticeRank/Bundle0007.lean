module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0027
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ConstantCoeffQZeroEqP
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0006
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GradNPfC
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0028

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ExponentRecursionOfDimension
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.CrystallineExponents

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem exponent_recursion_of_dimension (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h1 : Formalism.MainNotions.ElementDenominator.adm1 D HW F Cm) (h8 : Formalism.MainNotions.ElementDenominator.adm8 D)
    (hdim : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL)
      (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((D.loc l).PD K) T.ρ →
      ∀ (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1),
        finrank ↥LL.1 ↥(Formalism.MainNotions.DeltaInvariantLattices.ιDi ((HW l).W K 1 LL hG) T c) ≤
          finrank ↥LL.1 ↥(DdRE ((D.loc l).PD K) T.ρ τ)) :
    ExpansionFormAll D HW := by
  intro l _ hl K LL hG T h' hh' hT hJ c y _ hyc hk hexp
  obtain ⟨p1, -, p3, p4, p5, -⟩ := h1 l K 1 LL hG
  obtain ⟨⟨hfc, -⟩, hfd⟩ := h8 l K LL T
  have hFr : IsFractionRing ↥(OL LL) ↥LL.1 := by
    haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
    exact integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥LL.1
  haveI : FiniteDimensional ↥LL.1
      ↥(DcrisL ((D.loc l).PD K) T.ρ (((HW l).W K 1 LL hG).emb c)) :=
    Submodule.finiteDimensional_of_le (inf_le_left : _ ≤ Dcris ((D.loc l).PD K) T.ρ)
  haveI : FiniteDimensional ↥LL.1 ↥(Formalism.MainNotions.DeltaInvariantLattices.ιDi ((HW l).W K 1 LL hG) T c) := by
    unfold Formalism.MainNotions.DeltaInvariantLattices.ιDi
    infer_instance
  have hyc' : (letE c : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) • y = y := by
    have h := LinearMap.mem_ker.1 hyc
    simpa only [LinearMap.restrictScalars_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero] using h
  refine mem_N_of_exp ((HW l).W K 1 LL hG) hFr ((HW l).W_s K 1 LL hG) T
    (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) (M := fun _ => h') (h := fun _ => h') (p1 T hT) (p3 T hT)
    (p4 T hT) (p5 T _ _ hT fun τ _ _ => hJ τ) c (fun ζ hζ => ?_) (fun τ => (hfd τ).1)
    (hdim l K LL hG T hT c) y hyc' hk hexp
  rw [(D.loc l).PD_p] at hζ
  exact exists_pt D HW hG c ζ hζ

end Formalism.MainNotions.N.Ln34.CrystallineExponents

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfPt
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Zero

open PowerSeries

variable {LL : Type} [Field LL]

theorem framepf_exp_pow_sub_one (E : PowerSeries LL) (h0 : constantCoeff E = 1)
    (hd : PowerSeries.derivative E = E) (p : ℕ) :
    ∃ w : PowerSeries LL, E ^ p - 1 = X * w ∧ constantCoeff w = (p : LL) := by
  have hX1 : X ∣ E - 1 := by
    rw [PowerSeries.X_dvd_iff]
    simp [h0]
  obtain ⟨w1, hw1⟩ := hX1
  have hc1 : constantCoeff w1 = 1 := by
    have h2 : coeff 0 (PowerSeries.derivative E) = coeff 1 E := by
      rw [PowerSeries.coeff_derivative]
      simp
    rw [hd] at h2
    have h1 : coeff 1 (E - 1) = coeff 0 w1 := by
      rw [hw1]
      exact PowerSeries.coeff_succ_X_mul 0 w1
    have h3 : coeff 1 (E - 1) = coeff 1 E := by
      simp [PowerSeries.coeff_one]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← h1, h3, ← h2,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
  induction p with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨w, hw, hwc⟩ := ih
    refine ⟨w * E + w1, ?_, ?_⟩
    · have he : E ^ (k + 1) - 1 = (E ^ k - 1) * E + (E - 1) := by ring
      rw [he, hw, hw1]
      ring
    · simp [hwc, hc1, h0]

end Zero

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)


open PowerSeries in
theorem framepf_lev_q_simple (c : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) :
    ∃ u : PowerSeries LL, W.lev c ζ W.q = X * u ∧ constantCoeff u ≠ 0 := by
  obtain ⟨E, hE0, hEd, hE⟩ := W.lev_π c ζ ⟨1, by simpa using hζ⟩
  obtain ⟨w, hw, hwc⟩ := framepf_exp_pow_sub_one E hE0 hEd PD.p
  have hp0 : (PD.p : LL) ≠ 0 := by
    intro h
    have h1 := W.v_l
    rw [h, AddValuation.map_zero] at h1
    simp at h1
  have hp1 : PD.p ≠ 1 := by
    intro h
    have h1 := W.v_l
    rw [h, Nat.cast_one, AddValuation.map_one] at h1
    simp at h1
  have hζ1 : ζ ≠ 1 := by
    intro h
    have h2 := hζ.eq_orderOf
    rw [h, orderOf_one] at h2
    exact hp1 h2
  have hζp : ζ ^ PD.p = 1 := hζ.pow_eq_one
  have hq : (letπ : LetA O n) * W.q = (1 + letπ) ^ PD.p - 1 := by
    funext i
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Pi.add_apply, Pi.one_apply]
    exact W.q₀_def
  have hfq : W.lev c ζ letπ * W.lev c ζ W.q = E ^ PD.p - 1 := by
    rw [← map_mul, hq, map_sub, map_pow, map_add (f := _), map_one, hE, mul_pow, ← map_pow, hζp, map_one,
      one_mul]
  set P := W.lev c ζ letπ with hPdef
  have hP : P = C ζ * E - 1 := eq_sub_of_add_eq' hE
  have hPc : constantCoeff P = ζ - 1 := by
    rw [hP]
    simp [hE0]
  have hPne : constantCoeff P ≠ 0 := by
    rw [hPc]
    exact sub_ne_zero.mpr hζ1
  refine ⟨w * P⁻¹, ?_, ?_⟩
  · have hinv : P⁻¹ * P = 1 := PowerSeries.inv_mul_cancel P hPne
    calc W.lev c ζ W.q = (P⁻¹ * P) * W.lev c ζ W.q := by rw [hinv, one_mul]
      _ = P⁻¹ * (E ^ PD.p - 1) := by rw [mul_assoc, hfq]
      _ = X * (w * P⁻¹) := by rw [hw]; ring
  · rw [map_mul, hwc, PowerSeries.constantCoeff_inv, hPc]
    exact mul_ne_zero hp0 (inv_ne_zero (sub_ne_zero.mpr hζ1))

theorem framepf_Q_eq_q (hs : W.s = 1) : W.Q = W.q := by
  simp [Formalism.BasicNotions.LocWach.Q, hs]

theorem framepf_Q_at (hs : W.s = 1) (c : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) :
    PowerSeries.constantCoeff (W.lev c ζ W.Q) = 0 ∧ PowerSeries.coeff 1 (W.lev c ζ W.Q) ≠ 0 := by
  obtain ⟨u, hu, hu0⟩ := framepf_lev_q_simple W c ζ hζ
  rw [framepf_Q_eq_q W hs, hu]
  refine ⟨by simp, ?_⟩
  have h1 : PowerSeries.coeff 1 (PowerSeries.X * u) = PowerSeries.coeff 0 u :=
    PowerSeries.coeff_succ_X_mul 0 u
  rw [h1, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact hu0

end Local

theorem framepf_pt_prim (D : D7) (HW : HWOf D.loc) {l : ℕ} [Fact l.Prime] {K LL : FinExt l}
    (hG : Good K 1 LL) (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ) : IsPrimitiveRoot ζ l := by
  obtain ⟨τs, ⟨-, hroot⟩, -⟩ := hpt
  have hpow : (D.loc l).ζQ 1 ^ l = 1 := by
    have h := (D.loc l).ζQ_succ 0
    rwa [zero_add, (D.loc l).ζQ_zero] at h
  have hmem : (D.loc l).ζQ 1 ∈ Ks K 1 := by
    show _ ∈ K0 K ⊔ IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1}
    refine (le_sup_right : IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1} ≤ _) ?_
    apply IntermediateField.subset_adjoin
    show (D.loc l).ζQ 1 ^ (l ^ 1) = 1
    rw [pow_one]
    exact hpow
  set y : Ks K 1 := ⟨_, hmem⟩ with hydef
  have hyζ : τs y = ζ := hroot y rfl
  have hy1 : y ^ l = 1 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    exact hpow
  have hy2 : y ≠ 1 := by
    intro h
    apply (D.loc l).ζQ_one
    have h' := congrArg Subtype.val h
    exact h'
  have hprim : IsPrimitiveRoot y l := by
    have ho := orderOf_eq_prime hy1 hy2
    have h0 := IsPrimitiveRoot.orderOf y
    rwa [ho] at h0
  rw [← hyζ]
  exact hprim.map_of_injective τs.injective

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GradNPfB
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem gradNPf_cc_γ₀ (g : W.Gam) (a : PowerSeries O) :
    PowerSeries.constantCoeff (W.γ₀ g a) = PowerSeries.constantCoeff a := by
  exact Formalism.MainNotions.LiftingTheory.constantCoeff_gamma W g a

theorem gradNPf_γA_comm (g h : W.Gam) (a : LetA O n) :
    W.γA g (W.γA h a) = W.γA h (W.γA g a) := by
  exact Formalism.MainNotions.LiftingTheory.frame_γA_comm W g h a

theorem gradNPf_cc_f (s' : ℕ) (w : (LetA O n)ˣ) (π' f : LetA O n)
    (hw : π' = (w : LetA O n) * letπ ^ s') (hf : W.γA W.gam π' = π' * f) (i : ZMod n) :
    PowerSeries.constantCoeff (f i) = ((W.χΓ W.gam : Oˣ) : O) ^ s' := by
  have hi := congrFun hf i
  have hγi : (W.γA W.gam π') i = W.γ₀ W.gam (π' i) := rfl
  have hπi : π' i = (w : LetA O n) i * PowerSeries.X ^ s' := by rw [hw]; rfl
  have hX : W.γ₀ W.gam PowerSeries.X = PowerSeries.X *
      PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) (W.γ₀ W.gam PowerSeries.X)) := by
    conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const (W.γ₀ W.gam PowerSeries.X)]
    rw [(W.γ₀_X W.gam).1, map_zero, add_zero]
  have hh : PowerSeries.constantCoeff (PowerSeries.mk (fun p => PowerSeries.coeff (p + 1)
      (W.γ₀ W.gam PowerSeries.X))) = ((W.χΓ W.gam : Oˣ) : O) := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
    exact (W.γ₀_X W.gam).2
  rw [hγi, Pi.mul_apply, hπi, map_mul, map_pow, hX, mul_pow] at hi
  have h2 : PowerSeries.X ^ s' * (W.γ₀ W.gam ((w : LetA O n) i) *
      (PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) (W.γ₀ W.gam PowerSeries.X))) ^ s') =
      PowerSeries.X ^ s' * ((w : LetA O n) i * f i) := by
    linear_combination hi
  have h3 := congrArg PowerSeries.constantCoeff (PowerSeries.X_pow_mul_cancel h2)
  rw [map_mul, map_mul, map_pow, hh, gradNPf_cc_γ₀] at h3
  have hwu : IsUnit (PowerSeries.constantCoeff ((w : LetA O n) i)) :=
    (w.isUnit.map (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) i)).map PowerSeries.constantCoeff
  exact (hwu.mul_left_cancel h3).symm

theorem gradNPf_fΔ (s' : ℕ) (w : (LetA O n)ˣ) (π' f : LetA O n)
    (hw : π' = (w : LetA O n) * letπ ^ s') (hπΔ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hf : W.γA W.gam π' = π' * f) : ∀ δ ∈ W.DelF, W.γA δ f = f := by
  intro δ hδ
  have hu : IsUnit (algebraMap (LetA O n) W.EE π') := by
    rw [hw, map_mul, map_pow]
    have hl : IsUnit (algebraMap (LetA O n) W.EE letπ) := by simpa using Formalism.MainNotions.LiftingTheory.wmap_unit W 0
    exact (w.isUnit.map _).mul (hl.pow _)
  apply Formalism.MainNotions.LiftingTheory.lifta_reg W π' _ _ hu
  have h1 : W.γA δ (W.γA W.gam π') = W.γA W.gam π' := by
    rw [Formalism.MainNotions.LiftingTheory.frame_γA_comm, hπΔ δ hδ]
  rw [hf, map_mul, hπΔ δ hδ] at h1
  exact h1

theorem gradNPf_expand (π' a : LetA O n) (hπ0 : ∀ i, PowerSeries.constantCoeff (π' i) = 0)
    (F : ZMod n → PowerSeries O) (hF : ∀ i, a i = PowerSeries.subst (π' i) (F i))
    (c₀ : O) (hc : ∀ i, PowerSeries.constantCoeff (a i) = c₀) :
    ∃ t : LetA O n, a - algebraMap O (LetA O n) c₀ = π' * t := by
  have hS : ∀ i, PowerSeries.HasSubst (π' i) := fun i =>
    PowerSeries.HasSubst.of_constantCoeff_zero' (hπ0 i)
  refine ⟨fun i => PowerSeries.subst (π' i)
    (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (F i)), ?_⟩
  funext i
  have e1 : a i = π' i * PowerSeries.subst (π' i)
      (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (F i)) +
      PowerSeries.C (PowerSeries.constantCoeff (F i)) := by
    conv_lhs => rw [hF i, PowerSeries.eq_X_mul_shift_add_const (F i)]
    rw [PowerSeries.subst_add (hS i), PowerSeries.subst_mul (hS i), PowerSeries.subst_X (hS i),
      PowerSeries.subst_C]
    rfl
  have e3 : PowerSeries.constantCoeff (F i) = c₀ := by
    have := congrArg PowerSeries.constantCoeff e1
    rw [hc i, map_add (f := _), map_mul, hπ0 i, zero_mul, zero_add, PowerSeries.constantCoeff_C] at this
    exact this.symm
  rw [e3] at e1
  have hC : algebraMap O (PowerSeries O) c₀ = PowerSeries.C c₀ := by
    rw [PowerSeries.algebraMap_apply]
    rfl
  show a i - algebraMap O (PowerSeries O) c₀ = π' i * PowerSeries.subst (π' i)
    (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (F i))
  rw [hC, e1]
  ring

theorem exists_gam_pi_factor (T : LocLat G Qp LL O) (e s' : ℕ) (hs : 1 ≤ s') (π' : LetA O n)
    (E : ZMod n → Polynomial O) (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W e s' π' E) (π'₀ : LetA O n)
    (w₀ : (LetA O n)ˣ) (hw₀ : π'₀ = (w₀ : LetA O n) * letπ ^ s')
    (hm : ∀ y ∈ W.NΔ T, ∃ x' ∈ W.NΔ T, W.γ T y - y = π'₀ • x') :
    ∃ f t : LetA O n, W.γA W.gam π' = π' * f ∧
      f - algebraMap O (LetA O n) (((W.χΓ W.gam : Oˣ) : O) ^ s') = π' * t ∧
      IsUnit (algebraMap (LetA O n) W.EE π') ∧ (∀ δ ∈ W.DelF, W.γA δ π' = π') ∧
      (∀ y ∈ W.NΔ T, ∃ d ∈ W.N T, W.γD T W.gam y - y = π' • d) := by
  obtain ⟨w, hw⟩ := hR.2.2.1
  have hπΔ : ∀ δ ∈ W.DelF, W.γA δ π' = π' := fun δ hδ => hR.1 δ hδ
  obtain ⟨w', hw'⟩ := hR.2.2.2.2.2.2.1
  obtain ⟨f, hfdef⟩ : ∃ f : LetA O n, f = 1 + (w' : LetA O n) * Formalism.MainNotions.DeltaInvariantLattices.Eat E π' := ⟨_, rfl⟩
  have hf : W.γA W.gam π' = π' * f := by
    rw [hfdef]
    linear_combination hw'
  have hfΔ := gradNPf_fΔ W s' w π' f hw hπΔ hf
  obtain ⟨Fs, hFs, -⟩ := hR.2.1 f hfΔ
  have hπ0 : ∀ i, PowerSeries.constantCoeff (π' i) = 0 := by
    intro i
    have : π' i = (w : LetA O n) i * PowerSeries.X ^ s' := by rw [hw]; rfl
    rw [this, map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega), mul_zero]
  obtain ⟨t, ht⟩ := gradNPf_expand π' f hπ0 Fs hFs _ (gradNPf_cc_f W s' w π' f hw hf)
  refine ⟨f, t, hf, ht, ?_, hπΔ, ?_⟩
  · rw [hw, map_mul, map_pow]
    exact (w.isUnit.map _).mul (W.EE_π.pow _)
  · intro y hy
    obtain ⟨x', hx', hxe⟩ := hm y hy
    refine ⟨((w₀ : LetA O n) * ((w⁻¹ : (LetA O n)ˣ) : LetA O n)) • x', (W.N T).smul_mem _ hx'.1, ?_⟩
    have hπ₀ : π'₀ = ((w₀ : LetA O n) * ((w⁻¹ : (LetA O n)ˣ) : LetA O n)) * π' := by
      rw [hw₀, hw, mul_assoc, ← mul_assoc ((w⁻¹ : (LetA O n)ˣ) : LetA O n), Units.inv_mul, one_mul]
    rw [smul_smul, mul_comm π', ← hπ₀]
    exact hxe

end Local


set_option maxHeartbeats 1000000 in
theorem gradNPf_hyps (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h1 : adm1 D HW F Cm) (l : ℕ) [hpf : Fact l.Prime] (hl : l ≠ 2)
    (K LL : FinExt l) (hG : Good K 1 LL) (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (hs : 1 ≤ sK l K) :
    ∃ (f t : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (x u : ↥(OL LL)),
      IsUnit u ∧ x - 1 = (l : ↥(OL LL)) * u ∧
      ((HW l).W K 1 LL hG).γA ((HW l).W K 1 LL hG).gam π' = π' * f ∧
      f - algebraMap ↥(OL LL) (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (x ^ sK l K) = π' * t ∧
      IsUnit (algebraMap (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) ((HW l).W K 1 LL hG).EE π') ∧
      (∀ δ ∈ ((HW l).W K 1 LL hG).DelF, ((HW l).W K 1 LL hG).γA δ π' = π') ∧
      (∀ y ∈ ((HW l).W K 1 LL hG).NΔ T, ∃ d ∈ ((HW l).W K 1 LL hG).N T,
        ((HW l).W K 1 LL hG).γD T ((HW l).W K 1 LL hG).gam y - y = π' • d) ∧
      ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam ∧
      ∀ N : ℕ, ∃ a : ↥(OL LL), (l : ↥(OL LL)) ^ (N + padicValNat l N.factorial) =
        a * ∏ y ∈ Finset.Ico 1 (N + 1), ((x ^ sK l K) ^ y - 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, h9W, -⟩ := h1 l K 1 LL hG
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hp : ((D.loc l).PD K).p ≠ 2 := by rw [hpl]; exact hl
  have hs1 : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  obtain ⟨-, ⟨π'₀, E₀, hr₀, hm₀⟩, -⟩ := h9W T hT hs1 hp
  rw [hpl] at hr₀
  obtain ⟨w₀, hw₀⟩ := hr₀.2.2.1
  obtain ⟨f, t, hf, ht, hEE, hπΔ, hγN⟩ :=
    exists_gam_pi_factor _ T (eK K) (sK l K) hs π' E hR π'₀ w₀ hw₀ hm₀.2
  have hι : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  have hRv : ∀ y : ↥LL.1, 0 ≤ (D.loc l).v LL y ↔ ∃ a : ↥(OL LL), algebraMap ↥(OL LL) ↥LL.1 a = y := by
    intro y
    rw [(D.loc l).v_O LL y]
    exact ⟨fun h => ⟨⟨y, h⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.2⟩
  have hlv : (D.loc l).v LL (l : ↥LL.1) = 1 := (D.loc l).v_l LL
  have hlO : (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 (l : ↥(OL LL))) = 1 := by
    rw [map_natCast]
    exact hlv
  have hxv : (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1
      ((((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gam : (↥(OL LL))ˣ) : ↥(OL LL)) - 1) = 1 := by
    have := ((HW l).W K 1 LL hG).gam_gen
    rw [hs1, Nat.cast_one] at this
    exact this
  obtain ⟨u, hu, hxu⟩ := gradNPf_sub_one ((D.loc l).v LL) (algebraMap ↥(OL LL) ↥LL.1) hι hRv
    (l : ↥(OL LL)) _ hlO hxv
  have hsl : ¬ l ∣ sK l K := by
    apply Nat.not_dvd_of_pos_of_lt hs
    have h2 := hpf.out.two_le
    exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  exact ⟨f, t, (((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gam : (↥(OL LL))ˣ), u, hu, hxu, hf, ht, hEE, hπΔ, hγN,
    ((HW l).W K 1 LL hG).gamK_eq_one hs1 hp,
    fun N => gradNPf_prod ((D.loc l).v LL) (algebraMap ↥(OL LL) ↥LL.1) hι hRv l hl hlv _ u hu hxu
      (sK l K) (by omega) hsl N⟩

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Imports
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.UniversalLiftFrames

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def Phi (T : LocLat G Qp LL O) (c : ZMod n) (ζ : LL) {r : ℕ} (rep : Fin r → W.DD T) :
    (Fin r → LL) →ₗ[LL] T.V ⊗[Qp] BdR where
  toFun d := ∑ k, d k • valAt W T c ζ (rep k)
  map_add' d d' := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a d := by simp [Finset.smul_sum, smul_smul]

theorem Phi_apply (T : LocLat G Qp LL O) (c : ZMod n) (ζ : LL) {r : ℕ} (rep : Fin r → W.DD T)
    (d : Fin r → LL) : Phi W T c ζ rep d = ∑ k, d k • valAt W T c ζ (rep k) := rfl

end Formalism.MainNotions.N.Ln34.UniversalLiftFrames
end
end

