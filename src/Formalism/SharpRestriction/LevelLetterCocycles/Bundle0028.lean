module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0019
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVNonneg
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd
public import Formalism.SharpRestriction.LevelLetterCocycles.Step1KillXList
public import Formalism.SharpRestriction.LevelLetterCocycles.SaturationUnramifiedOfRingCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0025
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0026
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0022

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.MultVNonneg
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section Pass

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem finiteDimensional_filLev (c : ZMod n) (hfd : FiniteDimensional LL ↥(DcrisL PD T.ρ (W.emb c))) (u : ℤ) :
    FiniteDimensional LL ↥(Formalism.MainNotions.WachCoordinates.FilLev W T c 0 u) := by
  have hc : c - ((0 : ℕ) : ZMod n) = c := by simp
  haveI : FiniteDimensional LL
      ↥(Formalism.WeaklyAdmissibleFiltrations.FilCris PD T.ρ u ⊓ DcrisL PD T.ρ (W.emb (c - ((0 : ℕ) : ZMod n)))) := by
    rw [hc]
    exact Submodule.finiteDimensional_of_le inf_le_right
  unfold Formalism.MainNotions.WachCoordinates.FilLev
  infer_instance

theorem multV_nonneg' [NeZero n] (hFD : Sh.FilDim W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (hT : IsCrys PD T.ρ) (c : ZMod n) (τ : K →ₐ[Qp] LL) (hτ : Formalism.MainNotions.LiftingTheory.Over W τ c)
    (hfd : FiniteDimensional LL ↥(DcrisL PD T.ρ (W.emb c))) (k : ℤ) : 0 ≤ multV PD T.ρ τ k := by
  obtain ⟨-, hdim⟩ := hFD hA T hT c τ hτ
  have h1 := hdim k (k + 1) (by omega)
  have hI : Finset.Ico k (k + 1) = {k} := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_singleton]
    omega
  rw [hI, Finset.sum_singleton] at h1

  have hle : Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (k + 1) ≤ Formalism.MainNotions.WachCoordinates.FilLev W T c 0 k := by
    unfold Formalism.MainNotions.WachCoordinates.FilLev
    apply Submodule.map_mono
    apply Submodule.map_mono
    apply inf_le_inf_right
    unfold Formalism.WeaklyAdmissibleFiltrations.FilCris
    apply inf_le_inf_left
    apply Submodule.comap_mono
    unfold Formalism.WeaklyAdmissibleFiltrations.FilV
    intro x hx
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
    clear hx
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v w =>
      exact LinearMap.mem_range.mpr ⟨v ⊗ₜ ⟨(w : BdR), PD.Fil_anti k w.2⟩, by simp⟩
    | add y z hy hz =>
      rw [map_add (f := _)]
      exact add_mem hy hz
  haveI := finiteDimensional_filLev W T c hfd k
  have h2 : Module.finrank LL ↥(Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (k + 1)) ≤
      Module.finrank LL ↥(Formalism.MainNotions.WachCoordinates.FilLev W T c 0 k) :=
    LinearMap.finrank_le_finrank_of_injective (f := Submodule.inclusion hle)
      (Submodule.inclusion_injective hle)
  have h3 : ((Module.finrank LL ↥(Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (k + 1)) : ℕ) : ℤ) ≤
      Module.finrank LL ↥(Formalism.MainNotions.WachCoordinates.FilLev W T c 0 k) := by exact_mod_cast h2
  linarith

theorem sum_multV_le [NeZero n] (hFD : Sh.FilDim W) {d : ℕ} {T₁ T₂ : LocLat G Qp LL O}
    {F : LatHom T₁.L T₂.L} {b : ZMod n → ℕ} {S η m : ℕ} (hS : SetCS W d T₁ T₂ F b S η m)
    (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (c : ZMod n) (hc : c ∈ evens n d) (τ : K →ₐ[Qp] LL)
    (hτ : Formalism.MainNotions.LiftingTheory.Over W τ c) (a : ℕ) (ha : a < b c) :
    ∑ k ∈ Finset.Ico (-(a : ℤ)) 0, multV PD T₂.ρ τ k ≤ (m : ℤ) := by
  have hjump := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_jumps₂ W hE hC hQ hS c τ hτ
  have hfd := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fd_letter₂ W hS c
  have hT₂ : IsCrys PD T₂.ρ := hS.2.2.2.2.2.1.2.1
  have hev : (c.val + d) % 2 = 0 := by simpa [evens] using hc
  rw [← Finset.sum_filter_of_ne (p := fun k => k ∈ Finset.Icc (-(η : ℤ)) η)]
  · calc ∑ k ∈ (Finset.Ico (-(a : ℤ)) 0).filter (fun k => k ∈ Finset.Icc (-(η : ℤ)) η), multV PD T₂.ρ τ k
        ≤ ∑ k ∈ Finset.Icc (-(η : ℤ)) η, multV PD T₂.ρ τ k :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => (Finset.mem_filter.1 hk).2)
            (fun k _ _ => multV_nonneg' W T₂ hFD hS.1 hT₂ c τ hτ hfd k)
      _ ≤ (m : ℤ) := hS.2.2.2.2.2.2.2.1 c τ hτ
  · intro k hk hne
    have hj : IsJumpV PD T₂.ρ τ k := by
      by_contra hnj
      exact hne (Formalism.MainNotions.N.Pv.LocalLengthBound.rk_multV_of_not_jump PD T₂.ρ τ k hnj)
    have hw := hjump k hj
    simp only [Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS, hev, if_true, Set.mem_union, Set.mem_Icc] at hw
    have hk' := Finset.mem_Ico.1 hk
    simp only [Finset.mem_Icc]
    omega

theorem step1Pass_pass [NeZero n] (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hT : IsCrys PD T.ρ) (ζ : LL)
    (hζ : IsPrimitiveRoot ζ PD.p) (hEx : Sh.ExpRules W) (hER : Sh.ExpRing W) (hK : Sh.LemK W)
    (hFD : Sh.FilDim W) (c : ZMod n) (τ : K →ₐ[Qp] LL) (hτ : Formalism.MainNotions.LiftingTheory.Over W τ c)
    (hfd : FiniteDimensional LL ↥(DcrisL PD T.ρ (W.emb c))) [IsDomain O] [IsPrincipalIdealRing O]
    [IsFractionRing O LL] {FF : Type} [AddCommGroup FF] [Module O FF] [Module.Finite O FF]
    (u : FF →ₗ[O] W.DD T) (a m : ℕ)
    (hu : ∀ f, Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (u f) ∧ Formalism.MainNotions.LiftingTheory.qp W ^ a • u f ∈ W.N T ∧
      Formalism.MainNotions.CrystallineLiftingInputs.InPN W T 1 (W.γ T (u f) - u f))
    (hdim : ∑ k ∈ Finset.Ico (-(a : ℤ)) 0, multV PD T.ρ τ k ≤ (m : ℤ)) :
    (∀ (lenO : ℕ∞) (cc : ℝ) (A : Submodule O FF),
      ∃ B, PChain lenO m cc A B 1 0 ∧ ∀ f ∈ B, u f ∈ W.N T) ∧ (m = 0 → ∀ f, u f ∈ W.N T) := by
  have hlev : W.lev c ζ (Formalism.MainNotions.LiftingTheory.qp W ^ a) ≠ 0 := by
    obtain ⟨⟨w, hw, hq⟩, -, -⟩ := hER hA c ζ hζ
    rw [map_pow, hq, mul_pow]
    exact mul_ne_zero (pow_ne_zero _ hw.ne_zero) (pow_ne_zero _ PowerSeries.X_ne_zero)
  have R := hEx hA T hT c ζ hζ
  have hex : ∀ f, ∃! d, Sh.IsExp W T c ζ (u f) d := fun f => R.1 (u f) _ (hu f).2.1 hlev
  choose ex hexs huniq using hex
  have ex_add : ∀ f g, ex (f + g) = ex f + ex g := fun f g =>
    (huniq (f + g) _ (by rw [map_add (f := _)]; exact R.2.2.1 _ _ _ _ (hexs f) (hexs g))).symm
  have ex_smul : ∀ (r : O) f, ex (r • f) = fun k => algebraMap O LL r • ex f k := fun r f =>
    (huniq (r • f) _ (by rw [map_smul]; exact R.2.2.2.1 r _ _ (hexs f))).symm
  set F0 := Formalism.MainNotions.WachCoordinates.FilLev W T c 0 0 with hF0
  set Fa := Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (-(a : ℤ)) with hFa
  let φ : FF →+ (T.V ⊗[Qp] BdR) ⧸ F0 :=
    AddMonoidHom.mk' (fun f => Submodule.Quotient.mk (ex f 0)) (fun f g => by
      simp only [ex_add, Pi.add_apply, Submodule.Quotient.mk_add])
  have hφ : ∀ (r : O) f, φ (r • f) = algebraMap O LL r • φ f := by
    intro r f
    simp only [φ, AddMonoidHom.mk'_apply, ex_smul, Submodule.Quotient.mk_smul]
  have hLK : ∀ f, ex f 0 ∈ Fa ∧ (u f ∈ W.N T ↔ ex f 0 ∈ F0) := by
    intro f
    have hj : ∃ j : ℕ, ((PD.p : ℕ) : O) ^ j • (W.γ T (u f) - u f) ∈ W.N T := by
      obtain ⟨y, hy, -, he⟩ := (hu f).2.2
      exact ⟨0, by rw [pow_zero, one_smul, he]; exact (W.N T).smul_mem _ hy⟩
    exact (hK hA T hT c ζ hζ (u f) (ex f) (hu f).1 (hexs f) hj).2 a (hu f).2.1
  have hker : ∀ f, φ f = 0 ↔ u f ∈ W.N T := by
    intro f
    rw [(hLK f).2]
    exact Submodule.Quotient.mk_eq_zero _
  have := finiteDimensional_filLev W T c hfd (-(a : ℤ))
  have := finiteDimensional_filLev W T c hfd 0
  let Aq := Fa.map F0.mkQ
  have hle : F0 ≤ Fa := Formalism.MainNotions.UnusedSlot80.LevR.filLev_anti W T c 0 (by omega : -(a : ℤ) ≤ 0)
  have hAq : finrank LL ↥Aq ≤ m := by
    let g := F0.mkQ ∘ₗ Fa.subtype
    have hr : LinearMap.range g = Aq := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    have hk : LinearMap.ker g = F0.comap Fa.subtype := by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ]
    have h1 := LinearMap.finrank_range_add_finrank_ker g
    rw [hr, hk, (Submodule.comapSubtypeEquivOfLe hle).finrank_eq] at h1
    have h2 := (hFD hA T hT c τ hτ).2 (-(a : ℤ)) 0 (by omega)
    rw [← hF0, ← hFa] at h2
    omega
  have hrange : ∀ f, φ f ∈ Aq := fun f => Submodule.mem_map_of_mem (hLK f).1
  refine ⟨fun lenO cc A => ?_, fun hm0 f => ?_⟩
  · let φA : ↥A →+ (T.V ⊗[Qp] BdR) ⧸ F0 := φ.comp A.subtype.toAddMonoidHom
    have hφA : ∀ (r : O) (x : ↥A), φA (r • x) = algebraMap O LL r • φA x := fun r x => hφ r x
    have hm : finrank LL ↥(Submodule.span LL (Set.range φA)) ≤ m := by
      have : FiniteDimensional LL ↥Aq := inferInstance
      refine le_trans (Submodule.finrank_mono ?_) hAq
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact hrange x
    refine ⟨Formalism.MainNotions.N.Pv.LocalLengthBound.zeroSub A φA hφA,
      Formalism.MainNotions.N.Pv.LocalLengthBound.pchain_of_gen (Formalism.MainNotions.N.Pv.LocalLengthBound.pstep_rank A φA hφA hm), ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact (hker _).1 hy
  · subst hm0
    have h0 : Aq = ⊥ := Submodule.finrank_eq_zero.1 (by omega)
    have := hrange f
    rw [h0, Submodule.mem_bot] at this
    exact (hker f).1 this

end Pass

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RToolModDStab
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

open Polynomial

section DStab

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem γD_smul' (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  show W.γD T g (a • x) = letγ (W.γ₀ g) a • W.γD T g x
  rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul]

theorem rToolMod_geom (a : LetA O n) (m : ℕ) : ∃ g : LetA O n, (1 + a) ^ m = 1 + a * g := by
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
    obtain ⟨g, hg⟩ := ih
    exact ⟨1 + g + a * g, by rw [pow_succ, hg]; ring⟩

theorem rToolMod_unit (hπ : ∃ w : (LetA O n)ˣ, W.π₀ = (w : LetA O n) * letπ ^ (PD.p - 1))
    (t : LetA O n) (m : ℕ) : IsUnit ((1 + W.π₀ * t) ^ m) := by
  obtain ⟨w, hw⟩ := hπ
  have hp : 2 ≤ PD.p := by
    by_contra h
    have hv := W.v_l
    rcases (show PD.p = 0 ∨ PD.p = 1 by omega) with h0 | h0 <;> rw [h0] at hv
    · rw [Nat.cast_zero, AddValuation.map_zero] at hv
      exact WithTop.top_ne_coe (show (⊤ : WithTop ℚ) = ((1 : ℚ) : WithTop ℚ) from hv)
    · rw [Nat.cast_one, AddValuation.map_one] at hv
      have h01 : ((0 : ℚ) : WithTop ℚ) = ((1 : ℚ) : WithTop ℚ) := hv
      exact absurd (WithTop.coe_inj.mp h01) (by norm_num)
  have hp1 : PD.p - 1 ≠ 0 := by omega
  refine IsUnit.pow m ?_
  refine Pi.isUnit_iff.mpr fun i => ?_
  refine PowerSeries.isUnit_iff_constantCoeff.mpr ?_
  simp [hw, letπ, zero_pow hp1]

theorem rToolMod_qi_q (hqU : IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W))) (m : ℕ)
    (x : W.DD T) :
    Ring.inverse (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) ^ m • (Formalism.MainNotions.LiftingTheory.qp W ^ m • x) = x := by
  rw [← algebraMap_smul W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ m) x, smul_smul, map_pow, ← mul_pow,
    Ring.inverse_mul_cancel _ hqU, one_pow, one_smul]

theorem rToolMod_dStab [NeZero n] (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) : DerivationPreservesQLattice W := by
  unfold DerivationPreservesQLattice
  intro hA T' hT i k x hx
  obtain ⟨hbij, hs, hp2⟩ := hA
  have hfin : Module.finrank K₀ K = 1 := by
    rw [← (LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hbij).finrank_eq, Module.finrank_self]
  obtain ⟨-, -, h9⟩ := hP9 T' hT hs hp2
  obtain ⟨hring, hmod⟩ := h9 hfin
  obtain ⟨-, hmod2⟩ := hmod
  obtain ⟨hπΔ, -, ⟨w₁, hw₁⟩, -, -, -, ⟨w₂, hw₂⟩, -⟩ := hring
  have hΔπ : ∀ δ ∈ W.DelF, W.γA δ W.π₀ = W.π₀ := hπΔ
  have hEat : Formalism.MainNotions.DeltaInvariantLattices.Eat (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) W.π₀ =
      Formalism.MainNotions.LiftingTheory.qp W := by
    funext j
    simp [Formalism.MainNotions.DeltaInvariantLattices.Eat, Formalism.MainNotions.LiftingTheory.qp]
  have hγπ : W.γA W.gam W.π₀ = W.π₀ + (w₂ : LetA O n) * W.π₀ * Formalism.MainNotions.LiftingTheory.qp W := by
    rw [← hEat, ← hw₂]; ring
  have hγq : W.γA W.gam (Formalism.MainNotions.LiftingTheory.qp W) =
      Formalism.MainNotions.LiftingTheory.qp W * (1 + W.π₀ * (w₂ : LetA O n)) := by
    have e1 : W.γA W.gam (Formalism.MainNotions.LiftingTheory.qp W) = W.γA W.gam W.π₀ + ((PD.p : ℕ) : LetA O n) := by
      simp only [Formalism.MainNotions.LiftingTheory.qp, map_add (f := _), map_natCast]
    rw [e1, hγπ]
    simp only [Formalism.MainNotions.LiftingTheory.qp]
    ring
  have hΔq : ∀ δ ∈ W.DelF, W.γA δ (Formalism.MainNotions.LiftingTheory.qp W) = Formalism.MainNotions.LiftingTheory.qp W := by
    intro δ hδ
    simp only [Formalism.MainNotions.LiftingTheory.qp, map_add (f := _), map_natCast, hΔπ δ hδ]
  have ha : IsUnit (algebraMap (LetA O n) W.EE W.π₀) := by
    rw [hw₁, map_mul, map_pow]
    exact (w₁.isUnit.map _).mul (W.EE_π.pow _)
  have hqU : IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) := by
    haveI := W.EE_complete
    have hI : ((PD.p : ℕ) : W.EE) * Ring.inverse (algebraMap (LetA O n) W.EE W.π₀) ∈
        Ideal.span {((PD.p : ℕ) : W.EE)} := Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)
    have hJ : ((PD.p : ℕ) : W.EE) * Ring.inverse (algebraMap (LetA O n) W.EE W.π₀) ∈
        (⊥ : Ideal W.EE).jacobson := by
      first
        | exact IsAdicComplete.le_jacobson_bot (Ideal.span {((PD.p : ℕ) : W.EE)}) hI
        | exact IsAdicComplete.le_jacobson_bot (I := Ideal.span {((PD.p : ℕ) : W.EE)}) hI
        | exact HenselianRing.jac (I := Ideal.span {((PD.p : ℕ) : W.EE)}) hI
    have h1 := Ideal.mem_jacobson_bot.mp hJ 1
    have hinv := Ring.mul_inverse_cancel _ ha
    have h2 : algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W) = algebraMap (LetA O n) W.EE W.π₀ *
        (((PD.p : ℕ) : W.EE) * Ring.inverse (algebraMap (LetA O n) W.EE W.π₀) * 1 + 1) := by
      simp only [Formalism.MainNotions.LiftingTheory.qp, map_add (f := _), map_natCast]
      linear_combination (-((PD.p : ℕ) : W.EE)) * hinv
    rw [h2]; exact ha.mul h1
  obtain ⟨e, he⟩ : ∃ e, e = Ring.inverse (algebraMap (LetA O n) W.EE W.π₀) := ⟨_, rfl⟩
  have hcan1 : ∀ z : W.DD T', W.π₀ • (e • z) = z := by
    intro z
    rw [he, ← algebraMap_smul W.EE W.π₀, smul_smul, Ring.mul_inverse_cancel _ ha, one_smul]
  have hcan2 : ∀ z : W.DD T', e • (W.π₀ • z) = z := by
    intro z
    rw [he, ← algebraMap_smul W.EE W.π₀ z, smul_smul, Ring.inverse_mul_cancel _ ha, one_smul]
  have hinj : ∀ z₁ z₂ : W.DD T', W.π₀ • z₁ = W.π₀ • z₂ → z₁ = z₂ := by
    intro z₁ z₂ h; rw [← hcan2 z₁, h, hcan2]
  have hcomm : ∀ (b : LetA O n) (z : W.DD T'), b • (e • z) = e • (b • z) := by
    intro b z
    rw [← algebraMap_smul W.EE b (e • z), ← algebraMap_smul W.EE b z, smul_smul, smul_smul, mul_comm]
  have hγE : ∀ δ ∈ W.DelF, W.γE δ e = e := by
    intro δ hδ
    have h3 : W.γE δ (algebraMap (LetA O n) W.EE W.π₀) = algebraMap (LetA O n) W.EE W.π₀ := by
      rw [W.γE_ext]; exact congrArg (algebraMap (LetA O n) W.EE) (hΔπ δ hδ)
    rw [he]
    calc W.γE δ (Ring.inverse (algebraMap (LetA O n) W.EE W.π₀))
        = W.γE δ (Ring.inverse (algebraMap (LetA O n) W.EE W.π₀)) *
          (algebraMap (LetA O n) W.EE W.π₀ * Ring.inverse (algebraMap (LetA O n) W.EE W.π₀)) := by
          rw [Ring.mul_inverse_cancel _ ha, mul_one]
      _ = W.γE δ (Ring.inverse (algebraMap (LetA O n) W.EE W.π₀) * algebraMap (LetA O n) W.EE W.π₀) *
          Ring.inverse (algebraMap (LetA O n) W.EE W.π₀) := by rw [map_mul, h3]; ring
      _ = Ring.inverse (algebraMap (LetA O n) W.EE W.π₀) := by
          rw [Ring.inverse_mul_cancel _ ha, map_one, one_mul]
  have hγsm : ∀ (g : W.Gam) (b : LetA O n) (z : W.DD T'),
      W.γD T' g (b • z) = W.γA g b • W.γD T' g z := γD_smul' W T'
  have hdOp : ∀ z, Formalism.MainNotions.CrystallineLiftingInputs.dOp W T' z = e • (W.γD T' W.gam z - z) := fun z => by rw [he]; rfl
  have hγy : ∀ (m : ℕ) (z : W.DD T'), W.γD T' W.gam (Formalism.MainNotions.LiftingTheory.qp W ^ m • z) =
      (1 + W.π₀ * (w₂ : LetA O n)) ^ m • (Formalism.MainNotions.LiftingTheory.qp W ^ m • W.γD T' W.gam z) := by
    intro m z
    rw [hγsm, map_pow, hγq, mul_pow, smul_smul, mul_comm (Formalism.MainNotions.LiftingTheory.qp W ^ m)]
  obtain ⟨⟨hEx, hΔx⟩, hq⟩ := hx
  have hγE_i : W.γA W.gam (letE i : LetA O n) = letE i := by
    funext j
    show W.γ₀ W.gam ((letE i : LetA O n) j) = (letE i : LetA O n) j
    simp only [letE, Pi.single_apply]
    split_ifs <;> simp
  unfold Formalism.MainNotions.CrystallineLiftingInputs.InQN Formalism.MainNotions.CrystallineLiftingInputs.DL
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hEγ : (letE i : LetA O n) • W.γD T' W.gam x = W.γD T' W.gam x := by
      rw [← hγE_i, ← hγsm, hEx]
    rw [hdOp, hcomm, smul_sub, hEγ, hEx]
  · intro δ hδ
    rw [hdOp, W.γD_smul, hγE δ hδ, map_sub, ← W.γD_mul, mul_comm, W.γD_mul, hΔx δ hδ]
  · split_ifs at hq ⊢ with hk
    · obtain ⟨g, hg⟩ := rToolMod_geom (W.π₀ * (w₂ : LetA O n)) k.toNat
      have hu := rToolMod_unit W ⟨w₁, hw₁⟩ (w₂ : LetA O n) k.toNat
      have hpg : W.π₀ * ((w₂ : LetA O n) * g) = (1 + W.π₀ * (w₂ : LetA O n)) ^ k.toNat - 1 := by
        rw [hg]; ring
      have hyΔ : Formalism.MainNotions.LiftingTheory.qp W ^ k.toNat • x ∈ W.NΔ T' :=
        show Formalism.MainNotions.LiftingTheory.qp W ^ k.toNat • x ∈ W.N T' ∧ ∀ δ ∈ W.DelF,
            W.γD T' δ (Formalism.MainNotions.LiftingTheory.qp W ^ k.toNat • x) = Formalism.MainNotions.LiftingTheory.qp W ^ k.toNat • x from
          ⟨hq, fun δ hδ => by rw [hγsm, map_pow, hΔq δ hδ, hΔx δ hδ]⟩
      obtain ⟨x', ⟨hx'N, -⟩, hx'⟩ := hmod2 _ hyΔ
      have hx'' : W.γD T' W.gam (Formalism.MainNotions.LiftingTheory.qp W ^ k.toNat • x) - Formalism.MainNotions.LiftingTheory.qp W ^ k.toNat • x =
          W.π₀ • x' := hx'
      have key : Formalism.MainNotions.LiftingTheory.qp W ^ k.toNat • Formalism.MainNotions.CrystallineLiftingInputs.dOp W T' x = (↑hu.unit⁻¹ : LetA O n) •
          (x' - ((w₂ : LetA O n) * g) • (Formalism.MainNotions.LiftingTheory.qp W ^ k.toNat • x)) := by
        apply hinj
        rw [hdOp, smul_comm W.π₀ (Formalism.MainNotions.LiftingTheory.qp W ^ k.toNat), hcan1,
          smul_comm W.π₀ (↑hu.unit⁻¹ : LetA O n), smul_sub W.π₀, ← hx'', hγy, smul_smul W.π₀, hpg,
          sub_smul, one_smul]
        simp only [smul_sub, smul_smul, ← mul_assoc, hu.val_inv_mul, one_mul]
        abel
      rw [key]
      exact (W.N T').smul_mem _ ((W.N T').sub_mem hx'N ((W.N T').smul_mem _ hq))
    · obtain ⟨y, hyN, rfl⟩ := hq
      obtain ⟨g, hg⟩ := rToolMod_geom (W.π₀ * (w₂ : LetA O n)) (-k).toNat
      have hpg : W.π₀ * ((w₂ : LetA O n) * g) = (1 + W.π₀ * (w₂ : LetA O n)) ^ (-k).toNat - 1 := by
        rw [hg]; ring
      have hyΔ' : ∀ δ ∈ W.DelF, W.γD T' δ y = y := by
        intro δ hδ
        have h1 := hΔx δ hδ
        rw [hγsm, map_pow, hΔq δ hδ] at h1
        rw [← rToolMod_qi_q W T' hqU (-k).toNat (W.γD T' δ y), h1, rToolMod_qi_q W T' hqU]
      have hyΔ : y ∈ W.NΔ T' :=
        show y ∈ W.N T' ∧ ∀ δ ∈ W.DelF, W.γD T' δ y = y from ⟨hyN, hyΔ'⟩
      obtain ⟨x', ⟨hx'N, -⟩, hx'⟩ := hmod2 _ hyΔ
      have hx'' : W.γD T' W.gam y - y = W.π₀ • x' := hx'
      refine ⟨(1 + W.π₀ * (w₂ : LetA O n)) ^ (-k).toNat • x' + ((w₂ : LetA O n) * g) • y,
        (W.N T').add_mem ((W.N T').smul_mem _ hx'N) ((W.N T').smul_mem _ hyN), ?_⟩
      apply hinj
      rw [hdOp, hcan1, hγy, smul_comm W.π₀ (Formalism.MainNotions.LiftingTheory.qp W ^ (-k).toNat), smul_add W.π₀,
        smul_comm W.π₀ ((1 + W.π₀ * (w₂ : LetA O n)) ^ (-k).toNat), ← hx'', smul_smul W.π₀, hpg,
        sub_smul, one_smul]
      simp only [smul_sub, smul_add, smul_smul, mul_comm]
      abel

end DStab

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionFree
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

def UnivLinkStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (Fo : FonOf D.loc D.locA HW), HerrClassMapsLocal D HW Fo → dvdR →
    invLiftR D HW → classMapR D HW → frameR D HW → modelFR D HW → u1R D HW → kapPiR D HW →
    u2R D HW → DownSlotProposition D HW → UpSlotProposition D HW → MixedSlotProposition D HW → univR D HW

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionHypothesis
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

def FirstFrameOfModels : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    adm1 D HW F Cm → DdRFull D → DiRank D HW F Cm → modelLR D HW → modelFR D HW → u1R D HW

theorem first_frame_of_models (hL : FirstFrameOfModels) (hML : ModelLStep) :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
      DdRFull D → DiRank D HW F Cm → Adm1 D HW F Cm CA CB CK → modelFR D HW → u1R D HW :=
  fun D HW F Cm CA CB CK hd hr hA hMF => hL D HW F Cm hA.1 hd hr (hML D HW F Cm CA CB CK hA) hMF

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.SecondRankCount
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def SecondRankCount (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' : ℕ) (c : ZMod n) : Prop :=
  ∀ S : Submodule O (LcQ W T π' c),
    finrank O (IIrest W T Pt π' Eπ h' c S) ≤ (finrank K₀ K + 1) * finrank O S

end Local

def SecondRankCountAll (D : D7) (HW : HWOf D.loc) : Prop :=
  recU D HW fun l _ K LL hG π' E =>
    ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (h' : ℕ), 1 ≤ h' → IsCrys ((D.loc l).PD K) T.ρ →
      (∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (Set.Icc (-(h' : ℤ)) h')) →
      ∀ c, SecondRankCount ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' c

def SecondRankHypothesis : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → modelLR D HW → SecondRankCountAll D HW

def SecondPropositionOfRank : Prop := ∀ (D : D7) (HW : HWOf D.loc), modelQR D HW → SecondRankCountAll D HW → u2R D HW

theorem second_proposition_of_models (hL : SecondPropositionOfRank) (hQ : ModelQStep) (hR : SecondRankHypothesis) (hML : ModelLStep) : SecondPropositionHypothesis :=
  fun D HW F Cm CA CB CK hA =>
    hL D HW (hQ D HW F Cm CA CB CK hA) (hR D HW F Cm CA CB CK hA (hML D HW F Cm CA CB CK hA))

end Formalism.MainNotions.N.Ln34

end
end

