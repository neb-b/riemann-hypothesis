module

public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0015
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfPhi
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0016
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.PiNSOfPi
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0022

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfBeta
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
    {W : LocWach PD LL O v n} {T : LocLat G Qp LL O}

theorem framepf_smulLA_eq (π' : LetA O n) (c : ZMod n) (a : LetA O n) (z : W.EE ⊗[O] LcQ W T π' c) :
    smulLA W T π' c a z = algebraMap (LetA O n) W.EE a • z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e ℓ => rw [framepf_smulLA_tmul, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => rw [map_add (f := _), hx, hy, smul_add]

variable (Bs : FramepfBas W T) (π' : LetA O n) (c : ZMod n)
    (hπ0 : ∀ j, PowerSeries.constantCoeff (π' j) = 0)
    (hΔπ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hR2 : ∀ a : LetA O n, a ∈ W.AΔ → ∃! f : ZMod n → PowerSeries O,
      ∀ j, a j = PowerSeries.subst (π' j) (f j))
    (γ0 : ∀ δ ∈ W.DelF, PowerSeries.constantCoeff (W.γ₀ δ PowerSeries.X) = 0)
    (hu : IsUnit (algebraMap (LetA O n) W.EE π'))

include hπ0 hΔπ γ0 in
theorem framepf_φA_ι_mem (g : PowerSeries O) : W.φA (framepf_ι π' (c - 1) g) ∈ W.AΔ := by
  intro δ hδ
  rw [← LocWach.φA_γA, framepf_ι_Δ π' hπ0 hΔπ γ0 _ g δ hδ]

theorem framepf_φD_vec (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (k : Fin Bs.r) :
    W.φD T (framepf_vec Bs π' (c - 1) H k) =
      ∑ m, W.φA (framepf_ι π' (c - 1) (H m k)) • W.φD T (Bs.b m) := by
  unfold framepf_vec
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun m _ => framepf_φD_smul _ _

def framepf_ebar (j : Fin Bs.r) : LcQ W T π' c :=
  (framepf_Lbas Bs π' c hπ0 hΔπ hR2 γ0 hu).symm (Pi.single j 1)

theorem framepf_hh_ebar (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (j : Fin Bs.r) :
    framepf_hh Bs π' c hπ0 hΔπ hR2 γ0 hu H (framepf_ebar Bs π' c hπ0 hΔπ hR2 γ0 hu j) =
      framepf_vec Bs π' (c - 1) H j := by
  unfold framepf_hh framepf_ebar
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    Fintype.linearCombination_apply_single, one_smul]

def framepf_Ψβ (βφ : Module.Basis (Fin Bs.r) W.EE (W.DD T)) (F : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) :
    W.DD T →ₗ[W.EE] W.EE ⊗[O] LcQ W T π' c :=
  βφ.constr W.EE fun k => ∑ j, algebraMap (LetA O n) W.EE (W.φA (framepf_ι π' (c - 1) (F j k))) ⊗ₜ
    framepf_ebar Bs π' c hπ0 hΔπ hR2 γ0 hu j

variable (βφ : Module.Basis (Fin Bs.r) W.EE (W.DD T)) (hβφ : ∀ k, βφ k = W.φD T (Bs.b k))

include hβφ in
theorem framepf_Ψβ_sum (F : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (a : Fin Bs.r → LetA O n) :
    framepf_Ψβ Bs π' c hπ0 hΔπ hR2 γ0 hu βφ F (∑ k, a k • W.φD T (Bs.b k)) =
      ∑ j, algebraMap (LetA O n) W.EE (∑ k, a k * W.φA (framepf_ι π' (c - 1) (F j k))) ⊗ₜ
        framepf_ebar Bs π' c hπ0 hΔπ hR2 γ0 hu j := by
  have e1 : ∀ k, framepf_Ψβ Bs π' c hπ0 hΔπ hR2 γ0 hu βφ F (a k • W.φD T (Bs.b k)) =
      ∑ j, algebraMap (LetA O n) W.EE (a k * W.φA (framepf_ι π' (c - 1) (F j k))) ⊗ₜ
        framepf_ebar Bs π' c hπ0 hΔπ hR2 γ0 hu j := by
    intro k
    rw [← algebraMap_smul W.EE (a k), LinearMap.map_smul, ← hβφ k]
    unfold framepf_Ψβ
    rw [Module.Basis.constr_basis, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.smul_tmul', smul_eq_mul, ← map_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_congr rfl fun k _ => e1 k, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← TensorProduct.sum_tmul, ← map_sum]


include hπ0 hΔπ γ0 hβφ in
theorem framepf_Ψβ_Pc (hT : IsCrys PD T.ρ) (F : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O))
    (p : W.DD T) (hp : p ∈ PcS W T c) :
    ∃ t, framepf_Ψβ Bs π' c hπ0 hΔπ hR2 γ0 hu βφ F p = toLA W T π' c ⊤ t := by
  obtain ⟨a, haΔ, hac, hap⟩ := framepf_Pc_coord Bs hT c p hp
  have hmem : ∀ j, ∑ k, a k * W.φA (framepf_ι π' (c - 1) (F j k)) ∈ W.AΔ := fun j =>
    Subalgebra.sum_mem _ fun k _ => Subalgebra.mul_mem _ (haΔ k) (framepf_φA_ι_mem π' c hπ0 hΔπ γ0 _)
  refine ⟨∑ j, (⟨_, hmem j⟩ : ↥W.AΔ) ⊗ₜ (⟨framepf_ebar Bs π' c hπ0 hΔπ hR2 γ0 hu j, trivial⟩ :
    ↥(⊤ : Submodule O (LcQ W T π' c))), ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hap, framepf_Ψβ_sum Bs π' c hπ0 hΔπ hR2 γ0 hu βφ hβφ, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [framepf_toLA_tmul]
  congr 2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_assoc, hac k]

variable (Eπ : LetA O n) (hEu : IsUnit (algebraMap (LetA O n) W.EE Eπ))
    (hEΔ : ∀ δ ∈ W.DelF, W.γA δ Eπ = Eπ) (h' M : ℕ)


include hπ0 hΔπ γ0 hβφ hEΔ in
theorem framepf_Ψβ_Lam (hT : IsCrys PD T.ρ) (F : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O))
    (y : W.DD T) (hy : y ∈ LamPS W T Eπ h' c) :
    framepf_Ψβ Bs π' c hπ0 hΔπ hR2 γ0 hu βφ F y ∈ LamLA W T π' Eπ h' c ⊤ := by
  rw [mem_LamPS] at hy
  obtain ⟨h1, hΔ, hl⟩ := hy
  have hP : Eπ ^ h' • y ∈ PcS W T c := by
    unfold PcS
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨(Submodule.restrictScalars_mem _ _ _).2 h1, ?_⟩, ?_⟩
    · rw [mem_DelS]
      intro δ hδ
      rw [gradNPf_γD_smul, map_pow, hEΔ δ hδ, hΔ δ hδ]
    · rw [mem_letS, smul_smul, mul_comm, ← smul_smul, hl]
  obtain ⟨t, ht⟩ := framepf_Ψβ_Pc Bs π' c hπ0 hΔπ hR2 γ0 hu βφ hβφ hT F _ hP
  refine Submodule.mem_comap.2 ⟨t, ?_⟩
  rw [← ht, framepf_smulLA_eq, ← LinearMap.map_smul, algebraMap_smul]


include hπ0 hΔπ γ0 hβφ in
theorem framepf_Ψβ_J (hT : IsCrys PD T.ρ) (F : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O))
    (y : W.DD T) (hy : y ∈ JP W T π' Eπ h' M c) :
    framepf_Ψβ Bs π' c hπ0 hΔπ hR2 γ0 hu βφ F y ∈ JLA W T π' Eπ h' M c := by
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.1 hy
  obtain ⟨t, ht⟩ := framepf_Ψβ_Pc Bs π' c hπ0 hΔπ hR2 γ0 hu βφ hβφ hT F p hp
  refine Submodule.mem_map.2 ⟨_, ⟨t, rfl⟩, ?_⟩
  rw [framepf_smulLA_eq, ← ht, ← LinearMap.map_smul, algebraMap_smul]
  rfl

include hπ0 in
theorem framepf_ι_X_pow_mul (k : ℕ) (g : PowerSeries O) :
    framepf_ι π' (c - 1) (PowerSeries.X ^ k * g) = π' ^ k * framepf_ι π' (c - 1) g := by
  induction k with
  | zero => rw [pow_zero, one_mul, pow_zero, one_mul]
  | succ k ih =>
    rw [pow_succ', mul_assoc, framepf_ι_mul π' (c - 1) (hπ0 _), ih, framepf_ι_X π' (c - 1) (hπ0 _),
      pow_succ']
    have := framepf_letE_ι π' (c - 1) hπ0 g
    calc letE (c - 1) * π' * (π' ^ k * framepf_ι π' (c - 1) g)
        = π' * π' ^ k * (letE (c - 1) * framepf_ι π' (c - 1) g) := by ring
      _ = π' * π' ^ k * framepf_ι π' (c - 1) g := by rw [this]


include hπ0 in
theorem framepf_φA_ι_entry (M : ℕ) (lam : O) (K : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O))
    (j k : Fin Bs.r) :
    W.φA (framepf_ι π' (c - 1) ((PowerSeries.C lam • (1 : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) +
      (PowerSeries.X : PowerSeries O) ^ M • K) j k)) =
      (if j = k then algebraMap O (LetA O n) lam * letE c else 0) +
        W.φA π' ^ M * W.φA (framepf_ι π' (c - 1) (K j k)) := by
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
    framepf_ι_add π' (c - 1) (hπ0 _), map_add, framepf_ι_X_pow_mul π' c hπ0, map_mul, map_pow]
  congr 1
  by_cases h : j = k
  · subst h
    rw [Matrix.one_apply_eq, mul_one, framepf_ι_C π' (c - 1) (hπ0 _), map_mul,
      Formalism.MainNotions.LiftingTheory.wmap_φA_letE, AlgHom.commutes, if_pos rfl, mul_comm]
  · rw [Matrix.one_apply_ne h, mul_zero, framepf_ι_zero π' (c - 1) hπ0, map_zero, if_neg h]

include hπ0 in
theorem framepf_φA_ι_matmul (F H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (j k : Fin Bs.r) :
    ∑ m, W.φA (framepf_ι π' (c - 1) (F j m)) * W.φA (framepf_ι π' (c - 1) (H m k)) =
      W.φA (framepf_ι π' (c - 1) ((F * H) j k)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.mul_apply, framepf_ι_sum π' (c - 1) hπ0, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [framepf_ι_mul π' (c - 1) (hπ0 _), map_mul]

end Local

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.LVSmulA
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.UniversalFiltration

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 Formalism.MainNotions.N.Ln34.ModelFPf
open scoped TensorProduct

section Span

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (c : ZMod n) (ζ : LL)

def LV (K : ℕ) (x : W.DD T) : T.V ⊗[Qp] BdR :=
  open Classical in
  if h : W.Q ^ K • W.φD T x ∈ W.N T then W.levN T c ζ ⟨_, h⟩ K else 0

theorem LV_eq (K : ℕ) (x : W.DD T) (h : W.Q ^ K • W.φD T x ∈ W.N T) :
    LV W T c ζ K x = W.levN T c ζ ⟨_, h⟩ K := by
  unfold LV
  rw [dite_eq_left h]

theorem LV_add (K : ℕ) (x y : W.DD T) (hx : W.Q ^ K • W.φD T x ∈ W.N T)
    (hy : W.Q ^ K • W.φD T y ∈ W.N T) : LV W T c ζ K (x + y) = LV W T c ζ K x + LV W T c ζ K y := by
  have hxy : W.Q ^ K • W.φD T (x + y) ∈ W.N T := by
    rw [map_add (f := _), smul_add]
    exact Submodule.add_mem _ hx hy
  rw [LV_eq W T c ζ K _ hxy, LV_eq W T c ζ K _ hx, LV_eq W T c ζ K _ hy]
  rw [show (⟨_, hxy⟩ : ↥(W.N T)) = ⟨_, hx⟩ + ⟨_, hy⟩ from
    Subtype.ext (by simp only [map_add (f := _), smul_add, Submodule.coe_add]), map_add (f := _)]
  rfl

theorem LV_smulA (K : ℕ) (a : LetA O n) (x : W.DD T) (hx : W.Q ^ K • W.φD T x ∈ W.N T)
    (hv : ∀ j : ℤ, j < K → W.levN T c ζ ⟨_, hx⟩ j = 0) :
    W.Q ^ K • W.φD T (a • x) ∈ W.N T ∧
      LV W T c ζ K (a • x) = PowerSeries.constantCoeff (W.lev c ζ (W.φA a)) • LV W T c ζ K x := by
  have e : W.Q ^ K • W.φD T (a • x) = W.φA a • (W.Q ^ K • W.φD T x) := by
    rw [Formalism.MainNotions.LiftingTheory.wmap_φD_smul, smul_comm]
  have hax : W.Q ^ K • W.φD T (a • x) ∈ W.N T := e ▸ Submodule.smul_mem _ _ hx
  refine ⟨hax, ?_⟩
  rw [LV_eq W T c ζ K _ hax, LV_eq W T c ζ K _ hx]
  have hs : (⟨_, hax⟩ : ↥(W.N T)) = W.φA a • (⟨_, hx⟩ : ↥(W.N T)) := Subtype.ext e
  rw [hs, levN_eq_serMul, serMul_eq_sum _ _ K hv K 1 (by omega), Finset.sum_range_one,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp

theorem LV_smulO (K : ℕ) (o : O) (x : W.DD T) (hx : W.Q ^ K • W.φD T x ∈ W.N T) :
    W.Q ^ K • W.φD T (o • x) ∈ W.N T ∧
      LV W T c ζ K (o • x) = algebraMap O LL o • LV W T c ζ K x := by
  have e : W.Q ^ K • W.φD T (o • x) = algebraMap O (LetA O n) o • (W.Q ^ K • W.φD T x) := by
    rw [map_smul, smul_comm, algebraMap_smul]
  have hox : W.Q ^ K • W.φD T (o • x) ∈ W.N T := e ▸ Submodule.smul_mem _ _ hx
  refine ⟨hox, ?_⟩
  rw [LV_eq W T c ζ K _ hox, LV_eq W T c ζ K _ hx]
  have hs : (⟨_, hox⟩ : ↥(W.N T)) = algebraMap O (LetA O n) o • (⟨_, hx⟩ : ↥(W.N T)) := Subtype.ext e
  have hC : algebraMap O (PowerSeries LL) o = PowerSeries.C (algebraMap O LL o) := by
    rw [IsScalarTower.algebraMap_apply O LL (PowerSeries LL)]
    rfl
  rw [hs, levN_eq_serMul, AlgHom.commutes, hC]
  unfold serMul
  rw [finsum_eq_single _ 0]
  · simp
  · intro j hj
    rw [PowerSeries.coeff_C, if_neg hj, zero_smul]

variable {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop}

theorem levN_val (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T) {τ : K →ₐ[Qp] LL} (hPt : Pt c ζ τ)
    (hc0 : PowerSeries.constantCoeff (W.lev c ζ W.Q) = 0) (hc1 : PowerSeries.coeff 1 (W.lev c ζ W.Q) ≠ 0)
    (x : W.DD T) (hxN : x ∈ W.N T) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T) :
    W.levN T c ζ ⟨_, hk⟩ k = PowerSeries.coeff 1 (W.lev c ζ W.Q) ^ k • valAt W T c ζ x := by
  classical
  have hex : ∃ k, W.Q ^ k • W.φD T x ∈ W.N T := ⟨k, hk⟩
  unfold valAt
  rw [dite_eq_left hex]
  have hk0 : Nat.find hex ≤ k := Nat.find_min' hex hk
  have hk0m := Nat.find_spec hex
  have hv : ∀ j : ℤ, j < (Nat.find hex : ℤ) → W.levN T c ζ ⟨_, hk0m⟩ j = 0 :=
    fun j hj => ((hp4.2 c ζ τ hPt).1.1 ⟨x, hxN⟩ _ hk0m j).2 hj
  have hs : (⟨_, hk⟩ : ↥(W.N T)) = W.Q ^ (k - Nat.find hex) • (⟨_, hk0m⟩ : ↥(W.N T)) :=
    Subtype.ext (by
      show W.Q ^ k • W.φD T x = W.Q ^ (k - Nat.find hex) • W.Q ^ Nat.find hex • W.φD T x
      rw [smul_smul, ← pow_add, Nat.sub_add_cancel hk0])
  obtain ⟨B', hB'⟩ := PowerSeries.X_dvd_iff.2 hc0
  have hB0 : PowerSeries.constantCoeff B' = PowerSeries.coeff 1 (W.lev c ζ W.Q) := by
    rw [hB', PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [hs, levN_eq_serMul, serMul_eq_sum _ _ _ hv k (k - Nat.find hex + 1) (by omega),
    Finset.sum_eq_single (k - Nat.find hex)]
  · have e1 : (k : ℤ) - ((k - Nat.find hex : ℕ) : ℤ) = (Nat.find hex : ℤ) := by
      rw [Nat.cast_sub hk0]
      ring
    have hcoef : PowerSeries.coeff (k - Nat.find hex) ((W.lev c ζ W.Q) ^ (k - Nat.find hex)) =
        PowerSeries.coeff 1 (W.lev c ζ W.Q) ^ (k - Nat.find hex) := by
      rw [hB', mul_pow, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [e1, map_pow, hcoef, smul_smul, ← pow_sub₀ _ hc1 hk0]
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [map_pow, pow_vanish' _ hc0 _ j h, zero_smul]
    · rw [hv _ (by omega), smul_zero]
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h

end Span

end Formalism.MainNotions.N.Ln34.UniversalFiltration

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPfE
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.ModelFPf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 TensorProduct

section Core2

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)
    (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' M σ : ℕ) (c : ZMod n) (α : FrA W π' Eπ h' M c) (β : FrB W π' Eπ h' M c)

theorem beta_core (hfr : IsFrame W Pt π' Eπ h' M σ c α β) (hcry : IsCrys PD T.ρ)
    (hjmp : ∀ τ, JumpsInV PD T.ρ τ (Set.Icc (-(h' : ℤ)) h')) (hs : W.s = 1) {w w' : LetA O n}
    (hww : w' * w = 1) (hQ : W.Q = w * Eπ) (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T)
    (hpt : ∀ ζ τ, Pt c ζ τ → ζ ^ PD.p = 1 ∧ ζ ≠ 1)
    (y : W.DD T) (hy : y ∈ LamPS W T Eπ h' c) (hyN : y ∈ W.N T) (x : LA W T π' c)
    (hx : x ∈ LamLA W T π' Eπ h' c ⊤) (hβ : β T ⟨y, hy⟩ = mkLA W T π' Eπ h' M c x hx) :
    x ∈ NLset W T Pt π' Eπ h' c := by
  obtain ⟨m, a, z, hz, heq⟩ := range_rep W T π' c _ hx
  have hrep : IsRepL W T π' Eπ h' c x a z := ⟨hz, heq⟩
  refine ⟨m, a, z, hrep, ?_⟩
  intro τ ζ hPt i
  have hzN : ∀ j, z j ∈ W.N T := fun j => ((mem_NcS W T _ _).1 (hz j)).1
  have hα := (hfr.1 T hcry hjmp).2.2.2.1 y hy x hx hβ
  have hcE := levE_zero W Eπ c hs hww hQ ζ (hpt ζ τ hPt).1 (hpt ζ τ hPt).2
  rcases lt_or_ge i (4 * h') with hi | hi
  · have hpy : ((PD.p : ℕ) : O) ^ (2 * σ) • y ∈ W.N T := Submodule.smul_of_tower_mem _ _ hyN
    have hk : W.Q ^ 0 • (Eπ ^ h' • (((PD.p : ℕ) : O) ^ (2 * σ) • y)) ∈ W.N T := by
      rw [pow_zero, one_smul]
      exact Submodule.smul_mem _ _ hpy
    have hexp := (hfr.1 T hcry hjmp).2.2.2.2.2.2.2.2 τ ζ hPt x hx _ _ hα m a z hrep 0 hk i
      (by simpa using hi)
    have hl1 : W.lev c ζ (W.Q ^ 0) = 1 := by rw [pow_zero, map_one]
    rw [hl1, serMul_one] at hexp
    have hsub : (⟨_, hk⟩ : ↥(W.N T)) = Eπ ^ h' • (⟨_, hpy⟩ : ↥(W.N T)) :=
      Subtype.ext (by
        show W.Q ^ 0 • (Eπ ^ h' • (((PD.p : ℕ) : O) ^ (2 * σ) • y)) =
          Eπ ^ h' • (((PD.p : ℕ) : O) ^ (2 * σ) • y)
        rw [pow_zero, one_smul])
    have hL : W.levN T c ζ ⟨_, hk⟩ i ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ ((h' : ℤ) - i) := by
      rw [hsub, levN_eq_serMul]
      have := serMul_mem (fun i => Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (0 - i)) (FilC_mono_shift T τ 0)
        (W.lev c ζ (Eπ ^ h')) h' (by rw [map_pow]; exact pow_vanish' _ hcE h') _
        (fun i => by
          have := (Submodule.mem_inf.1 (levN_fil W T c hp4 hPt ⟨_, hpy⟩ i)).2
          simpa using this) i
      convert this using 2
      ring
    rw [hexp, ← Nat.cast_smul_eq_nsmul LL] at hL
    exact (Submodule.smul_mem_iff _ (by rw [Nat.cast_pow]; exact pow_ne_zero _ (p_ne_zero W))).1 hL
  · exact FilC_anti T τ (by omega) (ιDi_le_top W T h' c hp4 hPt (hjmp τ) (expS_mem W T c hp4 hPt _ z hzN i))

theorem JLA_le (hs : W.s = 1) {w w' : LetA O n} (hww : w' * w = 1) (hQ : W.Q = w * Eπ)
    (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T) (hpt : ∀ ζ τ, Pt c ζ τ → ζ ^ PD.p = 1 ∧ ζ ≠ 1)
    (hjmp : ∀ τ, JumpsInV PD T.ρ τ (Set.Icc (-(h' : ℤ)) h')) (hπΔ : π' ∈ W.AΔ) (hEΔ : Eπ ∈ W.AΔ)
    (j : ℕ) (hj : j ≤ M) : JLA W T π' Eπ h' M c ≤ piNL W T Pt π' Eπ h' c j := by
  intro u hu
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hu
  obtain ⟨m, a, z, hz, rfl⟩ := range_rep W T π' c v hv
  have hb : π' ^ (M - j) * Eπ ^ (3 * h') ∈ W.AΔ :=
    W.AΔ.mul_mem (W.AΔ.pow_mem hπΔ _) (W.AΔ.pow_mem hEΔ _)
  refine ⟨smulLA W T π' c (π' ^ (M - j) * Eπ ^ (3 * h')) (∑ k, algebraMap (LetA O n) W.EE
    ((letE c : LetA O n) * (a k : LetA O n)) ⊗ₜ mkL W T π' c (z k) (hz k)), ?_, ?_⟩
  · apply Submodule.subset_span
    refine ⟨m, fun k => ⟨Eπ ^ h' * ((π' ^ (M - j) * Eπ ^ (3 * h')) * a k),
      W.AΔ.mul_mem (W.AΔ.pow_mem hEΔ _) (W.AΔ.mul_mem hb (a k).2)⟩, z, ⟨hz, ?_⟩, ?_⟩
    · rw [smulLA_rep, smulLA_rep]
    · intro τ ζ hPt i
      have hzN : ∀ k, z k ∈ W.N T := fun k => ((mem_NcS W T _ _).1 (hz k)).1
      have hcE := levE_zero W Eπ c hs hww hQ ζ (hpt ζ τ hPt).1 (hpt ζ τ hPt).2
      rcases lt_or_ge i (4 * h') with hi | hi
      · unfold expS serC
        refine Submodule.sum_mem _ fun k _ => ?_
        split_ifs with h0
        · have e : Eπ ^ h' * ((π' ^ (M - j) * Eπ ^ (3 * h')) * (a k : LetA O n)) =
              Eπ ^ (4 * h') * (π' ^ (M - j) * a k) := by ring
          show PowerSeries.coeff i.toNat (W.lev c ζ (Eπ ^ h' * ((π' ^ (M - j) * Eπ ^ (3 * h')) *
            (a k : LetA O n)))) • valAt W T c ζ (z k) ∈ _
          rw [e, map_mul, map_pow, pow_vanish _ hcE _ _ _ (by omega), zero_smul]
          exact Submodule.zero_mem _
        · exact Submodule.zero_mem _
      · exact FilC_anti T τ (by omega)
          (ιDi_le_top W T h' c hp4 hPt (hjmp τ) (expS_mem W T c hp4 hPt _ z hzN i))
  · show smulLA W T π' c (π' ^ j) (smulLA W T π' c _ _) = _
    rw [smulLA_smulLA, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hj]

end Core2

end Formalism.MainNotions.N.Ln34.ModelFPf

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U1r2Basis
section
noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace Formalism.MainNotions.N.Ln34.UniversalLiftFrames

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules PowerSeries

theorem u1r2_pt (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : adm1 D HW F Cm) {l : ℕ} [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (ζ : ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ) :
    LevelExpansions.V.PtHyp (W := (HW l).W K 1 LL hG) T c ζ := by
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hz : IsPrimitiveRoot ζ ((D.loc l).PD K).p := by
    rw [hpl]
    exact framepf_pt_prim D HW hG c ζ τ hpt
  obtain ⟨hQ0, hQ1⟩ := framepf_Q_at ((HW l).W K 1 LL hG) hs c ζ hz
  obtain ⟨-, -, -, p4, -⟩ := hA l K 1 LL hG
  have hone : ∃ j : ℕ, IsPrimitiveRoot (1 : ↥LL.1) (((D.loc l).PD K).p ^ j) := ⟨0, by simp⟩
  have hπ1 : ∀ i, PowerSeries.constantCoeff (((HW l).W K 1 LL hG).lev i 1 letπ) = 0 := fun i => by
    rw [CrystallineExponents.cc_lev_pi _ i 1 hone, sub_self]
  have hX : ((HW l).W K 1 LL hG).X = letπ := by simp [LocWach.X, hs]
  refine ⟨hT, ⟨1, by simpa using hz⟩, hz.pow_eq_one, hQ0, hQ1, fun x k hk => ?_,
    fun x hx => ((HW l).W K 1 LL hG).N_φ T x hx⟩
  exact (((p4 T hT).1 (c - 1) 1 ⟨0, one_pow _⟩ (by rw [hX]; exact hπ1 _)).1 x k).2 hk

theorem u1r2_basis (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : adm1 D HW F Cm) {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) :
    ∃ (r : ℕ) (bL : Basis (Fin r) ↥(OL LL) (LcQ ((HW l).W K 1 LL hG) T π' c)) (rep : Fin r → ((HW l).W K 1 LL hG).DD T)
      (hrep : ∀ k, rep k ∈ NcS ((HW l).W K 1 LL hG) T (c - 1)), ∀ k, bL k = mkL ((HW l).W K 1 LL hG) T π' c (rep k) (hrep k) := by
  classical
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hp2 : ((D.loc l).PD K).p ≠ 2 := by rw [hpl]; exact hl
  have p9 := (hA l K 1 LL hG).2.2.2.2.2.2.2.2.1
  have h92 := (p9 T hT hs hp2).2.1
  obtain ⟨π₀, E₀, -, hm⟩ := h92
  obtain ⟨⟨r, b, hbΔ, hbu, hbe⟩, -⟩ := hm
  have hw := hp9.2.2.1
  obtain ⟨w₁, hw₁⟩ := hw
  have hs1 : 1 ≤ sK l K := DescentValuation.u3downPf_sK_pos hl K LL hG
  have hBL := MQ.basis_L ((HW l).W K 1 LL hG) T π' (sK l K) hs1 w₁ hw₁ hp9.2.1 b hbΔ hbu hbe c
  obtain ⟨bL⟩ := hBL
  have hsurj : ∀ k, ∃ y : ((HW l).W K 1 LL hG).DD T, ∃ hy : y ∈ NcS ((HW l).W K 1 LL hG) T (c - 1),
      bL k = mkL ((HW l).W K 1 LL hG) T π' c y hy := by
    intro k
    have hq := Submodule.Quotient.mk_surjective _ (bL k)
    obtain ⟨⟨y, hy⟩, hyk⟩ := hq
    exact ⟨y, hy, hyk.symm⟩
  choose rep hrep hbr using hsurj
  exact ⟨r, bL, rep, hrep, hbr⟩

end Formalism.MainNotions.N.Ln34.UniversalLiftFrames

end
end

