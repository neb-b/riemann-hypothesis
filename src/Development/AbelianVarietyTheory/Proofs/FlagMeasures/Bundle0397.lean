module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0283
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0394
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
public import Formalism.HermitianLattices.HermitianLatticesProofs.MassTelescope
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBoundedBasis
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0382
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0224
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0366
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0251
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0199
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
public import Formalism.FormalDegreeBessel.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalOrbitLatticesInfFrameSpanEq
section
noncomputable section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameSpanLat

variable {D : D7}

theorem localComplementUnitary_fixes_both_frames {Z : LocDat D} {p : PlF D} (P : LocNG.FPair (locH Z p) D.R.rS)
    {g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p} (hg : g ∈ P.UW0) :
    ∀ b, g (P.A.f b) = P.A.f b ∧ g (P.B.f b) = P.B.f b := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx.2
  | one => exact fun _ => ⟨rfl, rfl⟩
  | mul x y _ _ hx hy =>
    intro b
    change x (y _) = _ ∧ x (y _) = _
    rw [(hy b).1, (hy b).2]; exact hx b
  | inv x _ hx =>
    intro b
    refine ⟨?_, ?_⟩
    · change x.symm _ = _
      rw [LinearEquiv.symm_apply_eq, (hx b).1]
    · change x.symm _ = _
      rw [LinearEquiv.symm_apply_eq, (hx b).2]

theorem h_zero_left {Z : LocDat D} {p : PlF D} (y : Vp D p) : (locH Z p).h 0 y = 0 := by
  show LocFacts₂ Z.M p 0 y = 0
  simp [LocFacts₂]

theorem frame_ne_zero {Z : LocDat D} {p : PlF D} (Fr : LocNG.FrameD (locH Z p) D.R.rS) (hT : Fr.T ≠ 0)
    (a : Fin (D.R.rS + 1)) : Fr.f a ≠ 0 := by
  intro h0
  induction a using Fin.lastCases with
  | last =>
    have h1 := Fr.h_zz
    rw [h0, h_zero_left] at h1
    have h2 : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep Fr.T = 0 := neg_eq_zero.mp h1.symm
    exact hT ((map_eq_zero_iff _ (RingHom.injective _)).mp h2)
  | cast i =>
    have h1 := Fr.h_es i i
    rw [h0, h_zero_left, if_pos rfl] at h1
    exact zero_ne_one h1

theorem frFac_unit {p : PlF D} (δ : ∀ p, (D.s.atP p).Fp) (a : Fin (D.R.rS + 1)) (v : Vp D p)
    (hv : frFac δ p a • v ≠ 0) : IsUnit (frFac δ p a) := by
  unfold frFac at hv ⊢
  by_cases hu : IsUnit ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E)) ^
    (D.R.rS - a.val))
  · exact isUnit_ringInverse.mpr hu
  · rw [Ring.inverse_non_unit _ hu, zero_smul] at hv
    exact absurd rfl hv

def fixSub (p : PlF D) (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) : Submodule D.host.E (VS D).V where
  carrier := {u | g (baseChange₂ D p u) = baseChange₂ D p u}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add (f := _)] at *
    rw [ha, hb]
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at *
    rw [baseChange_smul₂, map_smul, ha]

theorem xplus_le {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (S : Submodule D.host.E (VS D).V)
    (h : ∀ a, frame F a ∈ S) : Xplus F ≤ S := by
  show F.fl.X ⊔ Submodule.span _ {F.fl.z} ≤ S
  refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨i, rfl⟩
    have := h i.castSucc
    simpa [frame, FlagG.fvec] using this
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    have := h (Fin.last _)
    simpa [frame, FlagG.fvec] using this

theorem le_of_loc (Z : LocDat D) (Λ₂ : LV D) (h2 : Submodule.IsLattice D.host.E Λ₂) (N : LV D)
    (hN : ∀ z ∈ N, ∀ p, baseChange₂ D p z ∈ lattice₂ D Z.M p Λ₂) : N ≤ Λ₂ := by
  intro x hx
  exact GlobalTheory.GenMass.GlueLoc.mem_of_bcP Z h2.fg (hN x hx)

theorem fix_span {u u' : D.what₂.Word}
    (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS)
    (hB : Based Z FP (Tu D u) (Tu D u') F F') (hR : ∀ p, (FP p).RelG (LocNG.theta (Z.M p))) (p : PlF D)
    {g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p} (hg : g ∈ (FP p).UW0) :
    Xplus F ⊔ Xplus F' ≤ fixSub p g := by
  have hN := (hR p).2.2.2.2.2.2
  refine sup_le (xplus_le F _ fun a => ?_) (xplus_le F' _ fun a => ?_)
  · have hfa := (localComplementUnitary_fixes_both_frames (FP p) hg a).1
    have hne := frame_ne_zero (FP p).A hN.2.1 a
    rw [(hB p).1] at hfa hne
    have hu := frFac_unit Z.δ a _ hne
    show g (baseChange₂ D p (frame F a)) = baseChange₂ D p (frame F a)
    rw [map_smul] at hfa
    exact hu.smul_left_cancel.mp hfa
  · have hfa := (localComplementUnitary_fixes_both_frames (FP p) hg a).2
    have hne := frame_ne_zero (FP p).B hN.2.2.2.1 a
    rw [(hB p).2.1] at hfa hne
    have hu := frFac_unit Z.δ a _ hne
    show g (baseChange₂ D p (frame F' a)) = baseChange₂ D p (frame F' a)
    rw [map_smul] at hfa
    exact hu.smul_left_cancel.mp hfa

theorem inf_span_eq : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λ) → Λ ⊓ toO (VS D) (Xplus F ⊔ Xplus F') = Λ₀ ⊓ toO (VS D) (Xplus F ⊔ Xplus F') := by
  intro D X Y u u' F F' w _ _ Z FP hB hR Λ₀ h0 Λ h1 hloc
  apply le_antisymm
  · refine le_inf (le_of_loc Z Λ₀ h0 _ fun z hz p => ?_) inf_le_right
    obtain ⟨g, hg, himg⟩ := hloc p
    have hfix : g (baseChange₂ D p z) = baseChange₂ D p z := fix_span F F' Z FP hB hR p hg hz.2
    have hm : baseChange₂ D p z ∈ lattice₂ D Z.M p Λ := Submodule.subset_span ⟨z, hz.1, rfl⟩
    rw [← himg] at hm
    obtain ⟨y, hy, hyz⟩ := Submodule.mem_map.1 hm
    have : g y = g (baseChange₂ D p z) := by rw [hfix]; exact hyz
    rw [g.injective this] at hy
    exact hy
  · refine le_inf (le_of_loc Z Λ h1 _ fun z hz p => ?_) inf_le_right
    obtain ⟨g, hg, himg⟩ := hloc p
    have hfix : g (baseChange₂ D p z) = baseChange₂ D p z := fix_span F F' Z FP hB hR p hg hz.2
    have hm : baseChange₂ D p z ∈ lattice₂ D Z.M p Λ₀ := Submodule.subset_span ⟨z, hz.1, rfl⟩
    rw [← himg, ← hfix]
    exact Submodule.mem_map_of_mem hm

end GlobalTheory.FrameSpanLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeanPrimitiveSublatticesGenusDefiniteLattice
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.PrimGenus

section
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]

theorem nondeg_of_pd (h : V →ₗ⋆[K] V →ₗ[K] K) (hp : GlobalTheory.Mass.PD h) : h.Nondegenerate := by
  unfold GlobalTheory.Mass.PD at hp
  have key : ∀ x, h x x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    have hlt := hp (Classical.arbitrary (K →+* ℂ)) x hne
    rw [hx, map_zero, Complex.zero_re] at hlt
    exact lt_irrefl _ hlt
  constructor
  · intro x hx
    exact key x (hx x)
  · intro y hy
    exact key y (hy y)

end

theorem gen_of_cyclic {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] {A B : Submodule R W} (hle : B ≤ A)
    (I : Ideal R) (e : (↥A ⧸ B.comap A.subtype) ≃ₗ[R] (R ⧸ I)) :
    ∃ t : Finset W, t.card ≤ 1 ∧ A = B ⊔ Submodule.span R (t : Set W) := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (e.symm (Ideal.Quotient.mk I 1))
  refine ⟨{(a : W)}, by simp, le_antisymm ?_ ?_⟩
  · intro x hx
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (e (Submodule.Quotient.mk ⟨x, hx⟩))
    have hmk : Ideal.Quotient.mk I r = r • Ideal.Quotient.mk I 1 := by
      rw [Algebra.smul_def, map_one, mul_one]
      rfl
    have h1 : Submodule.Quotient.mk (⟨x, hx⟩ : A) = Submodule.Quotient.mk (p := B.comap A.subtype) (r • a) := by
      rw [Submodule.Quotient.mk_smul, ha, ← LinearEquiv.map_smul, ← hmk, hr, LinearEquiv.symm_apply_apply]
    rw [Submodule.Quotient.eq] at h1
    have h2 : x - r • (a : W) ∈ B := by simpa using h1
    have h3 : x = (x - r • (a : W)) + r • (a : W) := by abel
    rw [h3]
    exact Submodule.add_mem_sup h2 (Submodule.smul_mem _ r (Submodule.subset_span (by simp)))
  · exact sup_le hle (Submodule.span_le.mpr (by simp [a.2]))

theorem exponents (n D k s l : ℝ) (hn : 1 ≤ n) (hD : 1 ≤ D) (hs : 0 ≤ s) :
    n ^ ((k - s) / 2) * (n * D) ^ ((9 * s + 8 + 4 * l) / 2) ≤
      D ^ ((k - 1) / 2) * ((n / D) ^ (k / 2) * (n * D) ^ (5 * s + 5 + 2 * (1 + l))) := by
  have hn0 : 0 < n := by linarith
  have hD0 : 0 < D := by linarith
  have ha : 0 ≤ Real.log n := Real.log_nonneg hn
  have hb : 0 ≤ Real.log D := Real.log_nonneg hD
  simp only [Real.rpow_def_of_pos hn0, Real.rpow_def_of_pos hD0, Real.rpow_def_of_pos (mul_pos hn0 hD0),
    Real.rpow_def_of_pos (div_pos hn0 hD0), Real.log_mul hn0.ne' hD0.ne', Real.log_div hn0.ne' hD0.ne',
    ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg ha hs, mul_nonneg hb hs]

private theorem finrank_eq_two_mul_fDeg (K : Type) [Field K] [NumberField K] [StarRing K] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) :
    Module.finrank ℚ K = 2 * Formalism.HermitianLatticesTheory.fDeg K := by
  haveI := hK.1
  rw [IsTotallyComplex.finrank]
  unfold Formalism.HermitianLatticesTheory.fDeg
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero,
    zero_add]

private theorem mass_bound_rpow_le (K : Type) [Field K] [NumberField K] [StarRing K] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hv : 1 ≤ Formalism.HermitianLatticesTheory.vInv K) :
    1 ≤ (20 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ 2) ^ (2 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) * (6 + cf K)) ∧
    (20 * (Formalism.HermitianLatticesTheory.fDeg K : ℝ) * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ 2) ^ (16 * Formalism.HermitianLatticesTheory.fDeg K) ≤
      (20 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ 2) ^ (2 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) * (6 + cf K)) := by
  have hd := finrank_eq_two_mul_fDeg K hK
  have hfpos : 0 < Formalism.HermitianLatticesTheory.fDeg K := by
    have : 0 < Module.finrank ℚ K := Module.finrank_pos
    omega
  have hf : (1 : ℝ) ≤ (Formalism.HermitianLatticesTheory.fDeg K : ℝ) := by exact_mod_cast hfpos
  have hB : 1 ≤ 20 * (Formalism.HermitianLatticesTheory.fDeg K : ℝ) * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ 2 := by nlinarith
  have hd2 : (2 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by
    rw [hd]
    push_cast
    linarith
  have hl : 1 ≤ Real.logb 2 (Module.finrank ℚ K : ℝ) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
    simpa using hd2
  have hcf : 2 ≤ cf K := by
    unfold cf
    linarith
  refine ⟨Real.one_le_rpow hB (by nlinarith), ?_⟩
  rw [← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le hB
  push_cast
  nlinarith

private theorem laurent_T_unit_zpow_eq_T (T : ℝ) (hT : 2 ≤ T) (k f : ℕ) (hk : 1 ≤ k) :
    (T ^ (2 * f)) ^ (((k : ℝ) - 1) / 2) ≤ ((T ^ k - 1) / (T - 1)) ^ f := by
  have hT0 : 0 ≤ T := by linarith
  have h1 : (T ^ (2 * f)) ^ (((k : ℝ) - 1) / 2) = (T ^ (k - 1)) ^ f := by
    rw [← Real.rpow_natCast T (2 * f), ← Real.rpow_mul hT0, ← pow_mul, ← Real.rpow_natCast]
    congr 1
    push_cast [Nat.cast_sub hk]
    ring
  rw [h1]
  apply pow_le_pow_left₀ (pow_nonneg hT0 _)
  rw [le_div_iff₀ (by linarith)]
  have h2 : (1 : ℝ) ≤ T ^ (k - 1) := one_le_pow₀ (by linarith)
  have h3 : T ^ k = T ^ (k - 1) * T := by
    rw [← pow_succ]
    congr 1
    omega
  rw [h3]
  nlinarith

private theorem le_dual_of_integral_form {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V)
    (hi : ∀ x ∈ L, ∀ y ∈ L, h x y ∈ (1 : Submodule (𝓞 K) K)) : L ≤ Formalism.HermitianLatticesTheory.dual h L := by
  intro x hx
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf]
  intro y hy
  first
  | exact hi x hx y hy
  | exact hi y hy x hx
  | simpa using hi x hx y hy
  | simpa using hi y hy x hx

private theorem norm_cofactor_le_of_factorization {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (h : V →ₗ⋆[K] V →ₗ[K] K)
    (L : Submodule (𝓞 K) V) (T : ℕ)
    (e : (↥(Formalism.HermitianLatticesTheory.dual h L) ⧸ L.comap (Formalism.HermitianLatticesTheory.dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)})) :
    GlobalTheory.Mass.discN h L = T ^ (2 * Formalism.HermitianLatticesTheory.fDeg K) := by
  have hc : GlobalTheory.Mass.discN h L = Nat.card (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)}) := by
    unfold GlobalTheory.Mass.discN GlobalTheory.Mass.idxN AddSubgroup.relIndex AddSubgroup.index
    exact Nat.card_congr e.toEquiv
  rw [hc, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton]
  have hT : ((T : 𝓞 K)) = algebraMap ℤ (𝓞 K) (T : ℤ) := by simp
  rw [hT, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, finrank_eq_two_mul_fDeg K hK]
  simp [Int.natAbs_pow]

private theorem mul_mul_mul_le_of_bounds (A Bm X Y C R Q1 Q2 G mk : ℝ) (h10 : Bm * A ≤ mk * C) (hexp : X * Y ≤ R * (Q1 * Q2))
    (htp : R ≤ G) (hXY : 0 ≤ X * Y) (hkC : 0 ≤ mk * C) (hQ : 0 ≤ Q1 * Q2) :
    A * Bm * X * Y ≤ mk * G * C * Q1 * Q2 := by
  calc A * Bm * X * Y = (Bm * A) * (X * Y) := by ring
    _ ≤ (mk * C) * (R * (Q1 * Q2)) := mul_le_mul h10 hexp hXY hkC
    _ ≤ (mk * C) * (G * (Q1 * Q2)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right htp hQ) hkC
    _ = mk * G * C * Q1 * Q2 := by ring

theorem main : GlobalTheory.Mass.MaxMass → Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → HasOrtho K → 1 ≤ Formalism.HermitianLatticesTheory.vInv K → GlobalTheory.Mass.PD H.B.flip → 3 ≤ (Module.finrank K V) → ∀ (T : ℕ) (L₀ : Submodule (𝓞 K) V) (Mb : ℝ), T.Prime → (∀ P : Ideal (𝓞 K), P.IsMaximal → (T : 𝓞 K) ∈ P → Ideal.absNorm P = T ∧ (T : 𝓞 K) ∉ P ^ 2) → GlobalTheory.Mass.IsIntLat H.B.flip L₀ → Nonempty ((↥(Formalism.HermitianLatticesTheory.dual H.B.flip L₀) ⧸ L₀.comap (Formalism.HermitianLatticesTheory.dual H.B.flip L₀).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)})) → Mb = (20 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ 2) ^ (2 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) * (6 + cf K)) → ∀ D₀ : ℝ, D₀ = (T : ℝ) ^ (2 * (Formalism.HermitianLatticesTheory.fDeg K)) → ∀ s n : ℕ, 1 ≤ s → s < (Module.finrank K V) → 1 ≤ n → GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom H.B.flip) (Formalism.HermitianLatticesTheory.genus H.B.flip L₀) (fun L => (((GlobalTheory.Mass.primSp H.B.flip L ((Module.finrank K V) - s) n).encard : ℕ∞) : ℝ≥0∞)) ≤ ENNReal.ofReal (Formalism.HermitianLatticesTheory.mass H.B.flip L₀ * (Mb * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (Formalism.HermitianLatticesTheory.fDeg K) * 16 ^ (s * (Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K))) * ((n : ℝ) / D₀) ^ (((Module.finrank K V) : ℝ) / 2) * ((n : ℝ) * D₀) ^ (5 * (s : ℝ) + 5 + 2 * cf K)) := by
  intro hMax hS K V _ _ _ _ _ _ _ _ H hK hO hv hPD hk T L₀ Mb hT hTP hL₀ hq hMb D₀ hD₀ s n hs hsk hn
  obtain ⟨ms, hms0, hms⟩ := GlobalTheory.OrthoMass.main K hK
  have hsymm : H.B.flip.IsSymm := GlobalTheory.HermLat.flip_isSymm H
  have hnd : H.B.flip.Nondegenerate := nondeg_of_pd H.B.flip hPD
  have hgen := GlobalTheory.T.cyclicDiscriminant_lattices_form_one_genus K V H.B.flip hK hsymm hnd T hT hTP
  obtain ⟨-, -, hstab, -⟩ := GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V H.B.flip hK hsymm hPD L₀ hL₀.1
  have hsk' : Module.finrank K V - s + s = Module.finrank K V := Nat.sub_add_cancel hsk.le
  have key := _root_.GlobalTheory.Mass.PrimMean.main hMax K V H.B.flip hK hsymm hPD hO (Module.finrank K V - s) s (by omega) hs hsk'
    (Fin (Module.finrank K V - s) → K) (Formalism.HermitianLatticesTheory.massTelescope_form K _) (Formalism.HermitianLatticesTheory.massTelescope_lat K _)
    (Formalism.HermitianLatticesTheory.massTelescope_symm K _) (Formalism.HermitianLatticesTheory.massTelescope_ortho K _)
    (Fin s → K) (Formalism.HermitianLatticesTheory.massTelescope_form K s) (Formalism.HermitianLatticesTheory.massTelescope_lat K s)
    (Formalism.HermitianLatticesTheory.massTelescope_symm K s) (Formalism.HermitianLatticesTheory.massTelescope_ortho K s)
    n (T ^ (2 * Formalism.HermitianLatticesTheory.fDeg K)) hn (Nat.one_le_pow _ _ hT.pos)
    (Formalism.HermitianLatticesTheory.genus H.B.flip L₀) hstab (fun L hL => by
      obtain ⟨hLi, ⟨eL⟩⟩ := (hgen.2 L₀ L hL₀ hq).mp hL
      exact ⟨hLi, norm_cofactor_le_of_factorization hK H.B.flip L T eL, gen_of_cyclic (le_dual_of_integral_form H.B.flip L hLi.2) _ eL⟩)
  have hm : ∀ j, Formalism.HermitianLatticesTheory.mass (Formalism.HermitianLatticesTheory.massTelescope_form K j) (Formalism.HermitianLatticesTheory.massTelescope_lat K j) = ms j :=
    fun j => hms j _ _ _ (Formalism.HermitianLatticesTheory.massTelescope_symm K j) (Formalism.HermitianLatticesTheory.massTelescope_ortho K j)
  rw [hm, hm] at key
  have hmass := _root_.GlobalTheory.Mass.CyclicDisc.main hMax K V H.B.flip hK hsymm hPD (by omega) (Fin (Module.finrank K V) → K)
    (Formalism.HermitianLatticesTheory.massTelescope_form K _) (Formalism.HermitianLatticesTheory.massTelescope_symm K _) (Formalism.HermitianLatticesTheory.massTelescope_lat K _)
    (Formalism.HermitianLatticesTheory.massTelescope_ortho K _) T hT hTP L₀ hL₀ hq
  rw [hm] at hmass
  obtain ⟨hMb1, hMbB⟩ := mass_bound_rpow_le K hK hv
  rw [← hMb] at hMb1 hMbB
  have hsmall : ∀ j, 1 ≤ j → j ≤ 2 → ms j ≤ Mb := fun j h1 h2 => by
    rw [← hm j]
    exact (GlobalTheory.SmallRankMass.mass_small hK hv h1 h2).trans hMbB
  have h10 := _root_.GlobalTheory.MassRatioBound.mass_mul_mass_le hS K hK hv (Module.finrank K V) s Mb ms hk hs hsk hms
    (hsmall 1 le_rfl (by norm_num)) (hsmall 2 (by norm_num) le_rfl) hMb1
  have hexp := exponents (n : ℝ) ((T : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K)) (Module.finrank K V : ℝ) (s : ℝ)
    (Real.logb 2 (Module.finrank ℚ K)) (by exact_mod_cast hn) (one_le_pow₀ (by exact_mod_cast hT.one_lt.le))
    (by positivity)
  have htp := laurent_T_unit_zpow_eq_T (T : ℝ) (by exact_mod_cast hT.two_le) (Module.finrank K V) (Formalism.HermitianLatticesTheory.fDeg K) (by omega)
  have hC : 0 ≤ Mb * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (Formalism.HermitianLatticesTheory.fDeg K) * 16 ^ (s * (Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K)) :=
    mul_nonneg (mul_nonneg (by linarith) (pow_nonneg (by linarith) _)) (by positivity)
  subst hD₀
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [hmass, Nat.cast_sub hsk.le, Nat.cast_pow]
  exact mul_mul_mul_le_of_bounds _ _ _ _ _ _ _ _ _ _ h10 hexp htp (by positivity) (mul_nonneg (hms0 _).le hC) (by positivity)

end GlobalTheory.DegCnt.PrimGenus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericCorankOneTermsFamilyCutByDefect
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam

namespace GlobalTheory.SnFam

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem famNG_holds : FamNG := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' hC => ?_⟩
  have hT : ConcTie X Y := hC.2.2
  exact ⟨rfl, _root_.GlobalTheory.Unfold.RowCls.clsRow_ngSet D X Y u u' hT, (GlobalTheory.NGClass.ngClass_rows D X Y u u' hT).2.1⟩

end GlobalTheory.SnFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RMeasExAll
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RMeasAll

theorem rMeasEx_all : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (C : Choice X 1) (u u' : D.what₂.Word), (∀ τ, GoodW D τ u u' 1 (locW C u u' τ)) → RMeasEx hI C u u' := by
  intro D X Y hF hI C u u' hW t hG hr τ
  obtain ⟨_, _, h3, h4, h5, h6, h7, _⟩ := hW τ
  have hTu : 0 < Formalism.MainNotions.S.Tr D u := Nat.cast_pos.2 (D.mem u).A.T_prime.pos
  have hTu' : 0 < Formalism.MainNotions.S.Tr D u' := Nat.cast_pos.2 (D.mem u').A.T_prime.pos
  obtain ⟨p, hp⟩ := Formalism.L2.SG.LoopTerm.relPtEx_holds hI C u u' t hG hr τ
  exact GlobalTheory.Amp.RootQuot.exists_rMeas D (locW C u u' τ) _ p h3 h4 (by rw [h5]; exact hTu) (by rw [h6]; exact hTu') h7 hp

end GlobalTheory.RMeasAll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RatCoordConjEqStCoord
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopVol

private theorem hJ_smul_right_flag_measures {n : ℕ} (ε : Fin n → Bool) (c : ℂ) (x y : Fin n → ℂ) :
    Formalism.L2.SG.HidaSetting.hJ ε x (c • y) = c * Formalism.L2.SG.HidaSetting.hJ ε x y := by
  unfold Formalism.L2.SG.HidaSetting.hJ
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem ratCoord_conj_eq_stCoord : ∀ (D : D7) (X : HidaSetting D) (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (γ s y : X.B.I.Ginf) (τ : D.what₂.Tau) (q : GlobalTheory.LoopV.roots (ptMat w)) (p : Formalism.L2.SG.RealObj.FreeE w), p.1 = q.1 → GlobalTheory.LoopVol.ratCoord X u' w γ s (s * y * s⁻¹) τ q = ((D.host.rdE : ℂ) ^ (q.1.2.1 - q.1.1.1))⁻¹ * Formalism.L2.SG.RealObj.stCoord X u' w γ y (X.pl.symm τ) p := by
  intro D X u' w γ s y τ q p hpq
  obtain ⟨pq, hp⟩ := p
  obtain ⟨qq, hq⟩ := q
  simp only at hpq
  subst hpq

  have hconj : s⁻¹ * (s * y * s⁻¹) * s = y := by group
  have hab : pq.1.val < pq.2.val := hp.1
  have hbr : pq.2.val ≤ D.R.rS := Nat.lt_succ_iff.mp pq.2.isLt
  have hrd : (D.host.rdE : ℂ) ≠ 0 := by
    have h1 := GlobalTheory.RealPlaces.one_le_rdE D
    exact Complex.ofReal_ne_zero.mpr (by linarith)
  unfold GlobalTheory.LoopVol.ratCoord Formalism.L2.SG.RealObj.stCoord
  rw [hconj]
  unfold Formalism.L2.SG.RealObj.frm Formalism.L2.SG.RealObj.famSc
  simp only [Complex.ofReal_one, one_pow, inv_one, one_smul, Matrix.mulVec_smul, hJ_smul_right_flag_measures]

  have hsplit : D.R.rS - pq.1.val = (pq.2.val - pq.1.val) + (D.R.rS - pq.2.val) := by omega
  rw [hsplit, pow_add]
  field_simp

end GlobalTheory.LoopVol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UpUniMul
section
universe u_1

namespace GlobalTheory.UpperUnipotentProductFlagMeasures

theorem upUni_mul {R : Type u_1} [CommRing R] {n : ℕ} {l l' : Matrix (Fin n) (Fin n) R}
    (h : Formalism.MainNotions.S.IsUpUni l) (h' : Formalism.MainNotions.S.IsUpUni l') : Formalism.MainNotions.S.IsUpUni (l * l') := by
  intro i j
  refine ⟨fun hji => ?_, fun hij => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k i with hk | hk
    · rw [(h i k).1 hk, zero_mul]
    · rw [(h' k j).1 (lt_of_lt_of_le hji hk), mul_zero]
  · subst hij
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [(h i i).2 rfl, (h' i i).2 rfl, mul_one]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with hk | hk
      · rw [(h i k).1 hk, zero_mul]
      · rw [(h' k i).1 hk, mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi

end GlobalTheory.UpperUnipotentProductFlagMeasures
end

