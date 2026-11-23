module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.LocalToGlobal.NumberFieldFamilies.JMtInjective
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Formalism.LocalToGlobal.HermitianForms.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0322
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0073

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericUnipotentCharacterAtSideEqThetaSide
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsStep

theorem star_mul_self_of_pow (D : D7) (ζ : (↥D.LL0)ˣ) (n : ℕ) (hn : n ≠ 0) (h : ζ ^ n = 1) :
    star ((ζ : ↥D.LL0) : D.what₂.LL) * ((ζ : ↥D.LL0) : D.what₂.LL) = 1 := by
  apply D.what₂.embLL.injective
  rw [map_mul, map_one, D.starLL_cx]
  have hp : ((ζ : ↥D.LL0) : D.what₂.LL) ^ n = 1 := by
    have e := congrArg (fun u : (↥D.LL0)ˣ => ((u : ↥D.LL0) : D.what₂.LL)) h
    simpa using e
  have hz : (D.what₂.embLL ((ζ : ↥D.LL0) : D.what₂.LL)) ^ n = 1 := by
    rw [← map_pow, hp, map_one]
  have hn1 : ‖D.what₂.embLL ((ζ : ↥D.LL0) : D.what₂.LL)‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz hn
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn1]
  simp

theorem readT_false_eq (D : D7) (T : TwR D.LL0 D.nd) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0)
    (i : T.Tw) (x : ↥D.LL0) : readT D T i false x = readT D T i true ⟨star (x : D.what₂.LL), hstar x⟩ := by
  simp only [readT, RingHom.comp_apply, Bool.false_eq_true, if_false, if_true]
  rw [T.restX_coefficientEmbedding_conj i x ⟨star (x : D.what₂.LL), hstar x⟩ rfl]

theorem readT_false_mul_true (D : D7) (T : TwR D.LL0 D.nd) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0)
    (i : T.Tw) (ζ : (↥D.LL0)ˣ) (n : ℕ) (hn : n ≠ 0) (h : ζ ^ n = 1) :
    readT D T i false (ζ : ↥D.LL0) * readT D T i true (ζ : ↥D.LL0) = 1 := by
  rw [readT_false_eq D T hstar, ← map_mul]
  have e : (⟨star ((ζ : ↥D.LL0) : D.what₂.LL), hstar _⟩ : ↥D.LL0) * (ζ : ↥D.LL0) = 1 :=
    Subtype.ext (star_mul_self_of_pow D ζ n hn h)
  rw [e, map_one]

theorem mul_pow_g_eq_one (g : ℕ) (m : Multiplicative (ZMod g)) : m ^ g = 1 := by
  rw [← ofAdd_toAdd m, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]

theorem psiUT_eq_thSide : ∀ (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (T : TwR D.LL0 D.nd),
    (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    (∀ i b (u : Formalism.IndefR.NX.U D.nd), psiUT D T In.θ i b u = psiUOf D.nd (NX.xiRed D)
      (thSide D.host.g (fun k => (Units.map (readT D T i true).toMonoidHom).comp (In.θ k)) b) u) ∧
    (2 ≤ D.R.r → ∀ i k, (Units.map (readT D T i true).toMonoidHom).comp (In.θ k) ≠ 1) := by
  intro D S In T hstar
  refine ⟨fun i b u => ?_, fun _ i k h => ?_⟩
  · simp only [psiUT, MonoidHom.comp_apply, psiUOf_apply, map_prod]
    refine Finset.prod_congr rfl fun kv _ => ?_
    cases b
    · simp only [thSide, Bool.false_eq_true, if_false, MonoidHom.inv_apply, MonoidHom.comp_apply]
      apply Units.ext
      rw [Units.coe_map, Units.val_inv_eq_inv_val, Units.coe_map]
      refine eq_inv_of_mul_eq_one_left ?_
      exact readT_false_mul_true D T hstar i _ (D.host.g kv.1) (D.host.g_prime kv.1).ne_zero
        (by rw [← map_pow, mul_pow_g_eq_one, map_one])
    · rfl
  · apply In.θ_ne k
    refine MonoidHom.ext fun x => Units.ext ?_
    apply (readT D T i true).injective
    have e := congrArg (fun u : (FractionRing (T.O i))ˣ => (u : FractionRing (T.O i))) (DFunLike.congr_fun h x)
    simpa using e

end GlobalTheory.HeightCounting.FormsStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeAlgebraCompUnitaryGroupAntidiagTransportMem
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd

noncomputable section

namespace GlobalTheory.SatInd

section HeckeTransport

theorem hecke_comp_of_inverse {G G' : Type} [Group G] [Group G'] (φ : G →* G') (ψ : G' →* G)
    (hψφ : ∀ y, ψ (φ y) = y) {K : Subgroup G} {K' : Subgroup G'} (hφK : ∀ a ∈ K, φ a ∈ K')
    (hψK : ∀ a ∈ K', ψ a ∈ K) (h' : G' → ℂ) (hh : h' ∈ Formalism.UG.Hecke ℂ K') :
    (fun y => h' (φ y)) ∈ Formalism.UG.Hecke ℂ K := by
  classical
  have hh' : Formalism.UG.IsBiInv K' h' ∧ Formalism.UG.FinDosetSupp K' h' := hh
  obtain ⟨hbi, S', hS'⟩ := hh'
  show Formalism.UG.IsBiInv K (fun y => h' (φ y)) ∧ Formalism.UG.FinDosetSupp K (fun y => h' (φ y))
  refine ⟨fun a b y => ?_, S'.image ψ, fun y hy => ?_⟩
  · show h' (φ ((a : G) * y * b)) = h' (φ y)
    rw [map_mul, map_mul]
    exact hbi ⟨φ a, hφK a a.2⟩ ⟨φ b, hφK b b.2⟩ (φ y)
  · obtain ⟨s, hs, a, b, e⟩ := hS' (φ y) hy
    refine ⟨ψ s, Finset.mem_image_of_mem _ hs, ⟨ψ a, hψK a a.2⟩, ⟨ψ b, hψK b b.2⟩, ?_⟩
    show y = ψ a * ψ s * ψ b
    rw [← map_mul, ← map_mul, ← e, hψφ]

end HeckeTransport

section KUTransport

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem guMap_mem_KU (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x))
    (hint : ∀ x, x ∈ intL K → g x ∈ intL K) (n : ℕ) (a : GU σ n) (ha : a ∈ KU σ n) :
    guMap g hg n a ∈ KU σ' n := by
  simp only [KU, Subgroup.mem_subgroupOf, intPts, Subgroup.mem_inf, MonoidHom.mem_range] at ha ⊢
  obtain ⟨-, b, hb⟩ := ha
  refine ⟨(guMap g hg n a).2, ?_⟩
  let gi : intL K →+* intL K :=
    ((g : K →+* K).comp (intL K).subtype).codRestrict (intL K) (fun x => hint x x.2)
  refine ⟨bc (n := Fin n) gi b, ?_⟩
  apply Units.ext
  ext i j
  have hij := congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K) i j) hb
  simp only [bc, Units.coe_map, MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply] at hij ⊢
  rw [guMap_val, Matrix.map_apply, ← hij]
  rfl

theorem guMap_symm_guMap (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x))
    (hg' : ∀ x, g.symm (σ' x) = σ (g.symm x)) (n : ℕ) (y : GU σ n) :
    guMap g.symm hg' n (guMap g hg n y) = y := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [guMap_val, guMap_val]
  simp

theorem guMap_hecke_comap : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)), (∀ x, x ∈ intL K ↔ g x ∈ intL K) → ∀ (n : ℕ) (h' : GU σ' n → ℂ), h' ∈ Hecke ℂ (KU σ' n) → (fun y => h' (guMap g hg n y)) ∈ Hecke ℂ (KU σ n) := by
  intro K _ _ g σ σ' hg hint n h' hh
  have hg' : ∀ x, g.symm (σ' x) = σ (g.symm x) := by
    intro x
    apply g.injective
    rw [RingEquiv.apply_symm_apply, hg, RingEquiv.apply_symm_apply]
  have hint' : ∀ x, x ∈ intL K → g.symm x ∈ intL K := by
    intro x hx
    rw [hint (g.symm x), RingEquiv.apply_symm_apply]
    exact hx
  exact hecke_comp_of_inverse (guMap g hg n) (guMap g.symm hg' n) (guMap_symm_guMap g hg hg' n)
    (fun a ha => guMap_mem_KU g hg (fun x => (hint x).1) n a ha)
    (fun a ha => guMap_mem_KU g.symm hg' hint' n a ha) h' hh

end KUTransport

end GlobalTheory.SatInd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeComparisonUnitAtFrobeniusEqDelta
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.HeightCounting.FormsStep

theorem cHkT_eq_of_isFrob : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw) (b : Bool) (P : PlE D.host), P ∉ T.S0 i →
    ∀ σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om, IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) σ →
    cHkT D T i b P = Units.map (algebraMap (T.O0 i) (T.O i)).toMonoidHom
      (if b then T.delta i σ else (T.delta i σ)⁻¹) := by
  intro D T i b P hP σ hσ
  have hA := D.nd.plOm.2 P
  have key : ∀ τ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om, IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) τ →
      T.delta i τ = T.delta i σ := by
    intro τ hτ
    have hmem := inv_mul_mem_Ine_of_isFrob hσ hτ
    have h1 : T.delta i (σ⁻¹ * τ) = 1 := by
      by_contra hne
      exact hP (T.primes_subset_exceptional i ((T.delta_ram i P _ hA).1 ⟨_, hmem, hne⟩))
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1.symm
  unfold cHkT
  rw [dite_eq_left ⟨σ, hσ⟩, key _ (Exists.choose_spec (⟨σ, hσ⟩ : ∃ τ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om,
    IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) τ))]

end GlobalTheory.HeightCounting.FormsStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeEigenspaceNeBotEveryLocalisationPoint
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.EigOcc

open Module Module.End

section Lin

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem inf_ker_ne_bot {a : End K V} {c : K} {U : Submodule K V} (hU : U ≠ ⊥)
    (hle : U ≤ a.maxGenEigenspace c) (hinv : ∀ y ∈ U, a y ∈ U) :
    U ⊓ LinearMap.ker (a - c • 1) ≠ ⊥ := by
  classical
  obtain ⟨y, hyU, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  have hy := hle hyU
  rw [mem_maxGenEigenspace] at hy
  have hP : ∃ n : ℕ, ((a - c • (1 : End K V)) ^ n) y = 0 := hy
  have hm : ((a - c • 1) ^ Nat.find hP) y = 0 := Nat.find_spec hP
  have hm0 : Nat.find hP ≠ 0 := by
    intro h
    rw [h, pow_zero, Module.End.one_apply] at hm
    exact hy0 hm
  obtain ⟨m', hm'⟩ : ∃ m', Nat.find hP = m' + 1 := ⟨Nat.find hP - 1, by omega⟩
  have hne : ((a - c • 1) ^ m') y ≠ 0 := Nat.find_min hP (by omega)
  have hinv' : ∀ k : ℕ, ((a - c • 1) ^ k) y ∈ U := by
    intro k
    induction k with
    | zero => simpa using hyU
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      exact U.sub_mem (hinv _ ih) (U.smul_mem c ih)
  intro hbot
  apply hne
  have hmem : ((a - c • 1) ^ m') y ∈ U ⊓ LinearMap.ker (a - c • 1) := by
    refine ⟨hinv' m', ?_⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, ← Module.End.mul_apply, ← pow_succ', ← hm']
    exact hm
  rw [hbot] at hmem
  exact (Submodule.mem_bot K).1 hmem

theorem exists_common_eigvec (S : Set (End K V)) (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b) (χ : End K V → K)
    (W0 : Submodule K V) (hW : W0 ≠ ⊥) (hle : ∀ a ∈ S, W0 ≤ a.maxGenEigenspace (χ a))
    (hinv : ∀ a ∈ S, ∀ y ∈ W0, a y ∈ W0) :
    ∃ u ∈ W0, u ≠ 0 ∧ ∀ a ∈ S, a u = χ a • u := by
  classical
  have hP : ∃ n, ∃ U : Submodule K V, U ≤ W0 ∧ U ≠ ⊥ ∧ (∀ a ∈ S, ∀ y ∈ U, a y ∈ U) ∧ finrank K U = n :=
    ⟨_, W0, le_rfl, hW, hinv, rfl⟩
  obtain ⟨U, hUW, hU0, hUinv, hUn⟩ := Nat.find_spec hP
  have key : ∀ a ∈ S, U ≤ LinearMap.ker (a - χ a • 1) := by
    intro a ha
    have hU'0 : U ⊓ LinearMap.ker (a - χ a • 1) ≠ ⊥ := inf_ker_ne_bot hU0 (hUW.trans (hle a ha)) (hUinv a ha)
    have hU'inv : ∀ b ∈ S, ∀ y ∈ U ⊓ LinearMap.ker (a - χ a • 1), b y ∈ U ⊓ LinearMap.ker (a - χ a • 1) := by
      rintro b hb y ⟨hyU, hyk⟩
      refine ⟨hUinv b hb y hyU, ?_⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker] at hyk
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      have hc : Commute (a - χ a • 1) b := (hS a ha b hb).sub_left ((Commute.one_left b).smul_left _)
      rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply, hyk, map_zero]
    have hle' : finrank K U ≤ finrank K ↥(U ⊓ LinearMap.ker (a - χ a • 1)) := by
      rw [hUn]
      exact Nat.find_min' hP ⟨_, inf_le_left.trans hUW, hU'0, hU'inv, rfl⟩
    have heq : U ⊓ LinearMap.ker (a - χ a • 1) = U := Submodule.eq_of_le_of_finrank_le inf_le_left hle'
    rw [← heq]
    exact inf_le_right
  obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  refine ⟨u, hUW huU, hu0, fun a ha => ?_⟩
  have h := key a ha huU
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h
  exact h

end Lin

end GlobalTheory.EigOcc

namespace GlobalTheory.EigOcc

theorem mem_heckeEig_of_gen {O X M : Type} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    (T : Subalgebra O (X → O)) (act : T →ₐ[O] Module.End O M) (x : X) (G : Set (X → O))
    (hT : T = Algebra.adjoin O G) (z : TensorProduct O (FractionRing O) M)
    (hG : ∀ f : T, (f : X → O) ∈ G →
      ((act f).baseChange (FractionRing O)) z = algebraMap O (FractionRing O) ((f : X → O) x) • z) :
    z ∈ heckeEig T act x := by
  rw [heckeEig, Submodule.mem_iInf]
  intro f
  rw [Module.End.mem_eigenspace_iff]
  obtain ⟨g, hgT⟩ := f
  have hg : g ∈ Algebra.adjoin O G := hT ▸ hgT
  induction hg using Algebra.adjoin_induction with
  | mem g hg' => exact hG ⟨g, hgT⟩ hg'
  | algebraMap r =>
    have e1 : (⟨algebraMap O (X → O) r, hgT⟩ : T) = algebraMap O T r := rfl
    rw [e1, AlgHom.commutes, Algebra.algebraMap_eq_smul_one r, LinearMap.baseChange_smul, LinearMap.baseChange_one,
      LinearMap.smul_apply, Module.End.one_apply, ← algebraMap_smul (FractionRing O) r z]
    rfl
  | add g1 g2 h1 h2 ih1 ih2 =>
    have m1 : g1 ∈ T := hT ▸ h1
    have m2 : g2 ∈ T := hT ▸ h2
    have e1 : (⟨g1 + g2, hgT⟩ : T) = ⟨g1, m1⟩ + ⟨g2, m2⟩ := rfl
    rw [e1, map_add (f := _), LinearMap.baseChange_add, LinearMap.add_apply, ih1 m1, ih2 m2]
    simp only [Subalgebra.coe_add, Pi.add_apply, map_add (f := _), add_smul]
  | mul g1 g2 h1 h2 ih1 ih2 =>
    have m1 : g1 ∈ T := hT ▸ h1
    have m2 : g2 ∈ T := hT ▸ h2
    have e1 : (⟨g1 * g2, hgT⟩ : T) = ⟨g1, m1⟩ * ⟨g2, m2⟩ := rfl
    rw [e1, map_mul, LinearMap.baseChange_mul, Module.End.mul_apply, ih2 m2, LinearMap.map_smul, ih1 m1, smul_smul]
    simp only [Subalgebra.coe_mul, Pi.mul_apply, map_mul, mul_comm]

end GlobalTheory.EigOcc

namespace GlobalTheory.EigOcc

section Main

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}


set_option maxHeartbeats 1000000 in
theorem heckeEig_ne_bot (B : LocBase0 H what₂) (hs : HeckeStd0 B) (hd : FinDimV B) (hL : MtLoc B (partCompl_of hs hd))
    (hAct : ActEx B (partCompl_of hs hd)) (hH : ActHK B hs hd hL hAct) (i : LocT B) (x : XOf B i) :
    heckeEig (TOf B i) (actC B (partCompl_of hs hd) hAct i) x ≠ ⊥ := by
  classical
  haveI := hd (jOf B i) (wOf B i)
  let S : Set (Module.End (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i))) :=
    {f | ∃ v k, GenAt0 H (lOf B i) (B.Qw (wOf B i)) v k ∧ f = B.hK (jOf B i) (wOf B i) v k}
  let χ : Module.End (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i)) → FractionRing (OOf B i) :=
    fun a => if h : a ∈ hAlg B i then NCov.pt x.1 ⟨a, h⟩ else 0
  have hSc : ∀ a ∈ S, ∀ b ∈ S, Commute a b := std_comm (j := jOf B i) (w := wOf B i) hs i.2.2.2.1 i.2.2.2.2.1
  have hmem : ∀ a ∈ S, a ∈ hAlg B i := fun a ha => Algebra.subset_adjoin ha
  have hχ : ∀ a (ha : a ∈ S), χ a = NCov.pt x.1 ⟨a, hmem a ha⟩ := fun a ha => dif_pos (hmem a ha)
  obtain ⟨u, huW, hu0, hu⟩ := exists_common_eigvec S hSc χ (NCov.W (hAlg B i) (NCov.pt x.1)) x.2.2
    (fun a ha => by
      rw [hχ a ha]
      exact NCov.W_le (hAlg B i) (NCov.pt x.1) ⟨a, hmem a ha⟩)
    (fun a ha y hy => by
      rw [NCov.W, Submodule.mem_iInf] at hy ⊢
      intro t
      exact Module.End.mapsTo_maxGenEigenspace_of_comm (NCov.commute_adjoin hSc t.2 (hmem a ha)) _ (hy t))
  have hpart : u ∈ NCov.part (hAlg B i) i.2.1 :=
    (le_iSup₂ (f := fun (ψ : hAlg B i →ₐ[OOf B i] OOf B i) (_ : NCov.cls ψ = i.2.1) => NCov.W (hAlg B i) (NCov.pt ψ))
      x.1 x.2.1) huW
  obtain ⟨z, hz⟩ := (PsiC_range B (partCompl_of hs hd) hL i u).1 hpart
  have hG : ∀ f : TOf B i, (f : XOf B i → OOf B i) ∈ {f | ∃ v k, GenAt0 H (lOf B i) (B.Qw (wOf B i)) v k ∧ f = hTfun B i v k} →
      ((actC B (partCompl_of hs hd) hAct i f).baseChange (FractionRing (OOf B i))) z =
        algebraMap (OOf B i) (FractionRing (OOf B i)) ((f : XOf B i → OOf B i) x) • z := by
    rintro f ⟨v, k, hvk, hf⟩
    have e1 : f = hTOf B i v k := Subtype.ext (by rw [hf]; simp [hTOf, dif_pos hvk])
    subst e1
    apply PsiC_inj B (partCompl_of hs hd) hL i
    rw [hH i v k hvk z, hz, map_smul, hz, hu _ ⟨v, k, hvk, rfl⟩, hχ _ ⟨v, k, hvk, rfl⟩]
    exact congrArg (· • u) (congrArg (algebraMap (OOf B i) (FractionRing (OOf B i))) (ptX_val B i v k hvk x).symm)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [map_zero] at hz
    exact hu0 hz.symm
  intro hbot
  apply hz0
  have hzm : z ∈ heckeEig (TOf B i) (actC B (partCompl_of hs hd) hAct i) x :=
    mem_heckeEig_of_gen (TOf B i) (actC B (partCompl_of hs hd) hAct i) x _ rfl z hG
  rw [hbot] at hzm
  exact (Submodule.mem_bot _).1 hzm

end Main

end GlobalTheory.EigOcc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeOperatorIntegralOnLatticeAtTwistedPlaces
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.HeckeLocN

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

theorem exists_preimage_comb {K L V W : Type} [Field K] [Field L] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module L W]
    (σ : K →+* L) (f : V →ₛₗ[σ] W) (hf : Function.Injective f) (S : Finset W) (hS : ∀ y ∈ S, y ∈ Set.range f)
    (c : W → K) (x : V) (hx : f x = ∑ g ∈ S, σ (c g) • g) :
    ∃ F : Finset V, (↑F ⊆ {x : V | f x ∈ S}) ∧ x = ∑ y ∈ F, c (f y) • y := by
  classical
  refine ⟨S.preimage f hf.injOn, fun y hy => by simpa using hy, hf ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hx, map_sum]
  simp only [LinearMap.map_smulₛₗ]
  exact (Finset.sum_preimage f S hf.injOn (fun g => σ (c g) • g) (fun g hg hn => absurd (hS g hg) hn)).symm

theorem heckeIntTw_base : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q) (X : CoefIn D.what₂) (hS : SplitK (mt0 M) C.Q hR X) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E), MtInput D M tup C.Q → (∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) → HeckeIntTw (base M C hR X hS) := by
  intro D M C hR X hS tup hI hsp j w h1 h2 hw v k hg x hx
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨s, ϖ, hc, hu⟩ := hsp v hg.1
  obtain ⟨c, hc0, he⟩ := hI.int w ⟨j', by omega⟩ v k s ϖ hw hg hc hu _ hx
  have h3 := hLC_spec (mt0 M) C.Q hR (j' + 1) w v k h1 h2 hg s ϖ hc hu x
  have h4 := (M (D.what₂.muTw w) (j' + 1) h1 h2).real_inj (h3.trans he)
  obtain ⟨F, hF, hsum⟩ := exists_preimage_comb D.what₂.embLL (D.what₂.jMt (D.what₂.muTw w) (j' + 1))
    (LatticeFinitenessFree.jMt_injective _ _) _ (D.what₂.MtLat_sub _ _) c _ h4
  exact ⟨F, fun y => c (D.what₂.jMt (D.what₂.muTw w) (j' + 1) y), hF, fun y _ => hc0 _, hsum⟩

end GlobalTheory.HeckeLocN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeRingActsOnLatticeAsOperators
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.HeckeLocN

theorem actHK_holds {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (B : LocBase0 H what₂) (hs : HeckeStd0 B) (hd : FinDimV B)
    (hL : MtLoc B (partCompl_of hs hd)) (hAct : ActEx B (partCompl_of hs hd)) : ActHK B hs hd hL hAct := by
  intro i v k hg z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul c m =>
    rw [LinearMap.baseChange_tmul]
    have hs1 := ((hAct i).choose_spec.2 v k hg m)
    have e : ∀ m' : MtSub B (partCompl_of hs hd) i, PsiC B (partCompl_of hs hd) hL i (c ⊗ₜ m') = c • ((m' : partOf B i) : B.V (jOf B i) (wOf B i)) := by
      intro m'
      haveI := hL i
      simp only [PsiC, mtEquiv, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Submodule.coe_subtype]
      rw [IsBaseChange.equiv_tmul]
      rfl
    rw [e, e, map_smul]
    congr 1

end GlobalTheory.HeckeLocN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianColumnsGeneratorsBaseLatticesFunctional
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC


set_option maxHeartbeats 4000000 in
theorem herm_rest_tied : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → CarT H F A → (∀ u (w : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (h : ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ w.asIdeal) (a : intV (I.rec7 l Z).host.E w), (a : TensorProduct (I.rec7 l Z).host.F (I.rec7 l Z).host.E (w.adicCompletion (I.rec7 l Z).host.F)) = inclE (F := (I.rec7 l Z).host.F) (w.adicCompletion (I.rec7 l Z).host.F) ((A u).piU : (I.rec7 l Z).host.E) → ∀ m : (H.lev0 u).fM w h, a • m = 0) → Formalism.L2.Herm.SymmetricCofactorCompatibility (I.rec7 l Z) H A ∧ Formalism.L2.Herm.SymmetricBaseCompatibility (I.rec7 l Z) H A ∧ Nonempty (Formalism.L2.Herm.SymmetricResidueFieldLevels (I.rec7 l Z) H A) ∧ ∃ X0 : Formalism.L2.Herm.SymmetricLevelZeroData (I.rec7 l Z) H A, ∀ u, (X0 u).piG = X.piG := by
  intro B X I hOk hP l Z H F A hS hH hT hπ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u
    have h1 := (hT.piU u).symm.trans (hS u).1.piU
    have h2 := (hT.piU (I.rec7 l Z).u₀).symm.trans (hS _).1.piU
    rw [h1, h2]
    exact hP.cof u
  · intro u pb hpb
    exact ⟨_root_.GlobalTheory.Mem.Col2.TC.base_step_zero_tied I hOk hP l Z H F A hS hH hT u pb hpb, _root_.GlobalTheory.Mem.Col2.TC.chart_base_sup_dual I hOk hP l Z H F A hS hH hT u pb hpb⟩
  · refine ⟨fun u i h1 hm v β => ?_⟩
    by_cases h2 : i + 1 ≤ (I.rec7 l Z).R.m
    · exact (_root_.GlobalTheory.Mem.Col2.TC.fvTie_charts I hOk hP l Z H F A hS hH hT u i h1 h2 v β).some
    · have he : i = (I.rec7 l Z).R.m := by omega
      subst he
      exact (_root_.GlobalTheory.Mem.Col2.TC.fvTie_chart_top I hOk hP l Z H F A hS hH hT u h1 v β).some
  · choose x hx using GlobalTheory.T.stepZeroLevel_typePrimeOrientation_frames_functionals I hOk hP l Z H F A hS hH hT hπ
    exact ⟨x, hx⟩

end GlobalTheory.Mem.Col2.TC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NTiedLocTiedOfBuilt
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.HeightCounting

theorem locTied_any (D' : D7) : Nonempty (Formalism.L2.LocTied D') :=
  ⟨⟨fun l _ => GlobalTheory.LocArith.arithTied l (D'.loc l), fun i w hw => D'.nbr_ind i w hw,
    fun i w hw => D'.ntwbr_ind i w hw⟩⟩

end GlobalTheory.HeightCounting

end
end

