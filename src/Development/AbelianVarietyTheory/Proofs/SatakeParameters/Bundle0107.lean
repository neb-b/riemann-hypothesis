module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0036

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdmissibleOfRankOneUnitary
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

namespace GlobalTheory.RowTie

theorem admissible_of_rank_one_unitary : ∀ (D : D7) (T : WDTie D.nd D.naut), RankOneUnitary T → (∀ (a : ℕ) (π : D.naut.CG a), 2 ≤ a → D.naut.csd π → D.naut.ralg π → ∀ w, D.naut.tempered (D.naut.locG π w)) → Formalism.MainNotions.SumRepresentations.adm7 D := by
  intro D T hT h2
  exact (_root_.GlobalTheory.RowTie.tempered_all_ranks D T hT h2).1

end GlobalTheory.RowTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockCharIntegral
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

noncomputable section

namespace GlobalTheory.SplitRead

open Formalism.MainNotions.SumRepresentations.At

theorem charpoly_fin_one {k : Type} [CommRing k] (M : Matrix (Fin 1) (Fin 1) k) :
    M.charpoly = X - C (M 0 0) := by
  simp [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply]

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def blockShift (R : Ranks) : ℝ := ((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2

theorem blockChar_integral (hAut : TieAut N A) (hMu : MuInt N A) (i : N.Loc) (τ : H.E →+* ℂ) (z : ℂ)
    (hz : z ∈ A.infG (A.tw (A.muC i) A.etaTinv) τ) : ∃ k : ℤ, z + ((blockShift R : ℝ) : ℂ) = (k : ℂ) := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  have h2 := R.two_le_m
  obtain ⟨c, hc⟩ : ∃ c : ℕ, R.r = 2 * c + 1 := ⟨a + b - 1, by simp only [Ranks.r]; omega⟩
  have hs : ((blockShift R : ℝ) : ℂ) = -(c : ℂ) - 1 / 2 := by
    have : blockShift R = -(c : ℝ) - 1 / 2 := by
      simp only [blockShift, Ranks.nV, hc]
      push_cast
      ring
    rw [this]
    push_cast
    ring
  obtain ⟨h1, h3⟩ := hAut.2.1 τ
  rcases h1 with h1 | h1
  · have he : A.infG A.etaTinv τ = {-(1 / 2)} := by rw [h3, h1]; simp
    rw [A.infG_tw _ _ _ _ he, Multiset.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨m, rfl⟩ := hMu i τ y hy
    exact ⟨m - c - 1, by rw [hs]; push_cast; ring⟩
  · have he : A.infG A.etaTinv τ = {1 / 2} := by rw [h3, h1]; simp
    rw [A.infG_tw _ _ _ _ he, Multiset.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨m, rfl⟩ := hMu i τ y hy
    exact ⟨m - c, by rw [hs]; push_cast; ring⟩

theorem finite_placesOver (l : ℕ) (hl : l ≠ 0) : (placesOver H.E l).Finite := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 H.E)} ≠ 0 := by
    simpa using hl
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.2 hv

theorem blockChar_eq (h5 : JacquetShalikaStrongMultOne N A) (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin 1) (Qbar (N.l i)))
    (hρ : ContQ N i ρ)
    (hwd : ∀ w, w ∉ placesOver H.E (N.l i) →
      A.wdOf i ρ w = A.lpTw (A.locG (A.tw (A.muC i) A.etaTinv) w) (blockShift R))
    (g : G H.E N.Om) :
    ((ρ g : GL (Fin 1) (Qbar (N.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (N.l i))) 0 0 =
      iotaOQ N A i (chi1 N i g) := by
  have hl : N.l i ≠ 0 := (Fact.out : (N.l i).Prime).ne_zero
  have hfin : (placesOver H.E (N.l i) ∪ ((N.S i : Set _) ∪ (N.Q i : Set _))).Finite :=
    (finite_placesOver (H := H) _ hl).union ((N.S i).finite_toSet.union (N.Q i).finite_toSet)
  have hd := h5.2.2.1 _ hfin
  have hc1 : Continuous fun g : G H.E N.Om =>
      ((ρ g : GL (Fin 1) (Qbar (N.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (N.l i))) 0 0 :=
    (continuous_apply_apply 0 0).comp hρ
  have hc2 : Continuous fun g : G H.E N.Om => iotaOQ N A i (chi1 N i g) :=
    (GlobalTheory.CoeffEmbedding.continuous_iotaOQ_of_data N A i).comp (N.chi_cont i 1)
  refine congrFun (Continuous.ext_on (dense_iff_closure_eq.2 hd) hc1 hc2 ?_) g
  rintro σ ⟨w, hw, hsp, B, hB, hσ⟩
  simp only [Set.mem_union, Finset.mem_coe, not_or] at hw
  obtain ⟨hwl, hwS, hwQ⟩ := hw
  have hso : SplitOut N i w := ⟨hsp, hwl, hwS, hwQ⟩
  obtain ⟨hu, hf⟩ := A.chi_mu i w hso
  have hun : A.unr (A.wdOf i ρ w) := by
    rw [hwd w hwl]; exact (A.unr_tw _ _).2 hu
  have e := A.wdOf_frob i ρ w hwl hρ hun B σ hB hσ
  rw [hwd w hwl, show blockShift R = ((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2 from rfl, hf B σ hB hσ,
    charpoly_fin_one] at e
  simp only [Multiset.map_singleton, Multiset.prod_singleton, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C] at e
  have e2 := C_injective (sub_right_injective e)
  exact (A.iotaQC i).injective e2

end GlobalTheory.SplitRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharPolLpCharOfUnr
section
noncomputable section

namespace GlobalTheory.SplitRead.BlockParam

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL
  GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
open GlobalTheory.WeilDeligne (WD Weil ineIncl)

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}

theorem charpoly_smul_one {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (c : ℂ) :
    (c • (1 : Module.End ℂ V)).charpoly = (X - C c) ^ Module.finrank ℂ V := by
  rw [← LinearMap.charpoly_toMatrix _ (Module.finBasis ℂ V), map_smul, LinearMap.toMatrix_one,
    Matrix.smul_one_eq_diagonal, Matrix.charpoly_diagonal]
  simp

theorem charPol_lpChar_of_unr (a χ : WD h) (ha : a.unr) (σ : Ine (F := E) B) (c : ℂ)
    (hc : χ.charPol (ineIncl h σ) = X - C c) :
    (a.lpChar χ).charPol (ineIncl h σ) = (X - C c) ^ a.lpDim := by
  have hd : χ.lpDim = 1 := by rw [← WD.charPol_natDegree χ (ineIncl h σ), hc, natDegree_X_sub_C]
  induction a using WD.ind with
  | hP n a =>
  induction χ using WD.ind with
  | hP m b =>
    rw [WD.unr_mk] at ha
    rw [WD.lpDim_mk] at hd
    rw [WD.charPol_mk] at hc
    have h3 := LinearMap.aeval_self_charpoly (b.ρ (ineIncl h σ))
    rw [hc, map_sub, aeval_X, aeval_C, sub_eq_zero, Algebra.algebraMap_eq_smul_one] at h3
    rw [WD.lpChar_mk, WD.charPol_mk, WD.lpDim_mk, GlobalTheory.WeilDeligne.WDRep.tensor_ρ, ha.2, h3,
      TensorProduct.map_smul_right, TensorProduct.map_one, charpoly_smul_one, Module.finrank_tensorProduct, hd,
      mul_one]

theorem irreducible_twist {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ Γ V}
    (hρ : ρ.IsIrreducible) (χ : Γ →* ℂˣ) : (twist ρ χ).IsIrreducible :=
  OrderIso.isSimpleOrder_iff (α := Subrepresentation (twist ρ χ)) (β := Subrepresentation ρ)
    { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        have := S.toSubmodule.smul_mem (((χ g)⁻¹ : ℂˣ) : ℂ) (S.apply_mem_toSubmodule g hv)
        simpa [smul_smul] using this⟩
      invFun := fun S => ⟨S.toSubmodule, fun g v hv => S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl } |>.2 hρ

def detIrr (n : ℕ) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : Irr k n where
  V := ℂ
  π := detRep (Fin n) χ
  smooth := (isSmooth_ofChar_iff _).2 hχ.detChar
  irr := isIrreducible_ofChar _

def twistIrr {n : ℕ} (π : Irr k n) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : Irr k n where
  V := π.V
  π := twist π.π (detChar (Fin n) χ)
  smooth := isSmooth_twist π.smooth hχ.detChar
  irr := irreducible_twist π.irr _

end Local

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end GlobalTheory.SplitRead.BlockParam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompletedLatticeIntegralityFacts
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatIntFacts

theorem intValuation_uniformiser {R : Type} [CommRing R] [IsDedekindDomain R] (P : HeightOneSpectrum R) {ϖ : R}
    (h1 : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2) : P.intValuation ϖ = WithZero.exp (-1 : ℤ) := by
  have a1 : P.intValuation ϖ ≤ WithZero.exp (-((1 : ℕ) : ℤ)) :=
    (P.intValuation_le_pow_iff_mem ϖ 1).2 (by rw [pow_one]; exact h1)
  have a2 : ¬ P.intValuation ϖ ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
    fun h => h2 ((P.intValuation_le_pow_iff_mem ϖ 2).1 h)
  have a0 : P.intValuation ϖ ≠ 0 := fun h => a2 (h ▸ zero_le')
  rw [← WithZero.exp_log a0] at a1 a2 ⊢
  rw [WithZero.exp_le_exp] at a1 a2
  congr 1
  omega

theorem exists_left_inverse {R : Type} [CommRing R] {n : ℕ} (ε : R) (B C : Matrix (Fin n) (Fin n) R)
    (hε : ε * ε = ε) (h : ε • (B * C) = ε • (1 : Matrix (Fin n) (Fin n) R)) :
    ε • (C * B) = ε • (1 : Matrix (Fin n) (Fin n) R) := by
  have key : ∀ X Y : Matrix (Fin n) (Fin n) R,
      (ε • X + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R)) * (ε • Y + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R)) =
        ε • (X * Y) + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R) := by
    intro X Y
    have e1 : ε * (1 - ε) = 0 := by linear_combination -hε
    have e2 : (1 - ε) * ε = 0 := by linear_combination -hε
    have e3 : (1 - ε) * (1 - ε) = 1 - ε := by linear_combination hε
    simp only [add_mul, mul_add, smul_mul_smul_comm, hε, e1, e2, e3, zero_smul, mul_one, add_zero, zero_add]
  have h1 := key B C
  rw [h, ← add_smul, add_sub_cancel, one_smul] at h1
  have h2 := mul_eq_one_comm.1 h1
  rw [key] at h2
  rw [eq_sub_of_add_eq h2, sub_smul, one_smul, sub_sub_cancel]


set_option maxHeartbeats 1000000 in
theorem int_facts : ∀ {D : D7} (V : HSp D), (∀ a ∈ intAE D, ∀ y ∈ LamHat V, (fun i => a * y i) ∈ LamHat V) ∧ (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (ϖ ϖ' : 𝓞 D.host.E), IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ϖ' ∈ P.asIdeal → ϖ' ∉ P.asIdeal ^ 2 → ∀ n : ℤ, finPart D e * finPart D (incA D ((ϖ' : D.host.E) ^ n / (ϖ : D.host.E) ^ n)) ∈ intAE D) ∧ ∀ (ε : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (B : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)), ε * ε = ε → (∀ y ∈ LamHat V, ∃ z, (fun a => ε * y a) = fun a => ε * B.mulVec z a) → ∃ C : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), ε • (B * C) = ε • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) ∧ ε • (C * B) = ε • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) := by
  intro D V
  refine ⟨GlobalTheory.LatDual.smul_mem_lamHat V, ?_, ?_⟩
  · intro P e ϖ ϖ' he h1 h2 h1' h2' n
    have hv : P.valuation D.host.E ((ϖ' : D.host.E) ^ n / (ϖ : D.host.E) ^ n) ≤ 1 := by
      have v1 : P.valuation D.host.E (ϖ : D.host.E) = WithZero.exp (-1 : ℤ) :=
        (P.valuation_of_algebraMap ϖ).trans (intValuation_uniformiser P h1 h2)
      have v2 : P.valuation D.host.E (ϖ' : D.host.E) = WithZero.exp (-1 : ℤ) :=
        (P.valuation_of_algebraMap ϖ').trans (intValuation_uniformiser P h1' h2')
      rw [map_div₀, map_zpow₀, map_zpow₀, v1, v2]
      exact div_self_le_one _
    obtain ⟨a, b, hab⟩ := P.exists_primeCompl_mul_eq_of_integer _ hv
    have hb : (b : 𝓞 D.host.E) ∉ P.asIdeal := b.2
    have hb0 : (b : 𝓞 D.host.E) ≠ 0 := fun h => hb (h ▸ zero_mem _)
    have hb1 : ((b : 𝓞 D.host.E) : D.host.E) ≠ 0 := by exact_mod_cast hb0
    have hi : finPart D (e * incA D (((b : 𝓞 D.host.E) : D.host.E)⁻¹)) ∈ intAE D := by
      by_contra hc
      exact hb ((he.2 _ hb0).2 hc)
    have hq : (ϖ' : D.host.E) ^ n / (ϖ : D.host.E) ^ n = (a : D.host.E) * ((b : 𝓞 D.host.E) : D.host.E)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hb1]
      exact hab
    have ha : finPart D (incA D (a : D.host.E)) ∈ intAE D :=
      AddSubgroup.subset_closure ⟨1, fun v => one_mem _, a, rfl⟩
    have hm : ∀ {x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E}, x ∈ intAE D → y ∈ intAE D → x * y ∈ intAE D := by
      intro x y hx hy
      refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
      · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
        refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
        · rw [map_mul]; exact mul_mem (ha w) (hb w)
        · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
      · intro x _; rw [zero_mul]; exact zero_mem _
      · intro x _; rw [mul_zero]; exact zero_mem _
      · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
      · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
      · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
      · intro x y _ _ h; rw [mul_neg]; exact neg_mem h
    have := hm ha hi
    rw [RingHom.map_mul, mul_left_comm] at this
    rw [hq, RingHom.map_mul, RingHom.map_mul]
    exact this
  · intro ε B hε h
    obtain ⟨-, -, -, hspan, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
    have hx : ∀ x : Fin V.rank → D.host.E, ∃ z, ∀ a,
        ε * ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] x a) = ε * B.mulVec z a := by
      intro x
      have hx : x ∈ Submodule.span D.host.E (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
        rw [hspan]; trivial
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨z, hz⟩ := h (fun a => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] x a) (by
          rw [GlobalTheory.LatDual.lamHat_eq_hat]
          exact AddSubgroup.subset_closure ⟨1, fun v => one_mem _, x, hx, rfl⟩)
        exact ⟨z, congrFun hz⟩
      | zero => exact ⟨0, fun a => by simp⟩
      | add u w _ _ hu hw =>
        obtain ⟨z, hz⟩ := hu
        obtain ⟨z', hz'⟩ := hw
        exact ⟨z + z', fun a => by
          rw [Pi.add_apply, TensorProduct.tmul_add, mul_add, hz, hz', Matrix.mulVec_add, Pi.add_apply, mul_add]⟩
      | smul c u _ hu =>
        obtain ⟨z, hz⟩ := hu
        refine ⟨((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] c) • z, fun a => ?_⟩
        rw [Matrix.mulVec_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, ← hz,
          mul_left_comm, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    choose z hz using hx
    have hBC : ε • (B * Matrix.of fun j i => z (Pi.single i 1) j) =
        ε • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) := by
      refine Matrix.ext fun a i => ?_
      rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
      refine (hz (Pi.single i 1) a).symm.trans ?_
      congr 1
      by_cases hai : a = i
      · subst hai
        rw [Pi.single_eq_same, Matrix.one_apply_eq]; rfl
      · rw [Pi.single_eq_of_ne hai, Matrix.one_apply_ne hai, TensorProduct.tmul_zero]
    exact ⟨_, hBC, exists_left_inverse ε B _ hε hBC⟩

end GlobalTheory.LatIntFacts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjMemCompletedLatticeIffDualSplitPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitDualLat

variable {D : D7}

theorem ringHom_sum {A B ι : Type} [Semiring A] [Semiring B] [Fintype ι] (f : A →+* B) (g : ι → A) :
    f (∑ i, g i) = ∑ i, f (g i) := map_sum f g _

theorem cA_cA (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy]
  | tmul a x =>
    change a ⊗ₜ[D.host.F] star (star x) = _
    rw [star_star]

theorem cA_incA (x : D.host.E) : cA D (incA D x) = incA D (star x) := rfl

theorem finPart_cA (x : AE D) : finPart D (cA D x) = sigR (Af D.host.F) D.sp.cm.sig (finPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add x y hx hy => simp only [RingHom.map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem finPart_surjective : Function.Surjective (finPart D) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, RingHom.map_add _ _ _⟩
  | tmul a x => exact ⟨pairA D.host.F 0 a ⊗ₜ[D.host.F] x, rfl⟩

theorem sigR_mem_intAE {z : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) :
    sigR (Af D.host.F) D.sp.cm.sig z ∈ intAE D := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, o, rfl⟩ := hw
    exact AddSubgroup.subset_closure ⟨a, ha, ⟨D.sp.cm.sig (o : D.host.E),
      (show IsIntegral ℤ (o : D.host.E) from o.2).map (D.sp.cm.sig : D.host.E →+* D.host.E).toIntAlgHom⟩, rfl⟩
  | zero => rw [RingHom.map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [RingHom.map_add (f := _)]; exact add_mem hx hy
  | neg x _ hx => rw [RingHom.map_neg]; exact neg_mem hx

def form (V : HSp D) (x z : Fin V.rank → AE D) : AE D := ∑ i, ∑ j, cA D (x i) * incA D (V.gram i j) * z j

theorem finPart_form (V : HSp D) (x z : Fin V.rank → AE D) :
    finPart D (form V x z) =
      hR (Af D.host.F) D.sp.cm.sig V.gram (fun i => finPart D (x i)) fun i => finPart D (z i) := by
  simp only [form, ringHom_sum, RingHom.map_mul, finPart_cA]
  rfl

theorem cA_form (V : HSp D) (x z : Fin V.rank → AE D) : cA D (form V x z) = form V z x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [form, map_sum, RingHom.map_mul, cA_cA, cA_incA, GlobalTheory.LatVac.gram_star]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem form_mul (V : HSp D) (a b : AE D) (x z : Fin V.rank → AE D) :
    form V (fun i => a * x i) (fun i => b * z i) = cA D a * b * form V x z := by
  simp only [form, RingHom.map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem mem_iff (V : HSp D) (x : Fin V.rank → AE D) :
    (fun i => finPart D (x i)) ∈ LamHat V ↔
      ∀ z : Fin V.rank → AE D, (fun i => finPart D (z i)) ∈ LamHat V → finPart D (form V x z) ∈ intAE D := by
  rw [(GlobalTheory.LatDual.lamHat_selfDual_and_module V).1]
  constructor
  · intro h z hz
    rw [← cA_form, finPart_cA, finPart_form]
    exact sigR_mem_intAE (h _ hz)
  · intro h z hz
    obtain ⟨w, rfl⟩ : ∃ w : Fin V.rank → AE D, (fun i => finPart D (w i)) = z := by
      choose s hs using finPart_surjective (D := D)
      exact ⟨fun i => s (z i), funext fun i => hs _⟩
    rw [← finPart_form, ← cA_form, finPart_cA]
    exact sigR_mem_intAE (h _ hz)

theorem map_form (V : HSp D) {K : Type} [CommRing K] (π : AE D →+* K) (x z : Fin V.rank → AE D) :
    π (form V x z) =
      ((fun i => π (cA D (x i))) ᵥ* (V.gram.map fun a => π (incA D a))) ⬝ᵥ fun k => π (z k) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [form, map_sum, RingHom.map_mul, dotProduct, vecMul, Finset.sum_mul, Matrix.map_apply]
  exact Finset.sum_comm

theorem conj_mem_lamHat_iff : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ (V : HSp D) (β : GL (Fin V.rank) (Fv D.host.F v)), Frame V e π β → ∀ y : Fin V.rank → AE D, (fun i => finPart D (cA D e * y i)) ∈ LamHat V ↔ ∀ j, IsInt (Ov D v) (((fun i => π (cA D (y i))) ᵥ* ((V.gram.map fun a => π (incA D a)) * β.1)) j) := by
  intro D e v π he hπ V β hβ y
  rw [mem_iff]
  constructor
  · intro h j
    choose s hs using hπ.1
    have h1 : (fun k => π (s (β.1 k j))) = β.1 *ᵥ Pi.single j 1 := by
      funext k
      rw [hs, Matrix.mulVec_single_one]
      rfl
    have h2 := h _ ((hβ fun k => s (β.1 k j)).2 fun i => by
      rw [h1, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      by_cases hi : i = j
      · subst hi; rw [Pi.single_eq_same]; exact ⟨1, map_one _⟩
      · rw [Pi.single_eq_of_ne hi]; exact ⟨0, map_zero _⟩)
    rw [form_mul, cA_cA, he.1, hπ.2.2.2, map_form, h1, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      dotProduct_single, mul_one] at h2
    exact h2
  · intro h z hz
    have h1 := (GlobalTheory.LatDual.lamHat_selfDual_and_module V).2 _
      (GlobalTheory.AdIdem.idempotent_mem_intAE D (finPart D e) (by rw [← RingHom.map_mul, he.1])) _ hz
    simp only [← RingHom.map_mul] at h1
    have h2 := (hβ z).1 h1
    have h3 := form_mul V (cA D e) 1 y z
    simp only [one_mul, mul_one, cA_cA] at h3
    have h4 : (fun k => π (z k)) = β.1 *ᵥ ((β⁻¹).1 *ᵥ fun k => π (z k)) := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    rw [h3, hπ.2.2.2, map_form, h4, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, isInt_iff]
    exact sum_mem fun i _ => mul_mem (isInt_iff.1 (h i)) (isInt_iff.1 (h2 i))

end GlobalTheory.SplitDualLat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LowCoefficientsOfParameterCoefficientsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowCoefficients_of_parameterCoefficients : ∀ (p : ℕ) [Fact p.Prime] (ι : Type) [Fintype ι] (K1 : Type) [Field K1] [Algebra (K0 p) K1] (Un : (ι →₀ ℕ) → MvPowerSeries ι (K0 p)), (∀ n, inParam p (Un n) = MvPowerSeries.monomial n 1 ∧ (∀ m : ι →₀ ℕ, m.degree < n.degree → MvPowerSeries.coeff m (Un n) = 0)) → ∀ (U : MvPowerSeries ι K1) (d : ℕ) (S : Finset (ι →₀ ℕ)), (∀ n : ι →₀ ℕ, n.degree ≤ d → n ∈ S) → ∀ m : ι →₀ ℕ, m.degree ≤ d → MvPowerSeries.coeff m U = ∑ n ∈ S, MvPowerSeries.coeff n (inParamK p K1 U) * algebraMap (K0 p) K1 (MvPowerSeries.coeff m (Un n)) := by
  first | exact @GlobalTheory.TwU.low_coeff_of_param | exact GlobalTheory.TwU.low_coeff_of_param | (intros; apply GlobalTheory.TwU.low_coeff_of_param <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitThetaCorrespondenceOfLocalPairings
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

namespace GlobalTheory.RowTie

theorem split_theta_correspondence_of_local_pairings : ∀ D : D7, (∀ i, PairLift D.nd D.naut i) → Formalism.MainNotions.SumRepresentations.adm3 D := by
  intro D h i σ P hθ w hw
  exact GlobalTheory.RowTie.splitLift_of_pairLift _ _ _ D.nd D.naut i (h i) σ P hθ w hw

end GlobalTheory.RowTie
end

