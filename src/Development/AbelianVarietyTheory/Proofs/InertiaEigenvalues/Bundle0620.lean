module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlternatingDifferenceTermWindow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteStableLatticesDifferenceTermNeZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0604
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0448
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineIffMemH1f
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0611
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0610
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeEqFiltrationSumAtLevel
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComponentWachLetterBasisFiltration
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachWeierstrassTestAndDensity
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionBasisDivisibility
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionsSpanFullLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0216

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoSignedLatticeSumSubNormCharacterMul
section
noncomputable section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

namespace GlobalTheory.UnitLemma.Desc

variable {K : UQ} (B : InvAlg K) {ι : Type}

theorem eS_mul_eS_of_disjoint_inv [Fintype ι] {e : ι → B.A} (he : CompleteOrthogonalIdempotents e)
    {I J : Finset ι} (h : Disjoint I J) : eS B e I * eS B e J = 0 := by
  unfold eS
  rw [Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
  exact he.ortho (fun hij => Finset.disjoint_left.1 h hi (hij ▸ hj))

theorem eS_mul_self_inv [Fintype ι] {e : ι → B.A} (he : CompleteOrthogonalIdempotents e) (I : Finset ι) :
    eS B e I * eS B e I = eS B e I := by
  unfold eS
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i]
  · exact (he.idem i).eq
  · intro j _ hji; exact he.ortho (Ne.symm hji)
  · intro h; exact absurd hi h

theorem σ_eS_inv [Fintype ι] {e : ι → B.A} {S : Finset ι} (hP : IsPre B e S) (I : Finset ι) :
    B.σ (eS B e I) = eS B e I := by
  unfold eS
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨f, -, -, -, h1, h2⟩ := hP.2 i
  by_cases hi : i ∈ S
  · obtain ⟨h, hf⟩ := h1 hi; rw [h, hf]
  · obtain ⟨-, h⟩ := h2 hi; rw [h, map_add (f := _), B.σ_σ, add_comm]

theorem HH_sub_chi_mul_HH_negligible : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] [DecidableEq ι]
    (e π : ι → B.A) (S : Finset ι) (a : K.O), B.LieReg → K.Small a → IsFrame B e π S → ∀ I ⊆ S, ∀ x : B.A,
    B.Plus x → Tendsto (fun k : ℕ => (((HH B π I (S \ I) (x * algebraMap K.O B.A a ^ (2 * k)) 1 -
      chi B e I x * HH B π I (S \ I) (algebraMap K.O B.A a ^ (2 * k)) 1 : ℚ) : ℝ) /
      (B.rho (algebraMap K.O B.A a ^ k) : ℝ))) atTop (𝓝 0) := by
  intro K B ι _ _ e π S a hL ha hF I hI x hx
  have hEE := eS_mul_self_inv B hF.1.1 I
  have hE'E := eS_mul_eS_of_disjoint_inv B hF.1.1 (Finset.sdiff_disjoint (s := I) (t := S))
  have hσE := σ_eS_inv B hF.1 I
  have hcov : ∀ i ∈ S, i ∈ I ∨ i ∈ S \ I := fun i hi => by
    by_cases h : i ∈ I
    · exact Or.inl h
    · exact Or.inr (Finset.mem_sdiff.2 ⟨hi, h⟩)
  set E := eS B e I with hEdef
  set E' := eS B e (S \ I) with hE'def
  obtain ⟨xi, hxi⟩ : ∃ xi : B.A, x * xi = 1 := ⟨_, hx.1.mul_val_inv⟩

  have hyu : IsUnit (x * E + (1 - E)) :=
    IsUnit.of_mul_eq_one (xi * E + (1 - E)) (by linear_combination (E * E) * hxi + (2 - x - xi) * hEE)
  have hx'u : IsUnit (x * (1 - E) + E) :=
    IsUnit.of_mul_eq_one (xi * (1 - E) + E) (by linear_combination (1 - E) ^ 2 * hxi + (2 - x - xi) * hEE)
  have hyP : B.Plus (x * E + (1 - E)) := ⟨hyu, by simp only [map_add (f := _), map_mul, map_sub, map_one, hx.2, hσE]⟩
  have hxy : (x * E + (1 - E)) * (x * (1 - E) + E) = x := by linear_combination (-(x - 1) ^ 2) * hEE
  have hchi : chi B e I x = K.eta (Algebra.norm K.E (x * E + (1 - E))) := rfl

  have haU : IsUnit (algebraMap K.O B.A a) := by
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A a]
    refine (IsUnit.mk0 _ fun h => ha.1 ?_).map _
    exact IsFractionRing.injective K.O K.E (h.trans (map_zero _).symm)

  obtain ⟨N, hN⟩ := _root_.GlobalTheory.UnitLemma.Desc.exists_pos K B ι e π S a hL.2 ha hF
  obtain ⟨L₀, hL₀⟩ := _root_.GlobalTheory.UnitLemma.Desc.term_window K B ι e π S a hL.2 ha hF I (S \ I) hI Finset.sdiff_subset hcov N
    (x * (1 - E) + E) (x * E + (1 - E)) hx'u hyu
  obtain ⟨L₁, hL₁⟩ := _root_.GlobalTheory.UnitLemma.Desc.term_window K B ι e π S a hL.2 ha hF I (S \ I) hI Finset.sdiff_subset hcov N
    1 1 isUnit_one isUnit_one
  obtain ⟨F, hFdef⟩ : ∃ F : ℕ → Submodule K.O B.A → ℚ, ∀ k M, F k M =
      B.sgnLat M * term B π I (S \ I) ((x * (1 - E) + E) * algebraMap K.O B.A a ^ (2 * k)) (x * E + (1 - E)) M :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨G, hGdef⟩ : ∃ G : ℕ → Submodule K.O B.A → ℚ, ∀ k M, G k M =
      B.sgnLat M * term B π I (S \ I) (algebraMap K.O B.A a ^ (2 * k)) 1 M := ⟨_, fun _ _ => rfl⟩
  have hsg : ∀ M, |B.sgnLat M| = 1 := fun M => by unfold InvAlg.sgnLat; exact abs_eta _
  have hFfin : ∀ k, (B.Lin ∩ Function.support (F k)).Finite := fun k =>
    (_root_.GlobalTheory.UnitLemma.Desc.finite_term_ne_zero K B ι e π S hL.2 hF I (S \ I) hI Finset.sdiff_subset _ _ ((hx'u.mul (haU.pow _))) hyu).subset
      fun M ⟨hM, h⟩ => ⟨hM, fun h0 => h (by rw [hFdef, h0, mul_zero])⟩
  have hGfin : ∀ k, (B.Lin ∩ Function.support (G k)).Finite := fun k =>
    (_root_.GlobalTheory.UnitLemma.Desc.finite_term_ne_zero K B ι e π S hL.2 hF I (S \ I) hI Finset.sdiff_subset _ _ (haU.pow _) isUnit_one).subset
      fun M ⟨hM, h⟩ => ⟨hM, fun h0 => h (by rw [hGdef, h0, mul_zero])⟩
  have hsub : ∀ k, ∑ᶠ M ∈ B.Lin, (F k M - G k M) = ∑ᶠ M ∈ B.Lin, F k M - ∑ᶠ M ∈ B.Lin, G k M := by
    intro k
    have hFG : (B.Lin ∩ Function.support (fun M => F k M - G k M)).Finite :=
      ((hFfin k).union (hGfin k)).subset fun M ⟨hM, h⟩ => by
        by_cases h1 : F k M = 0
        · exact Or.inr ⟨hM, fun h2 => h (show F k M - G k M = 0 by rw [h1, h2, sub_zero])⟩
        · exact Or.inl ⟨hM, h1⟩
    rw [eq_sub_iff_add_eq, ← finsum_mem_add_distrib' hFG (hGfin k)]
    simp only [sub_add_cancel]

  have key : ∀ k : ℕ, HH B π I (S \ I) (x * algebraMap K.O B.A a ^ (2 * k)) 1 -
      chi B e I x * HH B π I (S \ I) (algebraMap K.O B.A a ^ (2 * k)) 1 =
      K.eta (Algebra.norm K.E (x * E + (1 - E))) * ∑ᶠ M ∈ B.Lin, (F k M - G k M) := by
    intro k
    have hx_eq : x * algebraMap K.O B.A a ^ (2 * k) =
        (x * E + (1 - E)) * ((x * (1 - E) + E) * algebraMap K.O B.A a ^ (2 * k)) := by
      rw [← mul_assoc, hxy]
    rw [hx_eq, _root_.GlobalTheory.UnitLemma.Move.HH_mul_unit K B ι π I (S \ I) _ 1 _ hL hyP, hchi, mul_one, hsub, ← mul_sub]
    congr 1
    unfold HH
    congr 1
    · exact finsum_congr fun M => finsum_congr fun _ => (hFdef k M).symm
    · exact finsum_congr fun M => finsum_congr fun _ => (hGdef k M).symm

  have hcmp := _root_.GlobalTheory.UnitLemma.Desc.tendsto_badWindow_div_rho K B ι e π S a hL.2 ha hF I (S \ I) hcov N (max L₀ L₁)
    (2 * 2 ^ I.card * 2 ^ (S \ I).card) (fun k M => F k M - G k M) hN
    (by
      intro k M
      rw [hFdef, hGdef, ← mul_sub, abs_mul, hsg, one_mul]
      calc _ ≤ |term B π I (S \ I) ((x * (1 - E) + E) * algebraMap K.O B.A a ^ (2 * k)) (x * E + (1 - E)) M| +
            |term B π I (S \ I) (algebraMap K.O B.A a ^ (2 * k)) 1 M| := abs_sub _ _
        _ ≤ 2 ^ I.card * 2 ^ (S \ I).card + 2 ^ I.card * 2 ^ (S \ I).card :=
            add_le_add (abs_term _ _ _ _ _ _ _) (abs_term _ _ _ _ _ _ _)
        _ = _ := by ring)
    (by
      intro k hk M _ p hp hf
      rw [hFdef, hGdef, ← mul_sub] at hf
      have hne := right_ne_zero_of_mul hf
      obtain ⟨h1a, h1b⟩ := hL₀ (max L₀ L₁) (le_max_left _ _) k hk M p hp
      obtain ⟨h2a, h2b⟩ := hL₁ (max L₀ L₁) (le_max_right _ _) k hk M p hp
      rw [one_mul] at h2a h2b
      rw [← hEdef, ← hE'def] at h1b h2b
      have hW : Win I (S \ I) (max L₀ L₁) k p := by
        by_cases h : term B π I (S \ I) ((x * (1 - E) + E) * algebraMap K.O B.A a ^ (2 * k))
            (x * E + (1 - E)) M = 0
        · exact h2a fun h2 => hne (by rw [h, h2, sub_zero])
        · exact h1a h
      refine ⟨hW, fun hmid => hne ?_⟩
      have hEx : E * ((x * (1 - E) + E) * algebraMap K.O B.A a ^ (2 * k)) = E * algebraMap K.O B.A a ^ (2 * k) := by
        linear_combination algebraMap K.O B.A a ^ (2 * k) * (1 - x) * hEE
      have hE'y : E' * (x * E + (1 - E)) = E' * 1 := by linear_combination (x - 1) * hE'E
      rw [h1b hW hmid, h2b hW hmid, hEx, hE'y, sub_self])
  have hfun : (fun k : ℕ => (((HH B π I (S \ I) (x * algebraMap K.O B.A a ^ (2 * k)) 1 -
      chi B e I x * HH B π I (S \ I) (algebraMap K.O B.A a ^ (2 * k)) 1 : ℚ) : ℝ) /
      (B.rho (algebraMap K.O B.A a ^ k) : ℝ))) = fun k : ℕ =>
      (K.eta (Algebra.norm K.E (x * E + (1 - E))) : ℝ) * (((∑ᶠ M ∈ B.Lin, (F k M - G k M) : ℚ) : ℝ) /
        (B.rho (algebraMap K.O B.A a ^ k) : ℝ)) := by
    funext k
    rw [key k, Rat.cast_mul, mul_div_assoc]
  rw [hfun]
  simpa using hcmp.const_mul (K.eta (Algebra.norm K.E (x * E + (1 - E))) : ℝ)

end GlobalTheory.UnitLemma.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedTrivialLocal
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.UnramifiedTrivial

theorem unramifiedCocycles_le_blochKatoFinite_trivial {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)
    (T : LocTied l P AI) (K LL : FinExt l) :
    Z1ur (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) (IK K) ≤
      finiteCocycles (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) := by
  intro c hc
  obtain ⟨hZ, x, hx⟩ := hc
  refine ⟨hZ, ?_⟩
  obtain ⟨hcont, hadd⟩ := hZ
  haveI := LL.2
  let v := Module.finBasis ℚ_[l] ↥LL.1
  have hI : ∀ g ∈ IK K, c g = 0 := fun g hg => by simpa using hx g hg
  have hex : ∀ i, ∃ b : P.R.B, ∀ g : ↥(GK K),
      P.actQ g b - b = algebraMap ℚ_[l] _ (v.coord i (c g)) := fun i =>
    GlobalTheory.UnramifiedCrys.exists_rat AI T K (fun g => v.coord i (c g))
      ((v.coord i).continuous_of_finiteDimensional.comp hcont)
      (fun g h => by rw [hadd, map_add (f := _)]; rfl) (fun g hg => by rw [hI g hg, map_zero])
  choose b hb using hex
  refine ⟨∑ i, v i ⊗ₜ[ℚ_[l]] b i, fun g => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← Finset.sum_sub_distrib]
  conv_lhs => rw [← v.sum_repr (c g), TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : actVB (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) g (v i ⊗ₜ[ℚ_[l]] b i) =
      v i ⊗ₜ[ℚ_[l]] P.actQ g (b i) := by
    rw [← P.PD_actB]
    rfl
  rw [h1, ← TensorProduct.tmul_sub, hb, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
  rfl

theorem Z1ur_ne_bot {l : ℕ} [Fact l.Prime] (K LL : FinExt l) :
    Z1ur (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) (IK K) ≠ ⊥ := by
  obtain ⟨δ, hδc, hδa, hδI, g₀, hg₀⟩ := GlobalTheory.UnramZl.exists_unramified_character l K
  haveI := LL.2
  let c : ↥(GK K) → ↥LL.1 := fun g => algebraMap ℚ_[l] ↥LL.1 (δ g)
  have hcc : Continuous c :=
    (Algebra.linearMap ℚ_[l] ↥LL.1).continuous_of_finiteDimensional.comp hδc
  have hmem : c ∈ Z1ur (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) (IK K) := by
    refine ⟨⟨hcc, fun g h => ?_⟩, 0, fun g hg => ?_⟩
    · simp [c, hδa, map_add (f := _)]
    · simp [c, hδI g hg]
  intro h
  rw [h] at hmem
  have := congrFun ((Submodule.mem_bot _).1 hmem) g₀
  exact hg₀ (by simpa [c] using this)

end GlobalTheory.UnramifiedTrivial

namespace GlobalTheory.UnramifiedTrivial
theorem finrank_Z1f_trivial {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) :
    finrank ↥LL.1 ↥(finiteCocycles (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)) =
      finrank ↥LL.1 (FiniteCohomology (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)) := by
  have hB1 : B1 (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨x, rfl⟩
    ext g
    simp [cob]
  have hc : (B1 (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)).comap
      (finiteCocycles (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)).subtype = ⊥ := by
    rw [hB1, Submodule.comap_bot, Submodule.ker_subtype]
  exact (Submodule.quotEquivOfEqBot _ hc).finrank_eq.symm
end GlobalTheory.UnramifiedTrivial

namespace GlobalTheory.UnramifiedTrivial
theorem unrTriv_of_finrank {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)
    (T : LocTied l P AI) (K LL : FinExt l)
    (h1 : finrank ↥LL.1 (FiniteCohomology (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)) = 1) :
    UnrTriv (P.PD K) (LL := ↥LL.1) (IK K) := by
  have hZ : finrank ↥LL.1 ↥(finiteCocycles (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)) = 1 :=
    (finrank_Z1f_trivial P K LL).trans h1
  haveI : FiniteDimensional ↥LL.1 ↥(finiteCocycles (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)) :=
    Module.finite_of_finrank_eq_succ hZ
  have hle := unramifiedCocycles_le_blochKatoFinite_trivial AI T K LL
  haveI := Submodule.finiteDimensional_of_le hle
  have hpos : 0 < finrank ↥LL.1 ↥(Z1ur (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) (IK K)) := by
    refine Nat.pos_of_ne_zero fun h0 => Z1ur_ne_bot K LL ?_
    exact Submodule.finrank_eq_zero.1 h0
  unfold UnrTriv
  exact (Submodule.eq_of_le_of_finrank_le hle (by rw [hZ]; exact hpos)).symm
end GlobalTheory.UnramifiedTrivial

namespace GlobalTheory.UnramifiedTrivial

theorem unrTriv : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K LL : FinExt l), UnrTriv (P.PD K) (LL := ↥LL.1) (IK K) := by
  intro l _ P AI T K LL
  haveI := LL.2
  obtain ⟨hgood, -⟩ := GlobalTheory.LocalIntegers.good_integers l LL
  let A : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) :=
    { V := ↥LL.1
      ρ := 1
      cont := fun x => (continuous_const : Continuous fun _ : ↥(GK K) => x) }
  have hDR : IsDR (P.PD K) A.ρ := GlobalTheory.CrysExt.isDR_trivial (P.PD K)
  obtain ⟨hfin, hdim⟩ := GlobalTheory.T.finrank_H1f_de_rham l P AI T K ↥LL.1 ↥(OL LL) hgood A hDR
  have hH0 : H0V A.ρ = ⊤ := by
    refine eq_top_iff.2 fun x _ => (Submodule.mem_iInf _).2 fun g => ?_
    simp [A, H0V]
  have hFil : DdR (P.PD K) A.ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := A.V) 0 = DdR (P.PD K) A.ρ := by
    refine inf_eq_left.2 fun x hx => ?_
    change x ∈ DdR (P.PD K) (Representation.trivial ↥LL.1 ↥(GK K) ↥LL.1) at hx
    rw [GlobalTheory.CrysExt.ddR_trivial] at hx
    obtain ⟨z, rfl⟩ := hx
    exact GlobalTheory.CrysExt.incl_mem_FilV (P.PD K) le_rfl z
  have e1 : finrank ↥LL.1 ↥(H0V A.ρ) = 1 := by rw [hH0, finrank_top]; exact Module.finrank_self _
  rw [hFil] at hdim
  have h1' : finrank ↥LL.1 (FiniteCohomology (P.PD K) A.ρ) = 1 := by omega
  have h1 : finrank ↥LL.1 (FiniteCohomology (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)) = 1 := h1'
  exact unrTriv_of_finrank AI T K LL h1

end GlobalTheory.UnramifiedTrivial
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeExpansionAtLowLevelPoints
section
noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.LatLevel

section Series

variable {LL M : Type} [Field LL] [AddCommGroup M] [Module LL M]

theorem conv_smul (c : LL) (e : PowerSeries LL) (f : ℤ → M) : conv (c • e) f = c • conv e f := by
  funext k
  unfold conv
  simp only [Pi.smul_apply, map_smul, smul_eq_mul, mul_smul]
  rw [smul_finsum]

theorem conv_congr (e e' : PowerSeries LL) (f : ℤ → M) (a m : ℕ)
    (hf : ∀ r : ℤ, r < -(a : ℤ) → f r = 0) (hd : PowerSeries.X ^ m ∣ e - e') (r : ℤ)
    (hr : r < (m : ℤ) - a) : conv e f r = conv e' f r := by
  by_cases h : r < -(a : ℤ)
  · rw [LatFil.conv_vanish e f _ hf r h, LatFil.conv_vanish e' f _ hf r h]
  · obtain ⟨q, rfl⟩ : ∃ q : ℕ, r = (q : ℤ) - a := ⟨(r + a).toNat, by omega⟩
    rw [LatFil.conv_eq_sum e f a hf, LatFil.conv_eq_sum e' f a hf]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < m := by have := Finset.mem_range.1 hj; omega
    have := (PowerSeries.X_pow_dvd_iff.1 hd) j hj'
    rw [map_sub, sub_eq_zero] at this
    rw [this]

theorem approx_step (bb c cc : LL) (e q : PowerSeries LL) (f : ℤ → M) (a m : ℕ)
    (hf : ∀ r : ℤ, r < -(a : ℤ) → f r = 0) (hd : PowerSeries.X ^ m ∣ PowerSeries.C c * q - e)
    (hcc : bb * c = cc) (r : ℤ) (hr : r < (m : ℤ) - a) : bb • conv e f r = conv (PowerSeries.C cc * q) f r := by
  subst hcc
  have h1 : bb • conv e f r = conv (PowerSeries.C bb * e) f r := by
    rw [← PowerSeries.smul_eq_C_mul, conv_smul]
    rfl
  rw [h1]
  refine conv_congr _ _ f a m hf ?_ r hr
  have h2 : PowerSeries.C bb * e - PowerSeries.C (bb * c) * q = -(PowerSeries.C bb * (PowerSeries.C c * q - e)) := by
    rw [map_mul]
    ring
  rw [h2, dvd_neg]
  exact Dvd.dvd.mul_left hd _

end Series

end GlobalTheory.NL.LatLevel

namespace GlobalTheory.NL.LatLevel


set_option maxHeartbeats 20000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem lattice_at_level : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), P4 D HW F Cm := by
  intro D HW F Cm l _ K s LL h T hT
  have hP4a := GlobalTheory.NL.LowLevel.expansions_low_and_pullback_record D HW F Cm l K s LL h T hT
  unfold p4
  refine ⟨hP4a.1, fun i ζ τ hpt => ⟨hP4a.2 i ζ τ hpt, ?_, ?_⟩⟩
  · intro x k
    have hmem : ex (Cm l) h T i ζ ((letE i : AA K LL) • x) ∈ Lat (Cm l) h T i ζ :=
      Submodule.subset_span ⟨1, _, (LowLevel.conv_one _).symm⟩
    have hk := ((LatFil.lat_eq_fil D HW F Cm l K s LL h T hT i ζ τ hpt _).1 hmem).2 k
    rw [((Cm l).C K s LL h).tie.levN_eq]
    exact ⟨Submodule.mem_map_of_mem hk.1, hk.2⟩
  · intro k w hw
    obtain ⟨hprim, hτ, ι, hcomp⟩ := (GlobalTheory.NL.Points.points D HW l K s LL h).2.1 i ζ τ hpt
    have hC := GlobalTheory.NL.CompD.component D HW l K s LL h T hT i ζ τ ι hcomp hτ
    have hw' : w ∈ DdRE ((D.loc l).PD K) T.ρ τ ⊓ FilV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) (-k) := hw
    obtain ⟨d, hd, hdw⟩ := hC.2.2.1 w (Submodule.mem_inf.1 hw').1
    have hdF : ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d ∈ FilAt ((D.loc l).PD K) T τ (-k) := by
      have e1 : ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d =
          w + (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d - w) := by abel
      rw [e1]
      exact Submodule.add_mem_sup hw hdw
    have hlat := LatFil.lat_eq_fil D HW F Cm l K s LL h T hT i ζ τ hpt
    have hsingle : (Pi.single k d : ℤ → T.V ⊗[ℚ_[l]] (D.loc l).R.B) ∈ Lat (Cm l) h T i ζ := by
      refine (hlat _).2 ⟨⟨k, fun r hr => Pi.single_eq_of_ne hr.ne _⟩, fun r => ?_⟩
      by_cases hr : r = k
      · subst hr
        simp only [Pi.single_eq_same]
        exact ⟨hd, hdF⟩
      · rw [Pi.single_eq_of_ne hr, map_zero]
        exact ⟨zero_mem _, zero_mem _⟩
    have hfull := GlobalTheory.T.wach_expansions_span_full_lattice D HW F Cm l K s LL h T hT i ζ hprim
    obtain ⟨nb⟩ := @GlobalTheory.NL.N_basis D HW F l _ K s LL h T hT
    have hli := GlobalTheory.T.wachExpansion_basis_divisibility D HW F Cm l K s LL h T hT i ζ ⟨s, hprim⟩ hfull
    obtain ⟨e, he⟩ := (hli.2 _ nb).2.1 _ hsingle
    obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ℕ, ∀ j, ∀ r : ℤ, r < -(a₀ : ℤ) → ex (Cm l) h T i ζ (nb j) r = 0 := by
      choose m hm using fun j => ((Cm l).C K s LL h).tie.levB_supp T i ζ (nb j)
      refine ⟨∑ j, (-m j).toNat, fun j r hr => hm _ _ ?_⟩
      have := Finset.single_le_sum (f := fun j => (-m j).toNat) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j)
      omega
    obtain ⟨m, hm⟩ : ∃ m : ℕ, k < (m : ℤ) - a₀ := ⟨(k + a₀ + 1).toNat, by omega⟩
    have hwd := (GlobalTheory.NL.WDiv.weierstrass_dense D HW l K s LL h).2.2.2 i ζ hprim
    choose a c hc0 hca _ using fun j => hwd (e j) m
    have t1 : ∀ j, c j • ((HW l).W K s LL h).lev i ζ (a j) =
        PowerSeries.C (c j) * ((HW l).W K s LL h).lev i ζ (a j) := fun j => PowerSeries.smul_eq_C_mul _ _
    have hca' : ∀ j, PowerSeries.X ^ m ∣ PowerSeries.C (c j) * ((HW l).W K s LL h).lev i ζ (a j) - e j :=
      fun j => by rw [← t1 j]; exact hca j
    haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
    haveI : IsFractionRing ↥(OL LL) ↥LL.1 :=
      integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥LL.1
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ↥(OL LL))
      (Finset.univ : Finset (Fin _)) c
    choose o ho using fun j => hb j (Finset.mem_univ j)
    have ho' : ∀ j, algebraMap ↥(OL LL) ↥LL.1 (b : ↥(OL LL)) * c j = algebraMap ↥(OL LL) ↥LL.1 (o j) :=
      fun j => (Algebra.smul_def _ _).symm.trans (ho j).symm
    have hb0 : algebraMap ↥(OL LL) ↥LL.1 (b : ↥(OL LL)) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
    let x : ↥(((HW l).W K s LL h).N T) := ∑ j, (algebraMap ↥(OL LL) (AA K LL) (o j) * a j) • nb j
    have hx : ∀ r, ex (Cm l) h T i ζ x r =
        ∑ j, conv (((HW l).W K s LL h).lev i ζ (algebraMap ↥(OL LL) (AA K LL) (o j) * a j)) (ex (Cm l) h T i ζ (nb j)) r := by
      intro r
      show ((Cm l).C K s LL h).tie.levB T i ζ (∑ j, (algebraMap ↥(OL LL) (AA K LL) (o j) * a j) • nb j) r = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact congrFun (hli.1 _ _) r
    have hkey : ∀ r : ℤ, r < (m : ℤ) - a₀ →
        algebraMap ↥(OL LL) ↥LL.1 (b : ↥(OL LL)) • (Pi.single k d : ℤ → T.V ⊗[ℚ_[l]] (D.loc l).R.B) r =
          ex (Cm l) h T i ζ x r := by
      intro r hr
      rw [he, hx, Finset.sum_apply]
      refine Finset.smul_sum.trans (Finset.sum_congr rfl fun j _ => ?_)
      have hlev : ((HW l).W K s LL h).lev i ζ (algebraMap ↥(OL LL) (AA K LL) (o j) * a j) =
          PowerSeries.C (algebraMap ↥(OL LL) ↥LL.1 (o j)) * ((HW l).W K s LL h).lev i ζ (a j) := by
        letI : Algebra ↥(OL LL) (PowerSeries ↥LL.1) := MvPowerSeries.instAlgebra
        have hcom := (((HW l).W K s LL h).lev i ζ).commutes (o j)
        rw [map_mul, hcom, PowerSeries.algebraMap_apply]
      exact (approx_step (algebraMap ↥(OL LL) ↥LL.1 (b : ↥(OL LL))) (c j) _ (e j)
        (((HW l).W K s LL h).lev i ζ (a j)) (ex (Cm l) h T i ζ (nb j)) a₀ m (ha₀ j) (hca' j) (ho' j) r hr).trans
        (congrArg (fun p => conv p (ex (Cm l) h T i ζ (nb j)) r) hlev.symm)
    have hl1 := (GlobalTheory.NL.lev_at_root_of_unity D HW l K s LL h i ζ ⟨s, hprim⟩).2.1
    have hN1 : ∀ j, ((HW l).W K s LL h).levN T i ζ ((letE i : AA K LL) • x) j =
        ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) (ex (Cm l) h T i ζ x j) := by
      intro j
      rw [((HW l).W K s LL h).levN_smul, hl1]
      exact (congrFun (LowLevel.conv_one (((HW l).W K s LL h).levN T i ζ x)) j).trans
        (((Cm l).C K s LL h).tie.levN_eq T i ζ x j)
    have hc : ∀ j, j ≤ k → (algebraMap ↥(OL LL) ↥LL.1 (b : ↥(OL LL)))⁻¹ •
        ((HW l).W K s LL h).levN T i ζ ((letE i : AA K LL) • x) j =
          ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)
            ((Pi.single k d : ℤ → T.V ⊗[ℚ_[l]] (D.loc l).R.B) j) := by
      intro j hj
      rw [hN1, ← map_smul, ← hkey j (by omega), inv_smul_smul₀ hb0]
    refine ⟨x, (algebraMap ↥(OL LL) ↥LL.1 (b : ↥(OL LL)))⁻¹, inv_ne_zero hb0, fun j hj => ?_, ?_⟩
    · rw [hc j hj.le, Pi.single_eq_of_ne hj.ne, map_zero]
      exact zero_mem _
    · rw [hc k le_rfl, Pi.single_eq_same]
      exact Submodule.mem_sup_right hdw

end GlobalTheory.NL.LatLevel
end
end

