module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsZetaTW
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamFROfIsLamF
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApplyPolyOfStable
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0220
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0373
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0357
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0022
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0361
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0348
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0355
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedAwayFromLOfTwistedShapiroLimit
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0168
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousMatQApply
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedH1CardInvariants
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0363
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardGaloisInvariantsOrdinaryRankTwoModPowBounded

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAdmissibleHeckeProjectionNonvanishing
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois GlobalTheory.K4
open scoped TensorProduct MatrixGroups Matrix
open GlobalTheory.LambdaValuationPowers

noncomputable section

namespace GlobalTheory.AdmProj

theorem tmul_mem_VB {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime]
    {b : X.Fn l} (hb : b ∈ X.B N l w) : (1 : Qbar l) ⊗ₜ[ℤ_[l]] b ∈ X.VB N l w (Qbar l) :=
  LinearMap.mem_range.2 ⟨(1 : Qbar l) ⊗ₜ[ℤ_[l]] (⟨b, hb⟩ : X.B N l w), by simp⟩

theorem fixIc_mono {l : ℕ} [Fact l.Prime] {c c' : Coef l} (h : c.O ≤ c'.O) {x : Qbar l} (hx : FixIc c x) : FixIc c' x :=
  fun σ h1 h2 => hx σ (fun y hy => h1 y (h hy)) h2

theorem fixIc_l_pow_mul {l : ℕ} [Fact l.Prime] {c : Coef l} (a : ℕ) {x : Qbar l} (hx : FixIc c x) :
    FixIc c (((l : ℕ) : Qbar l) ^ a * x) := fun σ h1 h2 => by
  rw [map_mul, map_pow, map_natCast, hx σ h1 h2]

theorem exists_admissible_hecke_projection_nonvanishing_alt : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ)
  [Fact l.Prime] (e : ℕ) (S : Finset Pl) (W : R2 Ω l) (ψ : ZMod l → Qbar l) (ι : Qbar l ≃+* ℂ) (gN : Newform (2 * e + 1))
  (j : Ω →+* Qbar l),
  Nf e S A W → 1 ≤ e →
  (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → (l : Ω) ∈ A.nonunits → l ≠ 2 → ¬ l ∣ N → 5 ≤ N →
  (∀ x ∈ A, ‖j x‖ ≤ 1) →
  ∀ (ev : Letter → Qbar l) (ρ : (Ω ≃ₐ[ℚ] Ω) →* GL (Fin 2) (Qbar l)) (F : Finset Ω),
  (∀ s, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) = rhoK W e ψ s) →
  (∀ s ∈ Dec (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 0 = 0) →
  (∀ s ∈ Ine (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 = 1) →
  (∀ s ∈ Ine (F := ℚ) A, (∀ y ∈ F, s y = y) →
    (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 = ((cycZ ℚ Ω l s : ℤ_[l]) : Qbar l) ^ (2 * e - 1 + 1)) →
  (∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ev (Letter.T q) = ι.symm (gN.a q)) →
  ∀ (χ : ℕ → ℤ_[l]), (∀ d : ℕ, Nat.Coprime d N → ev (Letter.D d) = ((χ d : ℤ_[l]) : Qbar l)) →
  ∀ (m : ℕ) (π : Fin m → (Qbar l ⊗[ℤ_[l]] X.Fn l) →ₗ[Qbar l] (Fin 2 → Qbar l))
    (σ : Fin m → (Fin 2 → Qbar l) →ₗ[Qbar l] (Qbar l ⊗[ℤ_[l]] X.Fn l)) (P : FreeAlgebra (Qbar l) Letter),
  P ∈ admissibleLettersSubalgebra (Qbar l) N l → FreeAlgebra.lift (Qbar l) ev P = 1 → (∀ i v, σ i v ∈ X.VB N l (2 * e - 1) (Qbar l)) →
  (∀ i s, ∀ x ∈ X.VB N l (2 * e - 1) (Qbar l), π i (X.galV l (Qbar l) s x) = (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ π i x) →
  (∀ i s v, X.galV l (Qbar l) s (σ i v) = σ i ((ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ v)) →
  (∀ i (T : Letter) v, GlobalTheory.KZ.admitted N l T → X.opV N l (Qbar l) T (σ i v) = ev T • σ i v) →
  (∀ i (T : Letter), GlobalTheory.KZ.admitted N l T → ∀ x ∈ X.VB N l (2 * e - 1) (Qbar l), π i (X.opV N l (Qbar l) T x) = ev T • π i x) →
  (∀ i i' v, π i (σ i' v) = if i = i' then v else 0) →
  (∀ x ∈ X.VB N l (2 * e - 1) (Qbar l), FreeAlgebra.lift (Qbar l) (X.opV N l (Qbar l)) P x = ∑ i, σ i (π i x)) →
  ∀ (c : Coef l) (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l), FinSupp lam → (∀ i : ℕ, FixIc c (lam (Pi.single i 1))) →
  (∃ c₂ : ℕ, ∀ (n : ℕ), c₂ ≤ n → ∀ (T : Letter) (b : X.Fn l), GlobalTheory.KZ.admitted N l T → InChi X N (2 * e - 1) χ b →
    Cg (n - c₂) (lam (seqN 1 j (thN X A N l n 1 (X.op N l T b)))) (ev T * lam (seqN 1 j (thN X A N l n 1 b)))) →
  ∃ (pr : X.Fn l → Fin 2 → Qbar l) (a : ℕ) (cf : Coef l),
    c.O ≤ cf.O ∧ (∀ s i k, mat W s i k ∈ cf.O) ∧
    (∀ b b', pr (b + b') = pr b + pr b') ∧
    (∀ (z : ℤ_[l]) b, pr (z • b) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) • pr b) ∧
    (∀ b ∈ X.B N l (2 * e - 1), ∀ i, pr b i ∈ cf.O) ∧
    (∀ (s : Ω ≃ₐ[ℚ] Ω) b, b ∈ X.B N l (2 * e - 1) → pr (X.galB l s b) = rhoK W e ψ s *ᵥ pr b) ∧
    (∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ∀ b, b ∈ X.B N l (2 * e - 1) → pr (X.heckeT N l q b) = ι.symm (gN.a q) • pr b) ∧
    (∀ d : ℕ, Nat.Coprime d N → ∀ b, b ∈ X.B N l (2 * e - 1) → pr (X.diam N l d b) = ((χ d : ℤ_[l]) : Qbar l) • pr b) ∧
    (∀ b ∈ X.B N l (2 * e - 1), pr (X.heckeU l b) = ev Letter.U • pr b) ∧
    IsLamFR2 X A N (2 * e - 1) χ j pr cf ((((l : ℕ) : Qbar l) ^ a) • lam) := by
  intro Ω _ _ _ ε X A N l _ e S W ψ ι gN j hNf he hφ hlA hl2 hlN hN5 hj ev ρ F hρ hDec hIne hIne0 hev χ hχ m π σ P hPadm hPev
    hσV hπgal hσgal hσT heig hπσ hPx c lam hlamF hlamI hlamE
  classical
  have hodd : Odd (2 * e - 1) := ⟨e - 1, by omega⟩
  have hinj : Function.Injective ε := ε.injective
  have hφ' : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero) := by
    obtain ⟨φ, h1, h2⟩ := hφ; exact ⟨φ, h2, h1⟩
  have hcop : Nat.Coprime N l := ((Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).2 hlN).symm
  obtain ⟨pr0, ⟨κ, hκ⟩, hLam⟩ := GlobalTheory.LamChi.exists_pr_isLamFR ε X A N l (2 * e - 1) j hφ hlA hl2 hlN hN5 hodd hj ev ρ F hDec hIne hIne0
    m π σ P hPadm hPev hσV hπgal hσgal hσT hπσ hPx χ c lam hlamF hlamI hlamE

  have hadd0 : ∀ b b', pr0 (b + b') = pr0 b + pr0 b' := by
    intro b b'
    simp only [hκ, TensorProduct.tmul_add, map_add (f := _), smul_add, Finset.sum_add_distrib]
  have hsmul0 : ∀ (z : ℤ_[l]) b, pr0 (z • b) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) • pr0 b := by
    intro z b
    rw [hκ, hκ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.tmul_smul, ← algebraMap_smul (Qbar l) z, map_smul, smul_comm]
    rfl
  have hgal0 : ∀ (s : Ω ≃ₐ[ℚ] Ω) b, b ∈ X.B N l (2 * e - 1) → pr0 (X.galB l s b) = rhoK W e ψ s *ᵥ pr0 b := by
    intro s b hb
    rw [hκ, hκ, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 : (1 : Qbar l) ⊗ₜ[ℤ_[l]] X.galB l s b = X.galV l (Qbar l) s ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b) := by
      simp [Tower.galV]
    rw [e1, hπgal i s _ (tmul_mem_VB X N l (2 * e - 1) hb), hρ s, Matrix.mulVec_smul]
  have hop0 : ∀ T : Letter, GlobalTheory.KZ.admitted N l T → ∀ b, b ∈ X.B N l (2 * e - 1) → pr0 (X.op N l T b) = ev T • pr0 b := by
    intro T hT b hb
    rw [hκ, hκ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 : (1 : Qbar l) ⊗ₜ[ℤ_[l]] X.op N l T b = X.opV N l (Qbar l) T ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b) := by
      simp [Tower.opV]
    rw [e1, heig i T hT _ (tmul_mem_VB X N l (2 * e - 1) hb), smul_comm]

  obtain ⟨c1, hc1⟩ := hNf.int
  obtain ⟨c0, hcc0, hc10⟩ := (UpperTheory.V.HV.coefSup l).1 c c1
  have hfree := GlobalTheory.KZ.B_free_finite ε X hinj hφ' N l (2 * e - 1) hl2 hN5 hcop hodd
  haveI := hfree.1
  haveI := hfree.2
  let bs := Module.Free.chooseBasis ℤ_[l] (X.B N l (2 * e - 1))
  obtain ⟨a, ha⟩ := exists_le_l_pow l
    (∑ p : Module.Free.ChooseBasisIndex ℤ_[l] (X.B N l (2 * e - 1)) × Fin 2, ‖pr0 (bs p.1) p.2‖)
  have hsmall : ∀ p : Module.Free.ChooseBasisIndex ℤ_[l] (X.B N l (2 * e - 1)) × Fin 2,
      ‖((l : ℕ) : Qbar l) ^ a * pr0 (bs p.1) p.2‖ ≤ 1 := by
    intro p
    have h1 : ‖pr0 (bs p.1) p.2‖ ≤ (l : ℝ) ^ a :=
      le_trans (Finset.single_le_sum
        (f := fun p : Module.Free.ChooseBasisIndex ℤ_[l] (X.B N l (2 * e - 1)) × Fin 2 => ‖pr0 (bs p.1) p.2‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ p)) ha
    have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
    rw [norm_mul, norm_l_pow]
    calc ((l : ℝ)⁻¹) ^ a * ‖pr0 (bs p.1) p.2‖ ≤ ((l : ℝ)⁻¹) ^ a * (l : ℝ) ^ a :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ hl0.ne', one_pow]
  obtain ⟨cf, hcf, hs⟩ := GlobalTheory.PowerSeriesEvalAlgCl.exists_coef_ge_finset c0
    (Finset.univ.image fun p : Module.Free.ChooseBasisIndex ℤ_[l] (X.B N l (2 * e - 1)) × Fin 2 =>
      ((l : ℕ) : Qbar l) ^ a * pr0 (bs p.1) p.2)
    (fun y hy => by
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hy
      exact (GlobalTheory.PowerSeriesEvalAlgCl.isIntegral_iff_norm_le_one _).2 (hsmall p))

  obtain ⟨pr, hpr⟩ : ∃ pr : X.Fn l → Fin 2 → Qbar l, ∀ b, pr b = ((l : ℕ) : Qbar l) ^ a • pr0 b := ⟨_, fun _ => rfl⟩
  have hadd : ∀ b b', pr (b + b') = pr b + pr b' := by
    intro b b'; rw [hpr, hpr, hpr, hadd0, smul_add]
  have hsmul : ∀ (z : ℤ_[l]) b, pr (z • b) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) • pr b := by
    intro z b; rw [hpr, hpr, hsmul0, smul_comm]
  have hint : ∀ b ∈ X.B N l (2 * e - 1), ∀ i, pr b i ∈ cf.O := by
    intro b hb i
    let g : X.B N l (2 * e - 1) →ₗ[ℤ_[l]] Qbar l :=
      { toFun := fun y => pr y.1 i
        map_add' := fun y y' => by
          simp only [Submodule.coe_add, hadd, Pi.add_apply]
        map_smul' := fun z y => by
          simp only [SetLike.val_smul, hsmul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Algebra.smul_def]
          rfl }
    have hle : Submodule.span ℤ_[l] (Set.range bs) ≤ (Subalgebra.toSubmodule cf.O).comap g := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      have := hs _ (Finset.mem_image.2 ⟨(k, i), Finset.mem_univ _, rfl⟩)
      simpa [g, hpr] using this
    rw [bs.span_eq] at hle
    exact hle (Submodule.mem_top (x := (⟨b, hb⟩ : X.B N l (2 * e - 1))))
  have hgal : ∀ (s : Ω ≃ₐ[ℚ] Ω) b, b ∈ X.B N l (2 * e - 1) → pr (X.galB l s b) = rhoK W e ψ s *ᵥ pr b := by
    intro s b hb; rw [hpr, hpr, hgal0 s b hb, Matrix.mulVec_smul]
  have hhecke : ∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ∀ b, b ∈ X.B N l (2 * e - 1) →
      pr (X.heckeT N l q b) = ι.symm (gN.a q) • pr b := by
    intro q hq hqd b hb
    have hT : GlobalTheory.KZ.admitted N l (Letter.T q) := ⟨hq, fun h => hqd (by rwa [mul_comm] at h)⟩
    have := hop0 _ hT b hb
    rw [hpr, hpr, show X.heckeT N l q b = X.op N l (Letter.T q) b from rfl, this, hev q hq hqd, smul_comm]
  have hdiam : ∀ d : ℕ, Nat.Coprime d N → ∀ b, b ∈ X.B N l (2 * e - 1) →
      pr (X.diam N l d b) = ((χ d : ℤ_[l]) : Qbar l) • pr b := by
    intro d hd b hb
    have := hop0 (Letter.D d) hd b hb
    rw [hpr, hpr, show X.diam N l d b = X.op N l (Letter.D d) b from rfl, this, hχ d hd, smul_comm]
  have hU : ∀ b ∈ X.B N l (2 * e - 1), pr (X.heckeU l b) = ev Letter.U • pr b := by
    intro b hb
    have := hop0 Letter.U trivial b hb
    rw [hpr, hpr, show X.heckeU l b = X.op N l Letter.U b from rfl, this, smul_comm]
  have hnorm : ‖((l : ℕ) : Qbar l) ^ a‖ ≤ 1 := by
    rw [norm_l_pow]
    have h1 : (1 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).one_le
    exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ h1)
  have hccf : c.O ≤ cf.O := hcc0.trans hcf
  have hlam : IsLamFR X A N (2 * e - 1) χ j pr cf ((((l : ℕ) : Qbar l) ^ a) • lam) := by
    obtain ⟨hf, hw, cL, per, hper, hc⟩ := hLam
    refine ⟨hf.smul _, fun i => fixIc_l_pow_mul a (fixIc_mono hccf (hw i)), cL, per,
      fun n => ⟨(hper n).1, (hper n).2.1, fixIc_mono hccf (hper n).2.2⟩, fun n hn b hb φ hφ => ?_⟩
    have h := hc n hn b hb φ hφ
    unfold GlobalTheory.Ord2.Cg at h ⊢
    rw [hpr, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    calc ‖((l : ℕ) : Qbar l) ^ a * lam (seqN 1 j φ) - per n * (((l : ℕ) : Qbar l) ^ a * pr0 b 1)‖
        = ‖((l : ℕ) : Qbar l) ^ a‖ * ‖lam (seqN 1 j φ) - per n * pr0 b 1‖ := by
          rw [← norm_mul]; congr 1; ring
      _ ≤ 1 * ‖((l : ℕ) : Qbar l) ^ (n - cL)‖ := mul_le_mul hnorm h (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  exact ⟨pr, a, cf, hccf, fun s i k => hcf (hc10 (hc1 s i k)), hadd, hsmul, hint, hgal, hhecke, hdiam, hU, hdiam, hlam⟩

end GlobalTheory.AdmProj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHtPresNu7
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open scoped Matrix

namespace GlobalTheory.KZ.UnitPres

open GlobalTheory.KumUnit

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem kumVal_int {n : ℕ} {ζ u v : Ω} {s : G ℚ Ω} {j : ℤ} (hζ : ζ ^ (l ^ n) = 1) (hv : v ^ (l ^ n) = u)
    (hs : s v = ζ ^ j * v) : GlobalTheory.Col.KumVal (l := l) n ζ u s (j : ZMod (l ^ n)) := by
  have hpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  haveI : NeZero (l ^ n) := ⟨hpos.ne'⟩
  have h0 : ζ ≠ 0 := by rintro rfl; rw [zero_pow hpos.ne'] at hζ; exact zero_ne_one hζ
  refine ⟨v, hv, ?_⟩
  rw [hs, ← zpow_natCast, ZMod.val_intCast]
  congr 1
  conv_lhs => rw [← Int.emod_add_mul_ediv j ((l ^ n : ℕ) : ℤ)]
  rw [zpow_add₀ h0, zpow_mul, zpow_natCast, hζ, one_zpow, mul_one]

theorem cg_intCast (n : ℕ) (j : ℤ) : Cg (l := l) n (((j : ZMod (l ^ n)).val : ℕ) : Qbar l) (j : Qbar l) := by
  have hpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  haveI : NeZero (l ^ n) := ⟨hpos.ne'⟩
  have h1 : (((j : ZMod (l ^ n)).val : ℕ) : ℤ) - j = ((l ^ n : ℕ) : ℤ) * (-(j / ((l ^ n : ℕ) : ℤ))) := by
    rw [ZMod.val_intCast, Int.emod_def]; ring
  have e : (((j : ZMod (l ^ n)).val : ℕ) : Qbar l) - (j : Qbar l) =
      (l : Qbar l) ^ n * ((-(j / ((l ^ n : ℕ) : ℤ)) : ℤ) : Qbar l) := by
    have := congrArg (Int.cast : ℤ → Qbar l) h1
    rw [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, Nat.cast_pow] at this
    exact this
  rw [Cg, e, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one (Qbar l) _)

theorem exists_open [IsAlgClosure ℚ Ω] (h : G ℚ Ω → Qbar l) (hc : Continuous h) (h1 : h 1 = 0) (m : ℕ) :
    ∃ U : Subgroup (G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) ∧ ∀ s ∈ U, Cg m (h s) 0 := by
  have hl : (0 : ℝ) < ‖((l : ℕ) : Qbar l) ^ m‖ :=
    norm_pos_iff.2 (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero))
  have hn : {s | ‖h s‖ < ‖((l : ℕ) : Qbar l) ^ m‖} ∈ nhds (1 : G ℚ Ω) :=
    (isOpen_lt hc.norm continuous_const).mem_nhds (by simpa [h1] using hl)
  obtain ⟨E, hE, hsub⟩ := (krullTopology_mem_nhds_one_iff ℚ Ω _).1 hn
  refine ⟨E.fixingSubgroup, E.fixingSubgroup_isOpen, fun s hs => ?_⟩
  rw [Cg, sub_zero]
  exact le_of_lt (hsub hs)

theorem layer_one {c : Coef l} {A : ValuationSubring Ω} {ν : G ℚ Ω → (Qbar l)ˣ} {r : ℕ}
    {z : G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l} (hz : Layer2 c A ν r z) : z 1 1 = 0 := by
  have h := hz.2 1 (one_mem _) 1 (one_mem _) 1
  rw [mul_one, map_one, inv_one, mul_one] at h
  have h' : (ν 1 : Qbar l) * z 1 1 = 0 := by linear_combination -h
  exact (mul_eq_zero.1 h').resolve_left (ν 1).ne_zero

theorem layer_add {c : Coef l} {A : ValuationSubring Ω} {ν : G ℚ Ω → (Qbar l)ˣ} {r : ℕ}
    {z : G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l} (hz : Layer2 c A ν r z) {s t : G ℚ Ω} (hs : s ∈ Dec (F := ℚ) A)
    (ht : t ∈ Dec (F := ℚ) A) (hc : cycMod ℚ Ω l r s = 1) : z (s * t) 1 = z s 1 + (ν s : Qbar l) * z t 1 := by
  have h := hz.2 s hs t ht 1
  rwa [hc, inv_one, mul_one] at h

end GlobalTheory.KZ.UnitPres
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPolynomialPrimitiveRootOfCyclotomicInertiaStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polynomial_primitiveRoot_of_cyclotomic_inertia_fixed : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (m : ℕ) (ζ : Ω), IsPrimitiveRoot ζ (l ^ m) → ∀ u ∈ A, (∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 → s u = u) → ∃ P : Polynomial Ω, (∀ x ∈ P.coeffs, x ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s x = x) ∧ P.eval ζ = u := by
  first | exact @GlobalTheory.CycIne.exists_poly_of_fixed | exact GlobalTheory.CycIne.exists_poly_of_fixed | (intros; apply GlobalTheory.CycIne.exists_poly_of_fixed; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPrimitiveCharacterTwistStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primitive_character_twist : ∀ (l : ℕ) [Fact l.Prime] (φ : DirichletCharacter (Qbar l) l) (e k : ℕ) (ζ : Qbar l), l ≠ 2 → 1 ≤ k → IsPrimitiveRoot ζ (l ^ k) → ∃ ψ : DirichletCharacter (Qbar l) (l ^ (k + 1)), ψ.IsPrimitive ∧ InComp φ e ψ ∧ ψ⁻¹ (1 + (l : ZMod (l ^ (k + 1)))) = ζ := by
  first | (exact @GlobalTheory.KZ.Cmp.PrimChar.exists_primitive_inComp) | (exact GlobalTheory.KZ.Cmp.PrimChar.exists_primitive_inComp) | (intros; apply GlobalTheory.KZ.Cmp.PrimChar.exists_primitive_inComp  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsZetaDerivationInertiaCyclotomicAlgebraStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zeta_derivation_inertia_cyclotomic_algebra : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (N : ℕ) (z : A), IsPrimitiveRoot (z : Ω) (l ^ N) → ∃ D : A → FracA A, IsDerOn (cycAlg l A) D ∧ D z = Submodule.Quotient.mk ((z : Ω) * (l : Ω) / (l : Ω) ^ N) := by
  first | (exact @GlobalTheory.RecOne.zeta_derivation_cyc) | (exact GlobalTheory.RecOne.zeta_derivation_cyc) | (intros; apply GlobalTheory.RecOne.zeta_derivation_cyc  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlobOfShapiroSystem
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory.KZGlobAsm

theorem norm_le_one_of_mem {l : ℕ} [Fact l.Prime] (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.Rc8.norm_le_one_of_mem c hx

theorem inv_pow_val_mem (l : ℕ) [Fact l.Prime] (c : Coef l) (e r : ℕ) (x : (ZMod (l ^ r))ˣ) :
    ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ ∈ c.O :=
  _root_.GlobalTheory.PadicInversePower.inv_pow_mem l c e r x

theorem eta_compat (l : ℕ) [Fact l.Prime] (c : Coef l) (e : ℕ) (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l)
    (hχ : ∀ r x, χ r x ∈ c.O)
    (hχc : ∀ r (x : (ZMod (l ^ (r + 1)))ˣ), ‖χ (r + 1) x - χ r ((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖)
    (r : ℕ) (x : (ZMod (l ^ (r + 1)))ˣ) :
    ‖(fun x : (ZMod (l ^ (r + 1)))ˣ => ((((x : ZMod (l ^ (r + 1))).val : ℕ) : Qbar l) ^ e)⁻¹ * χ (r + 1) x) x -
      (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x)
        ((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ :=
  _root_.GlobalTheory.PadicNormCastBounds.twist_compat l c e χ hχ hχc r x

end GlobalTheory.KZGlobAsm

namespace GlobalTheory.KZ

end GlobalTheory.KZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GreenbergWilesDualSelmerLowerBoundModPrimePow
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.GwIneq

theorem exists_cc (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] :
    ∃ cc : InfinitePlace ℚ → G ℚ Ω, ∀ w, w.IsReal → IsCCAt w (cc w) := by
  have h : ∀ w : InfinitePlace ℚ, ∃ c : G ℚ Ω, w.IsReal → IsCCAt w c := fun w => by
    by_cases hw : w.IsReal
    · haveI : Module.IsTorsionFree ℚ Ω := DivisionSemiring.to_moduleIsTorsionFree
      haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
      haveI : IsGalois ℚ Ω := {}
      letI : Algebra ℚ ℂ := w.embedding.toAlgebra
      let j : Ω →ₐ[ℚ] ℂ := (by
        refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
        solve_by_elim* (maxDepth := 2) only [*,
          @_root_.DivisionSemiring.to_moduleIsTorsionFree,
          @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
      have hr : ComplexEmbedding.IsReal w.embedding := InfinitePlace.isReal_iff.1 hw
      let cj : ℂ →ₐ[ℚ] ℂ := { starRingEnd ℂ with commutes' := fun x => RingHom.congr_fun hr x }
      letI : Algebra Ω ℂ := j.toRingHom.toAlgebra
      haveI : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
      refine ⟨(cj.comp j).restrictNormal' Ω, fun _ => ⟨j.toRingHom, fun x => ?_, ?_⟩⟩
      · exact AlgHom.restrictNormal_commutes (cj.comp j) Ω x
      · rw [show j.toRingHom.comp (algebraMap ℚ Ω) = w.embedding from RingHom.ext fun x => j.commutes x]
        exact w.mk_embedding
    · exact ⟨1, fun h => absurd h hw⟩
  choose cc hcc using h
  exact ⟨cc, hcc⟩

theorem gw_ineq : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → ∀ (N : ℕ) (y : Fin N → G ℚ Ω → Fin 2 → Qbar l), (∀ i, GwCount.SelN c n S A W (y i)) → (∀ i j, i ≠ j → ¬ Cob1 c n W ⊤ (y i - y j)) → ∃ (N' : ℕ) (z : Fin N' → G ℚ Ω → Fin 2 → Qbar l), N ≤ C * N' ∧ (∀ i, GwCount.SelN c n S A (dual1 W) (z i)) ∧ ∀ i j, i ≠ j → ¬ Cob1 c n (dual1 W) ⊤ (z i - z j) := by
  classical
  intro hL l _ Ω _ _ _ e S A W hW c hint
  have hN := kills_NS hW
  obtain ⟨C0, hC0⟩ := _root_.GlobalTheory.Ord2.GwCard.exists_card_H0_rhoS_le l Ω e S A W hW c hint hN
  obtain ⟨CA, hCA⟩ := _root_.GlobalTheory.Ord2.GwIneq.CardOrd.card_ord hL l Ω e S A W hW c hint hN
  refine ⟨C0 * CA, fun n hn N y hy hyd => ?_⟩
  have hn0 : 0 < n := hn
  have hS := hW.above
  obtain ⟨μ, hμ⟩ := GlobalTheory.Published.PoitouTate.exists_lift_cycMod (F := ℚ) (Ω := Ω) (l := l) (r := n) (S := S) hS
  obtain ⟨cc, hcc⟩ := exists_cc Ω
  have hρ : ReciprocityTheory.Gal.ContAction (rhoS c n W hint S hN) := contAction_rhoS c n W hint S hN hW.cont
  have hgw := hL.gw ℚ Ω l n (Mn c n) S (rhoS c n W hint S hN) hn0 hW.l_odd hS hρ μ hμ (Av A S)
    (isPlaceOver_Av A S) cc hcc (Lc c n W hint S hN A)
  have hρd : ReciprocityTheory.Gal.ContAction (twDual μ (rhoS c n W hint S hN)) :=
    GlobalTheory.DualSide.contAction_twDual (GlobalTheory.Published.PoitouTate.contAction_charRep hμ) hρ
  haveI : Finite (TDual (ZMod (l ^ n)) (Mn c n)) := GlobalTheory.DualSide.finite_TDual
  haveI : Finite (H1 (rhoS c n W hint S hN)) := (hL.gf ℚ Ω l n (Mn c n) S _ hn0 hS hρ).2.1
  haveI : Finite (H1 (twDual μ (rhoS c n W hint S hN))) :=
    (hL.gf ℚ Ω l n (TDual (ZMod (l ^ n)) (Mn c n)) S _ hn0 hS hρd).2.1

  obtain ⟨v0, hA0, hl0⟩ := hW.atL
  let vA : S := ⟨v0, hS v0 hl0⟩
  have huniq : ∀ v w : Pl, IsPlaceOver A v → IsPlaceOver A w → v = w := fun v w hv hw =>
    HeightOneSpectrum.ext (Ideal.ext fun x => (hv x).symm.trans (hw x))
  have hLv : ∀ v : S, v ≠ vA → Nat.card (Lc c n W hint S hN A v) =
      Nat.card (H0 ((rhoS c n W hint S hN).comp (locFam S (Av A S) v))) := by
    intro v hv
    have hnp : ¬ IsPlaceOver A v.1 := fun h => hv (Subtype.ext (huniq _ _ h hA0))
    have e1 : Lc c n W hint S hN A v = H1ur ((rhoS c n W hint S hN).comp (locFam S (Av A S) v))
        ((Ine (F := ℚ) (Av A S v)).subgroupOf (Dec (F := ℚ) (Av A S v))) := if_neg hnp
    rw [e1]
    exact GlobalTheory.Ord2.UrCard.card_unramified_h1_eq_card_h0 ℚ Ω l n (Mn c n) (Av A S v) v.1 _
      (hρ.comp' (continuous_locFam S (Av A S) v)) (isPlaceOver_Av A S v)
  have harch := _root_.GlobalTheory.Ord2.GwIneq.Arch.archimedean_h0_card_eq l Ω e S A W hW c hint hN n hn cc hcc
  rw [harch, ← Finset.mul_prod_erase _ _ (Finset.mem_univ vA),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ vA),
    Finset.prod_congr rfl fun v hv => hLv v (Finset.ne_of_mem_erase hv)] at hgw
  have hLA := hCA n hn vA hA0
  have hH0 := hC0 n hn
  have hP : 0 < ∏ v ∈ Finset.univ.erase vA, Nat.card (H0 ((rhoS c n W hint S hN).comp (locFam S (Av A S) v))) :=
    Finset.prod_pos fun v _ => Nat.card_pos
  have hq : 0 < Nat.card (Qn c n) := Nat.card_pos
  have h1d : 1 ≤ Nat.card (H0 (twDual μ (rhoS c n W hint S hN))) := Nat.card_pos
  have h1A : 1 ≤ Nat.card (H0 ((rhoS c n W hint S hN).comp (locFam S (Av A S) vA))) := Nat.card_pos
  set P := ∏ v ∈ Finset.univ.erase vA, Nat.card (H0 ((rhoS c n W hint S hN).comp (locFam S (Av A S) v)))
  have hsel : Nat.card (SelG c n W hint S hN A) ≤ C0 * CA * Nat.card (SelD c n W hint S hN A hW.cont μ) := by
    have key : Nat.card (SelG c n W hint S hN A) * (Nat.card (Qn c n) * P) ≤
        (C0 * CA * Nat.card (SelD c n W hint S hN A hW.cont μ)) * (Nat.card (Qn c n) * P) := by
      calc Nat.card (SelG c n W hint S hN A) * (Nat.card (Qn c n) * P)
          = Nat.card (SelG c n W hint S hN A) * 1 * (1 * P) * Nat.card (Qn c n) := by ring
        _ ≤ Nat.card (SelG c n W hint S hN A) * Nat.card (H0 (twDual μ (rhoS c n W hint S hN))) *
            (Nat.card (H0 ((rhoS c n W hint S hN).comp (locFam S (Av A S) vA))) * P) * Nat.card (Qn c n) := by
          gcongr
        _ = Nat.card (SelD c n W hint S hN A hW.cont μ) * Nat.card (H0 (rhoS c n W hint S hN)) *
            (Nat.card (Lc c n W hint S hN A vA) * P) := hgw
        _ ≤ Nat.card (SelD c n W hint S hN A hW.cont μ) * C0 * (CA * Nat.card (Qn c n) * P) := by
          gcongr
        _ = (C0 * CA * Nat.card (SelD c n W hint S hN A hW.cont μ)) * (Nat.card (Qn c n) * P) := by ring
    exact Nat.le_of_mul_le_mul_right key (Nat.mul_pos hq hP)

  obtain ⟨cls, hcls, hinj⟩ := _root_.GlobalTheory.Ord2.SelLower.sel_lower l Ω e S A W hW c hint hN n hn
  have hN1 : N ≤ Nat.card (SelG c n W hint S hN A) := by
    let f : Fin N → SelG c n W hint S hN A := fun i => ⟨cls (y i), hcls _ (hy i)⟩
    have hf : Function.Injective f := by
      intro i j hij
      by_contra hne
      exact hyd i j hne (hinj _ _ (hy i) (hy j) (congrArg Subtype.val hij))
    simpa using Nat.card_le_card_of_injective f hf

  obtain ⟨z, hz, hzd⟩ := _root_.GlobalTheory.Ord2.SelPerp.sel_perp hL l Ω e S A W hW c hint hN n hn μ hμ
  let eqv := Finite.equivFin (SelD c n W hint S hN A hW.cont μ)
  refine ⟨Nat.card (SelD c n W hint S hN A hW.cont μ), fun i => z (eqv.symm i), ?_, fun i => hz _, ?_⟩
  · exact hN1.trans hsel
  · intro i j hij
    exact hzd _ _ (fun h => hij (eqv.symm.injective h))

end GlobalTheory.Ord2.GwIneq
end
end

