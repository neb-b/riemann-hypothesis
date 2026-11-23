module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CohomologyUnramifiedLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0368
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0348
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UntwistedRepresentationOrdinaryTriangularShape
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsZetaTW
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamFROfIsLamF
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0351
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0355
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardDualCocyclesModPrimePowUnramifiedOutsideSBou
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepresentationOfEigensystem
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0376
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0361
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0367
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0052

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CohomologyUnramifiedLiftStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomology_unramified_lift : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ (c : Coef l) (y z : G ℚ Ω → Fin 2 → Qbar l) (u : G ℚ Ω → Qbar l) (S' : Finset Pl) (n : ℕ), 1 ≤ n → (∀ s i j, mat W s i j ∈ c.O) → y ∈ Z1 (Loc.colRep W) → z ∈ Z1 (Loc.colRep (dual1 W)) → (∀ s i, y s i ∈ c.O) → (∀ s i, z s i ∈ c.O) → Unr W y → (∀ q : Pl, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B q → ∃ x : Fin 2 → Qbar l, (∀ i, x i ∈ c.O) ∧ ∀ s ∈ Ine (F := ℚ) B, z s = mat (dual1 W) s *ᵥ x - x) → (∃ x : Fin 2 → Qbar l, (∀ i, x i ∈ c.O) ∧ ∀ s ∈ Dec (F := ℚ) A, z s = mat (dual1 W) s *ᵥ x - x) → (∀ w : Pl, w ∉ S' → l ^ n ∣ normV w - 1 → ∀ ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n)), KillsMu (normV w) ψ → Function.Surjective ψ → Tame c W y n w ψ) → Continuous u → (∀ s, u s ∈ c.O) → (∀ s, ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cg n (u (s * a)) (u s)) → (∀ s t, Cg n (cup W y z s t) (eps l s * u t - u (s * t) + u s)) → ∀ σ ∈ ⁅H0g W, H0g W⁆, Cg n ((mat W σ - 1).det * ht W y z u σ) 0 := by
  first | exact @GlobalTheory.Ord2.ht_vanish_commutator | exact GlobalTheory.Ord2.ht_vanish_commutator | (intros; apply GlobalTheory.Ord2.ht_vanish_commutator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousOfCg
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4
open scoped Matrix MatrixGroups

namespace GlobalTheory.LambdaValuationPowers.AllRoots

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem pres_of_vanish (A : ValuationSubring Ω) (c : Coef l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (m : ℕ) (ζ : Ω)
    (hζ : IsPrimitiveRoot ζ (l ^ m)) (hZ : ∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 → Z m s 1 = 0) :
    ∃ (ι : Type) (_ : Fintype ι) (P : ι → Polynomial Ω) (o : ι → Qbar l), HTPresNuOfPolys A c m 0 Z ζ P o := by
  refine ⟨Empty, inferInstance, fun i => i.elim, fun i => i.elim, hζ, fun i => i.elim, fun i => i.elim, fun i => i.elim, ?_⟩
  have h := GlobalTheory.Col.kumPres_empty A (n := m - 0) (r := m) (ζ := ζ ^ l ^ 0) (by simpa using hζ) (by omega) (Z m) hZ
  convert h using 2 <;> exact Empty.elim ‹_›

theorem continuous_of_cg [Algebra.IsAlgebraic ℚ Ω] (f : G ℚ Ω → Qbar l)
    (h : ∀ n : ℕ, ∃ E0 : Finset Ω, ∀ s s' : G ℚ Ω, (∀ z ∈ E0, s' z = z) → Cg n (f (s * s')) (f s)) : Continuous f := by
  have hnl : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
    have : (l : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap', Padic.norm_p]
  have hlt1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  rw [continuous_iff_continuousAt]
  intro s
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hlt1
  obtain ⟨E0, hE⟩ := h n
  have hopen : ∀ᶠ t in nhds (1 : G ℚ Ω), ∀ z ∈ E0, t z = z := by
    rw [Filter.eventually_all_finset]
    intro z _
    have ho := stabilizer_isOpen_of_isIntegral (K := ℚ) (L := Ω) z
    exact ho.mem_nhds (one_mem _)
  have hcont : Filter.Tendsto (fun t : G ℚ Ω => s⁻¹ * t) (nhds s) (nhds 1) := by
    have := (continuous_const_mul s⁻¹).tendsto s
    rwa [inv_mul_cancel] at this
  filter_upwards [hcont.eventually hopen] with t ht
  have := hE s (s⁻¹ * t) ht
  rw [mul_inv_cancel_left, Cg, norm_pow, hnl] at this
  rw [dist_eq_norm]
  exact this.trans_lt hn

end GlobalTheory.LambdaValuationPowers.AllRoots
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAdmissibleHeckeProjectionNonvanishingStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois GlobalTheory.K4
open scoped TensorProduct MatrixGroups Matrix
open GlobalTheory.LambdaValuationPowers
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_admissible_hecke_projection_nonvanishing : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ)
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
  first | (exact @GlobalTheory.AdmProj.exists_admissible_hecke_projection_nonvanishing_alt) | (exact GlobalTheory.AdmProj.exists_admissible_hecke_projection_nonvanishing_alt) | (intros; apply GlobalTheory.AdmProj.exists_admissible_hecke_projection_nonvanishing_alt  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualSelmerClassesUnboundedOrder
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.GwCount

theorem dual_classes_unbounded : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ¬ GrZero W A → ∃ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) ∧ ∀ m : ℕ, ∃ (n : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l), Coc1 c n (dual1 W) ⊤ z ∧ (∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z a) 0) ∧ (∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧ Cob1 c n (dual1 W) (Ine (F := ℚ) B) z) ∧ (∃ x ∈ c.O, ∀ s ∈ Dec (F := ℚ) A, Cg n (z s 1) (mat (dual1 W) s 1 1 * x - x)) ∧ ¬ Cob1 c n (dual1 W) ⊤ (fun s => ((l : ℕ) : Qbar l) ^ m • z s) := by
  intro hL l _ Ω _ _ _ e S A W hN hG
  obtain ⟨y, hyZ, hyU, hyG, hyB⟩ : ∃ y ∈ Z1 (Loc.colRep W), Unr W y ∧ Gr W A y ∧
      y ∉ ReciprocityTheory.Gal.B1 (Loc.colRep W) := by
    unfold GrZero at hG; push_neg at hG; exact hG
  have hcol : ∀ s (x : Fin 2 → Qbar l), Loc.colRep W s x = mat W s *ᵥ x := fun s x => by
    simp [Loc.colRep, Matrix.toLin'_apply]
  obtain ⟨c0, hc0⟩ := hN.int
  obtain ⟨c, k, hle, hYi, hYu, -, hYg⟩ := GlobalTheory.T.galois_cocycle_integral_after_scaling l Ω S W c0 y hN.cont hc0 hN.unr hyZ hyU A
  have hW : ∀ s i j, mat W s i j ∈ c.O := fun s i j => hle (hc0 s i j)
  obtain ⟨Y, hY⟩ : ∃ Y : G ℚ Ω → Fin 2 → Qbar l, Y = fun s => ((l : ℕ) : Qbar l) ^ k • y s := ⟨_, rfl⟩
  have hYs : ∀ s, Y s = ((l : ℕ) : Qbar l) ^ k • y s := fun s => by rw [hY]
  have hYZ : Y ∈ Z1 (Loc.colRep W) := by
    have : Y = ((l : ℕ) : Qbar l) ^ k • y := by rw [hY]; rfl
    rw [this]; exact (Z1 _).smul_mem _ hyZ
  have hYcoc : ∀ s t, Y (s * t) = Y s + mat W s *ᵥ Y t := fun s t => by
    rw [hYZ.2 s t, hcol]
  have hYI : ∀ s i, Y s i ∈ c.O := fun s i => by
    rw [hYs, Pi.smul_apply, smul_eq_mul]; exact hYi s i
  have hl0 : ((l : ℕ) : Qbar l) ^ k ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hYB : Y ∉ ReciprocityTheory.Gal.B1 (Loc.colRep W) := by
    intro h; apply hyB
    rw [mem_coboundaries1] at h ⊢
    obtain ⟨x, hx⟩ := h
    refine ⟨(((l : ℕ) : Qbar l) ^ k)⁻¹ • x, fun g => ?_⟩
    have h1 := hx g
    rw [hYs] at h1
    rw [map_smul, ← smul_sub, ← h1, smul_smul, inv_mul_cancel₀ hl0, one_smul]
  obtain ⟨k0, hk0⟩ := _root_.GlobalTheory.Ord2.GwCount.closed_multiplier l Ω W c Y hW hYZ hYI hYB
  have hY0 : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Y a = 0 := by
    refine GlobalTheory.T.cocycle_vanishes_on_ker_toGS_of_inertia_coboundary l Ω e S A W Y hN hYZ fun q hq B hB => ?_
    have hlq : ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal := fun h => hq (hN.above q h)
    obtain ⟨x, -, hx⟩ := hYu q hlq B hB
    exact ⟨x, fun s hs => by rw [hYs]; exact hx s hs⟩
  refine ⟨c, hW, fun m => ?_⟩
  obtain ⟨C, hC⟩ := _root_.GlobalTheory.Ord2.GwIneq.gw_ineq hL l Ω e S A W hN c hW
  obtain ⟨B, hB⟩ := _root_.GlobalTheory.Ord2.TorsBound.tors_bound l Ω e S A W hN c hW (_root_.GlobalTheory.Ord2.GwFin.card_dualCocyclesModPrimePow_unramifiedOutsideS_bounded hL l Ω e S A W hN c hW) m
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t = C * B + 1 := ⟨_, rfl⟩
  have hlt : C * B < l ^ t := by
    have := Nat.lt_pow_self (Fact.out : l.Prime).one_lt (n := t)
    omega
  have hCv : ∀ {n : ℕ} (a b : Fin 2 → Qbar l), a = b → Cv n a b := fun a b h i => by
    subst h; simp [Cg]
  let yF : Fin (l ^ t) → G ℚ Ω → Fin 2 → Qbar l := fun j s => ((j : ℕ) : Qbar l) • Y s
  have hjO : ∀ j : Fin (l ^ t), ((j : ℕ) : Qbar l) ∈ c.O := fun j => natCast_mem _ _
  have hsel : ∀ j, GwCount.SelN c (t + k0) S A W (yF j) := by
    intro j
    refine ⟨⟨?_, fun s i => ?_, fun s _ r _ => hCv _ _ ?_⟩, fun a ha => hCv _ _ ?_, fun q _ hlq => ?_, ?_⟩
    · exact (hYZ.1.const_smul ((j : ℕ) : Qbar l)).continuousOn
    · simp only [yF, Pi.smul_apply, smul_eq_mul]; exact mul_mem (hjO j) (hYI s i)
    · simp only [yF]; rw [hYcoc, smul_add, Matrix.mulVec_smul]
    · simp only [yF]; rw [hY0 a ha, smul_zero]
    · obtain ⟨x, hxO, hx⟩ := hYu q hlq (placeOf Ω q) (isPlaceOver_placeOf Ω q)
      refine ⟨placeOf Ω q, isPlaceOver_placeOf Ω q, ((j : ℕ) : Qbar l) • x, fun i => ?_, fun s hs => hCv _ _ ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul]; exact mul_mem (hjO j) (hxO i)
      · simp only [yF]; rw [hYs, hx s hs, Matrix.mulVec_smul, smul_sub]
    · obtain ⟨x, hxO, hx⟩ := hYg hyG
      refine ⟨((j : ℕ) : Qbar l) * x, mul_mem (hjO j) hxO, fun s hs => ?_⟩
      have h1 : yF j s 1 = ((j : ℕ) : Qbar l) * (mat W s 1 1 * x - x) := by
        simp only [yF, Pi.smul_apply, smul_eq_mul]; rw [hYs, Pi.smul_apply, smul_eq_mul, hx s hs]
      have h2 : ((j : ℕ) : Qbar l) * (mat W s 1 1 * x - x) = mat W s 1 1 * (((j : ℕ) : Qbar l) * x) - ((j : ℕ) : Qbar l) * x := by ring
      rw [h1, h2]; simp [Cg]
  have hne : ∀ i j, i ≠ j → ¬ Cob1 c (t + k0) W ⊤ (yF i - yF j) := by
    intro i j hij h
    have e1 : yF i - yF j = fun s => ((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) : Qbar l) • Y s := by
      funext s; simp only [yF, Pi.sub_apply]; push_cast; rw [sub_smul]
    rw [e1] at h
    have hd := hk0 (t + k0) _ (intCast_mem _ _) h
    refine GlobalTheory.T.not_congruent_zero_intCast_mul_prime_pow l t k0 (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) ?_ ?_ hd
    · intro h0; apply hij; ext; omega
    · have hi := i.2; have hj := j.2
      have : ((l ^ t : ℕ) : ℤ) = (l : ℤ) ^ t := by push_cast; rfl
      rw [← this, abs_lt]; constructor <;> omega
  obtain ⟨N', z, hNC, hzS, hzne⟩ := hC (t + k0) (by omega) (l ^ t) yF hsel hne
  have hex : ∃ i, ¬ Cob1 c (t + k0) (dual1 W) ⊤ (fun s => ((l : ℕ) : Qbar l) ^ m • z i s) := by
    by_contra h
    push_neg at h
    have h1 := hB (t + k0) N' z hzS hzne h
    have h2 : C * N' ≤ C * B := Nat.mul_le_mul_left C h1
    omega
  obtain ⟨i, hi⟩ := hex
  obtain ⟨h1, h2, h3, h4⟩ := hzS i
  exact ⟨t + k0, z i, h1, h2, h3, h4, hi⟩

end GlobalTheory.Ord2.GwCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepresentationOfEigensystemStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_representation_of_eigensystem : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ {E : Type} [NormedField E] [IsAlgClosed E] [Algebra ℤ_[l] E], (∀ z : ℤ_[l], ‖algebraMap ℤ_[l] E z‖ = ‖z‖) → ∀ (lam : Letter → E), X.SSBB N l w E lam → ∀ (ρ : (Ω ≃ₐ[ℚ] Ω) →* GL (Fin 2) E) (S0 : Finset ℕ), (∀ δ : ℝ, 0 < δ → ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → ‖(fun s => Matrix.trace (ρ s : Matrix (Fin 2) (Fin 2) E)) (s * s') - (fun s => Matrix.trace (ρ s : Matrix (Fin 2) (Fin 2) E)) (s)‖ < δ) → (∀ δ : ℝ, 0 < δ → ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → ‖(fun s => Matrix.det (ρ s : Matrix (Fin 2) (Fin 2) E)) (s * s') - (fun s => Matrix.det (ρ s : Matrix (Fin 2) (Fin 2) E)) (s)‖ < δ) → (∀ q : ℕ, q.Prime → q ∉ S0 → ∀ s, FrobAt q s → Matrix.trace (ρ s : Matrix (Fin 2) (Fin 2) E) = lam (Letter.T q) ∧ Matrix.det (ρ s : Matrix (Fin 2) (Fin 2) E) = (q : E) ^ (w + 1) * lam (Letter.D q)) → (∀ V : Submodule E (Fin 2 → E), (∀ s v, v ∈ V → (ρ s : Matrix (Fin 2) (Fin 2) E) *ᵥ v ∈ V) → V = ⊥ ∨ V = ⊤) → ∃ (m : ℕ) (π : Fin m → (E ⊗[ℤ_[l]] X.Fn l) →ₗ[E] (Fin 2 → E)) (σ : Fin m → (Fin 2 → E) →ₗ[E] (E ⊗[ℤ_[l]] X.Fn l)) (P : FreeAlgebra E Letter), P ∈ admissibleLettersSubalgebra E N l ∧ FreeAlgebra.lift E lam P = 1 ∧ (∀ x ∈ X.VB N l w E, (∀ T : Letter, admitted N l T → X.opV N l E T x = lam T • x) → ∑ i, σ i (π i x) = x) ∧ (∀ i v, σ i v ∈ X.VB N l w E) ∧ (∀ i s, ∀ x ∈ X.VB N l w E, π i (X.galV l E s x) = (ρ s : Matrix (Fin 2) (Fin 2) E) *ᵥ π i x) ∧ (∀ i s v, X.galV l E s (σ i v) = σ i ((ρ s : Matrix (Fin 2) (Fin 2) E) *ᵥ v)) ∧ (∀ i (T : Letter) v, admitted N l T → X.opV N l E T (σ i v) = lam T • σ i v) ∧ (∀ i (T : Letter), admitted N l T → ∀ x ∈ X.VB N l w E, π i (X.opV N l E T x) = lam T • π i x) ∧ (∀ i j v, π i (σ j v) = if i = j then v else 0) ∧ ∀ x ∈ X.VB N l w E, FreeAlgebra.lift E (X.opV N l E) P x = ∑ i, σ i (π i x) := by
  first | (exact @GlobalTheory.KZ.HeckeProj.heckeProj_main) | (exact GlobalTheory.KZ.HeckeProj.heckeProj_main) | (intros; apply GlobalTheory.KZ.HeckeProj.heckeProj_main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemInertiaInvariantsCyclotomicAlgebraIffStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_inertiaInvariantsCyclotomicAlgebra_iff : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ x : A, x ∈ cycAlg l A ↔ ∀ s ∈ ineCyc l A, s (x : Ω) = x := by
  first | (exact @GlobalTheory.RecOne.mem_cycAlg_iff) | (exact GlobalTheory.RecOne.mem_cycAlg_iff) | (intros; apply GlobalTheory.RecOne.mem_cycAlg_iff  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLPowLe
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4
open scoped Matrix MatrixGroups

namespace GlobalTheory.HTLawZeta

open GlobalTheory.KummerEisensteinGalois GlobalTheory.LambdaValuationPowers

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem norm_l_pow_le (k : ℕ) : ‖((l : ℕ) : Qbar l) ^ k‖ ≤ 1 := by
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)

theorem cg_char_sum (n m : ℕ) (f g : (ZMod (l ^ m))ˣ → Qbar l) (ψ : DirichletCharacter (Qbar l) (l ^ m))
    (h : ∀ b, Cg n (f b) (g b)) :
    Cg n (∑ b : (ZMod (l ^ m))ˣ, ψ (b : ZMod (l ^ m)) * f b) (∑ b : (ZMod (l ^ m))ˣ, ψ (b : ZMod (l ^ m)) * g b) := by
  unfold Cg at *
  rw [← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun b _ => ?_
  rw [← mul_sub, norm_mul]
  have hψ : ‖ψ (b : ZMod (l ^ m))‖ ≤ 1 := by
    have h1 : (ψ (b : ZMod (l ^ m))) ^ orderOf b = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one, map_one]
    have h2 : ‖ψ (b : ZMod (l ^ m))‖ ^ orderOf b = 1 := by rw [← norm_pow, h1, norm_one]
    have hpos : orderOf b ≠ 0 := (orderOf_pos b).ne'
    exact le_of_eq ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hpos).1 h2)
  calc ‖ψ (b : ZMod (l ^ m))‖ * ‖f b - g b‖ ≤ 1 * ‖f b - g b‖ := by gcongr
    _ ≤ _ := by rw [one_mul]; exact h b

theorem htCoL_mono {A : ValuationSubring Ω} {c : Coef l} {j : Ω →+* Qbar l} {Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l}
    {m a b : ℕ} {y : (ZMod (l ^ m))ˣ} {h : Qbar l} (H : HTCoL A c j Z m a y h) (hab : a ≤ b) : HTCoL A c j Z m b y h := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  obtain ⟨q, o, w, ho, hs⟩ := H
  refine ⟨q, fun i => (l : Qbar l) ^ k * o i, w, fun i => ⟨?_, ?_, (ho i).2.2⟩, fun s h1 h2 => ?_⟩
  · rw [norm_mul]
    exact mul_le_one₀ (norm_l_pow_le k) (norm_nonneg _) (ho i).1
  · intro σ hσ hσ'
    rw [map_mul, map_pow, map_natCast, (ho i).2.1 σ hσ hσ']
  · have h3 := hs s h1 h2
    unfold Cg at *
    have e : (l : Qbar l) ^ (a + k) * Z m s y - ((l : Qbar l) ^ (a + k) * h * lamv l m s +
        ∑ i, (l : Qbar l) ^ k * o i * (j (s (w i)) - j (w i))) =
        (l : Qbar l) ^ k * ((l : Qbar l) ^ a * Z m s y - ((l : Qbar l) ^ a * h * lamv l m s +
        ∑ i, o i * (j (s (w i)) - j (w i)))) := by
      simp only [mul_assoc, ← Finset.mul_sum]
      ring
    rw [e, norm_mul]
    calc _ ≤ 1 * _ := mul_le_mul_of_nonneg_right (norm_l_pow_le k) (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact h3

def unitVal (ε : Ω →+* ℂ) (j : Ω →+* Qbar l) (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) (N k : ℕ) (c d w w' : ℤ) (m β : ℕ) :
    Qbar l :=
  haveI : CharZero Ω := algebraRat.charZero Ω
  lam (fun i => (l : Qbar l) ^ m * j (toQ (l ^ m)
    (pieceT N l m m k (1 : DirichletCharacter Ω (l ^ m)) c d (w, 0) (w', 0)
      (eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) ^ β)
      ((unitSet l m).filter fun γ => (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det = 1)) i))

theorem sum_unitVal [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (j : Ω →+* Qbar l) (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) (N k : ℕ)
    (c d w w' : ℤ) (m : ℕ) (β : (ZMod (l ^ m))ˣ → ℕ) (ψ : DirichletCharacter (Qbar l) (l ^ m)) (F : ℕ → Qbar l) (hN : ¬ l ∣ N)
    (hm : 1 ≤ m) (hβ : ∀ b, ((β b : ℕ) : ZMod (l ^ m)) = b ∧ ((β b : ℕ) : ZMod N) = 1)
    (hE : ∀ ζ : Qbar l, IsPrimitiveRoot ζ (N * l ^ m) → ∀ r : ℕ,
      toQ (l ^ m) (pieceT N l m m k ψ c d (w, 0) (w', 0) ζ (unitSet l m)) r =
        -((l : Qbar l) ^ (-(m : ℤ))) * gaussS l m ψ (ζ ^ N) * ψ⁻¹ (N : ZMod (l ^ m)) * (N : Qbar l) ^ ((2 : ℤ) - k) *
          up (l ^ m) F r) :
    ∑ b : (ZMod (l ^ m))ˣ, ψ b * unitVal ε j lam N k c d w w' m (β b) =
      -((N : Qbar l) ^ ((2 : ℤ) - k)) * (∑ a : ZMod (l ^ m), ψ a * (j (eOm ε (1 / (l : ℚ) ^ m))) ^ a.val) *
        ψ⁻¹ (N : ZMod (l ^ m)) * lam (up (l ^ m) F) := by
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hp : l.Prime := Fact.out
  have hN0 : 0 < N := Nat.pos_of_ne_zero (by rintro rfl; exact hN (dvd_zero _))
  obtain ⟨-, -, hr, hrN⟩ := GlobalTheory.Glue.Roots.eOm_isPrimitiveRoot_compatible Ω ε ε.injective l hp N hN0 m
  set ζ := eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) with hζ
  have hjζ : IsPrimitiveRoot (j ζ) (N * l ^ m) := hr.map_of_injective j.injective
  have hP := GlobalTheory.KummerEisensteinGalois.psum_galois_unitPiece N l m k (Qbar l) ψ c d (w, 0) (w', 0) (j ζ) β hp hN0
    ((Nat.Prime.coprime_iff_not_dvd hp).2 hN) hm hjζ hβ
  have hl0 : (l : Qbar l) ≠ 0 := by exact_mod_cast hp.ne_zero
  have key : ∀ (F : (ZMod (l ^ m))ˣ → ℕ → Qbar l) (C : Qbar l) (g : ℕ → Qbar l),
      (∀ i, ∑ b : (ZMod (l ^ m))ˣ, ψ b * F b i = C * g i) → ∑ b : (ZMod (l ^ m))ˣ, ψ b * lam (F b) = C * lam g := by
    intro F C g h
    have e : ∑ b : (ZMod (l ^ m))ˣ, ψ b • F b = C • g := by
      funext i
      simpa [Finset.sum_apply] using h i
    have e2 := congrArg lam e
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, map_smul] using e2
  refine key _ _ _ fun i => ?_
  have h1 := hE (j ζ) hjζ i
  rw [toQ, ← hP, gaussS, ← map_pow, hrN] at h1
  simp only [toQ, GlobalTheory.KummerEisensteinGalois.map_pieceT_one N l m k Ω (Qbar l) j, map_pow, ← hζ]
  simp only [mul_left_comm (ψ _) ((l : Qbar l) ^ m), ← Finset.mul_sum]
  rw [h1, zpow_neg, zpow_natCast]
  field_simp

theorem law_of_parts [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (cf : Coef l) (j : Ω →+* Qbar l) (ε : Ω →+* ℂ) (N : ℕ) [NeZero N]
    (cw : ZMod N → Qbar l) (c₀ : ℕ) (K : Qbar l) (U : ZMod N → ℕ → ℕ → ℤ → Qbar l)
    (F : ∀ m : ℕ, DirichletCharacter (Qbar l) (l ^ m) → ZMod N → ℕ → Qbar l) (Zx : ZMod N → ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l)
    (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) (per : ℕ → Qbar l) (κ₀ : Qbar l)
    (hZ : ∀ r s y, Z r s y = ∑ x, cw x * Zx x r s y) (hper : ∀ n, ‖per n‖ = 1 ∧ Cg n (per (n + 1)) (per n)) (hκ : κ₀ ≠ 0)
    (hK : K ≠ 0) (hN : ¬ l ∣ N) (hcw : ∀ x, cw x ∈ cf.O)
    (hU : ∀ x, cw x ≠ 0 → ∀ m : ℕ, 1 ≤ m → ∀ ψ : DirichletCharacter (Qbar l) (l ^ m), ψ.IsPrimitive →
      ∀ (β : (ZMod (l ^ m))ˣ → ℕ) (t : ℤ), (∀ b, ((β b : ℕ) : ZMod (l ^ m)) = b ∧ ((β b : ℕ) : ZMod N) = 1) →
      (l : ℤ) ^ m * t ≡ 1 [ZMOD N] → ∑ b : (ZMod (l ^ m))ˣ, ψ b * U x m (β b) t =
        K * (∑ a : ZMod (l ^ m), ψ a * (j (eOm ε (1 / (l : ℚ) ^ m))) ^ a.val) * ψ⁻¹ (N : ZMod (l ^ m)) *
          lam (up (l ^ m) (F m ψ x)))
    (hco : ∀ x, cw x ≠ 0 → ∃ c' : ℕ, ∀ m : ℕ, 1 ≤ m → ∀ (y : (ZMod (l ^ m))ˣ) (β : ℕ) (t : ℤ),
      (β : ZMod (l ^ m)) = (y : ZMod (l ^ m)) → (β : ZMod N) = 1 → (l : ℤ) ^ m * t ≡ 1 [ZMOD N] →
      HTCoL A cf j (Zx x) m c' y ((per m)⁻¹ * (l : Qbar l) ^ c₀ * κ₀ *
        U x m β t))
    (hpres : ∃ m₁ C : ℕ, ∀ m, m₁ ≤ m → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ m) →
      ∃ (ι : Type) (_ : Fintype ι) (P : ι → Polynomial Ω) (o : ι → Qbar l), HTPresNuOfPolys A cf m C Z ζ P o)
    (hloc : ∃ c₁ : ℕ, ∀ m C : ℕ, C + c₁ ≤ m → ∀ (ζ : Ω) (ι : Type) [Fintype ι] (P : ι → Polynomial Ω) (o : ι → Qbar l)
      (h : (ZMod (l ^ m))ˣ → Qbar l), HTPresNuOfPolys A cf m C Z ζ P o → (∀ y, HTCoL A cf j Z m C y (h y)) →
      ∀ y : (ZMod (l ^ m))ˣ, Cg (m - C - c₁) (htv j ζ P o (y : ZMod (l ^ m)).val) (h y)) :
    ∃ (m₀ c₁ : ℕ) (κ : Qbar l) (v : ℕ → Qbar l), κ ≠ 0 ∧ (∀ m, ‖v m‖ = 1 ∧ Cg m (v (m + 1)) (v m)) ∧
      HTLawCsOfCoef A cf Z j m₀ c₁
        (fun m ψ z => v m * κ * (∑ a : ZMod (l ^ m), ψ a * z ^ a.val) * ψ⁻¹ (N : ZMod (l ^ m)) *
          lam (up (l ^ m) (fun i => ∑ x : ZMod N, cw x * F m ψ x i))) := by
  classical
  have hp : l.Prime := Fact.out
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hcop : Nat.Coprime l N := (Nat.Prime.coprime_iff_not_dvd hp).2 hN
  obtain ⟨m₁, C₁, hpres⟩ := hpres
  obtain ⟨c₁, hloc⟩ := hloc
  choose! c' hc' using hco
  set C : ℕ := C₁ + ∑ x, c' x with hC
  have hle : ∀ x, c' x ≤ C := fun x =>
    (Finset.single_le_sum (f := c') (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)).trans (Nat.le_add_left _ _)
  have hroot := fun m => GlobalTheory.Glue.Roots.eOm_isPrimitiveRoot_compatible Ω ε ε.injective l hp N hN0 m
  have hl0 : (l : Qbar l) ≠ 0 := by exact_mod_cast hp.ne_zero
  refine ⟨m₁ + C + c₁ + 1, C + c₁, (l : Qbar l) ^ c₀ * κ₀ * K,
    fun m => (per m)⁻¹, mul_ne_zero (mul_ne_zero (pow_ne_zero _ hl0) hκ) hK,
    fun m => ⟨by rw [norm_inv, (hper m).1, inv_one], ?_⟩,
    fun m => eOm ε (1 / (l : ℚ) ^ m), fun m => ⟨(hroot m).1, (hroot m).2.1⟩, fun m hm => ?_⟩
  · have h0 : ∀ n, per n ≠ 0 := fun n h => by simpa [h] using (hper n).1
    have h1 := (hper m).2
    unfold Cg at *
    rw [inv_sub_inv (h0 _) (h0 _), norm_div, norm_mul, (hper m).1, (hper (m + 1)).1, mul_one, div_one, norm_sub_rev]
    exact h1
  obtain ⟨ι, hι, P, o, hP⟩ := hpres m (by omega) _ (hroot m).1
  have hcm : Nat.Coprime (l ^ m) N := Nat.Coprime.pow_left m hcop
  obtain ⟨t, ht⟩ : ∃ t : ℤ, (l : ℤ) ^ m * t ≡ 1 [ZMOD N] := by
    refine ⟨Int.gcdA ((l ^ m : ℕ) : ℤ) N, ?_⟩
    have h := Int.gcd_eq_gcd_ab ((l ^ m : ℕ) : ℤ) (N : ℤ)
    rw [Int.gcd_natCast_natCast, hcm] at h
    refine (Int.modEq_iff_dvd.2 ⟨Int.gcdB ((l ^ m : ℕ) : ℤ) N, ?_⟩)
    push_cast at h ⊢
    linear_combination h
  have hβ : ∀ b : (ZMod (l ^ m))ˣ, ∃ β : ℕ, (β : ZMod (l ^ m)) = b ∧ (β : ZMod N) = 1 := fun b => by
    obtain ⟨β, h1, h2⟩ := Nat.chineseRemainder hcm (b : ZMod (l ^ m)).val 1
    refine ⟨β, ?_, ?_⟩
    · rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 h1, ZMod.natCast_zmod_val]
    · rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 h2, Nat.cast_one]
  choose β hβ using hβ
  set u : ZMod N → (ZMod (l ^ m))ˣ → Qbar l := fun x y => (per m)⁻¹ * (l : Qbar l) ^ c₀ * κ₀ *
    U x m (β y) t with hu
  have hH : ∀ y, HTCoL A cf j Z m C y (∑ x, cw x * u x y) := by
    intro y
    have h1 := GlobalTheory.LambdaValuationPowers.htCoL_sum l Ω A cf j (ZMod N) cw (fun x => if cw x = 0 then 0 else Zx x) m C y
      (fun x => if cw x = 0 then 0 else u x y) (fun x => ⟨GlobalTheory.LambdaValuationPowers.norm_le_one_of_mem (hcw x), fun σ h _ => h _ (hcw x)⟩)
      (fun x => by
        by_cases hx : cw x = 0
        · simp only [hx, if_true]
          exact htCoL_of_eq A cf j _ m C y 0 (fun s => by simp)
        · simp only [hx, if_false]
          exact htCoL_mono (hc' x hx m (by omega) y (β y) t (hβ y).1 (hβ y).2 ht) (hle x))
    convert (preTransparency := .reducible) h1 using 1
    · funext r s y'
      rw [hZ]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : cw x = 0 <;> simp [hx]
    · refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : cw x = 0 <;> simp [hx]
  have hPC := htPresNu7_mono_loss l Ω A cf Z m C₁ C _ ι P o hP (Nat.le_add_right _ _)
  refine ⟨ι, hι, P, o, htPresNu7_mono_loss l Ω A cf Z m C (C + c₁) _ ι P o hPC (Nat.le_add_right _ _), fun ψ hψ => ?_⟩
  have h2 := cg_char_sum _ m _ _ ψ (hloc m C (by omega) _ ι P o _ hPC hH)
  rw [Nat.sub_sub] at h2
  convert h2 using 1
  have hup : up (l ^ m) (fun i => ∑ x : ZMod N, cw x * F m ψ x i) =
      ∑ x : ZMod N, cw x • up (l ^ m) (F m ψ x) := by
    funext i
    simp [up, Finset.sum_apply]
  have hsw : ∑ b : (ZMod (l ^ m))ˣ, ψ b * ∑ x, cw x * u x b = ∑ x, ∑ b : (ZMod (l ^ m))ˣ, ψ b * (cw x * u x b) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.mul_sum _ _ _
  beta_reduce
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsw, hup, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : cw x = 0
  · simp [hx]
  have h3 := hU x hx m (by omega) ψ hψ β t hβ ht
  have h4 : ∑ b : (ZMod (l ^ m))ˣ, ψ b * (cw x * u x b) = cw x * ((per m)⁻¹ * (l : Qbar l) ^ c₀ * κ₀) *
      ∑ b : (ZMod (l ^ m))ˣ, ψ b * U x m (β b) t := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [hu]
    ring
  rw [h4, h3, map_smul, smul_eq_mul]
  ring

end GlobalTheory.HTLawZeta

end
end

