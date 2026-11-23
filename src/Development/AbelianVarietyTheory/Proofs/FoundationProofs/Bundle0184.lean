module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTOperatorExplicitSemisimpleCuspForms
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0002
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0177
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0154

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTqSemisimpleCuspFormsGamma1
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.SemisimpleLevelOne

lemma lev_one (N : ℕ) : GlobalTheory.Hk.lev N 1 = CongruenceSubgroup.Gamma1 N := by
  ext γ
  simp only [GlobalTheory.Hk.lev, Subgroup.mem_inf, CongruenceSubgroup.Gamma0_mem, and_iff_left_iff_imp]
  intro _
  exact Subsingleton.elim _ _

theorem tq_semisimple : ∀ (N k q : ℕ) (σ : SL(2, ℤ)), 5 ≤ N → 3 ≤ k → q.Prime → ¬ q ∣ N →
    IsDiam N 1 (q : ZMod N) σ →
    ∀ (f : CuspForm (CongruenceSubgroup.Gamma1 N) (k : ℤ)) (c : ℂ) (n : ℕ),
      (fun F => TqF (k : ℤ) q σ F - c • F)^[n] ⇑f = 0 → TqF (k : ℤ) q σ ⇑f = c • ⇑f := by
  intro N k q σ hN _ hq hqN hσ f c n h
  obtain ⟨-, -, hT, hD, -⟩ := GlobalTheory.SlashUpperTriangularMatrices.bridge
  have hT' : TqF (k : ℤ) q σ = GlobalTheory.Hk.heckeT (k : ℤ) q σ := funext fun F => hT _ _ _ F hq.pos
  have hσ' : GlobalTheory.Hk.IsDia N 1 (q : ℤ) σ := (hD N 1 (q : ℤ) σ).1 (by simpa using hσ)
  rw [hT'] at h ⊢
  let g : CuspForm (GlobalTheory.Hk.lev N 1) (k : ℤ) := f.copy ⇑f rfl (by rw [lev_one])
  exact _root_.GlobalTheory.Hk.Semisimple.heckeT_semisimple N 1 q (k : ℤ) σ c n (by omega) one_pos hq (by simpa using hqN) hσ' g h

end GlobalTheory.HeckeFamilyMatrices.SemisimpleLevelOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InclWFrobIter
section
noncomputable section

namespace GlobalTheory.TorsionBoundCompare

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW inclR φR gR πA)

theorem TWact_smul (f : RW →ₐ[O] RW) (T : LocLat G Qp LL O) (g : G) (r : RW) (y : TW RW T) :
    TWact f T g (r • y) = f r • TWact f T g y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp [TWact, TensorProduct.smul_tmul']
  | add a b ha hb => simp [ha, hb]

theorem TWmap_smul (f : RW →ₐ[O] RW) (T : LocLat G Qp LL O) (r : RW) (y : TW RW T) :
    TWmap f T (r • y) = f r • TWmap f T y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp [TWmap, TensorProduct.smul_tmul']
  | add a b ha hb => simp [ha, hb]

theorem unit_cancel (hO : Function.Injective (algebraMap O LL)) :
    ∃ (e : W.DD W.one) (e₀ : ↥W.one.L.T), E.jD W.one e = (1 : RW) ⊗ₜ[O] e₀ ∧
      ∀ r r' : RW, r • ((1 : RW) ⊗ₜ[O] e₀) = r' • ((1 : RW) ⊗ₜ[O] e₀) → r = r' := by
  obtain ⟨e, e₀, h1, h2, -⟩ := E.one_e
  obtain ⟨x, hx, hT⟩ := W.one_line
  have h0 : (e₀ : W.one.V) ≠ 0 := by
    intro h
    have hm : (⟨x, by rw [hT]; exact Submodule.mem_span_singleton_self x⟩ : ↥W.one.L.T) ∈
        Submodule.span O {e₀} := by rw [h1]; trivial
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
    have := congrArg Subtype.val hc
    simp only [SetLike.val_smul, h, smul_zero] at this
    exact hx this.symm
  have hb : Function.Bijective (LinearMap.toSpanSingleton O _ e₀) := by
    refine ⟨(injective_iff_map_eq_zero _).mpr fun c hc => ?_, ?_⟩
    · have := congrArg Subtype.val hc
      simp only [LinearMap.toSpanSingleton_apply, SetLike.val_smul, ZeroMemClass.coe_zero] at this
      rw [← algebraMap_smul LL, smul_eq_zero] at this
      exact hO (by rw [this.resolve_right h0, map_zero])
    · rw [← LinearMap.range_eq_top, ← LinearMap.span_singleton_eq_range, h1]
  let lam := (LinearEquiv.ofBijective _ hb).symm
  have hl : lam e₀ = 1 := by
    rw [LinearEquiv.symm_apply_eq]; simp
  refine ⟨e, e₀, h2, fun r r' h => ?_⟩
  have := congrArg (fun y => TensorProduct.rid O RW (LinearMap.lTensor RW lam.toLinearMap y)) h
  simpa [TensorProduct.smul_tmul', hl] using this

theorem ioE_φ (hO : Function.Injective (algebraMap O LL)) (a : W.EE) :
    E.ioE (W.φE a) = φR (E.ioE a) := by
  obtain ⟨e, e₀, h1, h2⟩ := unit_cancel E hO
  have h3 : TWmap φR W.one ((1 : RW) ⊗ₜ[O] e₀) = (1 : RW) ⊗ₜ[O] e₀ := by simp [TWmap]
  have := E.jD_φ W.one (a • e)
  rw [W.φD_smul, E.jD_smul, E.jD_smul, E.jD_φ, TWmap_smul, h1, h3] at this
  exact h2 _ _ this

theorem ioE_γ (hO : Function.Injective (algebraMap O LL)) (g : G) (a : W.EE) :
    E.ioE (W.γE (W.resΓ g) a) = gR g (E.ioE a) := by
  obtain ⟨e, e₀, h1, h2⟩ := unit_cancel E hO
  have h4 : W.one.actT g e₀ = e₀ := Subtype.ext (W.one_triv g _)
  have h3 : TWact (gR g) W.one g ((1 : RW) ⊗ₜ[O] e₀) = (1 : RW) ⊗ₜ[O] e₀ := by simp [TWact, h4]
  have := E.jD_act W.one g (a • e)
  rw [W.γD_smul, E.jD_smul, E.jD_smul, E.jD_act, TWact_smul, h1, h3] at this
  exact h2 _ _ this

def sc : LetA O n →ₐ[O] RW := inclR.comp E.io

theorem sc_φ (hO : Function.Injective (algebraMap O LL)) (a : LetA O n) :
    sc E (W.φA a) = φR (sc E a) := by
  have := ioE_φ E hO (algebraMap _ _ a)
  rwa [W.φE_ext, E.ioE_ext, E.ioE_ext] at this

def cst (c : ZMod n → O) : LetA O n := fun i => PowerSeries.C (c i)

theorem φA_cst (c : ZMod n → O) : W.φA (cst c) = cst fun i => c (i - 1) := by
  funext i
  exact W.φ₀.commutes (c (i - 1))

theorem iter_sc_cst (hO : Function.Injective (algebraMap O LL)) (c : ZMod n → O) (k : ℕ) :
    φR^[k] (sc E (cst c)) = sc E (cst fun i => c (i - k)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, ← sc_φ E hO, φA_cst]
    congr 2
    funext i
    congr 1
    push_cast
    ring

end Generic

section Comp

variable {Z O R R' : Type} [CommRing Z] [CommRing O] [CommRing R] [CommRing R'] [Algebra Z O]
  [Algebra Z R] [Algebra Z R']

def cf (lam : O →ₗ[Z] Z) : O ⊗[Z] R →ₗ[Z] R :=
  (TensorProduct.lid Z R).toLinearMap ∘ₗ lam.rTensor R

end Comp

section Situation

open GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified

variable {l : ℕ} [Fact l.Prime]

theorem inclW_frob (a : Ainf l) : inclW l (WittVector.frobenius a) = frobW l (inclW l a) := by
  ext n
  change ((WittVector.map _ _ : WCb l)).coeff n = (WittVector.map (frobenius (Cb l) l) (inclW l a)).coeff n
  simp [inclW, WittVector.map_coeff, frobenius_def]

theorem tmul_iter (LL : FinExt l) (k : ℕ) (x : WCb l) :
    (φRW LL)^[k] ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] x) = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (frobW l)^[k] x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]; rfl

variable {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l}
  {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))}
  (E : EtTie W (RA LL) (RW LL) (inclR LL) (φRW LL) (fun g : ↥(GK K) => AI.gRW LL (g : GQ l))
    ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] piS AI s))

theorem frob_teich (x : OCb l) :
    WittVector.frobenius (WittVector.teichmuller l x) = WittVector.teichmuller l (x ^ l) := by
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def]

end Situation

end GlobalTheory.TorsionBoundCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCupProductCoboundaryTheorem
section
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory.KummerCob

theorem cup_eq_coboundary_vanishing_on_inertia : ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N →
    ∀ (a b : K) (α β : Ω), a ∈ FunctionField.ringOfIntegers k K → a⁻¹ ∈ FunctionField.ringOfIntegers k K →
      b ∈ FunctionField.ringOfIntegers k K → b⁻¹ ∈ FunctionField.ringOfIntegers k K → a ≠ 0 → b ≠ 0 →
      α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
      ∃ η : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant η ∧
        (∀ g h, kum ζ α g * kum ζ β h = η h - η (g * h) + η g) ∧
        ∀ B : ValuationSubring Ω, Over (FunctionField.ringOfIntegers k K).toSubring B → ∀ g, Inert B g → η g = 0 := by
  intro k K Ω _ _ _ _ _ _ _ _ _ _ _ N ζ hN hζ a b α β haA hai hbA hbi ha0 hb0 hα hβ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap (RatFunc k) K).injective
  obtain ⟨z, hz⟩ := zeta_mem_range k K Ω N ζ hN hζ
  have hfix : ∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ := fun g => by rw [← hz]; exact g.commutes z
  have hC1 : IsFirstChernClassOfLineBundle K := _root_.GlobalTheory.NeedB.tsen k K
  have hnorm : ∀ (L : IntermediateField K Ω), FiniteDimensional K L → ∀ c : K, c ≠ 0 →
      ∃ x : L, Algebra.norm K x = c := fun L _ c hc => _root_.GlobalTheory.norm_surjective_of_is_c1 K L hC1 c hc
  obtain ⟨η₀, hη₀c, hη₀⟩ := _root_.GlobalTheory.cup_kummer_coboundary_of_norms K Ω N ζ hN hζ hfix hnorm a b α β ha0 hb0 hα hβ
  obtain ⟨θ, hθ0, hθE, hθη, hθs⟩ :=
    _root_.GlobalTheory.eta_kummer_galoisInvariant K Ω N ζ hN hζ hfix a b α β ha0 hb0 hα hβ η₀ hη₀c hη₀
  obtain ⟨f, hf0, hfB⟩ := _root_.GlobalTheory.KummerCob.divisor_descends k K Ω N ζ hN hζ a b α β haA hai hbA hbi ha0 hb0 hα hβ θ hθ0 hθE hθs
  obtain ⟨θ₀, hθ₀⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K Ω f) hN
  have hθ₀0 : θ₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hθ₀
    exact hf0 ((map_eq_zero_iff _ (algebraMap K Ω).injective).1 hθ₀.symm)
  obtain ⟨hk0c, -, hk0add, -⟩ :=
    GlobalTheory.NeedB.KumLemma.kummer_character_main K Ω N ζ θ₀ hN hζ hfix hθ₀0 ⟨f, hθ₀.symm⟩
  refine ⟨fun g => η₀ g - kum ζ θ₀ g, hη₀c.sub hk0c, ?_, ?_⟩
  · intro g h
    simp only
    rw [hη₀ g h, hk0add g h]
    ring
  · intro B hB g hg
    obtain ⟨c, hcE, hc0, hcv⟩ := hfB B hB
    rw [← hθ₀] at hcv
    obtain ⟨hgE, hk⟩ := GlobalTheory.T.inertia_fixes_adjoin_kummer_roots_and_values_eq k K Ω N ζ hN hζ a b α β haA hai hbA hbi ha0 hb0 hα hβ θ θ₀ hθ0 hθ₀0 hθE
      ⟨f, hθ₀.symm⟩ B hB g hg c hcE hc0 hcv
    show η₀ g - kum ζ θ₀ g = 0
    rw [hθη g hgE, hk, sub_self]

theorem thmA : GlobalTheory.NeedB.ThmA := by
  intro k K Ω _ _ _ _ _ _ _ _ _ _ _ N ζ hN hζ a b α β ha0 hb0 haA hai hbA hbi hα hβ
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  obtain ⟨z, hz⟩ := zeta_mem_range k K Ω N ζ hN hζ
  have hfix : ∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ := fun g => by rw [← hz]; exact g.commutes z
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hα
    exact ha0 ((map_eq_zero_iff _ (algebraMap K Ω).injective).1 hα.symm)
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hβ
    exact hb0 ((map_eq_zero_iff _ (algebraMap K Ω).injective).1 hβ.symm)
  obtain ⟨hαc, -, hαadd, -⟩ :=
    GlobalTheory.NeedB.KumLemma.kummer_character_main K Ω N ζ α hN hζ hfix hα0 ⟨a, hα.symm⟩
  obtain ⟨hβc, -, hβadd, -⟩ :=
    GlobalTheory.NeedB.KumLemma.kummer_character_main K Ω N ζ β hN hζ hfix hβ0 ⟨b, hβ.symm⟩
  exact ⟨hαadd, hαc, hβadd, hβc,
    cup_eq_coboundary_vanishing_on_inertia k K Ω N ζ hN hζ a b α β haA hai hbA hbi ha0 hb0 hα hβ⟩

end GlobalTheory.KummerCob
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankinIntegralTendstoAtZero
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

lemma rpow_le_add_inv_of_mem_Icc {y s : ℝ} (hy : 0 < y) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    y ^ s ≤ y + y⁻¹ := by
  rcases le_or_gt 1 y with h | h
  · have : y ^ s ≤ y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h hs1
    rw [Real.rpow_one] at this
    have : 0 ≤ y⁻¹ := inv_nonneg.mpr hy.le
    linarith
  · have h1 : y ^ s ≤ 1 := Real.rpow_le_one hy.le h.le hs0
    have h2 : 1 ≤ y⁻¹ := by rw [le_inv_comm₀ one_pos hy]; simpa using h.le
    linarith

lemma mod_ofReal_norm {F : ℍ → ℂ} (hF : Mod F) : Mod (fun τ => ((‖F τ‖ : ℝ) : ℂ)) := by
  obtain ⟨C, A, h⟩ := hF
  exact ⟨C, A, fun τ => by simpa using h τ⟩

lemma mod_im_pow (A : ℕ) : Mod (fun τ : ℍ => (((τ.im ^ A + (τ.im ^ A)⁻¹ : ℝ)) : ℂ)) := by
  refine ⟨1, A, fun τ => ?_⟩
  have h0 : 0 ≤ τ.im ^ A + (τ.im ^ A)⁻¹ := by
    have := τ.im_pos; positivity
  rw [Complex.norm_real, Real.norm_of_nonneg h0, one_mul]

lemma mod_im_add_inv : Mod (fun τ : ℍ => (((τ.im + τ.im⁻¹ : ℝ)) : ℂ)) := by
  refine ⟨1, 1, fun τ => ?_⟩
  have h0 : 0 ≤ τ.im + τ.im⁻¹ := by
    have := τ.im_pos; positivity
  rw [Complex.norm_real, Real.norm_of_nonneg h0, one_mul, pow_one]

theorem rankin_tendsto : ∀ (k j L L' N : ℕ) (ε : DirichletCharacter ℂ N) (Φ : ℤ × ℤ → ℂ) (ρ : ℍ → ℝ) (h b : ℕ → ℂ), 1 ≤ k → 2 ≤ j → 0 < L → 0 < L' → N ∣ L' → Wt L' ρ → CF k L' (ch ε) h → PolyB b → (∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) → Tendsto (fun s : ℝ => pet k ρ (qs h) (fun τ => qs b τ * lat j s L (0, 1) Φ τ * ((τ.im ^ s : ℝ) : ℂ))) (𝓝[>] 0) (𝓝 (pet k ρ (qs h) (fun τ => qs b τ * lat j 0 L (0, 1) Φ τ))) := by
  intro k j L L' N ε Φ ρ h b hk hj hL hL' hN hρ hh hb hΦ
  obtain ⟨⟨C, A, hC⟩, hmeas, hlim⟩ := _root_.GlobalTheory.EisM.LatBd.lat_mod_meas_tendsto j L Φ hj hL hΦ
  have hbc : Continuous (qs b) := (_root_.GlobalTheory.EisM.qs_summable_continuous b hb).2
  have hhc : Continuous (qs h) := (_root_.GlobalTheory.EisM.qs_summable_continuous h hh.1.1).2
  have him : Continuous (fun τ : ℍ => τ.im) := UpperHalfPlane.continuous_im
  set G : ℍ → ℂ := fun τ => ((‖qs b τ‖ : ℝ) : ℂ) * ((C : ℂ) * (((τ.im ^ A + (τ.im ^ A)⁻¹ : ℝ)) : ℂ)) *
    (((τ.im + τ.im⁻¹ : ℝ)) : ℂ) with hG
  have hGc : Continuous G := by
    have h1 : Continuous (fun τ : ℍ => (τ.im ^ A)⁻¹) :=
      (him.pow A).inv₀ (fun τ => (pow_pos τ.im_pos A).ne')
    have h2 : Continuous (fun τ : ℍ => τ.im⁻¹) := him.inv₀ (fun τ => τ.im_pos.ne')
    simp only [hG]
    fun_prop
  have hGmod : Mod G := by
    have M := _root_.GlobalTheory.EisM.mod_algebra
    exact (M.1 _ _ ((M.1 _ _ (mod_ofReal_norm (_root_.GlobalTheory.EisM.mod_qs_of_polyB b hb))
      ((M.1 _ _ (M.2.1 (C : ℂ)) (mod_im_pow A)).2)).2) mod_im_add_inv).2
  have hint := _root_.GlobalTheory.EisM.integrable_pet_integrand k L' L' N ε h ρ G hk hL' hN hρ hh hGc.aestronglyMeasurable hGmod
  have hρm : Measurable (fun τ => (ρ τ : ℂ)) := Complex.measurable_ofReal.comp hρ.meas
  simp only [pet]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun τ => ‖(ρ τ : ℂ) * (conj (qs h τ) * G τ * (τ.im : ℂ) ^ k)‖) ?_ ?_ hint.norm ?_
  · refine Filter.Eventually.of_forall (fun s => ?_)
    have hs : Measurable (fun τ : ℍ => (((τ.im ^ s : ℝ)) : ℂ)) :=
      Complex.measurable_ofReal.comp ((him.measurable).pow_const s)
    exact (hρm.mul ((((Complex.continuous_conj.comp hhc).measurable).mul ((hbc.measurable.mul (hmeas s)).mul hs)).mul
      ((Complex.measurable_ofReal.comp him.measurable).pow_const k))).aestronglyMeasurable
  · have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
    filter_upwards [hev] with s hs
    refine Filter.Eventually.of_forall (fun τ => ?_)
    have hy := τ.im_pos
    have hρ0 := hρ.nonneg τ
    have hl := hC s τ hs.1.le hs.2.le
    have hys := rpow_le_add_inv_of_mem_Icc hy hs.1.le hs.2.le
    have hX : 0 ≤ C * (τ.im ^ A + (τ.im ^ A)⁻¹) := le_trans (norm_nonneg _) hl
    have hys0 : 0 ≤ τ.im ^ s := Real.rpow_nonneg hy.le s
    have key : ‖lat j s L (0, 1) Φ τ‖ * τ.im ^ s ≤
        |C * (τ.im ^ A + (τ.im ^ A)⁻¹)| * (τ.im + τ.im⁻¹) :=
      mul_le_mul (hl.trans (le_abs_self _)) hys hys0 (abs_nonneg _)
    simp only [hG, norm_mul, Complex.norm_real, Complex.norm_conj, norm_pow, Real.norm_eq_abs,
      norm_norm, abs_norm, Complex.ofReal_mul]
    rw [abs_of_nonneg hy.le, abs_of_nonneg (Real.rpow_nonneg hy.le s),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ τ.im + τ.im⁻¹)]
    have hcomb : |C| * |τ.im ^ A + (τ.im ^ A)⁻¹| = |C * (τ.im ^ A + (τ.im ^ A)⁻¹)| := (abs_mul _ _).symm
    have hP : 0 ≤ |ρ τ| * ‖qs h τ‖ * ‖qs b τ‖ * τ.im ^ k := by positivity
    calc |ρ τ| * (‖qs h τ‖ * (‖qs b τ‖ * ‖lat j s L (0, 1) Φ τ‖ * τ.im ^ s) * τ.im ^ k)
        = (|ρ τ| * ‖qs h τ‖ * ‖qs b τ‖ * τ.im ^ k) * (‖lat j s L (0, 1) Φ τ‖ * τ.im ^ s) := by ring
      _ ≤ (|ρ τ| * ‖qs h τ‖ * ‖qs b τ‖ * τ.im ^ k) * (|C * (τ.im ^ A + (τ.im ^ A)⁻¹)| * (τ.im + τ.im⁻¹)) :=
        mul_le_mul_of_nonneg_left key hP
      _ = |ρ τ| * (‖qs h τ‖ * (‖qs b τ‖ * (|C| * |τ.im ^ A + (τ.im ^ A)⁻¹|) * (τ.im + τ.im⁻¹)) * τ.im ^ k) := by
        rw [hcomb]; ring
  · refine Filter.Eventually.of_forall (fun τ => ?_)
    have hy := τ.im_pos
    have h1 : Tendsto (fun s : ℝ => (((τ.im ^ s : ℝ)) : ℂ)) (𝓝[>] 0) (𝓝 (((τ.im ^ (0:ℝ) : ℝ)) : ℂ)) := by
      have : ContinuousAt (fun s : ℝ => τ.im ^ s) 0 :=
        Real.continuousAt_const_rpow hy.ne'
      exact (Complex.continuous_ofReal.continuousAt.tendsto.comp this.tendsto).mono_left nhdsWithin_le_nhds
    have h2 := ((tendsto_const_nhds (x := (ρ τ : ℂ))).mul
      (((tendsto_const_nhds (x := conj (qs h τ))).mul (((tendsto_const_nhds (x := qs b τ)).mul (hlim τ)).mul h1)).mul
        (tendsto_const_nhds (x := (τ.im : ℂ) ^ k))))
    simpa only [Real.rpow_zero, Complex.ofReal_one, mul_one] using h2

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TqFSemisimple
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem tqF_semisimple : ∀ (N l k : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → 3 ≤ k → ∀ (q : ℕ) (σ : SL(2, ℤ)), q.Prime → ¬ q ∣ N * l → IsDiam N l (q : ZMod N) σ →
  ∀ (f : CuspForm (Lev N l) (k : ℤ)) (c : ℂ) (n : ℕ), (fun F => TqF (k : ℤ) q σ F - c • F)^[n] ⇑f = 0 → TqF (k : ℤ) q σ ⇑f = c • ⇑f := by
  intro N l k hN hl hlN hk q σ hq hqNl hσ f c n hf
  obtain ⟨_, _, hT, hD, _⟩ := _root_.GlobalTheory.SlashUpperTriangularMatrices.bridge
  have hq0 : 0 < q := hq.pos
  have hfun : (fun F => TqF (k : ℤ) q σ F - c • F) = (fun h => GlobalTheory.Hk.heckeT (k:ℤ) q σ h - c • h) := by
    funext F; rw [hT _ _ _ _ hq0]
  have hσ' : GlobalTheory.Hk.IsDia N l ((q:ℕ):ℤ) σ := (hD N l q σ).1 (by simpa using hσ)
  rw [hfun] at hf
  rw [hT _ _ _ _ hq0]
  exact _root_.GlobalTheory.Hk.Semisimple.heckeT_semisimple N l q k σ c n (by omega) hl.pos hq hqNl hσ' f hf

end GlobalTheory.HeckeFamilyMatrices
end

