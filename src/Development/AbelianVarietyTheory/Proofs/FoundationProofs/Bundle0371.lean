module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0365
public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0361
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0366
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0367
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0368
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0346
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0354
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0022
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedCocycleKillsRoots
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaTransportsKaehlerRelationsOverInvariants
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0362

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupProductUnramifiedClassesVanishesStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cupProduct_unramifiedClasses_vanishes : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (W : R2 Ω l) (q : Pl) (B : ValuationSubring Ω) (a b : G ℚ Ω → Fin 2 → Qbar l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → dt W ^ 2 = 1 → IsPlaceOver B q → ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → Coc1 c n W (Dec (F := ℚ) B) a → Coc1 c n (dual1 W) (Dec (F := ℚ) B) b → Cob1 c n W (Ine (F := ℚ) B) a → Cob1 c n (dual1 W) (Ine (F := ℚ) B) b → Cob2 c n (Dec (F := ℚ) B) (cup W a b) := by
  first | exact @GlobalTheory.Ord2.UnrCup.cup_unr_cob | exact GlobalTheory.Ord2.UnrCup.cup_unr_cob | (intros; apply GlobalTheory.Ord2.UnrCup.cup_unr_cob <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CyclotomicDvdOfAevalPrimitiveRootInertiaFixedStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomic_dvd_of_aeval_primitive_root_inertia_fixed : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (n : ℕ) (z : A), IsPrimitiveRoot (z : Ω) (l ^ n) → ∀ R : Polynomial (fixA A), Polynomial.aeval z R = 0 → Polynomial.cyclotomic (l ^ n) (fixA A) ∣ R := by
  first | (exact @GlobalTheory.RecOne.CycDvd.cyclotomic_dvd) | (exact GlobalTheory.RecOne.CycDvd.cyclotomic_dvd) | (intros; apply GlobalTheory.RecOne.CycDvd.cyclotomic_dvd  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualCocycleCoboundaryOnInertiaOfOrthogonalStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

theorem _root_.GlobalTheory.T.dualCocycle_coboundary_on_inertia_of_orthogonal : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ), 1 ≤ n → ∀ (S : Finset Pl) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ n)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation (ZMod (l ^ n)) (GS Ω (S : Set Pl)) M) (hrho : ContAction rho) (μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ), μ.comp (toGS Ω (S : Set Pl)) = cycMod ℚ Ω l n → ∀ (B : ValuationSubring Ω) (q : Pl), IsPlaceOver B q → ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ f : Z1 ((twDual μ rho).comp (locHom (S : Set Pl) B)), (∀ a ∈ H1ur (rho.comp (locHom (S : Set Pl) B)) ((Ine (F := ℚ) B).subgroupOf (Dec (F := ℚ) B)), cupH1H1TwistedDual μ rho (locHom (S : Set Pl) B) (hrho.comp' (continuous_locHom _ B)) (Submodule.mkQ _ f) a = 0) → ∃ m : TDual (ZMod (l ^ n)) M, ∀ s : Dec (F := ℚ) B, (s : G ℚ Ω) ∈ Ine (F := ℚ) B → f.1 s = twDual μ rho (locHom (S : Set Pl) B s) m - m := by
  first | exact @GlobalTheory.Ord2.GwIneq.dual_cocycle_cob_on_inertia | exact GlobalTheory.Ord2.GwIneq.dual_cocycle_cob_on_inertia | (intros; apply GlobalTheory.Ord2.GwIneq.dual_cocycle_cob_on_inertia <;> assumption) | exact @GlobalTheory.Ord2.GwIneq.cob_of_perp_transport | exact GlobalTheory.Ord2.GwIneq.cob_of_perp_transport | (intros; apply GlobalTheory.Ord2.GwIneq.cob_of_perp_transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualCocycleCoboundaryOnStableLineOfOrthogonalStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

theorem _root_.GlobalTheory.T.dualCocycle_coboundary_on_stableLine_of_orthogonal : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ), 1 ≤ n → ∀ (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hcont : Continuous W) (S : Finset Pl) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ), μ.comp (toGS Ω (S : Set Pl)) = cycMod ℚ Ω l n → ∀ (B : ValuationSubring Ω) (v : Pl), IsPlaceOver B v → (∀ s ∈ Dec (F := ℚ) B, mat W s 1 0 = 0) → ∀ f : Z1 ((twDual μ (rhoS c n W hint S hN)).comp (locHom (S : Set Pl) B)), (∀ a ∈ ordCond c n W hint S hN B, cupH1H1TwistedDual μ (rhoS c n W hint S hN) (locHom (S : Set Pl) B) ((contAction_rhoS c n W hint S hN hcont).comp' (continuous_locHom _ B)) (Submodule.mkQ _ f) a = 0) → ∃ m : TDual (ZMod (l ^ n)) (Mn c n), ∀ (s : Dec (F := ℚ) B) (u : Qn c n), f.1 s (Pi.single 0 u) = twDual μ (rhoS c n W hint S hN) (locHom (S : Set Pl) B s) m (Pi.single 0 u) - m (Pi.single 0 u) := by
  first | exact @GlobalTheory.Ord2.OrdCob.dual_cob_on_line | exact GlobalTheory.Ord2.OrdCob.dual_cob_on_line | (intros; apply GlobalTheory.Ord2.OrdCob.dual_cob_on_line <;> assumption) | exact @GlobalTheory.Ord2.OrdCob.rhoS_single | exact GlobalTheory.Ord2.OrdCob.rhoS_single | (intros; apply GlobalTheory.Ord2.OrdCob.rhoS_single <;> assumption) | exact @GlobalTheory.Ord2.OrdCob.contAction_rhoL | exact GlobalTheory.Ord2.OrdCob.contAction_rhoL | (intros; apply GlobalTheory.Ord2.OrdCob.contAction_rhoL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualSelmerUnboundedOrderNonzeroOrdinaryClass
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem gw_limit : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → (∀ m : ℕ, ∃ (n : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l), Coc1 c n (dual1 W) ⊤ z ∧ (∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z a) 0) ∧ (∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧ Cob1 c n (dual1 W) (Ine (F := ℚ) B) z) ∧ (∃ x ∈ c.O, ∀ s ∈ Dec (F := ℚ) A, Cg n (z s 1) (mat (dual1 W) s 1 1 * x - x)) ∧ ¬ Cob1 c n (dual1 W) ⊤ (fun s => ((l : ℕ) : Qbar l) ^ m • z s)) → ¬ GrZero (dual1 W) A := by
  intro hL l _ Ω _ _ _ e S A W hW c hc H hGr
  have h1 := _root_.GlobalTheory.Ord2.DualCont.continuous_galoisRepRankTwoTateDual l Ω e S A W hW
  have h2 := _root_.GlobalTheory.Ord2.galoisRepRankTwoTateDual_matrix_mem_coefRing_of_normalForm l Ω e S A W hW c hc
  have h3 := _root_.GlobalTheory.Ord2.galoisRepRankTwoTateDual_exists_no_eigenvalue_one_alt l Ω e S A W hW
  have h4 := _root_.GlobalTheory.Ord2.galoisRepRankTwoTateDual_eq_one_of_mem_ker_unramified l Ω e S A W hW
  have h5 := GlobalTheory.T.galoisRepRankTwoTateDual_upperTriangular_decompositionGroup l Ω e S A W hW
  have hunb := GlobalTheory.T.exists_cocycle_local_conditions l Ω S A (dual1 W) c h2 h3 H
  have hfin := _root_.GlobalTheory.Ord2.finite_lTorsion_divSel hL l Ω S A (dual1 W) c hW.above h1 h2 h4
  obtain ⟨x, hx0, hx⟩ := _root_.GlobalTheory.Ord2.DivChain.exists_divisible_chain l (DivSel c (dual1 W) S A) (divSel_torsion c (dual1 W) S A) hfin hunb
  obtain ⟨a, N, p1, p2, p3, p4, p5, p6, p7, p8⟩ := GlobalTheory.T.divisibleOrdinarySelmerChain_exists_integral_representatives l Ω S A (dual1 W) c h1 h2 h4 h5 x hx0 hx
  exact GlobalTheory.T.nonzero_ordinary_class_of_compatible_cocycles_mod_pow l Ω S A (dual1 W) c h1 h2 h3 a N p1 p2 p3 p4 p5 p6 p7 p8 hGr

end GlobalTheory.Ord2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDecompositionInvariantRealValuationStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_decomposition_invariant_real_valuation : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∃ v : Valuation Ω ℝ≥0, (∀ x : Ω, v x ≤ 1 ↔ x ∈ A) ∧ (∀ s ∈ Dec (F := ℚ) A, ∀ x : Ω, v (s x) = v x) ∧ 0 < v (l : Ω) ∧ v (l : Ω) < 1 := by
  first | (exact @GlobalTheory.RecOne.exists_real_valuation) | (exact GlobalTheory.RecOne.exists_real_valuation) | (intros; apply GlobalTheory.RecOne.exists_real_valuation  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPolynomialInPrimitiveRootOfInertiaFixed
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

theorem GlobalTheory.ZetaPoly.exists_poly : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (n : ℕ) (ζ : Ω), IsPrimitiveRoot ζ (l ^ n) → ∀ u ∈ A, (∀ s ∈ Ine (F := ℚ) A, s ζ = ζ → s u = u) → ∃ Q : Polynomial Ω, (∀ d, Q.coeff d ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s (Q.coeff d) = Q.coeff d) ∧ Q.eval ζ = u := by
  intro l _ Ω _ _ _ A hA n ζ hζ u hu hfix
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hζ1 : ζ = 1 := by simpa using hζ
    subst hζ1
    refine ⟨Polynomial.C u, fun d => ?_, by simp⟩
    rw [Polynomial.coeff_C]
    split_ifs
    · exact ⟨hu, fun s hs => hfix s hs (map_one s)⟩
    · exact ⟨A.zero_mem, fun s _ => map_zero s⟩
  obtain ⟨P, hPfix, hPev⟩ := GlobalTheory.T.exists_polynomial_eval_eq_of_inertia_fixed Ω A ζ u hfix
  set N := (l ^ n).totient with hN
  have hlpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  have hNpos : 0 < N := Nat.totient_pos.2 hlpos
  set Φ := Polynomial.cyclotomic (l ^ n) Ω with hΦ
  have hΦm : Φ.Monic := Polynomial.cyclotomic.monic _ _
  have hΦdeg : Φ.natDegree = N := Polynomial.natDegree_cyclotomic _ _
  have hΦ1 : Φ ≠ 1 := by
    intro h; rw [h, Polynomial.natDegree_one] at hΦdeg; omega
  set P' := P %ₘ Φ with hP'
  have hroot : Φ.eval ζ = 0 := (hζ.isRoot_cyclotomic hlpos)
  have hev : P'.eval ζ = u := by
    rw [← hPev]
    show (P %ₘ Φ).eval ζ = P.eval ζ
    conv_rhs => rw [← Polynomial.modByMonic_add_div P Φ]
    rw [Polynomial.eval_add, Polynomial.eval_mul, hroot, zero_mul, add_zero]
  have hdeg : P'.natDegree < N := hΦdeg ▸ Polynomial.natDegree_modByMonic_lt P hΦm hΦ1
  have hPmap : ∀ s ∈ Ine (F := ℚ) A, P.map (s : Ω →+* Ω) = P := fun s hs =>
    Polynomial.ext fun d => by rw [Polynomial.coeff_map]; exact hPfix s hs d
  have hP'map : ∀ s ∈ Ine (F := ℚ) A, P'.map (s : Ω →+* Ω) = P' := fun s hs => by
    rw [hP', Polynomial.map_modByMonic _ hΦm, hPmap s hs, hΦ, Polynomial.map_cyclotomic]
  set T := Polynomial.taylor (1 : Ω) P' with hT
  have hTmap : ∀ s ∈ Ine (F := ℚ) A, T.map (s : Ω →+* Ω) = T := fun s hs => by
    rw [hT, Polynomial.map_taylor, hP'map s hs, map_one]
  have hTdeg : T.natDegree < N := by rw [hT, Polynomial.natDegree_taylor]; exact hdeg
  have hsum : (∑ i ∈ Finset.range N, T.coeff i * (ζ - 1) ^ i) = u := by
    rw [← Polynomial.eval_eq_sum_range' hTdeg, hT, Polynomial.taylor_eval, sub_add_cancel, hev]
  obtain ⟨v, hv, hlv⟩ := hA
  have hl1 : A.valuation (l : Ω) < 1 := by
    have := (hv ((l : ℕ) : 𝓞 ℚ)).2 hlv
    simpa using this
  have hl0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hcA : ∀ i < N, T.coeff i ∈ A := by
    refine GlobalTheory.T.coeff_mem_of_sum_mul_pow_mem_of_valuation_zpow Ω A N (ζ - 1) (l : Ω) (fun i => T.coeff i) hNpos hl0 hl1
      (GlobalTheory.T.valuationSubring_primitiveRoot_sub_one_pow_totient_ratAlg l Ω A n ζ hn hζ) (fun i _ hc => ?_) (hsum ▸ hu)
    refine GlobalTheory.T.inertiaFixed_valuation_eq_zpow_prime_ratAlgClosure l Ω A ⟨v, hv, hlv⟩ _ hc (fun s hs => ?_)
    have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p i) (hTmap s hs)
    simpa [Polynomial.coeff_map] using this
  have hcA' : ∀ i, T.coeff i ∈ A := fun i => by
    rcases lt_or_ge i N with h | h
    · exact hcA i h
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; exact A.zero_mem
  have hlift : T ∈ Polynomial.lifts (A.subtype) :=
    (Polynomial.lifts_iff_coeff_lifts T).2 fun i => ⟨⟨_, hcA' i⟩, rfl⟩
  obtain ⟨T₀, hT₀⟩ := Polynomial.mem_lifts T |>.1 hlift
  have hback : Polynomial.taylor (-1 : Ω) T = P' := by
    rw [hT, Polynomial.taylor_taylor, neg_add_cancel, Polynomial.taylor_zero]
  refine ⟨P', fun d => ⟨?_, fun s hs => ?_⟩, hev⟩
  · rw [← hback, ← hT₀]
    have : ((-1 : A) : Ω) = -1 := by simp
    rw [← this, show ((-1 : A) : Ω) = A.subtype (-1) from rfl, ← Polynomial.map_taylor, Polynomial.coeff_map]
    exact (Polynomial.taylor (-1 : A) T₀).coeff d |>.2
  · have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p d) (hP'map s hs)
    simpa [Polynomial.coeff_map] using this

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FixedElementLthPowerModStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_element_lth_power_mod : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ a : fixA A, ∃ (b : fixA A) (z : A), (a : A) = (b : A) ^ l + (l : A) * z := by
  first | (exact @GlobalTheory.RecOne.fixA_eq_pow_add_mul) | (exact GlobalTheory.RecOne.fixA_eq_pow_add_mul) | (intros; apply GlobalTheory.RecOne.fixA_eq_pow_add_mul  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaFixedValuationEqZpowPrimeValuationStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_fixed_valuation_eq_zpow_prime_valuation : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ x : Ω, x ≠ 0 → (∀ s ∈ Ine (F := ℚ) A, s x = x) → ∃ k : ℤ, A.valuation x = A.valuation (l : Ω) ^ k := by
  first | exact @GlobalTheory.InertiaFieldUnram.valuation_eq_zpow | exact GlobalTheory.InertiaFieldUnram.valuation_eq_zpow | (intros; apply GlobalTheory.InertiaFieldUnram.valuation_eq_zpow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaTransportsKaehlerRelationsOverInvariantsStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_transports_kaehler_relations_over_invariants : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (s : G ℚ Ω), s ∈ Ine (F := ℚ) A → ∀ a b a' b' c d c' d' : A, (c : Ω) = s a → (d : Ω) = s b → (c' : Ω) = s a' → (d' : Ω) = s b' → a • dA A b = a' • dA A b' → c • dA A d = c' • dA A d' := by
  first | (exact @GlobalTheory.RecOne.transp_rel) | (exact GlobalTheory.RecOne.transp_rel) | (intros; apply GlobalTheory.RecOne.transp_rel  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalDualityCharacterOrthogonalClassesStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_duality_character_orthogonal_classes : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (A : ValuationSubring Ω) (k k' a b : G ℚ Ω → Qbar l), OverL l A → ContinuousOn k (Dec (F := ℚ) A) → ContinuousOn k' (Dec (F := ℚ) A) → ContinuousOn a (Dec (F := ℚ) A) → ContinuousOn b (Dec (F := ℚ) A) → (∀ s ∈ Dec (F := ℚ) A, k s ∈ c.O ∧ k' s ∈ c.O ∧ a s ∈ c.O ∧ b s ∈ c.O ∧ k s * k' s = eps l s) → (∀ s ∈ Dec (F := ℚ) A, ∀ t ∈ Dec (F := ℚ) A, k (s * t) = k s * k t ∧ k' (s * t) = k' s * k' t ∧ b (s * t) = b s + k s * b t ∧ a (s * t) = a s + k' s * a t) → (∃ s ∈ Dec (F := ℚ) A, k s ≠ 1) → (∃ s ∈ Dec (F := ℚ) A, k' s ≠ 1) → (∀ n : ℕ, Cob2 c n (Dec (F := ℚ) A) (fun s t => b s * (k' s * a t))) → (∃ x : Qbar l, ∀ s ∈ Dec (F := ℚ) A, b s = k s * x - x) ∨ ∃ x : Qbar l, ∀ s ∈ Dec (F := ℚ) A, a s = k' s * x - x := by
  first | exact @GlobalTheory.Ord2.localDuality_char | exact GlobalTheory.Ord2.localDuality_char | (intros; apply GlobalTheory.Ord2.localDuality_char <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormGaussSumModPrimePowerLeHalfPowerStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_gaussSumModPrimePower_le_half_power : ∀ (l : ℕ) [Fact l.Prime] (m : ℕ) (z : Qbar l) (ψ : DirichletCharacter (Qbar l) (l ^ m)), z ^ (l ^ m) = 1 → ‖gSum m z ψ‖ ≤ ‖(l : Qbar l) ^ (m / 2)‖ := by
  first | (exact @GlobalTheory.KZ.Cmp.norm_gSum_le) | (exact GlobalTheory.KZ.Cmp.norm_gSum_le) | (intros; apply GlobalTheory.KZ.Cmp.norm_gSum_le  <;> assumption)
end

