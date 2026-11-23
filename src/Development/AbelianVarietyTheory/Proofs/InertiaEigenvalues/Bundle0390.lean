module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0354
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.MemTypeSubspaceIffUnipotentCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0003
public import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0366
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0358
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0359
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinSeedDiscNormBounds
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.RhoZeroNormBounds

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

theorem ρ₀_pos (bk : BK K) : 0 < bk.ρ₀ := by
  have hl0 : (0 : ℝ≥0) < l := Nat.cast_pos.2 hl.out.pos
  unfold BK.ρ₀
  exact NNReal.rpow_pos hl0

theorem ρ₀_pow (bk : BK K) : bk.ρ₀ ^ bk.Ep.natDegree = (l : ℝ≥0)⁻¹ := by
  have hl0 : (0 : ℝ≥0) < l := Nat.cast_pos.2 hl.out.pos
  have he : (bk.Ep.natDegree : ℝ) ≠ 0 := Nat.cast_ne_zero.2 bk.deg_pos.ne'
  unfold BK.ρ₀
  rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul, neg_mul, one_div, inv_mul_cancel₀ he, NNReal.rpow_neg_one]

theorem norm_l_mul (bk : BK K) (y : bk.DA bk.ρ₀) : ‖(l : bk.DA bk.ρ₀) * y‖ = (l : ℝ)⁻¹ * ‖y‖ := by
  rw [(GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l (Ainf l) (bk.ev X) bk.ρ₀).2.1 y, div_eq_inv_mul]

theorem norm_iS_le (bk : BK K) (x : bk.S) : ‖bk.iS x‖ ≤ 1 :=
  norm_toDisc_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) (bk.ev x)

theorem norm_iS_E (bk : BK K) : ‖bk.iS bk.E‖ ≤ (l : ℝ)⁻¹ := by
  haveI := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l (Ainf l) (bk.ev X) bk.ρ₀).1
  have hE : bk.E = bk.Ep.eval₂ PowerSeries.C PowerSeries.X := (Polynomial.eval₂_C_X_eq_coe).symm
  rw [hE, Polynomial.hom_eval₂, Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ]
  have hinv : (0 : ℝ) ≤ (l : ℝ)⁻¹ := by positivity
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hinv fun i hi => ?_
    obtain ⟨d, hd⟩ := bk.dvd_coeff i (Finset.mem_range.1 hi)
    have e : (bk.iS.comp PowerSeries.C) (bk.Ep.coeff i) * bk.iS PowerSeries.X ^ i =
        (l : bk.DA bk.ρ₀) * bk.iS (PowerSeries.C d * PowerSeries.X ^ i) := by
      rw [hd, RingHom.comp_apply, map_mul, map_mul, map_mul, map_pow, map_natCast, map_natCast, mul_assoc]
    rw [e, norm_l_mul]
    exact mul_le_of_le_one_right hinv (norm_iS_le bk _)
  · rw [bk.monic.coeff_natDegree, map_one, one_mul, ← map_pow]
    change ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev (PowerSeries.X ^ bk.Ep.natDegree))‖ ≤ _
    rw [map_pow]
    refine (norm_toDisc_pow_le _ (ρ₀_pos bk)).trans ?_
    rw [← NNReal.coe_pow, ρ₀_pow, NNReal.coe_inv, NNReal.coe_natCast]

theorem norm_iA_ker (bk : BK K) (a : Ainf l) (ha : Per.θ l a = 0) : ‖bk.iA a‖ ≤ (l : ℝ)⁻¹ := by
  have hmem : a ∈ Ideal.span {bk.ev bk.E} := by rw [bk.span_ev]; exact ha
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hmem
  rw [map_mul]
  refine (norm_mul_le _ _).trans ?_
  have h1 : ‖bk.iA c‖ ≤ 1 := norm_toDisc_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) c
  have h2 : ‖bk.iA (bk.ev bk.E)‖ ≤ (l : ℝ)⁻¹ := norm_iS_E bk
  calc ‖bk.iA c‖ * ‖bk.iA (bk.ev bk.E)‖ ≤ 1 * (l : ℝ)⁻¹ := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem seed_norms : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ‖bk.iS bk.E‖ ≤ (l : ℝ)⁻¹ ∧ (∀ y : bk.DA bk.ρ₀, ‖(l : bk.DA bk.ρ₀) * y‖ = (l : ℝ)⁻¹ * ‖y‖) ∧ ∀ a : Ainf l, Per.θ l a = 0 → ‖bk.iA a‖ ≤ (l : ℝ)⁻¹ :=
  fun _ _ _ bk => ⟨norm_iS_E bk, norm_l_mul bk, norm_iA_ker bk⟩

end GlobalTheory.BSP.RhoZeroNormBounds
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentOfComm
section
noncomputable section

open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.IdemAlg

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (Y : NExp D.R D.host D.what₂ D.LL0 N X)

theorem card_eq : D.what₂.restRowsFiniteGroupCard = Nat.card (G0g N) := by
  have : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  rw [N.restN_card_levelGroup_eq, Nat.card_pi, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  change _ = ∏ _y : N.PlG k, Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k)))
  rw [Finset.prod_const, Finset.card_univ, N.card_PlG k]

theorem idem_integral (i : X.Tw) (b : Bool) :
    ∃ c : MonoidAlgebra (X.O i) (G0g N),
      MonoidAlgebra.map (algebraMap (X.O i) (FractionRing (X.O i))).toAddMonoidHom c =
        ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i)) • Y.eAlg i b := by
  have : CharZero (FractionRing (X.O0 i)) := charZero_of_injective_ringHom (X.emb0 i).injective
  have : CharZero (X.O0 i) := (algebraMap (X.O0 i) (FractionRing (X.O0 i))).charZero
  have : CharZero (X.O i) := charZero_of_injective_ringHom (X.O_inj i)
  have : CharZero (FractionRing (X.O i)) :=
    charZero_of_injective_ringHom (IsFractionRing.injective (X.O i) (FractionRing (X.O i)))
  have hc := card_eq (N := N)
  have : Finite (G0g N) := Nat.finite_of_card_ne_zero (hc ▸ D.what₂.restRowsFiniteGroupCard_pos.ne')
  let : Fintype (G0g N) := Fintype.ofFinite _
  choose c hcc using _root_.GlobalTheory.CentralIdemIntegral.card_mul_coeff_mem (G0g N) (X.O i) (FractionRing (X.O i)) (Y.eAlg i b) (Y.eAlg_idem i b)
    (Y.eAlg_central i b)
  refine ⟨MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm c), ?_⟩
  ext g
  rw [hc, Nat.card_eq_fintype_card]
  simp [hcc]

theorem admALG_of_commG : ∀ D : D7, CommG D → IntegralHeckeForms.GroupAlgebraIntegrality D.nexp := fun D h =>
  (GlobalTheory.TwistInputsTest.admissibleGoodIdempotent_iff_reduced D.nexp).2 fun i hi b => ⟨idem_integral D.nexp i b, h i hi b⟩

end GlobalTheory.IdemAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIntegralPreservesLocalisedLatticeImage
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf Formalism.MainNotions.PairedCharacterCondition
open scoped TensorProduct

namespace GlobalTheory.PendOf.CenLat

theorem prMt_mem_range (D : D7) (i : D.nd.Loc)
    (hO : ∀ a : 𝓞 D.what₂.LL, D.nd.embK i (a : D.what₂.LL) ∈
      (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).range)
    (y : D.what₂.MtL (D.nd.mu i) (D.nd.j i)) (hy : y ∈ GlobalTheory.EtaJoin.lat D (D.nd.mu i) (D.nd.j i)) :
    D.nd.prMt i y ∈ LinearMap.range
      (TensorProduct.mk (D.nd.O i) (FractionRing (D.nd.O i)) (D.nd.Mt i) 1) := by
  unfold GlobalTheory.EtaJoin.lat at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    rw [← D.nd.prMt_lat i]
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    obtain ⟨b, hb⟩ := hO a
    have h1 : a • x = (a : D.what₂.LL) • x := rfl
    rw [h1, LinearMap.map_smulₛₗ, ← hb, algebraMap_smul]
    exact Submodule.smul_mem _ _ hx

theorem cenInt_lat : ∀ (D : D7) (i : D.nd.Loc) (S : Sec D i), (∀ a : 𝓞 D.what₂.LL, D.nd.embK i (a : D.what₂.LL) ∈ (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).range) → (∀ (c : MonoidAlgebra ℂ (G0g D.nd)) (x y : D.what₂.MtL (D.nd.mu i) (D.nd.j i)), D.what₂.jMt _ _ y = D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c (D.what₂.jMt _ _ x) → S.Φ (D.nd.prMt i y) = D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c (S.Φ (D.nd.prMt i x))) → CenInt D → ∀ (c : MonoidAlgebra ℤ (G0g D.nd)), (∀ a, c * a = a * c) → ∀ m : D.nd.Mt i, ∃ m' : D.nd.Mt i, S.Φ ((1 : KK D.nd i) ⊗ₜ[D.nd.O i] m') = D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (mapCoef (Int.castRingHom ℂ) c) (S.Φ ((1 : KK D.nd i) ⊗ₜ[D.nd.O i] m)) := by
  intro D i S hO hΦ hC c hc m
  have hm : (1 : KK D.nd i) ⊗ₜ[D.nd.O i] m ∈ LinearMap.range
      (TensorProduct.mk (D.nd.O i) (FractionRing (D.nd.O i)) (D.nd.Mt i) 1) := ⟨m, rfl⟩
  rw [← D.nd.prMt_lat i] at hm
  generalize (1 : KK D.nd i) ⊗ₜ[D.nd.O i] m = v at hm
  induction hm using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨x, hx, rfl⟩ := hv
    obtain ⟨y, hy, hxy⟩ := hC i c hc x hx
    obtain ⟨m', hm'⟩ := prMt_mem_range D i hO y hy
    refine ⟨m', ?_⟩
    rw [← hΦ _ x y hxy, ← hm']
    rfl
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [TensorProduct.tmul_add, map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]⟩
  | smul a x _ hx =>
    obtain ⟨b, hb⟩ := hx
    refine ⟨a • b, ?_⟩
    rw [TensorProduct.tmul_smul, ← algebraMap_smul (KK D.nd i) a, ← algebraMap_smul (KK D.nd i) a x,
      S.semi, S.semi, map_smul, hb]

end GlobalTheory.PendOf.CenLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscCoefficientsTopologicallyFree
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem disc_coefficients : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type) (TB : TopBasis s bk.J ι) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ j : bk.DS ρ →+* Disc l (s X) ρ, IsDiscMap (l := _) (u := _) (ρ := _) s j → ∃ cD : ι → (Disc l (s X) ρ →+ bk.DS ρ), (∀ i a, cD i (toDisc l (s X) ρ a) = toDisc l (X : bk.S) ρ (TB.c i a)) ∧ (∀ i x y, cD i (j x * y) = x * cD i y) ∧ (∀ i y, ‖cD i y‖ ≤ ‖y‖) ∧ (∀ y, Filter.Tendsto (fun i => cD i y) Filter.cofinite (nhds 0)) ∧ (∀ y, HasSum (fun i => j (cD i y) * toDisc l (s X) ρ (TB.b i)) y) ∧ (∀ y (r : ℝ), 0 ≤ r → (∀ i, ‖cD i y‖ ≤ r) → ‖y‖ ≤ r) ∧ (∀ z : ι → bk.DS ρ, Filter.Tendsto z Filter.cofinite (nhds 0) → ∃ y, ∀ i, cD i y = z i) ∧ ∀ x, ‖j x‖ = ‖x‖ := by
  intro l _ K bk A _ s ι TB ρ h0 h1 j hj
  obtain ⟨cD, hc1, hc2, hc3⟩ := GlobalTheory.T.exists_topologicalBasis_coeff_disc_extension l K bk A s ι TB ρ h0 h1 j hj
  have hs := GlobalTheory.T.closedDisc_topologicalBasis_expansion l K bk A s ι TB ρ h0 h1 j hj cD ⟨hc1, hc2, hc3⟩
  haveI : IsUltrametricDist (Disc l (s X) ρ) := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l A (s X) ρ).1
  have hb : ∀ (x : bk.DS ρ) (i : ι), ‖j x * toDisc l (s X) ρ (TB.b i)‖ ≤ ‖x‖ := fun x i =>
    (norm_mul_le _ _).trans ((mul_le_mul (hj.norm_le x) (norm_toDisc_le _) (norm_nonneg _)
      (norm_nonneg _)).trans (mul_one _).le)
  have hcont : ∀ i, Continuous (cD i) := fun i =>
    AddMonoidHomClass.continuous_of_bound _ 1 fun y => (hc3 i y).trans (one_mul _).ge
  refine ⟨cD, hc1, hc2, hc3, fun y => (hs y).1, fun y => (hs y).2, ?_, ?_, ?_⟩
  · intro y r hr h
    rw [← (hs y).2.tsum_eq]
    exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hr fun i => (hb _ i).trans (h i)
  · intro z hz
    have ht : Filter.Tendsto (fun i => j (z i) * toDisc l (s X) ρ (TB.b i)) Filter.cofinite (nhds 0) :=
      squeeze_zero_norm (fun i => hb (z i) i) (tendsto_zero_iff_norm_tendsto_zero.1 hz)
    have hsum := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ht
    refine ⟨_, fun i => ((hsum.hasSum.map (cD i) (hcont i)).unique ?_)⟩
    classical
    have e : ((cD i) ∘ fun i => j (z i) * toDisc l (s X) ρ (TB.b i)) = fun i' => if i' = i then z i else 0 := by
      funext i'
      simp only [Function.comp]
      rw [hc2, hc1]
      split_ifs with h
      · subst h
        rw [TB.c_self, map_one, mul_one]
      · rw [TB.c_ne _ _ (Ne.symm h), map_zero, mul_zero]
    rw [e]
    exact hasSum_ite_eq i (z i)
  · intro x
    refine le_antisymm (hj.norm_le x) ?_
    have e : cD TB.i₀ (j x * toDisc l (s X) ρ (TB.b TB.i₀)) = x := by
      rw [hc2, hc1, TB.c_self, map_one, mul_one]
    have h := hc3 TB.i₀ (j x * toDisc l (s X) ρ (TB.b TB.i₀))
    rwa [e, TB.b_i₀, map_one, mul_one] at h

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComparisonCocycles
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

noncomputable section

namespace GlobalTheory.NewPrime

section
variable {A : Type} [CommRing A] {a r : ℕ}

theorem rect_map {B B' : Type} [AddCommGroup B] [Module A B] [AddCommGroup B'] [Module A B'] (p : B →ₗ[A] B')
    (Z : Matrix (Fin r) (Fin a) A) (x : Fin a → B) : p.compLeft (Fin r) (rect Z x) = rect Z (p ∘ x) := by
  funext c
  set_option synthInstance.maxHeartbeats 100000 in
    simp [rect, map_sum]

theorem matAct_map {B B' : Type} [AddCommGroup B] [Module A B] [AddCommGroup B'] [Module A B'] (p : B →ₗ[A] B')
    (Φ : Matrix (Fin a) (Fin a) A) (x : Fin a → B) : p ∘ matAct Φ x = matAct Φ (p ∘ x) := by
  funext c
  set_option synthInstance.maxHeartbeats 100000 in
    simp [matAct, map_sum]

end

theorem comparison_cocycles : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q Q' : Finset (PlE D.host)) (a a' : ℕ) (Φ : Matrix (Fin a) (Fin a) A) (Φ' : Matrix (Fin a') (Fin a') A) Z Z' (γ σ : Bool → GE N), Univ bkP i s κ Q Φ Z → Univ bkP i s κ Q' Φ' Z' → (∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (f : GE N → Fin D.R.r → Y), SelC bkP i s κ Y Q' f → (∀ b, f (γ b) = 0) → SelC bkP i s κ Y Q f) → (∀ (Y : Type) [AddCommGroup Y] [Module A Y] b m, repOn (Tgl i s) κ Y (σ b) m = m) → ∃ E : Matrix (Fin a) (Fin a') A, what₂ E ⊔ (what₂ Φ' ⊔ what₂ (fun j : Bool × Fin D.R.r => Z' (γ j.1) j.2)) = ⊤ ∧ (∀ b, (Φ * E) b ∈ what₂ Φ' ⊔ what₂ (fun j : Bool × Fin D.R.r => Z' (γ j.1) j.2)) ∧ ∀ j : Bool × Fin D.R.r, Z' (σ j.1) j.2 - Matrix.vecMul (Z (σ j.1) j.2) E ∈ what₂ Φ' ⊔ what₂ (fun j : Bool × Fin D.R.r => Z' (γ j.1) j.2) := by
  intro D N X bkP i s A _ _ κ Q Q' a a' Φ Φ' Z Z' γ σ hU hU' hSel hσ
  set W : Submodule A (Fin a' → A) := what₂ Φ' ⊔ what₂ (fun j : Bool × Fin D.R.r => Z' (γ j.1) j.2) with hW
  letI tY : TopologicalSpace ((Fin a' → A) ⧸ W) := ⊥
  haveI : DiscreteTopology ((Fin a' → A) ⧸ W) := ⟨rfl⟩
  let gens : Fin a' → (Fin a' → A) ⧸ W := fun j => W.mkQ (Pi.single j 1)
  have hsum : ∀ v : Fin a' → A, ∑ j, v j • gens j = W.mkQ v := by
    intro v
    have : v = ∑ j, v j • (Pi.single j (1 : A) : Fin a' → A) := by
      funext c
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [this]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [gens, map_sum]
  have hrect : ∀ g c, rect (Z' g) gens c = W.mkQ (Z' g c) := fun g c => hsum _
  have hgens : matAct Φ' gens = 0 := by
    funext b
    have : matAct Φ' gens b = W.mkQ (Φ' b) := hsum (Φ' b)
    rw [this]
    exact (Submodule.Quotient.mk_eq_zero W).2 ((le_sup_left : what₂ Φ' ≤ W) (Submodule.subset_span ⟨b, rfl⟩))
  have hf' := (hU' ((Fin a' → A) ⧸ W)).1 gens hgens
  have hγ : ∀ b, (fun g => rect (Z' g) gens) (γ b) = 0 := by
    intro b
    funext c
    show rect (Z' (γ b)) gens c = 0
    rw [hrect]
    exact (Submodule.Quotient.mk_eq_zero W).2
      ((le_sup_right : what₂ (fun j : Bool × Fin D.R.r => Z' (γ j.1) j.2) ≤ W) (Submodule.subset_span ⟨(b, c), rfl⟩))
  have hf := hSel _ _ hf' hγ
  obtain ⟨x, hx, m, hm⟩ := (hU ((Fin a' → A) ⧸ W)).2.2 _ hf
  obtain ⟨E, hE⟩ : ∃ E : Matrix (Fin a) (Fin a') A, ∀ b, W.mkQ (E b) = x b :=
    ⟨fun b => (Submodule.mkQ_surjective W (x b)).choose, fun b => (Submodule.mkQ_surjective W (x b)).choose_spec⟩
  have hvm : ∀ v : Fin a → A, W.mkQ (∑ k, v k • E k) = ∑ k, v k • x k := fun v => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_smul, hE]
  refine ⟨E, ?_, ?_, ?_⟩
  · let S : Submodule A ((Fin a' → A) ⧸ W) := Submodule.span A (Set.range x)
    letI tS : TopologicalSpace (((Fin a' → A) ⧸ W) ⧸ S) := ⊥
    haveI : DiscreteTopology (((Fin a' → A) ⧸ W) ⧸ S) := ⟨rfl⟩
    have hpx : S.mkQ ∘ x = 0 := by
      funext b
      exact (Submodule.Quotient.mk_eq_zero S).2 (Submodule.subset_span ⟨b, rfl⟩)
    have hz : S.mkQ ∘ gens = 0 := by
      refine (hU' (((Fin a' → A) ⧸ W) ⧸ S)).2.1 _ ?_ ⟨S.mkQ.compLeft (Fin D.R.r) m, fun g => ?_⟩
      · rw [← matAct_map, hgens]
        funext b
        simp
      · have e := congrArg (S.mkQ.compLeft (Fin D.R.r)) (hm g)
        rw [map_sub, map_sub, rect_map, rect_map, hpx, repOn_map] at e
        have h0 : rect (Z g) (0 : Fin a → ((Fin a' → A) ⧸ W) ⧸ S) = 0 := by
          funext c
          simp [rect]
        rw [h0, sub_zero] at e
        exact e
    have hgS : ∀ j, gens j ∈ S := fun j =>
      (Submodule.Quotient.mk_eq_zero S).1 (congrFun hz j)
    rw [eq_top_iff]
    intro v _
    have hvS : W.mkQ v ∈ S := by
      rw [← hsum]
      exact S.sum_mem fun j _ => S.smul_mem _ (hgS j)
    have hSm : S = (what₂ E).map W.mkQ := by
      show Submodule.span A (Set.range x) = (Submodule.span A (Set.range E)).map W.mkQ
      rw [Submodule.map_span]
      congr 1
      ext y
      constructor
      · rintro ⟨b, rfl⟩
        exact ⟨E b, ⟨b, rfl⟩, hE b⟩
      · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
        exact ⟨b, (hE b).symm⟩
    rw [hSm] at hvS
    obtain ⟨e, he, hev⟩ := hvS
    have hd : v - e ∈ W := by
      rw [← Submodule.Quotient.mk_eq_zero W, ← Submodule.mkQ_apply, map_sub, hev, sub_self]
    have : v = e + (v - e) := by abel
    rw [this]
    exact Submodule.add_mem_sup he hd
  · intro b
    rw [← Submodule.Quotient.mk_eq_zero W, ← Submodule.mkQ_apply]
    have e1 : (Φ * E) b = ∑ k, Φ b k • E k := by
      funext c
      simp [Matrix.mul_apply, Finset.sum_apply]
    rw [e1, hvm (Φ b)]
    exact congrFun hx b
  · rintro ⟨b, c⟩
    rw [← Submodule.Quotient.mk_eq_zero W, ← Submodule.mkQ_apply]
    have e1 : Matrix.vecMul (Z (σ b) c) E = ∑ k, Z (σ b) c k • E k := by
      funext t
      simp [Matrix.vecMul, dotProduct, Finset.sum_apply]
    have e2 := congrFun (hm (σ b)) c
    rw [hσ, sub_self] at e2
    show W.mkQ (Z' (σ b) c - Matrix.vecMul (Z (σ b) c) E) = 0
    rw [map_sub, e1, hvm (Z (σ b) c), ← hrect]
    exact e2

end GlobalTheory.NewPrime
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComparisonMapIntertwinesGroupAlgebraAction
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf Formalism.MainNotions.PairedCharacterCondition
open scoped TensorProduct

namespace GlobalTheory.PendOf.CenKey

theorem stable (D : D7) (i : D.nd.Loc) (h : OnMtPreservesTypeV D) (c : MonoidAlgebra ℂ (G0g D.nd))
    (s : Set (D.naut.AV i)) (F : D.what₂.Mt (D.nd.mu i) (D.nd.j i))
    (hF : F ∈ ⨆ P ∈ s, D.naut.typeV i P) :
    D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c F ∈ ⨆ P ∈ s, D.naut.typeV i P := by
  have : (⨆ P ∈ s, D.naut.typeV i P) ≤
      (⨆ P ∈ s, D.naut.typeV i P).comap (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c) := by
    refine iSup₂_le fun P hP G hG => ?_
    exact le_biSup (D.naut.typeV i) hP (h i P c G hG)
  exact this hF

theorem phi_mem (D : D7) (i : D.nd.Loc) (S : Sec D i)
    (u : TensorProduct (D.nd.O i) (KK D.nd i) (D.nd.Mt i)) :
    S.Φ u ∈ ⨆ P ∈ {P | D.naut.ptV i P ≠ none}, D.naut.typeV i P := by
  have hu : u ∈ ⨆ x, heckeEig (D.nd.T i) (D.nd.act i) x := by
    rw [Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.EigSpan_holds D.nd i]; exact Submodule.mem_top
  induction hu using Submodule.iSup_induction' with
  | mem x u hu =>
    have hle : typeSum D i (some x) ≤ ⨆ P ∈ {P | D.naut.ptV i P ≠ none}, D.naut.typeV i P := by
      refine iSup₂_le fun P hP => ?_
      have hP' : D.naut.ptV i P = some x := hP
      exact le_biSup (D.naut.typeV i)
        (show P ∈ {P | D.naut.ptV i P ≠ none} from by simp [hP'])
    exact hle (S.eig x u hu)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb

theorem phi_onMt : ∀ (D : D7) (i : D.nd.Loc) (S : Sec D i), OnMtPreservesTypeV D →
    ∀ (c : MonoidAlgebra ℂ (G0g D.nd)) (x y : D.what₂.MtL (D.nd.mu i) (D.nd.j i)),
    D.what₂.jMt _ _ y = D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c (D.what₂.jMt _ _ x) →
    S.Φ (D.nd.prMt i y) = D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c (S.Φ (D.nd.prMt i x)) := by
  intro D i S h c x y hxy
  have hd : Disjoint (⨆ P ∈ {P | D.naut.ptV i P ≠ none}, D.naut.typeV i P)
      (⨆ P ∈ {P | D.naut.ptV i P = none}, D.naut.typeV i P) :=
    (D.naut.typeV_indep i).disjoint_biSup_biSup
      (Set.disjoint_left.2 fun P h1 h2 => h1 h2)
  have h1 := Submodule.sub_mem _ (phi_mem D i S (D.nd.prMt i y))
    (stable D i h c _ _ (phi_mem D i S (D.nd.prMt i x)))
  have h2 := Submodule.sub_mem _ (stable D i h c {P | D.naut.ptV i P = none} _ (S.split x)) (S.split y)
  have e : D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c (D.what₂.jMt _ _ x - S.Φ (D.nd.prMt i x)) -
      (D.what₂.jMt _ _ y - S.Φ (D.nd.prMt i y)) =
      S.Φ (D.nd.prMt i y) - D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c (S.Φ (D.nd.prMt i x)) := by
    rw [map_sub, hxy]; abel
  rw [e] at h2
  exact sub_eq_zero.1 (Submodule.disjoint_def.1 hd _ h1 h2)

end GlobalTheory.PendOf.CenKey
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCConj
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet

namespace GlobalTheory.NewPrime

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem exists_isDual (i : X.Tw) (s : X.Sig i) : ∃ ρ, IsDual i s ρ := by
  have hu : ∀ g, IsUnit (Tmat i s g).det := fun g => by
    rw [← Tgl_coe]; exact Matrix.isUnits_det_units _
  let τ : GE N →* Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i) :=
    { toFun := Tdual i s
      map_one' := by
        rw [Tdual, ← Tgl_coe, map_one, map_one]; simp
      map_mul' := fun g h => by
        simp only [Tdual, ← Tgl_coe, map_mul, Units.val_mul, Matrix.mul_inv_rev, Matrix.transpose_mul, smul_mul_smul_comm] }
  exact ⟨τ.toHomUnits, fun g => rfl⟩


end GlobalTheory.NewPrime
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCoboundaryLiftStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_coboundary_lift : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ A : GRep ↥(GK K) ℚ_[l] LL O, IsDR (P.PD K) A.ρ → ∀ (c : ↥(GK K) → A.V) (x : A.V ⊗[ℚ_[l]] P.R.B), (∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) A.ρ g x - x) → x - φVB (P.PD K) (LL := LL) (V := A.V) x ∈ Dcris (P.PD K) A.ρ ∧ ∃ d ∈ DdR (P.PD K) A.ρ, ιV (P.PD K) (LL := LL) (V := A.V) x - d ∈ FilV (P.PD K) (LL := LL) (V := A.V) 0 := by
  first | exact @GlobalTheory.CobCrisLift.coboundary_lift | exact GlobalTheory.CobCrisLift.coboundary_lift | (intros; apply GlobalTheory.CobCrisLift.coboundary_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFilteredComparisonCoordinatesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_filtered_comparison_coordinates : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]), IsDR (P.PD K) (qRep ρ) → ∀ (a : ℤ) (y : Fin d → P.R.BdR), (∀ i, y i ∈ (P.PD K).Fil a) → ∃ (m : ℕ) (k : Fin m → ℤ) (b : Fin m → P.R.BdR) (z : Fin m → Fin d → P.R.BdR), (∀ r, (∀ g : ↥(GK K), (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) *ᵥ (fun i => P.actQdR (g : GQ l) (z r i)) = z r) ∧ (∀ i, z r i ∈ (P.PD K).Fil (k r)) ∧ b r ∈ (P.PD K).Fil (a - k r)) ∧ y = ∑ r, b r • z r := by
  first | (exact @GlobalTheory.DRFilCoord.filtered_coords) | (exact GlobalTheory.DRFilCoord.filtered_coords) | (intros; apply GlobalTheory.DRFilCoord.filtered_coords  <;> assumption)
end

