module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2135
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2138
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0539
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2144
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2163
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2169
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2174
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2183

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.AmpleAddNefIsAmple
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.ample_add_nef_is_ample : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsProjOver p → ∀ (A N P : LB X) (hA : IsAmpleLB A) (hN : letI := algebraΓOfHom p; IsNef k N) (hP : P.IsLB), cls P hP = cls A hA.isLB + cls N (letI := algebraΓOfHom p; hN.isLB) → IsAmpleLB P := by
  first | exact @_root_.GlobalTheory.isAmpleLB_of_cls_eq_ample_add_nef | exact _root_.GlobalTheory.isAmpleLB_of_cls_eq_ample_add_nef | (intros; apply _root_.GlobalTheory.isAmpleLB_of_cls_eq_ample_add_nef <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CanonicalDivisorOfForm
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.canonical_divisor_of_form : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (η : RatForms q n), η ≠ 0 → (∃ K : CartierDiv Y, IsDivOfForm K η) ∧ ∀ K : CartierDiv Y, IsDivOfForm K η → ∀ Kc : CanonLB q n, toPic K = cls Kc.bundle Kc.isLB := by
  first | exact @_root_.GlobalTheory.Discrepancy.exists_isDivOfForm_and_toPic | exact _root_.GlobalTheory.Discrepancy.exists_isDivOfForm_and_toPic | (intros; apply _root_.GlobalTheory.Discrepancy.exists_isDivOfForm_and_toPic <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CodimOnePointMinimalPrime
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.codim_one_point_minimal_prime : ∀ (X : Scheme.{0}) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U) (z : X) (hz : z ∈ U), Order.coheight z = 1 → (hU.primeIdealOf ⟨z, hz⟩).asIdeal ≠ ⊥ ∧ ∀ Q : Ideal Γ(X, U), Q.IsPrime → Q ≠ ⊥ → Q ≤ (hU.primeIdealOf ⟨z, hz⟩).asIdeal → Q = (hU.primeIdealOf ⟨z, hz⟩).asIdeal := by
  first | exact @_root_.GlobalTheory.primeIdealOf_minimal_of_coheight_eq_one | exact _root_.GlobalTheory.primeIdealOf_minimal_of_coheight_eq_one | (intros; apply _root_.GlobalTheory.primeIdealOf_minimal_of_coheight_eq_one <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CohomologyVanishingIntersections
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
namespace GlobalTheory

private theorem exists_sec_lbPow_add_nonzeroLocus_eq_inf {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {m n : ℕ} (s : (lbPow L m).Sec) (s' : (lbPow L n).Sec) :
    ∃ τ : (lbPow L (m + n)).Sec, nonzeroLocus τ = nonzeroLocus s ⊓ nonzeroLocus s' := by
  refine ⟨powSecMk (m + n) (fun i => powSecFn s i * powSecFn s' i) ?_, ?_⟩
  · intro i j
    rw [map_mul, map_mul, powSecFn_compat s i j, powSecFn_compat s' i j, pow_add]
    ring
  · rw [nonzeroLocus_powSecMk]
    simp_rw [Scheme.basicOpen_mul, ← nonzeroLocus_inf_powSecFn]
    apply le_antisymm
    · exact iSup_le fun i => le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
    · intro x hx
      have hx' : x ∈ ⨆ i, L.U i := by rw [hL.cover]; trivial
      rw [TopologicalSpace.Opens.mem_iSup] at hx' ⊢
      obtain ⟨i, hi⟩ := hx'
      exact ⟨i, ⟨hx.1, hi⟩, ⟨hx.2, hi⟩⟩

theorem exists_sec_lbPow_nonzeroLocus_eq_iInf {X : Scheme.{0}} {H : LB X} (hH : H.IsLB)
    {r : ℕ} (e : Fin r → ℕ) (σ : ∀ a, (lbPow H (e a)).Sec) (he : ∀ a, 0 < e a)
    (t : Finset (Fin r)) (ht : t.Nonempty) :
    ∃ N : ℕ, 0 < N ∧ ∃ τ : (lbPow H N).Sec, nonzeroLocus τ = ⨅ a ∈ t, nonzeroLocus (σ a) := by
  induction t using Finset.cons_induction with
  | empty => exact absurd ht Finset.not_nonempty_empty
  | cons a s ha ih =>
    rcases s.eq_empty_or_nonempty with hs | hs
    · subst hs
      refine ⟨e a, he a, σ a, ?_⟩
      simp
    · obtain ⟨N, hN, τ, hτ⟩ := ih hs
      obtain ⟨τ', hτ'⟩ := exists_sec_lbPow_add_nonzeroLocus_eq_inf hH (σ a) τ
      refine ⟨e a + N, by omega, τ', ?_⟩
      rw [hτ', hτ, Finset.cons_eq_insert, Finset.iInf_insert]

theorem subsingleton_cohOn_preimage_iInf_nonzeroLocus : ∀ (X Y : Scheme.{0}) [CompactSpace Y] [Y.IsSeparated] (s : Y ⟶ X) (F : Y.Modules) [F.IsQuasicoherent] (H : LB X), H.IsLB → ∀ j : ℕ, (∀ᶠ c : ℕ in atTop, Subsingleton (coh (twist F (lbPow (H.pull s) c)) j)) → ∀ (r : ℕ) (e : Fin r → ℕ) (σ : ∀ a, (lbPow H (e a)).Sec), (∀ a, 0 < e a) → ∀ t : Finset (Fin r), t.Nonempty → Subsingleton (cohOn F (s ⁻¹ᵁ (⨅ a ∈ t, nonzeroLocus (σ a))) j) := by
  intro X Y _ _ s F _ H hH j hev r e σ he t ht
  obtain ⟨N, hN, τ, hτ⟩ := exists_sec_lbPow_nonzeroLocus_eq_iInf hH e σ he t ht
  rw [← hτ, ← nonzeroLocus_secPowPull τ s]
  have hM : (H.pull s).IsLB := LB.isLB_pull hH s
  have hL : (lbPow (H.pull s) N).IsLB := isLB_lbPow hM N
  apply subsingleton_cohOn_nonzeroLocus_of_eventually_twist Y F (lbPow (H.pull s) N) hL
  obtain ⟨c0, hc0⟩ := eventually_atTop.1 hev
  refine eventually_atTop.2 ⟨c0, fun c hc => ?_⟩
  have hcls : cls (lbPow (lbPow (H.pull s) N) c) (isLB_lbPow hL c)
      = cls (lbPow (H.pull s) (N * c)) (isLB_lbPow hM (N * c)) := by
    rw [CechPic.cls_lbPow hL, CechPic.cls_lbPow hM, CechPic.cls_lbPow hM, smul_smul, mul_comm]
  obtain ⟨iso⟩ := nonempty_twist_iso_of_cls_eq F (isLB_lbPow hL c) (isLB_lbPow hM (N * c)) hcls
  have hsub := hc0 (N * c) (le_trans hc (Nat.le_mul_of_pos_left c hN))
  exact (cohOn.mapIso (Γ(Y, ⊤)) ⊤ j iso).toEquiv.subsingleton

end GlobalTheory
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.DivisorCenterProperLift
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.divisor_center_proper_lift : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → IsProper s → ∀ (E' : DivOver (s ≫ p)) (E : DivOver p), DivOver.Over s E' E → ∀ x : X, E.Through x → ∃ y : Y, s y = x ∧ E'.Through y := by
  first | exact @_root_.GlobalTheory.Discrepancy.DivOver.exists_through_of_isProper | exact _root_.GlobalTheory.Discrepancy.DivOver.exists_through_of_isProper | (intros; apply _root_.GlobalTheory.Discrepancy.DivOver.exists_through_of_isProper <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.EffectiveCartierLocalEquation
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.effective_cartier_local_equation : ∀ (Y : Scheme.{0}) [IsIntegral Y] (J : Y.IdealSheafData), FinalTheorems.EffCartier J → ∃ E : CartierDiv Y, E.Eff ∧ E.supp = J.support ∧ ∀ (y : Y) (U : Y.affineOpens) (f : Γ(Y, U.1)) (hy : y ∈ U.1) (hf : fnOf U.1 (gen_mem hy) f ≠ 0), J.ideal U = Ideal.span {f} → E.IsEqn y (Units.mk0 _ hf) := by
  first | exact @_root_.GlobalTheory.Cartier.IdealDiv.exists_cartierDiv_of_effCartier | exact _root_.GlobalTheory.Cartier.IdealDiv.exists_cartierDiv_of_effCartier | (intros; apply _root_.GlobalTheory.Cartier.IdealDiv.exists_cartierDiv_of_effCartier <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.EtaleCoordinatesKaehlerBasis
section
open scoped TensorProduct Polynomial
theorem _root_.GlobalTheory.T.etale_coordinates_kaehler_basis : ∀ (R B K : Type) [CommRing R] [CommRing B] [Field K] [Algebra R B] [Algebra B K] [Algebra.Smooth R B] (d : ℕ) (t : Fin d → B), Module.finrank K (K ⊗[B] Ω[B⁄R]) = d → LinearIndependent K (fun a => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B (t a)) → ∃ h : B, algebraMap B K h ≠ 0 ∧ (MvPolynomial.eval₂Hom (algebraMap R (Localization.Away h)) (fun a => algebraMap B (Localization.Away h) (t a))).Etale := by
  first | exact @_root_.GlobalTheory.EtaleCoordSpread.exists_away_etale | exact _root_.GlobalTheory.EtaleCoordSpread.exists_away_etale | (intros; apply _root_.GlobalTheory.EtaleCoordSpread.exists_away_etale <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsMultipleBelowThreshold
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.exists_multiple_below_threshold : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] [CompactSpace Y] (R Fd : CartierDiv Y) (m r a : ℕ), 0 < r → (∀ z, R.mult z < m) → ∃ b : ℕ, a ≤ b ∧ ∀ z, ((r * b) • R + m • Fd).mult z < (m * r * b : ℕ) := by
  first | exact @_root_.GlobalTheory.CoefBound.coef_lt_of_large | exact _root_.GlobalTheory.CoefBound.coef_lt_of_large | (intros; apply _root_.GlobalTheory.CoefBound.coef_lt_of_large <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsPushforwardRegularIdeal
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.exists_pushforward_regular_ideal : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s] [QuasiCompact s] (D : CartierDiv Y), ∃ J : X.IdealSheafData, (∀ (U : X.affineOpens) (f : Γ(X, U.1)), f ∈ J.ideal U ↔ ∀ (y : Y) (hy : s y ∈ U.1), D.RegularAt y (functionFieldMap s (fnOf U.1 (gen_mem hy) f))) := by
  first | exact @_root_.GlobalTheory.Cartier.PullIdeal.exists_idealSheaf | exact _root_.GlobalTheory.Cartier.PullIdeal.exists_idealSheaf | (intros; apply _root_.GlobalTheory.Cartier.PullIdeal.exists_idealSheaf <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FiniteCodimOnePointsClosed
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.finite_codim_one_points_closed : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsNoetherian Y] (B : Closeds Y), B ≠ ⊤ → {v : Y | Order.coheight v = 1 ∧ v ∈ B}.Finite := by
  first | exact @_root_.GlobalTheory.Cartier.finite_coheight_one_of_ne_top | exact _root_.GlobalTheory.Cartier.finite_coheight_one_of_ne_top | (intros; apply _root_.GlobalTheory.Cartier.finite_coheight_one_of_ne_top <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FormOrderBirationalPullback
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.form_order_birational_pullback : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → ∀ (E' : DivOver (s ≫ p)) (E : DivOver p), DivOver.Over s E' E → ∀ (n : ℕ) (η : RatForms p n), η ≠ 0 → (fun ω => @dite ℤ (∃ a, E'.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (EtaleKlt.ratPull p s n η) = (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η := by
  first | exact @_root_.GlobalTheory.BirOrd.formOrd_ratPull_of_over | exact _root_.GlobalTheory.BirOrd.formOrd_ratPull_of_over | (intros; apply _root_.GlobalTheory.BirOrd.formOrd_ratPull_of_over <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.HeightOnePrimePrincipalLocal
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.height_one_prime_principal_local : ∀ (R S : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CommRing S] [IsDomain S] [Algebra R S] (p P : Ideal R) [p.IsPrime] [IsLocalization.AtPrime S p] [UniqueFactorizationMonoid S], P.IsPrime → P ≤ p → P ≠ ⊥ → (∀ Q : Ideal R, Q.IsPrime → Q ≠ ⊥ → Q ≤ P → Q = P) → ∃ a ∈ P, a ≠ 0 ∧ ∃ t ∉ p, ∀ g ∈ P, ∃ r, t * g = a * r := by
  first | exact @_root_.GlobalTheory.heightOne_prime_locallyPrincipal_of_factorial_localization | exact _root_.GlobalTheory.heightOne_prime_locallyPrincipal_of_factorial_localization | (intros; apply _root_.GlobalTheory.heightOne_prime_locallyPrincipal_of_factorial_localization <;> assumption)
end

