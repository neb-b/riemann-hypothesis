module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JumpDictCrysAtOfWeights
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0514
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockCharactersCrystallineOfRules
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0489
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
public import Formalism.SharpRestriction.Bundle0002
public import Development.AutomorphicArithmetic.CyclotomicBounds.CyclotomicOrders.NuHost
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0503
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0466
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0453
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRpToBdR
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeExponentsAinfComparison
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0504
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleBasisOfFCrystal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0505
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0507

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChiOneAwayFromType
section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.ChiOneNoPt

open GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary GlobalTheory.JumpDictionaryFoundation

abbrev sOne (D : D7) : ℝ := ((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2

theorem charpoly_fin_one {R : Type} [CommRing R] (M : Matrix (Fin 1) (Fin 1) R) :
    M.charpoly = Polynomial.X - Polynomial.C (M 0 0) := by
  simp [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply]

theorem integral (D : D7) (hB : BlockCharParam D) (i : D.nd.Loc) :
    ∀ τ : D.host.E →+* ℂ, ∀ z ∈ D.naut.infG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) τ,
      ∃ k : ℤ, z + ((sOne D : ℝ) : ℂ) = (k : ℂ) := by
  intro τ z hz
  obtain ⟨ρ, b, rfl⟩ := exists_embOver D τ
  obtain ⟨a, ha⟩ := firstJump_int D i ρ b
  have hm : z + (blockExp D 1 : ℂ) ∈
      (D.naut.infG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) (embOver D ρ b)).map (· + (blockExp D 1 : ℂ)) :=
    Multiset.mem_map_of_mem (· + (blockExp D 1 : ℂ)) hz
  rw [inf_block D hB i 1 ρ b, Multiset.mem_singleton] at hm
  have hs : blockExp D 1 = sOne D := by simp [blockExp, sOne]
  refine ⟨-a, ?_⟩
  rw [← hs, hm, ha]
  push_cast
  ring

theorem eq_chi (D : D7) (h5 : SumRepresentations.adm5 D) (i : D.nd.Loc) (w₀ : HeightOneSpectrum (𝓞 D.host.E))
    (hw₀ : w₀ ∈ placesOver D.host.E (D.nd.l i)) (ρ : GE D.nd →* GL (Fin 1) (Qbar (D.nd.l i)))
    (hc : Continuous fun g =>
      ((ρ g : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))))
    (haway : ∀ w, w ∉ placesOver D.host.E (D.nd.l i) →
      D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) (sOne D)) :
    ρ = mapRep (iotaOQ D.nd D.naut i) (chiGL D i 1) := by
  have hl : (placesOver D.host.E (D.nd.l i)).Finite := by
    have h0 : ((D.nd.l i : ℕ) : 𝓞 D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.nd.lPrime i).out.ne_zero
    refine (Ideal.finite_factors (I := Ideal.span {((D.nd.l i : ℕ) : 𝓞 D.host.E)})
      (by simpa [Ideal.span_singleton_eq_bot] using h0)).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  let Sg : Set (HeightOneSpectrum (𝓞 D.host.E)) :=
    placesOver D.host.E (D.nd.l i) ∪ ↑(D.nd.S i) ∪ ↑(D.nd.Q i)
  have hSg : Sg.Finite := (hl.union (D.nd.S i).finite_toSet).union (D.nd.Q i).finite_toSet
  have hd := h5.2.2.1 Sg hSg
  have key : (fun g => ((ρ g : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0) =
      fun g => iotaOQ D.nd D.naut i ((D.nd.chi i 1 g : (D.nd.O i)ˣ) : D.nd.O i) := by
    refine Continuous.ext_on (dense_iff_closure_eq.2 hd)
      ((continuous_apply 0).comp ((continuous_apply 0).comp hc))
      ((continuous_iotaOQ D i w₀ hw₀).comp (D.nd.chi_cont i 1)) ?_
    rintro σ ⟨w, hwS, hsp, B, hB, hσ⟩
    simp only [Sg, Set.mem_union, Finset.mem_coe, not_or] at hwS
    have hso : SplitOut D.nd i w := ⟨hsp, hwS.1.1, hwS.1.2, hwS.2⟩
    obtain ⟨hu, hf⟩ := D.naut.chi_mu i w hso
    have hun : D.naut.unr (D.naut.wdOf i ρ w) := by
      rw [haway w hwS.1.1]; exact (D.naut.unr_tw _ _).2 hu
    have e := D.naut.wdOf_frob i ρ w hwS.1.1 hc hun B σ hB hσ
    rw [haway w hwS.1.1, hf B σ hB hσ, Multiset.map_singleton, Multiset.prod_singleton, charpoly_fin_one,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at e
    exact (D.naut.iotaQC i).injective (Polynomial.C_inj.1 (sub_right_injective e))
  ext g a b
  obtain rfl : a = 0 := Subsingleton.elim _ _
  obtain rfl : b = 0 := Subsingleton.elim _ _
  refine (congrFun key g).trans ?_
  rw [← chiGL_apply D i 1 g 0 0]
  rfl

theorem isConstituent_chiGL (D : D7) (i : D.nd.Loc) :
    GlobalTheory.IndefiniteRowSideFullHecke.BlockCharactersCrystallineNonGaloisCusps.IsConstituent D i (D.nd.chi i 1) ((Units.coeHom _).comp (chiGL D i 1)) := by
  refine ⟨fun _ => 1, fun h => one_ne_zero (congrFun h 0), fun g => ?_⟩
  funext a
  obtain rfl : a = 0 := Subsingleton.elim _ _
  simp [Matrix.mulVec, dotProduct, mapM, chiGL]

end GlobalTheory.ChiOneNoPt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChosenTwistAnnihilatesSelmerGroups
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem twist_kills_selmer : ∀ (D : D7) (C : NChoice D) (I : TwIn D) (ρ : FamilyRepresentationConstants.RhoFam D), NChTie D C → TwGoodAt D C I →
    KillingConditions.SignatureChoiceCondition ρ C → KillingConditions.KillAt ρ := by
  intro D C I ρ hT hG hA i hi
  have hw : D.what₂.muAt (D.nd.w i) ≠ D.what₂.mu0 := hi
  obtain ⟨-, hg⟩ := hG (D.nd.w i) hw
  obtain ⟨hA1, hA2⟩ := hA i hi
  obtain ⟨-, -, -, ⟨epsT, hT0, hTs, hTle⟩, -, hD⟩ := hg
  have hl : D.ntw.l (C.twI (D.nd.w i)) = D.nd.l i := by rw [← hT.twOf_eq]; exact D.ntw.twOf_l i
  have heps : twEps D (C.twI (D.nd.w i)) = Formalism.MainNotions.TwistedPlaces.epsL (D.nd.l i) := by
    rw [twEps, Formalism.MainNotions.TwistedPlaces.epsL, hl, one_div]
  refine ⟨fun π hπ => ?_, ?_⟩
  · obtain ⟨s, hs, hfin, hle⟩ := hA1 π hπ
    have h1 := hTle s hs
    have hsum : epsT s ≤ twEps D (C.twI (D.nd.w i)) :=
      le_trans (Finset.single_le_sum (fun s _ => hT0 s) ((Formalism.MainNotions.BlochKatoReduction.Gen.mem_SigG _ _ s).2 hs)) hTs
    have h0 : 0 ≤ (Formalism.MainNotions.BlochKatoReduction.Gen.nu D.ntw (C.twI (D.nd.w i)) : ℝ) + epsT s :=
      add_nonneg (Nat.cast_nonneg _) (hT0 s)
    have h2 := le_trans hle h1
    refine ⟨hfin (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1), ?_⟩
    rw [ENNReal.ofReal_le_ofReal_iff h0] at h2
    rw [← heps]
    rw [UpperTheory.KStar.nu_eq_nuL, hl] at h2
    linarith
  · rw [← heps]
    exact le_trans (mul_le_mul_of_nonneg_left hA2 (Nat.cast_nonneg _)) hD

end GlobalTheory.NLink
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CmHalfTypePlacesMeetConjugatePairsAndCountStatement
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes
open GlobalTheory.SplitCount in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmHalfTypePlaces_meet_conjugatePairs_and_count : ∀ (D : D7) (i : D.nd.Loc), SplitRowPrime D.host (D.nd.l i) → ∀ s : Bool, (∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ w', IsConjPl D.host w w' → Xor (w ∈ columns (N := D.nd) D.nbr i s) (w' ∈ columns (N := D.nd) D.nbr i s)) ∧ (columns (N := D.nd) D.nbr i s).Finite ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), locDeg D.host.E w * (columns (N := D.nd) D.nbr i s).ncard = D.R.f := by
  intro D i hl s
  have hx : ∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ w', IsConjPl D.host w w' →
      Xor (w ∈ columns (N := D.nd) D.nbr i s) (w' ∈ columns (N := D.nd) D.nbr i s) := by
    intro w hw w' h
    have hw' := mem_placesOver_of_conj D.host hw h
    have n1 := GlobalTheory.SplitRowProbe.not_both_columns D i w hw
    have n2 := GlobalTheory.SplitRowProbe.not_both_columns D i w' hw'
    rcases GlobalTheory.T.splitPrime_place_cmType_conjugate D i hl w w' hw hw' h with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> cases s
    · exact Or.inr ⟨⟨hw', h2⟩, fun ⟨_, h3⟩ => n1 ⟨h1, h3⟩⟩
    · exact Or.inl ⟨⟨hw, h1⟩, fun ⟨_, h3⟩ => n2 ⟨h3, h2⟩⟩
    · exact Or.inl ⟨⟨hw, h1⟩, fun ⟨_, h3⟩ => n2 ⟨h2, h3⟩⟩
    · exact Or.inr ⟨⟨hw', h2⟩, fun ⟨_, h3⟩ => n1 ⟨h3, h1⟩⟩
  have := D.host.hostE_isGalois
  obtain ⟨hfin, hdeg⟩ := locDeg_mul_ncard D.host.E hl.1
  let C := columns (N := D.nd) D.nbr i s
  have hsub : C ⊆ placesOver D.host.E (D.nd.l i) := fun _ ⟨hw, _⟩ => hw
  have hCf : C.Finite := hfin.subset hsub
  refine ⟨hx, hCf, fun w hw => ?_⟩
  have hinj : Function.Injective (cPl D.host) := Function.LeftInverse.injective (cPl_cPl D.host)
  have hun : placesOver D.host.E (D.nd.l i) = C ∪ cPl D.host '' C := by
    ext v
    constructor
    · intro hv
      rcases hx v hv _ (isConjPl_cPl D.host v) with h | h
      · exact Or.inl h.1
      · exact Or.inr ⟨_, h.1, cPl_cPl D.host v⟩
    · rintro (hv | ⟨u, hu, rfl⟩)
      · exact hsub hv
      · exact mem_placesOver_of_conj D.host (hsub hu) (isConjPl_cPl D.host u)
  have hdis : Disjoint C (cPl D.host '' C) := by
    rw [Set.disjoint_left]
    rintro _ hv ⟨u, hu, rfl⟩
    rcases hx u (hsub hu) _ (isConjPl_cPl D.host u) with h | h
    · exact h.2 hv
    · exact h.2 hu
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring
  have h := hdeg w hw
  rw [hun, Set.ncard_union_eq hdis hCf (hCf.image _), Set.ncard_image_of_injective _ hinj, hfr] at h
  rw [Nat.mul_add] at h
  change locDeg D.host.E w * C.ncard = D.R.f
  omega
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDeRhamPlusBasisTensorLatticeFree
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
theorem _root_.GlobalTheory.T.coeffDeRhamPlus_basis_tensorLattice_free : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (act : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (κ : Type) [Fintype κ] (b : Module.Basis κ ↥(OL LL) ↥T.L.T), (∀ v : T.V ⊗[ℚ_[l]] Pl.R.BdR, v ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (0) ↔ ∃ d : κ → OD l ↥(OL LL), v = ∑ k, act (d k) (((b k : ↥T.L.T) : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR))) ∧ ∀ d : κ → OD l ↥(OL LL), ∑ k, act (d k) (((b k : ↥T.L.T) : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR)) = 0 → ∀ k, d k = 0 := by
  intro l _ LL T Pl AI Td act hA κ _ b
  refine ⟨fun v => ⟨UpperTheory.KN.exists_BdRPlus_coeffs_of_mem_filZero_deRham l LL T Pl AI Td act hA κ b v, ?_⟩,
    UpperTheory.KN.linearIndependent_Ql_productBasis_of_Zl_lattice l LL T Pl AI Td act hA κ b⟩
  rintro ⟨d, rfl⟩
  exact Submodule.sum_mem _ fun k _ => UpperTheory.KN.latticeAction_mem_filZero_deRham l LL T Pl AI Td act hA (d k) _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComparisonMatrixExistsOnDisc
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.RelEx

theorem map_smul_ring {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {m n : Type} (a : R)
    (M : Matrix m n R) : (a • M).map φ = φ a • M.map φ := by
  ext i j; simp

theorem alg {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (N : ℕ)
    (A Zf Zfi G Y Zg : Matrix n n R) (gE fE wi c lam : R) (hZ : Zf * Zfi = 1) (hAG : A * G = lam • Y)
    (hw : gE * wi = fE) (hc : c * lam = 1) :
    gE ^ N • (A * Zf * ((wi ^ N * c) • (Zfi * G * Zg))) = fE ^ N • (Y * Zg) := by
  have h1 : A * Zf * (Zfi * G * Zg) = lam • (Y * Zg) := by
    rw [Matrix.mul_assoc A Zf, ← Matrix.mul_assoc Zf, ← Matrix.mul_assoc Zf, hZ, Matrix.one_mul,
      ← Matrix.mul_assoc, hAG, Matrix.smul_mul]
  rw [Matrix.mul_smul, h1, smul_smul, smul_smul]
  congr 1
  calc gE ^ N * (wi ^ N * c) * lam = (gE * wi) ^ N * (c * lam) := by ring
    _ = fE ^ N := by rw [hw, hc, mul_one]

theorem cancel {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (Xf X'f Y G : Matrix n n R)
    (e lk lc : R) (he : e ∈ nonZeroDivisors R) (hXX : Xf * X'f = (lc * e) • 1) (hG : e • G = lk • (X'f * Y)) :
    Xf * G = (lk * lc) • Y := by
  have h2 : e • (Xf * G) = e • ((lk * lc) • Y) := by
    rw [← Matrix.mul_smul, hG, Matrix.mul_smul, ← Matrix.mul_assoc, hXX, Matrix.smul_mul, Matrix.one_mul,
      smul_smul, smul_smul]
    congr 1; ring
  ext i j
  have h3 := congrFun (congrFun h2 i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h3
  exact (mul_cancel_left_mem_nonZeroDivisors he).1 h3

theorem map_unit_eq {R S : Type} [CommRing R] [CommRing S] (T : R →+* S) (a b : R) (w : Rˣ) (hw : a * w = b) :
    T b * T (↑w⁻¹ : R) = T a := by
  rw [← hw, ← map_mul, mul_assoc, Units.mul_inv, mul_one]

theorem inv_pow_map {R S : Type} [CommRing R] [CommRing S] (T : R →+* S) (x : R) (li : S) (h : li * T x = 1)
    (m : ℕ) : li ^ m * T (x ^ m) = 1 := by
  rw [map_pow, ← mul_pow, h, one_pow]

end GlobalTheory.BSP.RelEx

namespace GlobalTheory.BSP.Height

open GlobalTheory.BSP.RelEx

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ}
  {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]} {τ : Ainf l} {s : Seed bk d ρ τ} (ht : Height s)

theorem bas_map_disc {B : Obj l ↥(OL K)} (u : B.A) (h : Hom bk.prism B) (F : bk.DS bk.ρ₀ →+* Disc l u bk.ρ₀)
    (hF : IsDiscMap (l := _) (u := _) (ρ := _) (BK.hf h) F) :
    ht.bas.map F = (s.X.map (BK.hf h)).map (toDisc l u bk.ρ₀) * ht.Z.map F := by
  rw [Height.bas, Matrix.map_mul]
  congr 1
  ext i j
  simp only [Matrix.map_apply]
  exact hF.ext _

theorem rel_exists_of {B : Obj l ↥(OL K)} (u : B.A) (f g : Hom bk.prism B)
    (Ff Fg : bk.DS bk.ρ₀ →+* Disc l u bk.ρ₀) (hF : IsDiscMap (l := _) (u := _) (ρ := _) (BK.hf f) Ff) (hG : IsDiscMap (l := _) (u := _) (ρ := _) (BK.hf g) Fg)
    (w : B.Aˣ) (hw : BK.hf f bk.E * w = BK.hf g bk.E) (G : Matrix (Fin d) (Fin d) B.A) (m : ℕ)
    (hAG : s.X.map (BK.hf f) * G = (l : B.A) ^ m • s.X.map (BK.hf g)) :
    ∃ ε : Matrix (Fin d) (Fin d) (Disc l u bk.ρ₀), ht.Rel u f g ε := by
  obtain ⟨Z', hZ'⟩ : ∃ Z', ht.Z * Z' = 1 := by
    obtain ⟨U, hU⟩ := ht.Z_unit
    exact ⟨↑U⁻¹, by rw [← hU]; exact U.mul_inv⟩
  obtain ⟨li, hli⟩ : ∃ li : Disc l u bk.ρ₀, li * toDisc l u bk.ρ₀ (l : B.A) = 1 :=
    ((IsLocalization.Away.algebraMap_isUnit (S := PreDisc l u bk.ρ₀) (l : B.A)).map (ofPre l u bk.ρ₀)).exists_left_inv
  have key : toDisc l u bk.ρ₀ (BK.hf g bk.E) ^ s.N • (ht.bas.map Ff *
      ((toDisc l u bk.ρ₀ (↑w⁻¹ : B.A) ^ s.N * li ^ m) •
        (Z'.map Ff * G.map (toDisc l u bk.ρ₀) * ht.Z.map Fg))) =
      toDisc l u bk.ρ₀ (BK.hf f bk.E) ^ s.N • ht.bas.map Fg := by
    have e1 := ht.bas_map_disc u f Ff hF
    have e2 := ht.bas_map_disc u g Fg hG
    have h4 := alg s.N ((s.X.map (BK.hf f)).map (toDisc l u bk.ρ₀)) (ht.Z.map Ff) (Z'.map Ff)
      (G.map (toDisc l u bk.ρ₀)) ((s.X.map (BK.hf g)).map (toDisc l u bk.ρ₀)) (ht.Z.map Fg)
      (toDisc l u bk.ρ₀ (BK.hf g bk.E)) (toDisc l u bk.ρ₀ (BK.hf f bk.E))
      (toDisc l u bk.ρ₀ (↑w⁻¹ : B.A)) (li ^ m) (toDisc l u bk.ρ₀ ((l : B.A) ^ m))
      (by rw [← Matrix.map_mul, hZ', Matrix.map_one _ (map_zero _) (map_one _)])
      (by rw [← Matrix.map_mul, hAG, map_smul_ring])
      (map_unit_eq _ _ _ w hw)
      (inv_pow_map _ _ li hli m)
    exact (congrArg (fun M => toDisc l u bk.ρ₀ (BK.hf g bk.E) ^ s.N • (M *
      ((toDisc l u bk.ρ₀ (↑w⁻¹ : B.A) ^ s.N * li ^ m) • (Z'.map Ff * G.map (toDisc l u bk.ρ₀) * ht.Z.map Fg)))) e1).trans
      (h4.trans (congrArg (fun M => toDisc l u bk.ρ₀ (BK.hf f bk.E) ^ s.N • M) e2.symm))
  refine ⟨(toDisc l u bk.ρ₀ (↑w⁻¹ : B.A) ^ s.N * li ^ m) •
    (Z'.map Ff * G.map (toDisc l u bk.ρ₀) * ht.Z.map Fg), ?_⟩
  unfold Height.Rel
  intro Ff' Fg' hF' hG'
  have e1 : Ff' = Ff := (hF.unique hF').symm
  have e2 : Fg' = Fg := (hG.unique hG').symm
  subst e1 e2
  exact key

end GlobalTheory.BSP.Height

namespace GlobalTheory.BSP.Height

open GlobalTheory.BSP.RelEx

theorem rel_exists : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s)
    (B : Obj l ↥(OL K)) (u : B.A) (f g : Hom bk.prism B),
    ∃ ε : Matrix (Fin d) (Fin d) (Disc l u bk.ρ₀), ht.Rel u f g ε := by
  intro l _ K bk d ρ τ s ht B u f g
  by_cases hex : ∃ Ff Fg : bk.DS bk.ρ₀ →+* Disc l u bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) (BK.hf f) Ff ∧ IsDiscMap (BK.hf g) Fg
  swap
  · refine ⟨0, ?_⟩
    unfold Height.Rel
    intro Ff Fg hF hG
    exact (hex ⟨Ff, Fg, hF, hG⟩).elim
  obtain ⟨Ff, Fg, hF, hG⟩ := hex
  obtain ⟨hreg, ⟨w, hw⟩, -⟩ := _root_.GlobalTheory.BSP.hf_E_pair l K bk B f g
  obtain ⟨k, hk⟩ := s.nopole f g
  choose G hGc using hk
  have hXX : s.X.map (BK.hf f) * s.X'.map (BK.hf f) = ((l : B.A) ^ s.c₂ * BK.hf f bk.E ^ (2 * s.N)) • 1 := by
    rw [← Matrix.map_mul, s.X_mul, map_smul_ring, Matrix.map_one _ (map_zero _) (map_one _)]
    simp
  have hGm : BK.hf f bk.E ^ (2 * s.N) • Matrix.of G = (l : B.A) ^ k • (s.X'.map (BK.hf f) * s.X.map (BK.hf g)) := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
    exact (hGc i j).symm
  have hAG : s.X.map (BK.hf f) * Matrix.of G = (l : B.A) ^ (k + s.c₂) • s.X.map (BK.hf g) := by
    rw [pow_add]
    exact cancel _ _ _ _ _ _ _ (pow_mem hreg _) (by rw [hXX, mul_comm]) hGm
  exact ht.rel_exists_of u f g Ff Fg hF hG w hw (Matrix.of G) (k + s.c₂) hAG

end GlobalTheory.BSP.Height
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordEPowBasis
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal

noncomputable section

namespace GlobalTheory.BKGal.HatVal.BasisCoord

variable {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K]
  {G : Type} [Group G] [TopologicalSpace G]

theorem tWincl_smul' {R R' : Type} [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R'] (f : R →ₐ[O] R')
    (T : LocLat G ℚ_[l] K O) (r : R) (z : TW R T) : TWincl f T (r • z) = f r • TWincl f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul s x =>
    simp only [TWincl, smul_tmul', TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply,
      smul_eq_mul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

end GlobalTheory.BKGal.HatVal.BasisCoord


open GlobalTheory.BKGal.HatVal.BasisCoord in
theorem GlobalTheory.BKGal.HatVal.coord_E_pow_basis : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T) (ε δ : OCb l), IsEps ε → δ ^ l = ε → ∀ j : ι, ∃ c : ι → OA l O, inclL t ϖ D.toPhiMod c = inclO l O (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H) • (Pi.single j 1 : ι → OW l O) ∧ ∃ z : TW (OA l O) T, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf δ ^ η)) • R.jB (fun i => toB l O (c i)) = TWincl (toB l O) T (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H • z) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R ε δ hε hδ j

  let ej : Vec K a ι := fun _ => Pi.single j 1
  have hej : ej ∈ D.toPhiMod.M := mem_tot.2 fun τ i => by
    by_cases h : i = j
    · subst h; simp only [ej, Pi.single_eq_same]; exact one_mem _
    · simp only [ej, Pi.single_eq_of_ne h]; exact zero_mem _
  have hL : E K l e ^ H • ej ∈ D.toPhiMod.L := D.lower _ hej
  obtain ⟨c, hc⟩ := toW_mem_LA t ϖ D.toPhiMod hL

  have hw : toW t ϖ D.toPhiMod ⟨ej, mem_ME_of_mem_M hej⟩ = (Pi.single j 1 : ι → OW l O) := by
    ext1 i
    rw [toW_apply]
    by_cases h : i = j
    · subst h
      rw [Pi.single_eq_same]
      convert map_one (ϖ.iW t K) using 1
      exact congrArg _ (funext fun τ => Subtype.ext (by simp [ej]))
    · rw [Pi.single_eq_of_ne h]
      convert map_zero (ϖ.iW t K) using 1
      exact congrArg _ (funext fun τ => Subtype.ext (by simp [ej, Pi.single_eq_of_ne h]))

  have hE : ϖ.iW t K (fun _ => ⟨E K l e ^ H, le_away _ _ (pow_mem (E_mem l e _) H)⟩) =
      inclO l O (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H) := by
    have h1 := ϖ.iW_of_mem t K (fun _ => EIn l e (A O K) ^ H)
    have h2 : ϖ.iTot t K (fun _ => EIn l e (A O K) ^ H) = ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H := by
      rw [show (fun _ : ZMod a => EIn l e (A O K) ^ H) = (fun _ => EIn l e (A O K)) ^ H from rfl, map_pow,
        PiSys.iTot_E t K ϖ]
    rw [h2] at h1
    rw [← h1]
    exact congrArg _ (funext fun τ => Subtype.ext (by simp [EIn]))
  have hwE : toW t ϖ D.toPhiMod ⟨E K l e ^ H • ej, mem_ME_of_mem_L hL⟩ =
      inclO l O (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H) • (Pi.single j 1 : ι → OW l O) := by
    rw [toW_smul t ϖ D.toPhiMod (fun _ => ⟨E K l e ^ H, le_away _ _ (pow_mem (E_mem l e _) H)⟩)
      ⟨ej, mem_ME_of_mem_M hej⟩ _ (fun τ => rfl), hE, hw]
  have h1 : inclL t ϖ D.toPhiMod c =
      inclO l O (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H) • (Pi.single j 1 : ι → OW l O) :=
    hc.trans hwE
  refine ⟨c, h1, ?_⟩

  obtain ⟨-, hK2, -, -⟩ := _root_.GlobalTheory.BKExp.exponents l a e O K t ϖ ι D.toPhiMod T R.I η H D.upper D.lower ε δ hε hδ
  have hv : (Pi.single j 1 : ι → OW l O) ∈ MA D.toPhiMod :=
    ⟨Pi.single j 1, funext fun i => by
      by_cases h : i = j
      · subst h; simp [inclV]
      · simp [inclV, Pi.single_eq_of_ne h]⟩
  obtain ⟨z, hz⟩ := hK2 _ hv
  refine ⟨z, ?_⟩
  set m : OA l O := (1 : O) ⊗ₜ[ℤ_[l]] (muOf δ ^ η) with hm
  set Eh : OA l O := ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H with hEh
  have hB := R.cmp (fun i => m * c i) (Eh • z) (by
    rw [inclL_smul_coord, h1, smul_comm, map_smul, hz, tWincl_smul'])
  have e1 : (fun i => toB l O (m * c i)) = toB l O m • fun i => toB l O (c i) :=
    funext fun i => by simp only [map_mul, Pi.smul_apply, smul_eq_mul]
  rw [e1, map_smul] at hB
  exact hB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystalChangeOfBasisFrobeniusCompatStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystal_changeOfBasis_frobenius_compat : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : Lat a O K ϖ) (I : Ident t ϖ P T), letI := zlLat T; ∀ (E : FCrys l ↥(OL (ϖ.field a))) (jA : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T)), Realises (ϖ.field a) E (ainfObj _) (ainfId _) ↥T.L.T (actZ T) jA → (∀ y : TW (OW l O) T, (∃ x : E.M (ϖ.prism a), y = kappa T (jA (E.tr (ϖ.toAinf a) x))) ↔ ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) → ∀ (oE : O → FHom E E), (∀ (c : O) (x : E.M (ainfObj (ϖ.field a))), jA ((oE c).u (ainfObj (ϖ.field a)) x) = (OfCrystal.mulZ T c).lTensor (WCb l) (jA x)) → ∀ (b : ι → E.M (ϖ.prism a)), (∀ j, ∃ hm : (bas j : Vec K a ι) ∈ P.M, kappa T (jA (E.tr (ϖ.toAinf a) (b j))) = I.j (toW t ϖ P ⟨bas j, mem_ME_of_mem_M hm⟩)) → ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) → (∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f)) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (κ : ZMod a → PP.A →+* K⟦X⟧⟦X⟧), PP.I = Ideal.span {(l : PP.A)} → (∀ τ (x : (Wq l a)⟦X⟧), κ τ (p₀.f x) = PowerSeries.C (toAc t K (frobS l a x) τ : K⟦X⟧) ∧ κ τ (p₁.f x) = sh (toAc t K (frobS l a x) τ : K⟦X⟧)) → (∀ τ y, κ τ (PP.D.φ y) = φ₂ (κ (τ - 1) y)) → ∀ (Q : Type) [Fintype Q] (c : ι → ι → Q → O) (y : ι → ι → Q → PP.A), (∀ j, E.tr p₁ (b j) = ∑ i, ∑ q, y i j q • (oE (c i j q)).u PP (E.tr p₀ (b i))) → ∀ τ, (Matrix.of fun i j => ∑ q, c i j q • κ τ (y i j q)) * ((P.mx (τ - 1)).map (frob K l)).map sh = ((P.mx (τ - 1)).map (frob K l)).map PowerSeries.C * (Matrix.of fun i j => ∑ q, c i j q • κ (τ - 1) (y i j q)).map φ₂ := by
  first | exact @GlobalTheory.CrysEpsFrob.eps_frob_compat | exact GlobalTheory.CrysEpsFrob.eps_frob_compat | (intros; apply GlobalTheory.CrysEpsFrob.eps_frob_compat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineDiscPeriodsFrobeniusEqMulStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discPeriods_map_frobenius_eq_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → ((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) • s.W.map Φ = s.W * (s.X' * s.F.map (C : Wq l bk.a →+* bk.S) * s.X.map (frobS l bk.a)).map bk.iS := by
  first | exact @GlobalTheory.BSP.Seed.crystallineDiscPeriods_frobenius_eq_mul | exact GlobalTheory.BSP.Seed.crystallineDiscPeriods_frobenius_eq_mul | (intros; apply GlobalTheory.BSP.Seed.crystallineDiscPeriods_frobenius_eq_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinDivClosedDiscOfTopBasisStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_div_closedDisc_of_topBasis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → ∀ ρ : ℝ≥0, bk.ρ₀ ≤ ρ → ρ < 1 → (∀ y : Disc l (s X) ρ, ‖toDisc l (s X) ρ (s bk.E) * y‖ = (ρ : ℝ) ^ bk.Ep.natDegree * ‖y‖) ∧ ∀ R : Disc l (s X) ρ →+* Disc l (s X) bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id A) R → ∀ (h : ℕ) (y : Disc l (s X) ρ), toDisc l (s X) bk.ρ₀ (s bk.E) ^ h ∣ R y → toDisc l (s X) ρ (s bk.E) ^ h ∣ y := by
  first | exact @GlobalTheory.BSP.div_E_of_topBasis | exact GlobalTheory.BSP.div_E_of_topBasis | (intros; apply GlobalTheory.BSP.div_E_of_topBasis <;> assumption)
end

