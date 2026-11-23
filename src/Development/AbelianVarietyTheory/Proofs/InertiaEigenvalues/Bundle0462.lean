module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0424
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0420
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0422
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAlgebraMapPadicInt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCountOfSetup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConditionAboveLSaturatedOfSelmerSetup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerObstructionLeResidualSelmerSimpleExtension
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
public import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
public import Formalism.LocalToGlobal.LatticeGeometry.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0416
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0421
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0429
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerOrderFormulaDualSelmer
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.SelOrder

theorem cupB_sub_cob {Γ A M M' : Type} [Group Γ] [TopologicalSpace Γ] [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup M'] [Module A M'] [TopologicalSpace M] [DiscreteTopology M] [TopologicalSpace M'] [DiscreteTopology M']
    {n : ℕ} (χ : Γ → ZMod n) (π : Representation A Γ M) (π' : Representation A Γ M') (P : M →+ M' →+ ZMod n)
    (hP : ∀ g x y, P (π g x) (π' g y) = χ g * P x y) (x : Γ → M) (y y' : Γ → M') (m : M')
    (hx : Continuous x) (hx' : ∀ g h, x (g * h) = x g + π g (x h)) (hm : Continuous fun g => π' g m)
    (hy : ∀ g, y' g = y g - (π' g m - m))
    (h : CupB χ (fun g m => π' g m) P x y) : CupB χ (fun g m => π' g m) P x y' := by
  obtain ⟨F, hF, h⟩ := h
  refine ⟨F + fun g => P (x g) (π' g m), hF.add (((IsLocallyConstant.iff_continuous _).2 (hx.prodMk hm)).comp
    fun p : M × M' => P p.1 p.2), fun g k => ?_⟩
  have h1 := h g k
  have h2 := hP g (x k) (π' k m)
  simp only [hy, map_add (f := _), map_sub, AddMonoidHom.add_apply, Pi.add_apply, hx', map_mul, Module.End.mul_apply] at h1 ⊢
  linear_combination h1 + h2

theorem tors_all (A : Type) [CommRing A] [IsLocalRing A] [Finite A] (B : Type) [AddCommGroup B] [Module A B] :
    Tors A B := by
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hn
  refine fun b => ⟨n, fun x hx => ?_⟩
  rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at hx
  rw [hx, zero_smul]

section General

open Formalism.GaloisCohomology

variable {F Ω : Type} [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  (l : ℕ) [Fact l.Prime] (n : ℕ) {Λ W W' : Type} [CommRing Λ]
  [AddCommGroup W] [Module Λ W] [TopologicalSpace W] [DiscreteTopology W] [Finite W]
  [AddCommGroup W'] [Module Λ W'] [TopologicalSpace W'] [DiscreteTopology W'] [Finite W']

theorem order_formula (hPT : PoitouTateTotallyComplex) (hLF : LocalFiniteness) (hLD : LocalTateDuality)
    (hLE : LocalEulerChar) (hGF : GlobalFiniteness) (hGE : GlobalEulerChar)
    (ρ : Representation Λ (G F Ω) W) (ρ' : Representation Λ (G F Ω) W') (P : W →+ W' →+ ZMod (l ^ n)) (hn : 0 < n)
    (hc : ContAction ρ) (hc' : ContAction ρ') (hl : ∀ x, (∀ y, P x y = 0) → x = 0) (hr : ∀ y, (∀ x, P x y = 0) → y = 0)
    (hP : ∀ g x y, P (ρ g x) (ρ' g y) = ((cycMod F Ω l n g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * P x y)
    (A : Places F Ω) (T : Set (HeightOneSpectrum (𝓞 F))) (hT : T.Finite) (Q : Finset (HeightOneSpectrum (𝓞 F)))
    (hTl : ∀ v ∈ T, v ∉ placesOver F l) (hQl : ∀ v ∈ Q, v ∉ placesOver F l)
    (hur : ∀ v, v ∉ placesOver F l → v ∉ T → v ∉ Q → ∀ B : ValuationSubring Ω, IsPlaceOver B v →
      ∀ τ ∈ Ine (F := F) B, ρ τ = 1 ∧ ρ' τ = 1)
    (L : ∀ v, Submodule Λ (H1 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) (C : Set (H1 ρ'))
    (hC : ∀ c, c ∈ C ↔ ∃ y : Z1 ρ',
      ((∀ v, v ∉ placesOver F l → v ∉ T → v ∉ Q → ∀ τ ∈ Ine (F := F) (A.1 v), y.1 τ = 0) ∧
        (∀ v, v ∈ T ∨ v ∈ Q → ∃ m, ∀ g ∈ Dec (F := F) (A.1 v), y.1 g = ρ' g m - m) ∧
        ∀ v ∈ placesOver F l, ∀ x : Z1 (ρ.comp (Dec (F := F) (A.1 v)).subtype), Submodule.Quotient.mk x ∈ L v →
          CupB (fun g : Dec (F := F) (A.1 v) => ((cycMod F Ω l n g.1 : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)))
            (fun g m => ρ' g.1 m) P x.1 (fun g => y.1 g.1)) ∧ c = Submodule.Quotient.mk y)
    (h0 : H0 ρ = ⊥) (h0' : H0 ρ' = ⊥) (hT0 : ∀ v ∈ T, H0 (ρ'.comp (Dec (F := F) (A.1 v)).subtype) = ⊥)
    (hcount : ∏ᶠ v ∈ placesOver F l, Nat.card (L v) =
      (∏ᶠ v ∈ placesOver F l, Nat.card (H0 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) *
        Nat.card W ^ InfinitePlace.nrComplexPlaces F) :
    Finite C ∧ Nat.card (SelAll ρ A (bkCond ρ A l (T ∪ ↑Q) L)) =
      Nat.card C * ∏ v ∈ Q, Nat.card (H0 (ρ'.comp (Dec (F := F) (A.1 v)).subtype)) := by
  classical
  have hfin := GlobalTheory.SelObstruction.finite_above (F := F) l
  have hsub : ∀ {M : Type} [AddCommGroup M] [Module Λ M] [TopologicalSpace M] [DiscreteTopology M]
      (π : Representation Λ (G F Ω) M), ContAction π → ∀ U : Subgroup (G F Ω), ContAction (π.comp U.subtype) :=
    fun π h U => h.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hloc := fun v => GlobalTheory.T.localDuality_perfect_pair_finite_modules hLF hLD hLE F Ω l n (A.1 v) v (A.2 v) Λ W W'
    (ρ.comp (Dec (F := F) (A.1 v)).subtype) (ρ'.comp (Dec (F := F) (A.1 v)).subtype) P hn (hsub ρ hc _) (hsub ρ' hc' _)
    hl hr (fun g x y => hP g.1 x y)
  have hS : ∀ v, v ∈ hfin.toFinset ∪ (hT.toFinset ∪ Q) ↔ v ∈ placesOver F l ∨ v ∈ T ∨ v ∈ Q := by simp
  have hS' : ∀ v, v ∉ hfin.toFinset ∪ (hT.toFinset ∪ Q) ↔ v ∉ placesOver F l ∧ v ∉ T ∧ v ∉ Q := fun v => by
    rw [hS, not_or, not_or]
  have hnl : ∀ v, v ∈ T ∨ v ∈ Q → v ∉ placesOver F l := fun v h => h.elim (hTl v) (hQl v)
  have b1 : ∀ v ∈ placesOver F l, bkCond ρ A l (T ∪ ↑Q) L v = L v := fun v hv => if_pos hv
  have b2 : ∀ v, v ∈ T ∨ v ∈ Q → bkCond ρ A l (T ∪ ↑Q) L v = ⊤ := fun v hv => (if_neg (hnl v hv)).trans (if_pos hv)
  obtain ⟨fC, e⟩ := GlobalTheory.T.greenbergWiles_pair_alt hPT hLF hGF hGE F Ω l n Λ W W' ρ ρ' P hn hc hc' hl hr hP
    (hfin.toFinset ∪ (hT.toFinset ∪ Q)) A (fun v hv => (hS v).2 (.inl hv))
    (fun v hv => hur v ((hS' v).1 hv).1 ((hS' v).1 hv).2.1 ((hS' v).1 hv).2.2) (bkCond ρ A l (T ∪ ↑Q) L)
    (fun v hv => (if_neg ((hS' v).1 hv).1).trans (if_neg (not_or.2 ((hS' v).1 hv).2))) C (fun y => by
      rw [hC]
      constructor
      · rintro ⟨y', ⟨k1, k2, k3⟩, e⟩
        have e' : (y' - y).1 ∈ B1 ρ' := (Submodule.Quotient.eq ((B1 ρ').comap (Z1 ρ').subtype)).1 e.symm
        obtain ⟨m, hm⟩ := (mem_coboundaries1 ρ' _).1 e'
        have hm' : ∀ g, y.1 g = y'.1 g - (ρ' g m - m) := fun g => by
          rw [← hm g]
          exact (sub_sub_cancel _ _).symm
        refine ⟨fun v hv τ hτ => ?_, fun v hv x hx => ?_⟩
        · obtain ⟨a, b, c⟩ := (hS' v).1 hv
          rw [hm', k1 v a b c τ hτ, (hur v a b c _ (A.2 v) τ hτ).2]
          simp
        · rcases (hS v).1 hv with hv | hv
          · rw [b1 v hv] at hx
            exact cupB_sub_cob _ (ρ.comp (Dec (F := F) (A.1 v)).subtype) (ρ'.comp (Dec (F := F) (A.1 v)).subtype) P
              (fun g x y => hP g.1 x y) x.1 _ _ m x.2.1 x.2.2
              ((hsub ρ' hc' _).comp (continuous_id.prodMk continuous_const)) (fun g => hm' g.1) (k3 v hv x hx)
          · obtain ⟨m', hm''⟩ := k2 v hv
            refine ((hloc v).1 (restrictCocycles1 ρ' _ continuous_subtype_val y)).2 ⟨m' - m, fun g => ?_⟩ x
            change y.1 g.1 = ρ' g.1 (m' - m) - (m' - m)
            rw [hm', hm'' g.1 g.2, map_sub]
            abel
      · rintro ⟨k1, k2⟩
        refine ⟨y, ⟨fun v a b c => k1 v ((hS' v).2 ⟨a, b, c⟩), fun v hv => ?_, fun v hv x hx => ?_⟩, rfl⟩
        · obtain ⟨m, hm⟩ := ((hloc v).1 (restrictCocycles1 ρ' _ continuous_subtype_val y)).1 fun x =>
            k2 v ((hS v).2 (.inr hv)) x (by rw [b2 v hv]; trivial)
          exact ⟨m, fun g hg => hm ⟨g, hg⟩⟩
        · exact k2 v ((hS v).2 (.inl hv)) x (by rw [b1 v hv]; exact hx))
  refine ⟨fC, ?_⟩
  have hd : Disjoint hfin.toFinset (hT.toFinset ∪ Q) := Finset.disjoint_right.2 fun v hv h =>
    hnl v (by simpa using hv) (by simpa using h)
  rw [finprod_mem_eq_finite_toFinset_prod _ hfin, finprod_mem_eq_finite_toFinset_prod _ hfin] at hcount
  have e1 : ∏ v ∈ hfin.toFinset, Nat.card (bkCond ρ A l (T ∪ ↑Q) L v) = ∏ v ∈ hfin.toFinset, Nat.card (L v) :=
    Finset.prod_congr rfl fun v hv => by rw [b1 v (by simpa using hv)]
  have e2 : ∏ v ∈ hT.toFinset ∪ Q, Nat.card (bkCond ρ A l (T ∪ ↑Q) L v) =
      (∏ v ∈ hT.toFinset ∪ Q, Nat.card (H0 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) *
        ∏ v ∈ hT.toFinset ∪ Q, Nat.card (H0 (ρ'.comp (Dec (F := F) (A.1 v)).subtype)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v hv => ?_
    have hv' : v ∈ T ∨ v ∈ Q := by simpa using hv
    rw [b2 v hv', Nat.card_congr Submodule.topEquiv.toEquiv]
    exact (hloc v).2 (hnl v hv')
  have e3 : ∏ v ∈ Q, Nat.card (H0 (ρ'.comp (Dec (F := F) (A.1 v)).subtype)) =
      ∏ v ∈ hT.toFinset ∪ Q, Nat.card (H0 (ρ'.comp (Dec (F := F) (A.1 v)).subtype)) :=
    Finset.prod_subset Finset.subset_union_right fun v hv hv' => by
      have : v ∈ T ∨ v ∈ Q := by simpa using hv
      rw [hT0 v (this.resolve_right hv')]
      exact Nat.card_unique
  have hpos : 0 < (∏ v ∈ hfin.toFinset ∪ (hT.toFinset ∪ Q), Nat.card (H0 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) *
      Nat.card W ^ InfinitePlace.nrComplexPlaces F :=
    mul_pos (Finset.prod_pos fun v _ => Nat.card_pos) (pow_pos Nat.card_pos _)
  rw [h0, h0', Nat.card_unique (α := (⊥ : Submodule Λ W)), Nat.card_unique (α := (⊥ : Submodule Λ W')), mul_one, mul_one,
    Finset.prod_union hd (f := fun v => Nat.card (bkCond ρ A l (T ∪ ↑Q) L v)), e1, e2, hcount, ← e3, mul_assoc] at e
  refine Nat.eq_of_mul_eq_mul_right hpos (e.trans ?_)
  rw [Finset.prod_union hd]
  ring

end General

theorem orderFormula : PoitouTateTotallyComplex → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → Gen.ArchimedeanSignatureMatching → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → NoInvDual i κ ρ → OrderFormula bkP i s κ ρ Q := by
  intro hPT hLF hLD hLE hGF hGE h4 D N X bkP i s A _ _ _ _ κ Q ρ hS hK hD hNI Y Y' _ _ _ _ _ _ _ _ _ _ β hβ
  classical
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  haveI := hS.2.1
  have hcx : InfinitePlace.nrComplexPlaces D.host.E = D.R.f := by
    have h1 := IsTotallyComplex.finrank D.host.E
    have h2 : Module.finrank ℚ D.host.E = 2 * D.R.f := by
      rw [D.host.finrank_cmField]
      unfold Ranks.f Ranks.n
      ring
    omega
  obtain ⟨hc, hc', hP, hU⟩ := GlobalTheory.T.pairing_equivariant_alt D N X bkP i s A κ Q ρ hS hK hD Y Y' β hβ.1
  have hcount := _root_.GlobalTheory.LocCountFinite.locCountFin D N X bkP i s A κ Q hS hK
    (GlobalTheory.LocalSaturation.main hLF hLD hLE h4 D N X bkP i s A κ Q hS)
    (GlobalTheory.LocalConditionCount.locCount hLF hLD hLE h4 D N X bkP i s A κ Q hS) Y
  have hko : IsOpen ((κ⁻¹).ker : Set (GE N)) := by
    convert hS.2.2.2.1 using 2
    ext g
    simp
  refine order_formula (X.l i) (nu X i + 1) hPT hLF hLD hLE hGF hGE (repOn (Tgl i s) κ Y) (repOn ρ κ⁻¹ Y') (vecPair D.R.r β)
    (show 0 < nu X i + 1 by omega) hc hc' (fun x hx => funext fun c => hβ.2.1 _ fun y' => ?_) (fun y hy => funext fun c => hβ.2.2 _ fun x => ?_) hP
    N.plOm (Spl i) (GlobalTheory.SelObstruction.finite_Spl i) Q (fun v hv => hv.2) hS.2.2.2.2.2.2.1 hU
    (bkOn bkP i (Tgl i s) κ Y) (DualCl bkP i s κ ρ β Q) (fun c => Iff.rfl)
    (GlobalTheory.NoGlobalInv.noInv D N X bkP i s A κ Q hS Y (tors_all A Y)) (eq_bot_iff.2 fun m hm => hNI Y' m hm)
    (fun v hv => (GlobalTheory.PrimeToInertia.local_cohomology_vanishes D N X bkP i s hS.1 v hv A κ⁻¹ hko (fun g => ?_) Y'
      (tors_all A Y') ρ (.inr hD)).1) ?_
  · have := hx (Pi.single c y')
    rw [vecPair_apply, Finset.sum_eq_single c (fun b _ hb => by simp [hb]) (by simp)] at this
    simpa using this
  · have := hy (Pi.single c x)
    rw [vecPair_apply, Finset.sum_eq_single c (fun b _ hb => by simp [hb]) (by simp)] at this
    simpa using this
  · obtain ⟨n, hn⟩ := hS.2.2.2.2.1 g
    exact ⟨n, by rw [MonoidHom.inv_apply, inv_pow, hn, inv_one]⟩
  · rw [hcount, hcx, Nat.card_pi, Finset.prod_const, Finset.card_fin, ← pow_mul, mul_comm D.R.r]

end GlobalTheory.SelOrder
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SignsAndJumpSetsAtTypePrime
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

noncomputable section

namespace GlobalTheory.HostJumpSets

open AdmissibleParameterJ

variable {D : D7}

theorem Jp_finite (j : ℕ) (ρ : D.what₂.Tau) : (Jp D j ρ).Finite := by
  refine (((Set.finite_range fun a : Fin (D.R.k - 1) => sz D j ρ + (D.hc ρ).v a + c0 D).union
    (Set.finite_range fun a : Fin D.R.m => sz D j ρ - (D.hc ρ).b a + c0 D)).union
    (Set.finite_range fun c : Fin D.R.t => ((c : ℕ) : ℚ))).subset ?_
  rintro q ((⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨c, hc, rfl⟩)
  · exact Or.inl (Or.inl ⟨a, rfl⟩)
  · exact Or.inl (Or.inr ⟨a, rfl⟩)
  · exact Or.inr ⟨⟨c, hc⟩, rfl⟩

theorem refl_injective : Function.Injective (AdmissibleParameterJ.refl D) := by
  intro x y h
  simp only [AdmissibleParameterJ.refl] at h
  linarith

theorem refl_surjective : Function.Surjective (AdmissibleParameterJ.refl D) := by
  intro y
  refine ⟨((D.R.t : ℚ) - 1) - y, ?_⟩
  simp only [AdmissibleParameterJ.refl]
  ring

theorem JJ_finite (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) : (JJ D up j ρ).Finite := by
  cases up
  · exact (Jp_finite j ρ).preimage refl_injective.injOn
  · exact Jp_finite j ρ

theorem JJ_ncard (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) : (JJ D up j ρ).ncard = (Jp D j ρ).ncard := by
  cases up
  · exact Set.ncard_preimage_of_injective_subset_range refl_injective
      (fun q _ => refl_surjective q)
  · rfl

theorem abs_le_two_b (L : SizeData₂ D) (hJe : JumpAbsoluteBound L) {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ D.R.m)
    (ρ : D.what₂.Tau) (up : Bool) (q : ℚ) (hq : q ∈ JJ D up j ρ) : |(q : ℝ)| ≤ 2 * L.sc.b :=
  ((hJe.1 j hj1 hj2 ρ up q hq).trans hJe.2.1).trans hJe.2.2.2

theorem elem_ok (L : SizeData₂ D) (hJb : CloudCentreDistance L) (hJc : jcCondition L) (hJe : JumpAbsoluteBound L)
    {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ D.R.m) (ρ : D.what₂.Tau)
    (up : Bool) (a : ℤ) (ha : (a : ℚ) ∈ JJ D up j ρ) :
    ((0 ≤ a ∧ a < D.R.t) ∨ |(a : ℚ) - PairedCharacterCondition.cen (D := D)| ≤ (⌊L.etaSz⌋₊ : ℚ) + 1 ∨
        PairedCharacterCondition.cloud (D := D) up (⌊3 * L.sc.b⌋₊ + 2 + 0) a) ∧ a ≠ -1 ∧ a ≠ D.R.t := by
  have hnot := (hJc j hj1 hj2 ρ).2.1 up
  refine ⟨?_, fun h => hnot.1 (by rw [h] at ha; exact_mod_cast ha),
    fun h => hnot.2 (by rw [h] at ha; exact_mod_cast ha)⟩
  have hfl : 3 * L.sc.b < (⌊3 * L.sc.b⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hfe : L.etaSz < (⌊L.etaSz⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _

  have hcl : ∀ q ∈ cloudJ D j ρ, (D.R.t : ℚ) + 1 < q ∧ q ≤ ((⌊3 * L.sc.b⌋₊ + 2 + 0 : ℕ) : ℚ) := by
    intro q hq
    refine ⟨(hJc j hj1 hj2 ρ).2.2.1 q hq, ?_⟩
    have h2 := abs_le_two_b L hJe hj1 hj2 ρ true q (Or.inl (Or.inl hq))
    have h3 : (q : ℝ) ≤ ((⌊3 * L.sc.b⌋₊ + 2 + 0 : ℕ) : ℝ) := by
      push_cast
      linarith [le_abs_self (q : ℝ)]
    exact_mod_cast h3
  have hlow : ∀ q ∈ lowJ D j ρ, |q - c0 D| ≤ (⌊L.etaSz⌋₊ : ℚ) + 1 := by
    intro q hq
    have h1 := (hJb j hj1 hj2 ρ).2.1 q hq
    have h2 : ((|q - c0 D| : ℚ) : ℝ) ≤ (((⌊L.etaSz⌋₊ : ℚ) + 1 : ℚ) : ℝ) := by
      push_cast at h1 ⊢
      linarith
    exact_mod_cast h2
  cases up
  ·
    change AdmissibleParameterJ.refl D (a : ℚ) ∈ Jp D j ρ at ha
    rcases ha with (hq | hq) | ⟨c, hc, hx⟩
    · right; right
      obtain ⟨h1, h2⟩ := hcl _ hq
      simp only [PairedCharacterCondition.cloud, PairedCharacterCondition.cen, AdmissibleParameterJ.refl] at h1 h2 ⊢
      simp only [Bool.false_eq_true, if_false]
      constructor <;> linarith
    · right; left
      have h := hlow _ hq
      simp only [PairedCharacterCondition.cen, AdmissibleParameterJ.refl, c0] at h ⊢
      rw [show (a : ℚ) - ((D.R.t : ℚ) - 1) / 2 = -((D.R.t : ℚ) - 1 - (a : ℚ) - ((D.R.t : ℚ) - 1) / 2) by ring,
        abs_neg]
      exact h
    · left
      simp only [AdmissibleParameterJ.refl] at hx
      have hx' : (a : ℚ) = ((D.R.t : ℤ) - 1 - (c : ℤ) : ℤ) := by push_cast; linarith
      have hx'' : a = (D.R.t : ℤ) - 1 - c := by exact_mod_cast hx'
      omega
  · change (a : ℚ) ∈ Jp D j ρ at ha
    rcases ha with (hq | hq) | ⟨c, hc, hx⟩
    · right; right
      obtain ⟨h1, h2⟩ := hcl _ hq
      simp only [PairedCharacterCondition.cloud, PairedCharacterCondition.cen, if_true]
      constructor <;> linarith
    · right; left
      exact hlow _ hq
    · left
      have hx'' : a = c := by exact_mod_cast hx
      omega

theorem algHom_eq_of_finrank_one {F K A : Type} [Field F] [Field K] [Ring A] [Algebra F K] [Algebra F A]
    (h : finrank F K = 1) (f g : K →ₐ[F] A) : f = g := by
  ext x
  have hx : x ∈ (⊥ : Subalgebra F K) := by
    rw [Subalgebra.bot_eq_top_of_finrank_eq_one h]; trivial
  obtain ⟨c, rfl⟩ := Algebra.mem_bot.1 hx
  simp

theorem emb_inj (D : D7) : Function.Injective D.host.emb := by
  intro g g' h
  have h1 : D.host.sigmaOf g = D.host.sigmaOf g' :=
    AlgEquiv.ext fun x => D.host.φ₀.injective (RingHom.congr_fun h x)
  exact (D.host.gal).symm.injective h1

theorem decide_flip {P Q : Prop} {iP : Decidable P} {iQ : Decidable Q} (h : P ↔ ¬ Q) :
    @decide P iP = !@decide Q iQ := by
  by_cases hq : Q
  · rw [decide_eq_true hq, decide_eq_false (fun hp => h.1 hp hq)]; rfl
  · rw [decide_eq_false hq, decide_eq_true (h.2 hq)]; rfl

theorem typeU_flip (D : D7) (ep : Bool) (g : D.R.GG) :
    TypeU D ep g ↔ ¬ TypeU D ep (g * D.R.cc) := by
  have hP := Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g
  unfold TypeU
  cases ep <;> by_cases h : g ∈ D.R.Psi <;> simp_all

def incl (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1 :=
  ((D.nbr i w hw).Kw.1.val).codRestrict (D.nbr i w hw).LL.1.toSubalgebra
    (fun x => (D.nbr i w hw).LL_split (D.nbr i w hw).Kw.1.val x)

end GlobalTheory.HostJumpSets

end

noncomputable section

namespace GlobalTheory.HostJumpSets

open AdmissibleParameterJ

theorem main : ∀ (D : D7) (L : SizeData₂ D) (ep : Bool), AdmissibleParameterJ.hodgeTateJumpsAtModulesForSign D ep → AdmissibleParameterJ.CloudCentreDistance L → AdmissibleParameterJ.jcCondition L → AdmissibleParameterJ.JumpAbsoluteBound L → (D.R.t : ℝ) ≤ L.sc.b → ∀ (i : D.nd.Loc) (k : Fin 2) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), D.nd.l i = D.host.g k → GoodR D.nd i r → ∃ (sg : HeightOneSpectrum (𝓞 D.host.E) → Bool) (U : HeightOneSpectrum (𝓞 D.host.E) → Finset ℤ), PairedCharacterCondition.SignOK i sg ∧ PairedCharacterCondition.HostJ i r ⌊L.etaSz⌋₊ (⌊3 * L.sc.b⌋₊ + 2) 0 sg U := by
  intro D L ep hJa hJb hJc hJe _htb i k r hk hgood
  obtain ⟨hdeg, hemb⟩ := GlobalTheory.TypePlace.type_prime_places D i k hk
  have hj := D.nd.j_range i
  have hex := fun w (hw : w ∈ placesOver D.host.E (D.nd.l i)) =>
    hJa i r hgood w hw (TruncatedSeriesCountingIdentities.CoefExt.self i w hw) (incl D i w hw)
  choose gf ρf hR hJ using hex
  classical
  let sg : HeightOneSpectrum (𝓞 D.host.E) → Bool := fun w =>
    if hw : w ∈ placesOver D.host.E (D.nd.l i) then decide (TypeU D ep (gf w hw)) else false
  let U : HeightOneSpectrum (𝓞 D.host.E) → Finset ℤ := fun w =>
    if hw : w ∈ placesOver D.host.E (D.nd.l i) then
      (Finset.Icc (-((⌊3 * L.sc.b⌋₊ + 2 : ℕ) : ℤ)) ((⌊3 * L.sc.b⌋₊ + 2 : ℕ) : ℤ)).filter
        (fun a : ℤ => (a : ℚ) ∈ JJ D (sg w) (D.nd.j i) (ρf w hw))
    else ∅
  have hsg : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), sg w = decide (TypeU D ep (gf w hw)) :=
    fun w hw => dif_pos hw
  refine ⟨sg, U, ?_, ?_⟩
  · intro w w' hw hc _hne
    have hw' : w' ∈ placesOver D.host.E (D.nd.l i) := by
      have := hc ((D.nd.l i : ℕ) : 𝓞 D.host.E) ((D.nd.l i : ℕ) : 𝓞 D.host.E) (by simp)
      exact this.1 hw
    have hind : ∀ v (hv : v ∈ placesOver D.host.E (D.nd.l i)),
        InducesW D.nd i (gEmb (TruncatedSeriesCountingIdentities.CoefExt.self i v hv) (incl D i v hv)) v := fun v hv =>
      (GlobalTheory.LocalEmbedding.inducesW_and_exists_emb D i v hv _ (incl D i v hv) _ (fun _ => rfl)).1
    have heq : gEmb (TruncatedSeriesCountingIdentities.CoefExt.self i w hw) (incl D i w hw) =
        (gEmb (TruncatedSeriesCountingIdentities.CoefExt.self i w' hw') (incl D i w' hw')).comp (D.host.conj : D.host.E →+* D.host.E) := by
      apply hemb
      intro x
      let X : 𝓞 D.host.E := ⟨(D.host.conj : D.host.E →+* D.host.E) (x : D.host.E),
        (RingOfIntegers.isIntegral_coe x).map (D.host.conj : D.host.E →+* D.host.E).toIntAlgHom⟩
      rw [hind w hw x, RingHom.comp_apply]
      have h2 := hind w' hw' X
      rw [show ((X : 𝓞 D.host.E) : D.host.E) = (D.host.conj : D.host.E →+* D.host.E) (x : D.host.E) from rfl] at h2
      rw [h2]
      exact hc x X rfl
    have hg : gf w hw = gf w' hw' * D.R.cc := by
      apply emb_inj D
      rw [Formalism.L2.Geo.emb_mul_cc_comp, ← (hR w hw).1, ← (hR w' hw').1, heq]
      rfl
    rw [hsg w hw, hsg w' hw', hg]
    exact decide_flip (typeU_flip D ep (gf w' hw'))
  · intro w hw
    have hU : U w = (Finset.Icc (-((⌊3 * L.sc.b⌋₊ + 2 : ℕ) : ℤ)) ((⌊3 * L.sc.b⌋₊ + 2 : ℕ) : ℤ)).filter
        (fun a : ℤ => (a : ℚ) ∈ JJ D (sg w) (D.nd.j i) (ρf w hw)) := dif_pos hw
    refine ⟨?_, ?_, ?_⟩
    · rw [hU, ← Set.ncard_coe_finset]
      have h1 : ((Finset.filter (fun a : ℤ => (a : ℚ) ∈ JJ D (sg w) (D.nd.j i) (ρf w hw))
          (Finset.Icc (-((⌊3 * L.sc.b⌋₊ + 2 : ℕ) : ℤ)) ((⌊3 * L.sc.b⌋₊ + 2 : ℕ) : ℤ)) : Finset ℤ) : Set ℤ).ncard ≤
          (JJ D (sg w) (D.nd.j i) (ρf w hw)).ncard :=
        Set.ncard_le_ncard_of_injOn (fun a : ℤ => (a : ℚ))
          (fun a ha => (Finset.mem_filter.1 (Finset.mem_coe.1 ha)).2)
          (fun a _ b _ h => Int.cast_injective h) (JJ_finite _ _ _)
      rw [JJ_ncard] at h1
      exact h1.trans_eq ((hJb _ hj.1 hj.2 (ρf w hw)).2.2.2.2.2)
    · intro x τ a ha
      obtain rfl : τ = incl D i w hw := algHom_eq_of_finrank_one (hdeg w hw).1 _ _
      have e : TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i w hw) (rTwO D.nd i r x) = Br.loc D.nbr i w hw (rTwO D.nd i r x) := by
        ext; rfl
      have h1 := ((hJ w hw).1 x a).1
      rw [e] at h1
      have hmem := h1.1 ha
      rw [← hsg w hw] at hmem
      rw [hU, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨?_, hmem⟩
      have hb := abs_le_two_b L hJe hj.1 hj.2 (ρf w hw) _ _ hmem
      have hfl : 3 * L.sc.b < (⌊3 * L.sc.b⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      have h0 : 0 ≤ L.sc.b := by linarith [abs_nonneg ((a : ℚ) : ℝ)]
      rw [abs_le] at hb
      push_cast at hb
      have h3 : (a : ℝ) ≤ ((⌊3 * L.sc.b⌋₊ + 2 : ℕ) : ℝ) := by push_cast; linarith
      have h4 : -((⌊3 * L.sc.b⌋₊ + 2 : ℕ) : ℝ) ≤ (a : ℝ) := by push_cast; linarith
      constructor
      · exact_mod_cast h4
      · exact_mod_cast h3
    · intro a ha
      rw [hU, Finset.mem_filter] at ha
      exact elem_ok L hJb hJc hJe hj.1 hj.2 (ρf w hw) (sg w) a ha.2

end GlobalTheory.HostJumpSets

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameSettingGroupActionCompat
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKReal.SESExact

theorem homW_exact_middle : ∀ {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {G : Type} [Group G] [TopologicalSpace G] {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] {P₀ : PhiMod O K l e a ι} {P₁ : PhiMod O K l e a κ} {P₂ : PhiMod O K l e a μ} {T₀ T₁ T₂ : LocLat G ℚ_[l] K O} {I₀ : Ident t ϖ P₀ T₀} {I₁ : Ident t ϖ P₁ T₁} {I₂ : Ident t ϖ P₂ T₂} {f : LatHom T₀.L T₁.L} {g : LatHom T₁.L T₂.L} {F : GlobalTheory.BK.Hom P₀ P₁} {H : GlobalTheory.BK.Hom P₁ P₂} (hS : IsSESLat (Qp := ℚ_[l]) f g) (hF : IsMapOf I₀ I₁ f F) (hH : IsMapOf I₁ I₂ g H), ∀ v : κ → OW l O, homW t ϖ H v = 0 → ∃ w, homW t ϖ F w = v := by
  intro l _ a _ e _ O K _ _ _ _ _ _ _ _ _ t ϖ G _ _ ι κ μ _ _ _ _ _ _ P₀ P₁ P₂ T₀ T₁ T₂ I₀ I₁ I₂ f g F H hS hF hH v hv
  obtain ⟨-, -, hOnto, hker, hsat⟩ := hS
  set f₁ := (f.f.restrictScalars O).restrict f.T_le with hf₁
  set g₁ := (g.f.restrictScalars O).restrict g.T_le with hg₁
  have hgs : Function.Surjective g₁ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, hxy⟩ := hOnto y hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hex : Function.Exact f₁ g₁ := by
    rintro ⟨y, hy⟩
    constructor
    · intro h0
      have h0' : g.f y = 0 := congrArg Subtype.val h0
      obtain ⟨z, hz⟩ := (hker y).1 h0'
      have hzT : z ∈ T₀.L.T := hsat z (hz ▸ hy)
      exact ⟨⟨z, hzT⟩, Subtype.ext hz⟩
    · rintro ⟨⟨z, hzT⟩, hz⟩
      apply Subtype.ext
      have hz' : f.f z = y := congrArg Subtype.val hz
      exact (hker y).2 ⟨z, hz'⟩
  have hT := lTensor_exact (OW l O) hex hgs
  have h1 : latW g (I₁.j v) = 0 := by
    rw [← hH v, hv, map_zero]
  obtain ⟨z, hz⟩ := (hT (I₁.j v)).1 h1
  refine ⟨I₀.j.symm z, I₁.j.injective ?_⟩
  rw [hF, LinearEquiv.apply_symm_apply]
  exact hz

end GlobalTheory.BKReal.SESExact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDualityDegreeOneContinuousCocyclesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateDuality_degreeOne_continuous_cocycles : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l), ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m → ∃ β : ↥(continuousCocycles A.ρ) →ₗ[LL] ↥(continuousCocycles A'.ρ) →ₗ[LL] LL, (∀ a b, β a b = 0 ↔ CobL (P.PD K) (cupL A'.ρ m a.1 b.1)) ∧ (∀ a, (∀ b, β a b = 0) ↔ a.1 ∈ B1 A.ρ) ∧ ∀ b, (∀ a, β a b = 0) ↔ b.1 ∈ B1 A'.ρ := by
  first | exact @GlobalTheory.tateDuality_degreeOne_cocycles | exact GlobalTheory.tateDuality_degreeOne_cocycles | (intros; apply GlobalTheory.tateDuality_degreeOne_cocycles <;> assumption)
end

