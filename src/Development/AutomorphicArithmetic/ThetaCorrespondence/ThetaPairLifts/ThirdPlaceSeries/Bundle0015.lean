module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.CommTriv
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0010
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0003
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0013
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AutomorphicGaloisAdmissible
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0541
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TrivialLocalCondition
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0676
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
public import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0526
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0600
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0008
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0012

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepType
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Polynomial
open GlobalTheory.TypeAbove
noncomputable section
namespace UpperTheory.GalS
open UpperTheory.Lit.Car (IneAb comm_le_ine)
theorem stepType_alt : _root_.GlobalTheory.Pass.stepType_proof_tyz := by
  intro D P hDZ h0 h1 h2' h5 i k hl r hr x PI hPI v τ hτ hsq hroot
  have h2 := _root_.UpperTheory.GalS.weak' h2'
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hnc := nc_of_label P hDZ h1 i k v PI τ hτ hsq hroot
  obtain ⟨u, hu, hm0, hlab, hconj⟩ := hDZ i k v PI τ hτ hsq hroot
  refine ⟨u, hu, ?_⟩
  have hcard : ∀ a : (ZMod (D.host.g k))[X], Multiset.card (Formalism.CyclotomicNorms.rootsBar a) = a.natDegree := fun a => by
    unfold Formalism.CyclotomicNorms.rootsBar
    rw [← (IsAlgClosed.splits _).natDegree_eq_card_roots, natDegree_map]
  have hroot0 : ∀ y ∈ Formalism.CyclotomicNorms.rootsBar ((P.lz k).lab τ * (X - C (u : ZMod (D.host.g k))) ^ D.R.t), y ≠ 0 := by
    rintro y hy rfl
    unfold Formalism.CyclotomicNorms.rootsBar at hy
    have h := isRoot_of_mem_roots hy
    rw [IsRoot.def, ← coeff_zero_eq_eval_zero, coeff_map, map_eq_zero, mul_coeff_zero, coeff_zero_eq_eval_zero (_ ^ _)] at h
    rcases mul_eq_zero.1 h with h | h
    · exact ((P.lz k).lab_spec τ).2.2 h
    · simp at h
  have key : ∀ w, w ∈ placesOver D.host.E (D.host.g k) → IsSplitPl D.host w → Nc D.nd D.naut (D.naut.locV i PI w) →
      D.naut.mono0 (D.naut.locV i PI w) →
      (D.naut.items₂ k w (D.naut.locV i PI w)).natDegree = D.R.nV →
      (∀ y ∈ Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w (D.naut.locV i PI w)), y ≠ 0) →
      D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) (r x)) w ∧
      D.naut.mono0 (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w) ∧
      ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
        D.naut.inePol (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w) σ =
          ((Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w (D.naut.locV i PI w))).map
            fun y => X - C (P.om k w y σ)).prod := by
    intro w hw hs hn hm hdeg hnz
    have hwl : w ∈ placesOver D.host.E (D.nd.l i) := hl ▸ hw
    obtain ⟨Pa, hB⟩ := h1 i PI
    obtain ⟨hdR, heq, -⟩ := compatR D h0 h2 h5 i r hr x PI Pa hPI hB w hwl (by rw [hB.2.2.2.1 w hs]; exact hn)
    rw [hB.2.2.2.1 w hs] at heq
    have hdim : D.naut.lpDim (D.naut.locV i PI w) = D.R.nV := by
      have h := D.naut.wdOf_dim i (mapRep (iotaOQ D.nd D.naut i) (r x)) w
      rwa [heq.dim, D.naut.lpDim_tw] at h
    refine ⟨hdR, ?_, fun σ hσ => ?_⟩
    · refine heq.mono ?_
      rw [D.naut.monomial_twist_iff]; exact hm
    · have hab : IneAb D.nd D.naut (D.naut.lpTw (D.naut.locV i PI w) ((1 - (D.R.nV : ℝ)) / 2)) := fun s hs' => by
        rw [D.naut.inePol_tw _ _ s (comm_le_ine w hs'), D.naut.lpDim_tw,
          P.inertiaCharpoly_eigenvalues k w hw _ (hdeg.trans hdim.symm) s (comm_le_ine w hs'),
          Multiset.map_congr rfl (fun y hy => by rw [comm_triv _ (P.om k w y) (P.om_one k w y (hnz y hy)) (P.om_mul k w y (hnz y hy)) s hs', C_1]),
          Multiset.map_const', Multiset.prod_replicate, hcard, hdeg, hdim]
      rw [heq.ine ⟨(D.naut.monomial_twist_iff _ _).2 hm, hab⟩ σ hσ, D.naut.inePol_tw _ _ σ hσ]
      exact P.inertiaCharpoly_eigenvalues k w hw _ (hdeg.trans hdim.symm) σ hσ
  intro w M hwM
  rcases hwM with ⟨rfl, rfl⟩ | ⟨hc, rfl⟩
  · have hdeg : (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locV i PI (D.naut.plGw k v))).natDegree = D.R.nV := by
      rw [hlab, ((P.lz k).lab_spec τ).1.natDegree_mul ((monic_X_sub_C _).pow _),
        ((P.lz k).lab_spec τ).2.1, (monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]
      rfl
    have h := key _ (D.naut.plGw_over k v) (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v) (hnc _ (Or.inl rfl)) hm0 hdeg (by rw [hlab]; exact hroot0)
    rw [hlab] at h
    exact h
  · obtain ⟨hw, hs⟩ := conj_over_split D (D.naut.plGw_over k v) (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v) hc
    obtain ⟨hm, hdeg, hroots⟩ := hconj w hc
    have h := key w hw hs (hnc w (Or.inr hc)) hm hdeg (by
      rw [hroots]
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hy
      exact inv_ne_zero (hroot0 z hz))
    rw [hroots] at h
    exact h
end UpperTheory.GalS
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameOfFrobeniusDense
section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_any_at_conj_of_frobenius_dense : ∀ D : D7, WildOne D → (∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k), D.nd.l i ≠ D.host.g k → ∀ s ∈ wildSet D.nd (D.nd.plOm.1 (D.naut.plGw k v)), D.nd.chi i 1 s = 1) → _root_.UpperTheory.GalS.GalAwayN D → FrobDense D → ∀ (i : D.nd.Loc) (π : D.naut.CG D.R.r) (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), D.naut.csd π → D.naut.ralg π → _root_.UpperTheory.GalS.FullLabS D [⟨D.R.r, π, 1⟩] → IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ → ∀ k : Fin 2, D.nd.l i ≠ D.host.g k → ∀ (v : D.nd.PlG k) (w : PlE D.host), IsConjPl D.host (D.naut.plGw k v) w → TameGen D.nd (D.nd.plOm.1 w) (D.nd.gam0 i w) → TameAnyAt D i [⟨D.R.r, π, 1⟩] ρ k w := by
  first | exact @_root_.GlobalTheory.TypeLeaf.ConjPlace.tame_any_at_of_is_conj_pl_tame_gen | exact _root_.GlobalTheory.TypeLeaf.ConjPlace.tame_any_at_of_is_conj_pl_tame_gen | (intros; apply _root_.GlobalTheory.TypeLeaf.ConjPlace.tame_any_at_of_is_conj_pl_tame_gen <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnrCrysAtRangePrime
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.HubX
theorem unrCrysAtRangePrime_alt : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (L : SizeData₂ D) (X : KillingConditions.HubData D), (∀ i, GoodR D.nd i (X.r i)) → SumRepresentations.tie0 D → _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → SumRepresentations.adm5 D → _root_.Formalism.MainNotions.AdmissibleParameterJ.DeRhamFamilyAwayAlt D → GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.BlockCharParam D → GlobalTheory.HubX.MuUnr D → ∀ i : D.nd.Loc, TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D → KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.SplitK D (D.nd.l i) → (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), (D.nbr i w hw).Kw.1 ≤ Loc.MaximalUnramifiedExtension (D.nd.l i)) ∧ ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw), C.IsGood → ∀ x : D.nd.X i, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i (X.r i) x))) := by
  intro hF D L X hgood ht0 ha2 ha5 hG2 hpar hmu i _ hg hR _
  obtain ⟨h23, hqd, -⟩ := hR
  have hchi := _root_.GlobalTheory.T.chiOne_of_not_mem_gset hF D ht0 ha2 ha5 hpar hmu i hg
  have hg0 : D.nd.l i ≠ D.host.g 0 := fun h => hg (by simp [TwistedPlaces.gset, h])
  have hg1 : D.nd.l i ≠ D.host.g 1 := fun h => hg (by simp [TwistedPlaces.gset, h])
  refine ⟨_root_.GlobalTheory.HubLoc.kw_le_Kur_all D i (fun h => h23 (Or.inl h)) (fun h => hqd (Or.inl h)) (fun h => hqd (Or.inr h)), ?_⟩
  intro w hw C _ x
  exact _root_.GlobalTheory.T.isCrys_locC_of_chiOneE hF D i (X.r i) (hgood i) (hG2 i (X.r i) (hgood i)) hg0 hg1 hchi w hw C x
end GlobalTheory.HubX
end
end

