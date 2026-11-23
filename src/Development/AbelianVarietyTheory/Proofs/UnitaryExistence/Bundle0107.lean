module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0020
public import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
public import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0218
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0104

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsParPinsCanon
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

noncomputable section

namespace GlobalTheory.Member.ParExist

theorem datLaws_all (D : D7) : ∀ j, InR D j → ∃ hI : DatInt D j, DatLaws D j hI :=
  fun j hj => ⟨datInt_holds D j,
    { unimod := efW_unimod_holds D j _, rank := latW_rank D j hj, dom := datDom_holds D j hj _ }⟩

def parAtLevel (D : D7) (hF : OFull D) (hz : OZeta D) (hN : N1ab) (l : Level (hostOfRecord D))
    (hl : l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1) : Par D where
  H := hostOfRecord D
  l := l
  c :=
    { F := FO D
      fin := inferInstance
      conj := fun τ a => conj_mem_FO D τ a
      zeta_mem := by
        have h := (coeffFieldOfRecord D (hU := unramBridge D.host.E (cmUnram_conj D)) hz).zeta_mem
        have h1 : (levelG D (hU := unramBridge D.host.E (cmUnram_conj D))).M' = l.M' := by
          simp [Level.M', levelG, levelOfPs, hl.1, hl.2]
        rw [h1] at h
        exact h
      le := by
        have h := (coeffFieldOfRecord D (hU := unramBridge D.host.E (cmUnram_conj D)) hz).le
        have h1 : KA l = KA (levelG D (hU := unramBridge D.host.E (cmUnram_conj D))) := by
          unfold KA
          rw [hl.2]
          rfl
        rw [h1]
        exact h }
  Dw := datumAtLift D _ (datLaws_all D)
  Xo := fun j => Classical.choice (hN D.host.E _ (datumAtLift D _ (datLaws_all D) j) l (datumAtLift_pq_pos D _ (datLaws_all D) j))
  eO := eOf D hF

theorem exists_par_pins_canon (D : D7) (hF : OFull D) (hz : OZeta D)
    (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K))
    (hg : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (pb k).asIdeal) :
    ∃ Q : Par D, Q.Pins ∧ Q.Canon ∧ (∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) ∧
      Q.l.Mb = ∏ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) := by
  obtain ⟨l, hl, hb⟩ := levelPb_exists D pb hg
  refine ⟨parAtLevel D hF hz GlobalTheory.Moduli.moduli_scheme_exists l hl, ?_, ⟨rfl, fun j hj => ?_⟩, fun j => datumAtLift_pq_pos D _ (datLaws_all D) j, hb⟩
  · refine ⟨⟨rfl, rfl, rfl, tauEmb_sqrt D⟩, hl, eOf_spec D hF, fun j hj => ?_⟩
    show IsDatW D j (datumAtLift D _ (datLaws_all D) j)
    unfold datumAtLift
    rw [dite_eq_left hj]
    exact isDatW_datumOf D _ j _ _
  · show ∃ hP hd, HEq (datumAtLift D _ (datLaws_all D) j) (datumOfRecord D j hj hP hd)
    unfold datumAtLift
    rw [dite_eq_left hj]
    exact ⟨Formalism.IndefR.Fin.factPrincipalDatum, datDom_holds D j hj _, HEq.rfl⟩

end GlobalTheory.Member.ParExist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PeriodSpacesFixedByCmCurveTorsionFixingAutomorph
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat.AnyLevel

theorem conj_point_eq_of_isSplit {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty)
    (hD : 1 ≤ D.p + D.q) (hσ : σ (baseKA l).ρ = H.rt0) (hty : IsTypeFn H D.p D.q ty) (τ : ℂ ≃+* ℂ)
    (hτσ : (τ : ℂ →+* ℂ).comp σ = σ)
    (hfix : FixesCurve H τ l.M') (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) (hs : IsSplit hP) : spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i P := by
  obtain ⟨C, io, hC⟩ := hfix
  have hτ : τ H.rt0 = H.rt0 := by
    rw [← hσ]
    exact RingHom.congr_fun hτσ _
  obtain ⟨i', P', hP', hu⟩ := F.onto (spMap (τ : ℂ →+* ℂ) ≫ F.u i P)
    (by rw [Category.assoc, F.over_σ i P hP, GlobalTheory.ConjPermutes.spMap_comp, hτσ])
  obtain ⟨Φ, hE, hp, hm, hlevA, hlev⟩ := _root_.GlobalTheory.CompRat.marking_conj_lcm E H D l Xo σ g ty F hD hσ hty τ hτ C io hC.1 i P hP i' P' hP' hs
    hu.symm (1, 0) hC
  obtain ⟨L, hL⟩ := exists_complex_linear_of_pure_types E H _ _ g ty P P' hP hP' Φ hs (fun a ha => (hp a).2 ha)
    (fun a ha => (hm a).2 ha)
  have hw : wE H (1, 0) = 1 := by simp [wE]
  have hmem : ∀ v, F.t i v ∈ lat hP H.rt0 ⊔ lat hP (-H.rt0) := fun v => by
    rw [show lat hP H.rt0 ⊔ lat hP (-H.rt0) = ⊤ from hs]; trivial
  have hA' : ∀ v, ∃ x, Φ (F.t i v) = F.t i' v + l.A • x := fun v => by
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (hmem v)
    obtain ⟨e, he⟩ := hlevA v a ha b hb hab.symm
    rw [hw, map_one, one_smul, one_smul, hab] at he
    exact ⟨-e, by rw [he, smul_neg, add_neg_cancel_right]⟩
  refine hu.symm.trans ((GlobalTheory.UnifPoint.point_eq_iff_isometry_closed GlobalTheory.thetaUnifAV_all GlobalTheory.firstFiveLaws.1
      E H D l Xo σ g ty hD hσ hty (F.Di i) (F.Di i')
      (F.t i) (F.t i') P P' (F.u i P) (F.u i' P') (F.ex i P) (F.ex i' P')
      ⟨F.over_σ i P hP, hP, ⟨F.ex_add i P hP, F.ex_onto i P hP, isHolTo_ex_at_period F i P hP,
        (F.ex_diff i P hP).1, (F.ex_diff i P hP).2⟩, F.ex_ker i P hP, F.ex_lin i P hP, F.ex_weil i P hP,
        F.ex_eta i P hP, F.ex_etaA i P hP⟩
      ⟨F.over_σ i' P' hP', hP', ⟨F.ex_add i' P' hP', F.ex_onto i' P' hP', isHolTo_ex_at_period F i' P' hP',
        (F.ex_diff i' P' hP').1, (F.ex_diff i' P' hP').2⟩, F.ex_ker i' P' hP', F.ex_lin i' P' hP',
        F.ex_weil i' P' hP', F.ex_eta i' P' hP', F.ex_etaA i' P' hP'⟩).2 ⟨Φ, L, hE, fun v hv => ?_, hA', hL⟩).symm
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (hmem v)
  obtain ⟨e, he⟩ := hlev v hv a ha b hb hab.symm
  rw [hw, map_one, one_smul, one_smul, hab] at he
  exact ⟨-e, by rw [he, smul_neg, add_neg_cancel_right]⟩

theorem permutes_id_of_fixesCurve : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → (∀ x : KA l, σ x = (x : ℂ)) → (D.p = 0 ∨ D.q = 0 ∨ (3 ≤ D.p + D.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) → ∀ τ : ℂ ≃+* ℂ, (∀ x : KA l, τ (x : ℂ) = x) → FixesCurve H τ l.M' → ConjugationPermutesPeriods F τ id := by
  intro E _ _ _ H D l Xo σ g ty F hpq hσ hty hσx hsig τ hτ hC
  obtain ⟨π, hπ⟩ := _root_.GlobalTheory.ConjPermutesAnyLevel.exists_perm E H D l Xo σ g ty F hpq hσ hty hσx τ hτ
  have hτσ : (τ : ℂ →+* ℂ).comp σ = σ := RingHom.ext fun x => by
    show τ (σ x) = σ x
    rw [hσx, hτ]
  have hid : ∀ i, π i = i := by
    intro i
    obtain ⟨P, hP, hs⟩ := _root_.GlobalTheory.CompRat.exists_isSplit_period_anyLevel E H D l Xo σ g ty F hpq hσ hty hsig i
    have h1 := conj_point_eq_of_isSplit F hpq hσ hty τ hτσ hC i P hP hs
    obtain ⟨P', hP', h2⟩ := hπ i P hP
    exact (F.disj i (π i) P P' hP hP' (h1.symm.trans h2)).symm
  have : (π : Fin F.n → Fin F.n) = id := funext hid
  rwa [this] at hπ

end GlobalTheory.CompRat.AnyLevel
end

