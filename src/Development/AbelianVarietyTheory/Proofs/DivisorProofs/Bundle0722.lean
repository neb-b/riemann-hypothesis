module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0711
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0654
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0493
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0355
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0365
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0668
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootPowerSumCharpolyMemVirtualCharactersGLStatement
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.EqOfIsPrimitiveOfEqOnEllipticFiniteGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralOfModelAt
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem exists_integral_of_modelAt (F : IntermediateField ℚ ℂ) [NumberField F] (w : HeightOneSpectrum (𝓞 F))
    (V : ValuationSubring ℂ) (A : WeierstrassCurve F) (D : F)
    (hV : ∀ x : F, (x : ℂ) ∈ V ↔ x ∈ w.valuationSubringAtPrime F) (hD : D ≠ 0)
    (h : ModelAt V F (A.map (algebraMap F ℂ)) (D : ℂ)) :
    ∃ (C : VariableChange F) (u : (w.valuationSubringAtPrime F)ˣ),
      (C • A).IsIntegral (w.valuationSubringAtPrime F) ∧
        (C • A).Δ = ((u : w.valuationSubringAtPrime F) : F) * D := by
  obtain ⟨C, hu, hr, hs, ht, ⟨h1, h2, h3, h4, h6⟩, hΔ⟩ := h
  have hu0 : (⟨(C.u : ℂ), hu⟩ : F) ≠ 0 := by
    intro h0
    exact C.u.ne_zero (congrArg (fun x : F => (x : ℂ)) h0)
  let C' : VariableChange F := ⟨Units.mk0 _ hu0, ⟨C.r, hr⟩, ⟨C.s, hs⟩, ⟨C.t, ht⟩⟩
  have hC : C'.map (algebraMap F ℂ) = C := by
    ext <;> rfl
  have hmap : (C' • A).map (algebraMap F ℂ) = C • A.map (algebraMap F ℂ) := by
    rw [← hC, map_variableChange]
  rw [← hmap] at h1 h2 h3 h4 h6 hΔ
  set W := C' • A with hW
  have hD' : (D : ℂ) ≠ 0 := fun h0 => hD (Subtype.ext h0)
  have hvD : V.valuation (D : ℂ) ≠ 0 := by simpa using hD'
  rw [map_Δ] at hΔ
  have hΔ' : V.valuation ((W.Δ : F) : ℂ) = V.valuation (D : ℂ) := hΔ
  have hW0 : W.Δ ≠ 0 := by
    intro h0
    rw [h0] at hΔ'
    exact hvD (by simpa using hΔ'.symm)
  have hx : W.Δ / D ∈ w.valuationSubringAtPrime F := by
    rw [← hV, ← V.valuation_le_one_iff]
    push_cast
    rw [map_div₀, hΔ', div_self hvD]
  have hy : D / W.Δ ∈ w.valuationSubringAtPrime F := by
    rw [← hV, ← V.valuation_le_one_iff]
    push_cast
    rw [map_div₀, hΔ', div_self hvD]
  refine ⟨C', ⟨⟨_, hx⟩, ⟨_, hy⟩, ?_, ?_⟩, ?_, ?_⟩
  · apply Subtype.ext
    show W.Δ / D * (D / W.Δ) = 1
    field_simp
  · apply Subtype.ext
    show D / W.Δ * (W.Δ / D) = 1
    field_simp
  · refine ⟨⟨⟨⟨W.a₁, (hV _).1 h1⟩, ⟨W.a₂, (hV _).1 h2⟩, ⟨W.a₃, (hV _).1 h3⟩, ⟨W.a₄, (hV _).1 h4⟩,
      ⟨W.a₆, (hV _).1 h6⟩⟩, ?_⟩⟩
    ext <;> rfl
  · show W.Δ = W.Δ / D * D
    field_simp

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKernelEquivConjugatePoints
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.ConjPoint

lemma IsConj.mem_lattice_iff {L L' : PeriodPair} {σ : ℂ ≃+* ℂ} {t t' : ℂ}
    (h : IsConj L L' σ t t') : t ∈ L.lattice ↔ t' ∈ L'.lattice := by
  rcases h with h | h
  · exact iff_of_true h.1 h.2
  · exact iff_of_false h.1 h.2.1

theorem exists_equiv_kerReps_isConj :
    ∀ (L : PeriodPair) (σ : ℂ ≃+* ℂ) (α : ℂ) (S S' : Finset ℂ), L.g₂ = σ L.g₂ → L.g₃ = σ L.g₃ →
      MulStable L α → IsKerReps L α S → IsKerReps L (σ α) S' →
      ∃ e : S ≃ S', ∀ t : S, GlobalTheory.ConjPoint.IsConj L L σ (t : ℂ) (e t : ℂ) := by
  intro L σ α S S' h₂ h₃ hα hS hS'
  obtain ⟨s, -, hc⟩ := exists_conjEquiv h₂ h₃
  have hf : ∀ t : S, ∃ t' : S', IsConj L L σ (t : ℂ) (t' : ℂ) := by
    intro t
    obtain ⟨u, hu⟩ := latticePoint_surjective L (s (latticePoint L t))
    have h := (hc _ _).2 hu.symm
    obtain ⟨P, hP, hd⟩ := hS'.2.2 u ((IsConj.mul h₂ h₃ hα h).mem_lattice_iff.1 (hS.1 t t.2).1)
      (fun hm ↦ (hS.1 t t.2).2 (h.mem_lattice_iff.2 hm))
    exact ⟨⟨P, hP⟩, (hc _ _).2 (hu.symm.trans ((latticePoint_eq_iff L).2 hd))⟩
  choose f hf using hf
  refine ⟨Equiv.ofBijective f ⟨fun a b hab ↦ ?_, fun t' ↦ ?_⟩, hf⟩
  · have ha := (hc _ _).1 (hf a)
    have hb := (hc _ _).1 (hf b)
    rw [hab, ← hb] at ha
    exact Subtype.ext (hS.2.1 _ a.2 _ b.2 ((latticePoint_eq_iff L).1 (s.injective ha)))
  · obtain ⟨Q, hQ⟩ := s.surjective (latticePoint L t')
    obtain ⟨u, rfl⟩ := latticePoint_surjective L Q
    have h := (hc _ _).2 hQ
    obtain ⟨P, hP, hd⟩ := hS.2.2 u ((IsConj.mul h₂ h₃ hα h).mem_lattice_iff.2 (hS'.1 t' t'.2).1)
      (fun hm ↦ (hS'.1 t' t'.2).2 (h.mem_lattice_iff.1 hm))
    refine ⟨⟨P, hP⟩, Subtype.ext (hS'.2.1 _ (f _).2 _ t'.2 ((latticePoint_eq_iff L).1 ?_))⟩
    rw [← (hc _ _).1 (hf ⟨P, hP⟩), ← hQ, (latticePoint_eq_iff L).2 hd]

end GlobalTheory.ConjPoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKummerClassOnFinerEtaleNbhdCurve
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.KummerLoc

noncomputable abbrev gU (R : Type) [CommRing R] : Rˣ →* (Γ(Spec (CommRingCat.of R), ⊤))ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom

theorem pull_spMap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (φ : R →+* S) (ψ : S →+* T)
    {q : ℕ} {n i : ℤ} (x : Ht q (sp R) n i) :
    pull _ (spMap (ψ.comp φ)) _ _ x = pull _ (spMap ψ) _ _ (pull _ (spMap φ) _ _ x) := by
  rw [← pull_comp, ← Functor.map_comp, ← Spec.map_comp]; rfl

theorem pull_kum_gU (hnat : DivisorNaturality) (q : ℕ) [NeZero q] {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (hq : IsUnit (q : R)) (v : Rˣ) :
    pull _ (spMap φ) _ _ (kum q (gU R v)) = kum q (gU S (Units.map φ.toMonoidHom v)) := by
  have hq' : IsUnit (q : Γ(Spec (CommRingCat.of R), ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  rw [(hnat q).2.2.2 _ _ hq']
  congr 1
  ext
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
  have h2 := congrArg (fun g => g.hom (v : R)) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  simpa using h2.symm


set_option maxHeartbeats 1000000 in
theorem exists_kummer_on_finer_nbhd : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A' : Type) [CommRing A'] [Algebra B A'], IsExcisionNbhd B A' f → ∀ w : Ht q (sp (Localization.Away (algebraMap B A' f))) 1 1, ∃ (A₂ : Type) (_ : CommRing A₂) (_ : Algebra B A₂) (_ : Algebra A' A₂) (_ : IsScalarTower B A' A₂), IsExcisionNbhd B A₂ f ∧ ∃ c : (Γ(Spec (CommRingCat.of (Localization.Away (algebraMap B A₂ f))), ⊤))ˣ, ∀ φ : Localization.Away (algebraMap B A' f) →+* Localization.Away (algebraMap B A₂ f), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → pull _ (spMap φ) _ _ w = kum q c := by
  intro q _ k B _ _ _ _ _ _ hq f _ A' _ _ hA' w
  have hqB : IsUnit (q : B) := by simpa using hq.map (algebraMap k B)
  have hqA : IsUnit (q : A') := by simpa using hqB.map (algebraMap B A')
  haveI : Algebra.Etale B A' := hA'.1
  set SB : Submonoid B := (IsUnit.submonoid (B ⧸ Ideal.span {f})).comap
    (Ideal.Quotient.mk (Ideal.span {f})).toMonoidHom ⊔ Submonoid.powers f with hSB
  set M : Submonoid A' := Algebra.algebraMapSubmonoid A' SB with hM
  have hfM : (algebraMap B A' f) ∈ M := ⟨f, Submonoid.mem_sup_right (Submonoid.mem_powers f), rfl⟩
  let φf : Localization.Away (algebraMap B A' f) →+* Localization M :=
    IsLocalization.Away.lift (algebraMap B A' f) (IsLocalization.map_units (Localization M) (⟨(algebraMap B A' f), hfM⟩ : M))
  have hφf : φf.comp (algebraMap A' _) = algebraMap A' (Localization M) := IsLocalization.Away.lift_comp _ _
  haveI := GlobalTheory.T.subsingleton_pic_etale_localization_unitsModulo B f A'
  have hqL : IsUnit (q : Localization M) := by simpa using hqA.map (algebraMap A' (Localization M))
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_unit_kummer_eq_of_picard_torsionFree q (Localization M) hqL (fun c _ => Subsingleton.elim _ _) (pull _ (spMap φf) _ _ w)
  let u₀ : (Localization M)ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of (Localization M))).hom.hom.toMonoidHom u
  have hu₀ : gU _ u₀ = u := by ext; simp [u₀]
  obtain ⟨m₀, hm₀, v, hv⟩ := GlobalTheory.T.exists_away_unit_map_eq A' M u₀
  have hm₁ : (algebraMap B A' f) * m₀ ∈ M := M.mul_mem hfM hm₀
  have hunit1 : IsUnit (algebraMap A' (Localization.Away ((algebraMap B A' f) * m₀)) ((algebraMap B A' f) * m₀)) := IsLocalization.Away.algebraMap_isUnit _
  let α : Localization.Away (algebraMap B A' f) →+* Localization.Away ((algebraMap B A' f) * m₀) :=
    IsLocalization.Away.lift (algebraMap B A' f) (isUnit_of_mul_isUnit_left (by simpa using hunit1))
  let β : Localization.Away m₀ →+* Localization.Away ((algebraMap B A' f) * m₀) :=
    IsLocalization.Away.lift m₀ (isUnit_of_mul_isUnit_right (by simpa using hunit1))
  let φ₁ : Localization.Away ((algebraMap B A' f) * m₀) →+* Localization M :=
    IsLocalization.Away.lift ((algebraMap B A' f) * m₀) (IsLocalization.map_units (Localization M) (⟨_, hm₁⟩ : M))
  have hα : α.comp (algebraMap A' _) = algebraMap A' _ := IsLocalization.Away.lift_comp _ _
  have hβ : β.comp (algebraMap A' _) = algebraMap A' _ := IsLocalization.Away.lift_comp _ _
  have hφ₁ : φ₁.comp (algebraMap A' _) = algebraMap A' _ := IsLocalization.Away.lift_comp _ _
  have hqm₀ : IsUnit (q : Localization.Away m₀) := by simpa using hqA.map (algebraMap A' _)
  have hqm₁ : IsUnit (q : Localization.Away ((algebraMap B A' f) * m₀)) := by simpa using hqA.map (algebraMap A' _)
  have hnat := GlobalTheory.T.cup_chern_kummer_pullback_naturality
  set y := pull _ (spMap α) _ _ w - kum q (gU _ (Units.map β.toMonoidHom v)) with hy
  have hy0 : pull _ (spMap φ₁) _ _ y = 0 := by
    rw [hy, map_sub, ← pull_spMap_comp, pull_kum_gU hnat q _ hqm₁]
    have e1 : φ₁.comp α = φf := IsLocalization.ringHom_ext (Submonoid.powers (algebraMap B A' f)) (by rw [RingHom.comp_assoc, hα, hφ₁, hφf])
    have e2 : Units.map φ₁.toMonoidHom (Units.map β.toMonoidHom v) = u₀ := by
      rw [← hv (φ₁.comp β) (by rw [RingHom.comp_assoc, hβ, hφ₁])]; ext; rfl
    rw [e1, e2, hu₀, hu, sub_self]
  obtain ⟨m', hm', hψ⟩ := GlobalTheory.T.tateTwistCohomology_class_dies_on_localizationAway GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity q A' M 1 1 hqA ((algebraMap B A' f) * m₀) hm₁ y φ₁ hφ₁ hy0
  obtain ⟨b, hb, hbm⟩ := M.mul_mem hm₁ hm'
  obtain ⟨s, hs, t, ht, rfl⟩ := Submonoid.mem_sup.1 hb
  obtain ⟨n, rfl⟩ := ht
  have hs' : IsUnit (Ideal.Quotient.mk (Ideal.span {f}) s) := hs
  refine ⟨Localization.Away (algebraMap B A' s), inferInstance, inferInstance, inferInstance, inferInstance,
    GlobalTheory.T.isExcisionNbhd_away_of_isUnit_mod' B A' f s hA' hs', ?_⟩
  set A₂ := Localization.Away (algebraMap B A' s)
  set g : A' →+* Localization.Away (algebraMap B A₂ f) := (algebraMap A₂ _).comp (algebraMap A' A₂) with hg
  have hgu : IsUnit (g ((algebraMap B A' f) * m₀ * m')) := by
    rw [← hbm]
    simp only [map_mul, map_pow]
    refine IsUnit.mul ?_ (IsUnit.pow _ ?_)
    · exact (IsLocalization.Away.algebraMap_isUnit (algebraMap B A' s)).map (algebraMap A₂ _)
    · have : g (algebraMap B A' f) = algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (algebraMap B A₂ f) := by
        rw [hg, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply B A' A₂ f]
      rw [this]
      exact IsLocalization.Away.algebraMap_isUnit _
  let χ : Localization.Away ((algebraMap B A' f) * m₀ * m') →+* Localization.Away (algebraMap B A₂ f) :=
    IsLocalization.Away.lift ((algebraMap B A' f) * m₀ * m') hgu
  have hχ : χ.comp (algebraMap A' _) = g := IsLocalization.Away.lift_comp _ _
  have hunit2 : IsUnit (algebraMap A' (Localization.Away ((algebraMap B A' f) * m₀ * m')) ((algebraMap B A' f) * m₀ * m')) :=
    IsLocalization.Away.algebraMap_isUnit _
  let ψ : Localization.Away ((algebraMap B A' f) * m₀) →+* Localization.Away ((algebraMap B A' f) * m₀ * m') :=
    IsLocalization.Away.lift ((algebraMap B A' f) * m₀) (isUnit_of_mul_isUnit_left (by simpa using hunit2))
  have hψc : ψ.comp (algebraMap A' _) = algebraMap A' _ := IsLocalization.Away.lift_comp _ _
  have hqm₂ : IsUnit (q : Localization.Away ((algebraMap B A' f) * m₀ * m')) := by simpa using hqA.map (algebraMap A' _)
  clear_value χ ψ β α
  refine ⟨gU _ (Units.map (χ.comp (ψ.comp β)).toMonoidHom v), fun φ hφ => ?_⟩
  have e3 : φ = χ.comp (ψ.comp α) := IsLocalization.ringHom_ext (Submonoid.powers (algebraMap B A' f))
    (by rw [hφ, RingHom.comp_assoc, RingHom.comp_assoc, hα, hψc, hχ])
  have hw : pull _ (spMap α) _ _ w = y + kum q (gU _ (Units.map β.toMonoidHom v)) := by
    rw [hy, sub_add_cancel]
  subst e3
  rw [pull_spMap_comp, pull_spMap_comp, hw]
  have hψy := hψ ψ hψc
  rw [map_add (pull _ (spMap ψ) _ _)]
  rw [hψy, zero_add]
  rw [pull_kum_gU hnat q ψ hqm₁]
  have key : pull _ (spMap χ) _ _ (kum q (gU _ (Units.map ψ.toMonoidHom (Units.map β.toMonoidHom v)))) =
      kum q (gU _ (Units.map χ.toMonoidHom (Units.map ψ.toMonoidHom (Units.map β.toMonoidHom v)))) :=
    pull_kum_gU hnat q χ hqm₂ _
  refine key.trans ?_
  exact congrArg (kum q) (congrArg (gU _) (Units.ext rfl))

end GlobalTheory.EtC.KummerLoc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabel
section
noncomputable section

namespace GlobalTheory.CuspFormula

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI Formalism.CyclotomicNorms Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison GlobalTheory.GoodCharsCompare

theorem esymm_mem_virt (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (d k s : ℕ) :
    (fun x : GL (Fin d) F => (((Matrix.charpoly (x : Matrix (Fin d) (Fin d) F)).map
      (algebraMap F (AlgebraicClosure F))).roots.map fun α => θ α ^ k).esymm s) ∈ Virt ℂ ℂ (GL (Fin d) F) := by
  refine _root_.GlobalTheory.EsymmVirt.esymm_mem_virt _ _ _ (GlobalTheory.T.rootPowerSum_charpoly_mem_virtualCharacters_GL F θ hθ d k) (fun x j _ => ?_) s
  rw [rootSum, ← Matrix.charpoly_map, ← Matrix.charpoly_map, Units.val_pow_eq_pow_val, Matrix.map_pow,
    _root_.GlobalTheory.CharpolyPow.roots_charpoly_pow, Multiset.map_map, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun α _ => ?_
  simp only [Function.comp, map_pow, ← pow_mul, mul_comm]

theorem exists_regular (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (d : ℕ) (hd : 0 < d)
    (χ : GL (Fin d) F → ℂ) (hi : IsIrrChar ℂ ℂ χ) (hp : IsPrimitive (extZero χ)) :
    ∃ k : ℕ, (∀ i : ℕ, 0 < i → i < d → ¬ k * Nat.card F ^ i ≡ k [MOD Nat.card F ^ d - 1]) ∧
      ∀ x : GL (Fin d) F, χ x = (-1) ^ (d - 1) *
        psi (rootSum θ k) (Fin d → F) (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) := by
  classical
  have h := isCharacter_of_isIrreducibleCharacter_complex hi
  have hv : χ ∈ Virt ℂ ℂ (GL (Fin d) F) := AddSubgroup.subset_closure h
  obtain ⟨hval, -, hip, hcl⟩ := _root_.GlobalTheory.CuspGL.extZero_spec F d χ
  have hc := hcl (_root_.GlobalTheory.isChar_restrict_conj_one ℂ ℂ _ χ h).2.1
  have hr : Module.finrank F (Fin d → F) = d := by simp
  have hg := generalLinearGroupCardComplex_finiteField_ne_zero F d
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  obtain ⟨a, ha, -⟩ := GlobalTheory.T.exists_int_coeff_primitive_GL_character F θ hθ d χ hd h hp
  have haa := sum_coef_mul_eq_pair F θ hθ d hd χ χ h h hp hp a a ha ha
  rw [GlobalTheory.T.finiteGroupFunctionPairing_self_irreducible_algClosed ℂ _ χ hi, mul_one] at haa
  have hinv : ∀ k l i : ℕ, k * Nat.card F ^ i ≡ l [MOD Nat.card F ^ d - 1] → a k = a l := by
    intro k l i hkl
    have := GlobalTheory.T.innerProduct_rootPowerSum_eq_of_frobenius_modEq F (Fin d → F) θ _ hc hp (by rw [hr]; exact hd) k l i (by rw [hr]; exact hkl)
    rw [ha, ha] at this
    exact_mod_cast mul_right_cancel₀ hg this
  have hdvd : ∀ k s : ℕ, (d : ℤ) ∣ ∑ I ∈ (Finset.range d).powersetCard s, a (k * ∑ i ∈ I, Nat.card F ^ i) := by
    intro k s
    obtain ⟨m, hm⟩ := _root_.GlobalTheory.BI.finsum_mul_star_virt_int _ χ _ hv (esymm_mem_virt F θ hθ d k s)
    refine ⟨m, ?_⟩
    have : Fintype (GL (Fin d) F) := Fintype.ofFinite _
    have key : ((∑ I ∈ (Finset.range d).powersetCard s, a (k * ∑ i ∈ I, Nat.card F ^ i) : ℤ) : ℂ) * glCard F d =
        d * (m * glCard F d) := by
      push_cast
      rw [Finset.sum_mul]
      simp only [← ha, hip]
      rw [glCard, ← hm]
      simp only [finsum_eq_sum_of_fintype]
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.mul_sum, hval, ← star_sum, Matrix.charpoly_toLin']
      by_cases hx : ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧
          LinearMap.charpoly (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) = f ^ m
      · obtain ⟨f, m, hf, hirr, -, e⟩ := hx
        rw [Matrix.charpoly_toLin'] at e
        have hdeg : (f ^ m).natDegree = d := by rw [← e, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
        have := _root_.GlobalTheory.CuspGL.natDegree_mul_esymm_roots_pow F θ f m k s hf hirr
        rw [hdeg] at this
        rw [e, ← this, star_mul', star_natCast]
        ring
      · have := _root_.GlobalTheory.CuspGL.eq_zero_of_not_primary F _ _ hc hp (by rw [hr]; exact hd) _ hx
        rw [hval] at this
        simp [this]
    rw [← mul_assoc] at key
    exact_mod_cast mul_right_cancel₀ hg key
  obtain ⟨k, hk0, hk⟩ := _root_.GlobalTheory.exists_regular_exponent_of_sum_sq_eq _ d a hq hd hinv (by simp only [sq]; exact_mod_cast haa)
    (GlobalTheory.T.dvd_of_period_of_dvd_sum_powersetCard' _ d a hq hd hinv hdvd)
  refine ⟨k, hk, ?_⟩
  obtain ⟨h', hn⟩ := GlobalTheory.T.isCharacter_cuspidal_rootSum_regular F θ hθ d k hd hk
  have hv' := AddSubgroup.subset_closure (k := {χ | IsChar ℂ ℂ χ}) h'
  have hsq : ((-1 : ℂ) ^ (d - 1)) * (-1) ^ (d - 1) = 1 := by rw [← mul_pow]; simp
  have hi' := ((_root_.GlobalTheory.BI.irr_of_norm_one _ _ hv' (by
    rw [hip] at hn
    rw [← glCard, ← hn]
    refine finsum_congr fun x => ?_
    rw [star_mul', star_pow, star_neg, star_one, mul_mul_mul_comm, hsq, one_mul])).2 h').1
  by_contra hne
  have h0 := _root_.GlobalTheory.BI.pair_eq_zero_of_isIrrChar_ne _ _ _ hi hi' (fun e => hne (congrFun e))
  have h1 := GlobalTheory.T.invertibleEndomorphismInnerProduct_primitive_mobiusInverse F (Fin d → F) _ (_root_.GlobalTheory.CuspGL.rootSum_isAdditive_and_pow_X_sub_one F θ k).1 _ hp
  rw [ha, hip] at h1
  rw [pair, mul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact hg (inv_eq_zero.1 h0)
  · have h2 : ∑ᶠ x : GL (Fin d) F, χ x * ((-1) ^ (d - 1) * psi (rootSum θ k) (Fin d → F)
        (Matrix.toLin' ((x⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F))) = (-1) ^ (d - 1) * (a k * glCard F d) := by
      have : Fintype (GL (Fin d) F) := Fintype.ofFinite _
      rw [← h1]
      simp only [finsum_eq_sum_of_fintype]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← _root_.GlobalTheory.CuspGL.star_virt_eq_inv _ _ hv' x, hval, star_mul', star_pow, star_neg, star_one]
      ring
    rw [h2] at h0
    exact mul_ne_zero (pow_ne_zero _ (by simp)) (mul_ne_zero (by exact_mod_cast hk0) hg) h0

variable {g : ℕ} [Fact g.Prime]

theorem cuspVal_eq_psi (ω : Fbar g →*₀ ℂ) {ι : Type} [Fintype ι] [DecidableEq ι] (hd : 0 < Fintype.card ι)
    {x : Fbar g} (hx : x ^ (g ^ Fintype.card ι - 1) = 1) {k : ℕ} (hk : ω x = rootC (g ^ Fintype.card ι - 1) ^ k)
    (M : Matrix ι ι (ZMod g)) (hM : M.det ≠ 0) :
    cuspVal ω x M = (-1) ^ (Fintype.card ι - 1) *
      psi (rootSum (ω : Fbar g →* ℂ) k) (ι → ZMod g) (Matrix.toLin' M) := by
  classical
  haveI : NeZero g := ⟨(Fact.out : g.Prime).ne_zero⟩
  have hs := (_root_.GlobalTheory.CuspGL.rootSum_isAdditive_and_pow_X_sub_one (ZMod g) (ω : Fbar g →* ℂ) k).1
  unfold cuspVal
  split_ifs with hh
  · obtain ⟨p, m, hp, hm⟩ := hh
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_aeval_eq_zero (Fbar g) p (degree_pos_of_irreducible hp).ne'
    have hdeg := M.charpoly_natDegree_eq_dim
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with rfl | h
      · rw [hm] at hdeg
        simp at hdeg
        omega
      · exact h
    have hf : M.charpoly = minpoly (ZMod g) y ^ m := by
      have h1 := minpoly.eq_of_irreducible hp hy
      have h2 : p.leadingCoeff ^ m = 1 := by
        rw [← leadingCoeff_pow, ← hm]
        exact M.charpoly_monic
      rw [← h1, mul_pow, ← C_pow, inv_pow, h2, inv_one, C_1, mul_one, hm]
    have hirr := minpoly.irreducible (isInt y)
    have hR : (rootsBar M.charpoly).toFinset = (rootsBar (minpoly (ZMod g) y)).toFinset := by
      rw [hf, rootsBar_pow, Multiset.toFinset_nsmul _ _ hm0.ne']
    have hcard : (rootsBar M.charpoly).toFinset.card = dg y := by
      rw [hR, Multiset.toFinset_card_of_nodup (nodup_minpoly y), card_rootsBar]
    have he := fun z (hz : aeval z (minpoly (ZMod g) y) = 0) => _root_.GlobalTheory.finrank_ker_aeval_eq_natDegree_mul_finrank_eigenspace (ZMod g) ι M _ z hirr hz
    rw [_root_.GlobalTheory.CuspGL.psi_primary (ZMod g) _ _ hs _ _ m _ (minpoly.monic (isInt y)) hirr hm0
      (by rw [Matrix.charpoly_toLin', hf]) (he y (minpoly.aeval _ _)), Nat.card_zmod]
    congr 1
    have e1 : rootSum (ω : Fbar g →* ℂ) k (minpoly (ZMod g) y) =
        ∑ z ∈ (rootsBar M.charpoly).toFinset, ω z ^ k := by
      rw [hR, Finset.sum_eq_multiset_sum, Multiset.toFinset_val, (nodup_minpoly y).dedup]
      rfl
    rw [e1, Finset.sum_mul]
    convert Finset.sum_congr rfl (s₁ := (rootsBar M.charpoly).toFinset) fun z hz => ?_
    have hz1 := root_pow hM hp hm (Multiset.mem_toFinset.1 hz)
    have hz2 : aeval z (minpoly (ZMod g) y) = 0 := by
      rw [hR, Multiset.mem_toFinset] at hz
      exact (mem_rootsBar hirr.ne_zero).1 hz
    obtain ⟨a, ha⟩ := exists_log ω hd hz1
    have ht := Nat.eq_of_mul_eq_mul_left (dg_pos y) ((he z hz2).symm.trans (he y (minpoly.aeval _ _)))
    rw [labelChar_eq ω hd hx ha, hk, ha, ← pow_mul, ← pow_mul, mul_comm a k, ht]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hcard]
  · rw [_root_.GlobalTheory.CuspGL.eq_zero_of_not_primary (ZMod g) _ _ (fun e u => _root_.GlobalTheory.CuspGL.psi_conj _ _ _ _ e u) (_root_.GlobalTheory.CuspGL.isPrimitive_psi _ _ _ hs) (by simpa using hd),
      mul_zero]
    rintro ⟨f, m, -, hf, -, e⟩
    exact hh ⟨f, m, hf, by rw [← e, Matrix.charpoly_toLin']⟩

end GlobalTheory.CuspFormula
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPlacesIdempotentNearOneAdeles
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

noncomputable section
namespace GlobalTheory

open Filter

theorem placesIdem_mem_nhds_one (F : Type) [Field F] [NumberField F] (U : Set (AF F)) (hU : U ∈ 𝓝 (1 : AF F)) :
    ∃ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F),
      IsPlacesIdem S₁ S₂ ε ∧ ε ∈ U := by
  classical
  let x : Finset (HeightOneSpectrum (𝓞 F)) → Π v : HeightOneSpectrum (𝓞 F),
      ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun T v => if v ∈ T then ⟨1, (v.adicCompletionIntegers F).one_mem⟩ else ⟨0, (v.adicCompletionIntegers F).zero_mem⟩
  let one' : Π v : HeightOneSpectrum (𝓞 F), ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun v => ⟨1, (v.adicCompletionIntegers F).one_mem⟩
  let sm := RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite
  let e : Finset (HeightOneSpectrum (𝓞 F)) → AF F := fun T => ((1 : Ainf F), (sm (x T) : Af F))
  have hx : Tendsto x atTop (𝓝 one') := by
    rw [tendsto_pi_nhds]
    intro v
    apply tendsto_atTop_of_eventually_const (i₀ := {v})
    intro T hT
    simp [x, one', hT (Finset.mem_singleton_self v)]
  have h1 : (sm one' : Af F) = 1 := by
    ext v; rfl
  have he : Tendsto e atTop (𝓝 (1 : AF F)) := by
    have hc : Continuous sm := RestrictedProduct.isEmbedding_structureMap.continuous
    have h2 : Tendsto (fun T => (sm (x T) : Af F)) atTop (𝓝 (1 : Af F)) := by
      have h3 := (hc.tendsto one').comp hx
      rw [h1] at h3
      exact h3
    exact Tendsto.prodMk_nhds tendsto_const_nhds h2
  obtain ⟨T, hT⟩ := (he.eventually hU).exists
  refine ⟨Finset.univ, T, e T, ⟨?_, ?_, ?_, ?_⟩, hT⟩
  · intro w _; rfl
  · intro w hw; exact absurd (Finset.mem_univ w) hw
  · intro v hv
    show ((x T v : v.adicCompletion F)) = 1
    simp [x, hv]
  · intro v hv
    show ((x T v : v.adicCompletion F)) = 0
    simp [x, hv]

theorem placesIdem_tendsto_one : ∀ (F : Type) [Field F] [NumberField F], ∀ U : Set (AF F), U ∈ 𝓝 (1 : AF F) →
    ∃ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F),
      IsPlacesIdem S₁ S₂ ε ∧ ε ∈ U :=
  fun F _ _ U hU => placesIdem_mem_nhds_one F U hU

end GlobalTheory
end
end

