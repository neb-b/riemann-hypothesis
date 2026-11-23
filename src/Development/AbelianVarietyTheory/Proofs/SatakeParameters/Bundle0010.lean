module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteOrderValuation.WeakApprox
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsWeakApproxUnitFinitePlace
section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

namespace GlobalTheory.HkFin

theorem exists_weak_approx_unit (E : Type) [Field E] [NumberField E] (S : Finset (HeightOneSpectrum (𝓞 E)))
    (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ) (n : ℕ) :
    ∃ y : E, y ≠ 0 ∧ Valued.v ((y : w.adicCompletion E) * ((x⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1)
      ≤ WithZero.exp (-(n : ℤ)) ∧ ∀ v ∈ S, v ≠ w → v.valuation E (y - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  classical
  obtain ⟨a, ha0, ha, -⟩ := PI.FinOrdValD.WA.weakApprox (insert w S)
    (Function.update (fun v => (1 : v.adicCompletion E)) w (x : w.adicCompletion E))
    (Function.update (fun _ => exp (-(n : ℤ))) w (Valued.v (x : w.adicCompletion E) * exp (-(n : ℤ))))
    (fun v _ => by
      by_cases h : v = w
      · subst h; simp only [Function.update_self]
        exact mul_ne_zero ((Valuation.ne_zero_iff _).mpr x.ne_zero) exp_ne_zero
      · simp only [Function.update_of_ne h]; exact exp_ne_zero)
  refine ⟨a, ha0, ?_, fun v hv hvw => ?_⟩
  · have h := ha w (Finset.mem_insert_self w S)
    simp only [Function.update_self] at h
    have hx0 : Valued.v (x : w.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).mpr x.ne_zero
    have e1 : (a : w.adicCompletion E) * (((x⁻¹ : (w.adicCompletion E)ˣ)) : w.adicCompletion E) - 1 =
        (algebraMap E (w.adicCompletion E) a - x) * (((x⁻¹ : (w.adicCompletion E)ˣ)) : w.adicCompletion E) := by
      rw [sub_mul, Units.mul_inv]; rfl
    rw [e1, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
    rw [mul_comm] at h
    exact (mul_inv_lt_of_lt_mul₀ h).le
  · have h := ha v (Finset.mem_insert_of_mem hv)
    simp only [Function.update_of_ne hvw] at h
    rw [← map_one (algebraMap E (v.adicCompletion E)), ← map_sub, PI.FinOrdValD.WA.val_alg] at h
    exact h.le

end GlobalTheory.HkFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FunctionalFixedByIdempotentRepresentedStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_representing_of_comp_idempotent_of_nondegenerate : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ), (∀ φ, (∀ ψ, B φ ψ = 0) → φ = 0) → (∀ ψ, (∀ φ, B φ ψ = 0) → ψ = 0) → ∀ (P P' : Module.End ℂ V), P ∘ₗ P = P → FiniteDimensional ℂ (LinearMap.range P) → (∀ φ ψ, B (P φ) ψ = B φ (P' ψ)) → ∀ f : V →ₗ[ℂ] ℂ, f ∘ₗ P = f → ∃ ψ, ∀ φ, B φ ψ = f φ := by
  first | exact @GlobalTheory.functional_fixed_by_idempotent_represented | exact GlobalTheory.functional_fixed_by_idempotent_represented | (intros; apply GlobalTheory.functional_fixed_by_idempotent_represented <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeneralLinearTransitiveOnLatticesOverDVR
section
open GlobalTheory.LatHecke

namespace GlobalTheory.LatHecke

theorem gl_transitive_lattices : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ), (∀ L : Lat O K r, ∃ g : GL (Fin r) K, glMap g (std O K r).1 = L.1) ∧ ∀ (g : GL (Fin r) K) (L : Lat O K r), (glMap g L.1).IsLattice K := by
  intro O K _ _ _ _ _ _ _ r
  refine ⟨fun L => ?_, fun g L => (glMap_isLattice g L).toIsLattice⟩
  haveI := L.2
  haveI : Module.Free O L.1 := Submodule.IsLattice.free K L.1
  haveI : Module.Finite O L.1 := Module.Finite.iff_fg.2 L.2.fg
  have hr : Module.finrank O L.1 = r := by
    simpa using ((Submodule.IsFullLattice.finrank_eq K L.1).trans (Module.finrank_fintype_fun_eq_card K))
  let b : Module.Basis (Fin r) O L.1 := Module.finBasisOfFinrankEq O L.1 hr
  let c : Module.Basis (Fin r) K (Fin r → K) := b.extendOfIsLattice K
  have hc : ∀ i, c i = (b i : Fin r → K) := fun i => Module.Basis.extendOfIsLattice_apply K b i
  let e : (Fin r → K) ≃ₗ[K] (Fin r → K) := (Pi.basisFun K (Fin r)).equiv c (Equiv.refl _)
  have he : ∀ i, e (Pi.basisFun K (Fin r) i) = c i := fun i => by
    simpa using (Pi.basisFun K (Fin r)).equiv_apply i c (Equiv.refl _)
  let g : GL (Fin r) K :=
    ⟨LinearMap.toMatrix' (e : (Fin r → K) →ₗ[K] (Fin r → K)),
      LinearMap.toMatrix' (e.symm : (Fin r → K) →ₗ[K] (Fin r → K)),
      by rw [← LinearMap.toMatrix'_comp]; simp,
      by rw [← LinearMap.toMatrix'_comp]; simp⟩
  have hg : Matrix.toLin' (g : Matrix (Fin r) (Fin r) K) = (e : (Fin r → K) →ₗ[K] (Fin r → K)) :=
    Matrix.toLin'_toMatrix' _
  refine ⟨g, ?_⟩
  have h1 : Set.range (Subtype.val ∘ b) = L.1.subtype '' Set.range b := by
    rw [← Set.range_comp]; rfl
  change (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map
    ((Matrix.toLin' (g : Matrix (Fin r) (Fin r) K)).restrictScalars O) = L.1
  rw [hg, Submodule.map_span, ← Set.range_comp]
  have h2 : ((e : (Fin r → K) →ₗ[K] (Fin r → K)).restrictScalars O) ∘ (Pi.basisFun K (Fin r))
      = Subtype.val ∘ b := by
    funext i
    simp only [Function.comp_apply, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
    rw [he, hc]
  rw [h2, h1, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]

end GlobalTheory.LatHecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImEmbeddingNeZeroOfNotMemRangeOfTotallyRealQuadrStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.im_embedding_ne_zero_of_not_mem_range_algebraMap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] [Algebra.IsQuadraticExtension F E] (w : InfinitePlace E) (θ : E), θ ∉ Set.range (algebraMap F E) → (w.embedding θ).im ≠ 0 := by
  first | exact @GlobalTheory.im_embedding_ne_zero_of_not_mem_range_of_totallyReal_quadratic | exact GlobalTheory.im_embedding_ne_zero_of_not_mem_range_of_totallyReal_quadratic | (intros; apply GlobalTheory.im_embedding_ne_zero_of_not_mem_range_of_totallyReal_quadratic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfinitePlaceEqOfEmbeddingCompAlgebraMapEqStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinitePlace_eq_of_embedding_comp_algebraMap_eq' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] [Algebra.IsQuadraticExtension F E] (w₁ w₂ : InfinitePlace E), w₁.embedding.comp (algebraMap F E) = w₂.embedding.comp (algebraMap F E) → w₁ = w₂ := by
  first | exact @GlobalTheory.infinitePlace_eq_of_embedding_comp_algebraMap_eq | exact GlobalTheory.infinitePlace_eq_of_embedding_comp_algebraMap_eq | (intros; apply GlobalTheory.infinitePlace_eq_of_embedding_comp_algebraMap_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIndEtaleTensorProductLeft
section
open CategoryTheory

namespace GlobalTheory

theorem isIndEtale_tensorProduct_left (C A M : Type) [CommRing C] [CommRing A] [CommRing M]
    [Algebra C A] [Algebra C M] (h : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap C A)) :
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap M (TensorProduct C M A)) := by
  haveI : (RingHom.toMorphismProperty @RingHom.Etale).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2
      RingHom.Etale.isStableUnderBaseChange
  exact MorphismProperty.of_isPushout (P := MorphismProperty.ind.{0}
    (RingHom.toMorphismProperty @RingHom.Etale))
    (CommRingCat.isPushout_tensorProduct C M A) h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsReducedQuotientOfArtinianOfMaximalLeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isReduced_quotient_of_artinian_of_maximal_le' : ∀ (A : Type) [CommRing A] (I : Ideal A), IsArtinianRing (A ⧸ I) →
    (∀ m : Ideal A, m.IsMaximal → I ≤ m → m ≤ I ⊔ m ^ 2) → IsReduced (A ⧸ I) := by
  first | (exact @GlobalTheory.isReduced_quotient_of_artinian_of_maximal_le) | (exact GlobalTheory.isReduced_quotient_of_artinian_of_maximal_le) | (intros; apply GlobalTheory.isReduced_quotient_of_artinian_of_maximal_le  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSemisimpleOfLocallyFiniteCompactGroup
section
namespace GlobalTheory.LocFinSemisimple

variable {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ K V}

theorem exists_isAtom_le : ∀ (n : ℕ) (Y : Subrepresentation ρ),
    FiniteDimensional ℂ Y.toSubmodule → Module.finrank ℂ Y.toSubmodule = n → Y ≠ ⊥ →
      ∃ T : Subrepresentation ρ, IsAtom T ∧ T ≤ Y := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Y hY hn hne
    by_cases hA : IsAtom Y
    · exact ⟨Y, hA, le_rfl⟩
    · have : ∃ Z, Z < Y ∧ Z ≠ ⊥ := by
        by_contra hc
        push_neg at hc
        exact hA ⟨hne, hc⟩
      obtain ⟨Z, hZY, hZ⟩ := this
      have hlt : Z.toSubmodule < Y.toSubmodule :=
        lt_of_le_of_ne hZY.le fun h => hZY.ne (Subrepresentation.toSubmodule_injective h)
      have hZf : FiniteDimensional ℂ Z.toSubmodule := Submodule.finiteDimensional_of_le hlt.le
      have hr := Submodule.finrank_lt_finrank_of_lt hlt
      obtain ⟨T, hT, hTZ⟩ := ih _ (hn ▸ hr) Z hZf rfl hZ
      exact ⟨T, hT, hTZ.trans hZY.le⟩

def ofInvariant (U : Submodule ℂ V) (hU : ∀ k, ∀ u ∈ U, ρ k u ∈ U) : Subrepresentation ρ :=
  ⟨U, fun k _ hu => hU k _ hu⟩

variable [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]

theorem isSemisimple_ofInvariant (U : Submodule ℂ V) (hU : ∀ k, ∀ u ∈ U, ρ k u ∈ U)
    (hfd : FiniteDimensional ℂ U)
    (hc : ∀ (ℓ : Module.Dual ℂ V), ∀ u ∈ U, Continuous fun k => ℓ (ρ k u)) :
    (ofInvariant U hU).toRepresentation.IsSemisimpleRepresentation := by
  haveI : FiniteDimensional ℂ (ofInvariant U hU).toSubmodule := hfd
  refine GlobalTheory.isSemisimpleRepresentation_of_continuous_coeff _ fun l v => ?_
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (p := U) l
  have h : ∀ k, l ((ofInvariant U hU).toRepresentation k v) = g (ρ k v) := fun k => by
    rw [← hg]; rfl
  simp only [h]
  exact hc g v v.2

theorem le_iSup_atoms
    (H : ∀ v : V, ∃ U : Submodule ℂ V, v ∈ U ∧ FiniteDimensional ℂ U ∧ (∀ k, ∀ u ∈ U, ρ k u ∈ U) ∧
      ∀ (ℓ : Module.Dual ℂ V), ∀ u ∈ U, Continuous fun k => ℓ (ρ k u))
    (X : Subrepresentation ρ) :
    X.toSubmodule ≤ ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule := by
  set N := ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule with hNdef
  have hNX : N ≤ X.toSubmodule := iSup₂_le fun S hS => hS.2
  have hNinv : ∀ k, ∀ x ∈ N, ρ k x ∈ N := by
    intro k
    have : N ≤ N.comap (ρ k) := iSup₂_le fun S hS x hx =>
      (le_iSup₂ (f := fun (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X) => S.toSubmodule) S hS)
        (S.apply_mem_toSubmodule k hx)
    exact fun x hx => this hx
  intro x hxX
  obtain ⟨U, hxU, hfd, hU, hc⟩ := H x
  let R := ofInvariant U hU
  haveI : ComplementedLattice (Subrepresentation R.toRepresentation) :=
    isSemisimple_ofInvariant U hU hfd hc
  let W : Subrepresentation R.toRepresentation :=
    ⟨N.comap U.subtype, fun k w hw => hNinv k _ hw⟩
  obtain ⟨W', hW'⟩ := exists_isCompl W
  have hdis : W.toSubmodule ⊓ W'.toSubmodule = ⊥ :=
    congrArg Subrepresentation.toSubmodule hW'.inf_eq_bot
  have hsup : W.toSubmodule ⊔ W'.toSubmodule = ⊤ :=
    congrArg Subrepresentation.toSubmodule hW'.sup_eq_top
  let Xc : Submodule ℂ U := X.toSubmodule.comap U.subtype
  let Y : Subrepresentation ρ := ⟨(W'.toSubmodule ⊓ Xc).map U.subtype, by
    rintro k _ ⟨u, ⟨hu1, hu2⟩, rfl⟩
    exact ⟨R.toRepresentation k u, ⟨W'.apply_mem_toSubmodule k hu1,
      X.apply_mem_toSubmodule k hu2⟩, rfl⟩⟩
  have hY : Y = ⊥ := by
    by_contra hne
    haveI : FiniteDimensional ℂ Y.toSubmodule := Submodule.finiteDimensional_of_le
      (S₂ := U) (fun y hy => by obtain ⟨u, _, rfl⟩ := Submodule.mem_map.1 hy; exact u.2)
    obtain ⟨T, hT, hTY⟩ := exists_isAtom_le _ Y this rfl hne
    have hTX : T ≤ X := by
      intro t ht
      obtain ⟨u, ⟨_, hu2⟩, rfl⟩ := hTY ht
      exact hu2
    have hTN : T.toSubmodule ≤ N :=
      le_iSup₂ (f := fun (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X) => S.toSubmodule) T ⟨hT, hTX⟩
    have hT0 : T.toSubmodule ≠ ⊥ := fun h => hT.1 (Subrepresentation.toSubmodule_injective h)
    obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hT0
    obtain ⟨u, ⟨hu1, _⟩, rfl⟩ := hTY ht
    have hu : u ∈ W.toSubmodule ⊓ W'.toSubmodule := ⟨hTN ht, hu1⟩
    rw [hdis] at hu
    have hu0 : ((u : R.toSubmodule) : V) = 0 :=
      congrArg Subtype.val ((Submodule.mem_bot ℂ (M := R.toSubmodule) (x := u)).1 hu)
    exact ht0 hu0
  have hx' : (⟨x, hxU⟩ : R.toSubmodule) ∈ W.toSubmodule ⊔ W'.toSubmodule := by rw [hsup]; trivial
  obtain ⟨w, hw, w', hw', hww⟩ := Submodule.mem_sup.1 hx'
  have hsum : (w : V) + (w' : V) = x := congrArg Subtype.val hww
  have hw'X : w' ∈ Xc := by
    have h1 : (w : V) ∈ X.toSubmodule := hNX hw
    have h2 : (w' : V) = x - w := by
      rw [← hsum]; abel
    show (w' : V) ∈ X.toSubmodule
    rw [h2]
    exact X.toSubmodule.sub_mem hxX h1
  have hw'0 : (w' : V) ∈ Y.toSubmodule := ⟨w', ⟨hw', hw'X⟩, rfl⟩
  rw [hY] at hw'0
  have : (w' : V) = 0 := (Submodule.mem_bot ℂ).1 hw'0
  have hxw : x = w := by
    rw [← hsum, ‹(w' : V) = 0›, add_zero]
  rw [hxw]
  exact hw

theorem semisimple_of_locallyFinite : ∀ (K V : Type) [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ K V), (∀ v : V, ∃ U : Submodule ℂ V, v ∈ U ∧ FiniteDimensional ℂ U ∧
      (∀ k, ∀ u ∈ U, ρ k u ∈ U) ∧ ∀ (ℓ : Module.Dual ℂ V), ∀ u ∈ U, Continuous fun k => ℓ (ρ k u)) →
    ρ.IsSemisimpleRepresentation ∧ (∀ S : Subrepresentation ρ, IsAtom S →
      FiniteDimensional ℂ S.toSubmodule) ∧ ∀ X : Subrepresentation ρ,
        X.toSubmodule = ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule := by
  intro K V _ _ _ _ _ _ ρ H
  have hle := le_iSup_atoms H
  refine ⟨?_, ?_, fun X => le_antisymm (hle X) (iSup₂_le fun S hS => hS.2)⟩
  · rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule,
      ← sSup_simples_eq_top_iff_isSemisimpleModule]
    let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
    set s := sSup {m : Submodule (MonoidAlgebra ℂ K) ρ.asModule |
      IsSimpleModule (MonoidAlgebra ℂ K) m} with hs
    have hZ : (e.symm s).toSubmodule = ⊤ := by
      refine eq_top_iff.2 ((hle ⊤).trans (iSup₂_le fun S hS => ?_))
      have : S ≤ e.symm s := e.le_symm_apply.2
        (le_sSup (isSimpleModule_iff_isAtom.2 ((e.isAtom_iff S).2 hS.1)))
      exact this
    have h1 : e.symm s = ⊤ := Subrepresentation.toSubmodule_injective hZ
    rw [← e.apply_symm_apply s, h1, e.map_top]
  · intro S hS
    have hS0 : S.toSubmodule ≠ ⊥ := fun h => hS.1 (Subrepresentation.toSubmodule_injective h)
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
    obtain ⟨U, hvU, hfd, hU, -⟩ := H v
    rcases hS.le_iff.1 (inf_le_left : S ⊓ ofInvariant U hU ≤ S) with h | h
    · have hm : v ∈ (S ⊓ ofInvariant U hU).toSubmodule := ⟨hv, hvU⟩
      rw [h] at hm
      exact absurd ((Submodule.mem_bot ℂ).1 hm) hv0
    · have hSU : S.toSubmodule ≤ U := by
        rw [← h]; exact fun x hx => hx.2
      exact Submodule.finiteDimensional_of_le hSU

end GlobalTheory.LocFinSemisimple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthLeOfForallFgSubmoduleLengthLeStatement
section
open Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_le_of_forall_fg_submodule_length_le : ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (b : ℕ∞), (∀ N : Submodule O M, N.FG → Module.length O N ≤ b) → Module.length O M ≤ b := by
  first | exact @GlobalTheory.length_le_of_forall_fg_length_le | exact GlobalTheory.length_le_of_forall_fg_length_le | (intros; apply GlobalTheory.length_le_of_forall_fg_length_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormTensorProductMapLeftStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_tensorProduct_map_id_right : ∀ {R B L : Type} [inst : Field R] [inst_1 : CommRing B] [inst_2 : Algebra R B] [inst_3 : Field L] [inst_4 : Algebra R L] [FiniteDimensional R L] (f : B →ₐ[R] B) (w : B ⊗[R] L), Algebra.norm B (Algebra.TensorProduct.map f (AlgHom.id R L) w) = f (Algebra.norm B w) := by
  first | exact @GlobalTheory.norm_tensorProduct_map_left | exact GlobalTheory.norm_tensorProduct_map_left | (intros; apply GlobalTheory.norm_tensorProduct_map_left <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotIsUnramifiedAtOfSqEqNegPrime
section
open NumberField IsDedekindDomain

namespace GlobalTheory.SqrtNegRam

theorem not_isUnramifiedAt_of_sq_eq_neg :
    ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (p : ℕ), p.Prime →
      ¬ (p : ℤ) ∣ discr E → ∀ δ : K, δ ^ 2 = -(p : K) → ∀ w : HeightOneSpectrum (𝓞 K),
        (p : 𝓞 K) ∈ w.asIdeal → ¬ Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal := by
  intro E K _ _ _ _ _ p hp hd δ hδ w hpw hunr
  have hmax := w.isMaximal
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hv : Algebra.IsUnramifiedAt ℤ (w.asIdeal.under (𝓞 E)) := by
    refine (not_dvd_discr_iff_forall_mem E (𝓞 E) hpz).1 hd _ inferInstance ?_
    rw [Ideal.under, Ideal.mem_comap]
    simpa using hpw
  have h1 : w.asIdeal.ramificationIdx (𝓞 E) = 1 := Ideal.ramificationIdx_eq_one_iff.2 hunr
  have h2 : (w.asIdeal.under (𝓞 E)).ramificationIdx ℤ = 1 := Ideal.ramificationIdx_eq_one_iff.2 hv
  have h3 : w.asIdeal.ramificationIdx ℤ = 1 := by
    rw [Ideal.ramificationIdx_tower (R := ℤ) (w.asIdeal.under (𝓞 E)) w.asIdeal, h1, h2]
  have hZ : Algebra.IsUnramifiedAt ℤ w.asIdeal := Ideal.ramificationIdx_eq_one_iff.1 h3
  have hint : IsIntegral ℤ δ := by
    refine IsIntegral.of_pow two_pos ?_
    rw [hδ]
    have : (-(p : K)) = algebraMap ℤ K (-(p : ℤ)) := by simp
    rw [this]
    exact isIntegral_algebraMap
  set y : 𝓞 K := ⟨δ, hint⟩ with hy
  have hy2 : y ^ 2 = (p : 𝓞 K) * (-1) := by
    apply RingOfIntegers.ext
    change algebraMap (𝓞 K) K (y ^ 2) = algebraMap (𝓞 K) K ((p : 𝓞 K) * (-1))
    rw [map_pow, map_mul, map_neg, map_one, map_natCast]
    change δ ^ 2 = _
    rw [hδ]; ring
  have hu : (-1 : 𝓞 K) ∉ w.asIdeal := by
    intro h
    exact hmax.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using w.asIdeal.neg_mem h))
  exact GlobalTheory.UnramSquare.not_sq_mul_unit K w.asIdeal hZ p hp hpw y (-1) hu hy2

end GlobalTheory.SqrtNegRam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadraticExistsIntegralGeneratorCommonDenominato
section
open NumberField

namespace GlobalTheory

open NumberField in
private theorem exists_integral_generator_common_denom_of_finrank_two
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h : Module.finrank F E = 2) :
    ∃ θ : 𝓞 E, (θ : E) ∉ Set.range (algebraMap F E) ∧
      ∃ D : 𝓞 F, D ≠ 0 ∧ ∀ y : 𝓞 E, ∃ u v : 𝓞 F,
        algebraMap (𝓞 F) (𝓞 E) D * y =
          algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ := by
  classical
  obtain ⟨x, hx⟩ : ∃ x : E, x ∉ Set.range (algebraMap F E) := by
    by_contra! hx
    have htop : (⊤ : IntermediateField F E) = ⊥ := by
      ext x
      simp only [IntermediateField.mem_top, true_iff]
      exact IntermediateField.mem_bot.mpr (hx x)
    have h1 := IntermediateField.finrank_eq_one_iff.mpr htop
    rw [IntermediateField.finrank_top'] at h1
    omega
  obtain ⟨n, hn, hnx⟩ := exists_integral_multiples ℤ ℚ ({x} : Finset E)
  have hint : IsIntegral ℤ (n • x) := hnx x (Finset.mem_singleton_self x)
  obtain ⟨θ, hθx⟩ : ∃ θ : 𝓞 E, (θ : E) = (n : E) * x :=
    ⟨⟨n • x, hint⟩, by rw [← zsmul_eq_mul]; rfl⟩
  have hθ : (θ : E) ∉ Set.range (algebraMap F E) := by
    rintro ⟨a, ha⟩
    apply hx
    refine ⟨a / n, ?_⟩
    have hnE : (n : E) ≠ 0 := by exact_mod_cast hn
    rw [map_div₀, map_intCast, ha, hθx]
    field_simp
  have hli : LinearIndependent F ![(1 : E), (θ : E)] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right one_ne_zero, rfl⟩
    · exfalso
      apply hθ
      refine ⟨-s / t, ?_⟩
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
      have htE : algebraMap F E t ≠ 0 := (map_ne_zero _).mpr ht
      rw [map_div₀, map_neg]
      field_simp
      linear_combination -hst
  obtain ⟨b, hb1⟩ : ∃ b : Module.Basis (Fin 2) F E, ⇑b = ![(1 : E), (θ : E)] :=
    ⟨basisOfLinearIndependentOfCardEqFinrank hli (by rw [h, Fintype.card_fin]),
      coe_basisOfLinearIndependentOfCardEqFinrank _ _⟩
  have hb : ∀ z : E, z = algebraMap F E (b.repr z 0) + algebraMap F E (b.repr z 1) * θ := by
    intro z
    conv_lhs => rw [← b.sum_repr z]
    rw [Fin.sum_univ_two, hb1]
    simp [Algebra.smul_def]
  set B := RingOfIntegers.basis E
  obtain ⟨d, hd, hdint⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin 2 =>
      b.repr (B p.1 : E) p.2)
  have hmem : ∀ i k, IsIntegral ℤ (d • b.repr (B i : E) k) := fun i k =>
    hdint _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, k)))
  refine ⟨θ, hθ, (d : 𝓞 F), by exact_mod_cast hd, ?_⟩
  let M : Submodule ℤ (𝓞 E) :=
    { carrier := {z | ∃ u v : 𝓞 F, z = algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ}
      add_mem' := by
        rintro _ _ ⟨u, v, rfl⟩ ⟨u', v', rfl⟩
        exact ⟨u + u', v + v', by simp only [map_add (f := _)]; ring⟩
      zero_mem' := ⟨0, 0, by simp⟩
      smul_mem' := by
        rintro c _ ⟨u, v, rfl⟩
        exact ⟨c • u, c • v, by simp only [zsmul_eq_mul, map_mul, map_intCast]; ring⟩ }
  have hall : ∀ y : 𝓞 E, algebraMap (𝓞 F) (𝓞 E) (d : 𝓞 F) * y ∈ M := by
    intro y
    have hspan : y ∈ Submodule.span ℤ (Set.range B) := by rw [B.span_eq]; trivial
    induction hspan using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      refine ⟨⟨_, hmem i 0⟩, ⟨_, hmem i 1⟩, ?_⟩
      rw [RingOfIntegers.ext_iff]
      have e := hb (B i : E)
      have key : algebraMap F E (d : F) * (B i : E) =
          algebraMap F E (d • b.repr (B i : E) 0) +
            algebraMap F E (d • b.repr (B i : E) 1) * θ := by
        simp only [zsmul_eq_mul, map_mul, map_intCast]
        linear_combination (d : E) * e
      exact key
    | zero => simpa using M.zero_mem
    | add z w _ _ hz hw => rw [mul_add]; exact M.add_mem hz hw
    | smul c z _ hz => rw [mul_smul_comm]; exact M.smul_mem c hz
  intro y
  obtain ⟨u, v, huv⟩ := hall y
  exact ⟨u, v, huv⟩


open NumberField in
theorem _root_.GlobalTheory.quadratic_exists_integral_generator_common_denominator :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      [Algebra.IsQuadraticExtension F E], ∃ θ : 𝓞 E, (θ : E) ∉ Set.range (algebraMap F E) ∧
      ∃ D : 𝓞 F, D ≠ 0 ∧ ∀ y : 𝓞 E, ∃ u v : 𝓞 F,
        algebraMap (𝓞 F) (𝓞 E) D * y =
          algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ := by
  intro F E _ _ _ _ _ _
  exact exists_integral_generator_common_denom_of_finrank_two F E
    (Algebra.IsQuadraticExtension.finrank_eq_two F E)

end GlobalTheory
end

