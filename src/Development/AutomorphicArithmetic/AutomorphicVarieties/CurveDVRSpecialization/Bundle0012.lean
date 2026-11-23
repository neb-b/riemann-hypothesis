module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.EveryPointSatisfiesFrameCondition
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0218
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.Inertia
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CoefEx
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.HV

private theorem ce_norm {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) (h : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  intro n
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
  exact PadicInt.norm_le_one _

private theorem ce_char {l : ℕ} [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] (ka : Γ →* (PadicAlgCl l)ˣ) (h : Continuous ka) :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧
      ∀ g, (ka g).val ∈ E ∧ ‖(ka g).val‖ ≤ 1 := by
  have hc : Continuous fun g => (ka g).val := Units.continuous_val.comp h
  let r : Γ →* GL (Fin 1) (PadicAlgCl l) :=
    (Units.map (Matrix.scalar (Fin 1) : PadicAlgCl l →+* _).toMonoidHom).comp ka
  have hr : ∀ (g : Γ) (i j : Fin 1), (r g).val i j = (ka g).val := by
    intro g i j
    obtain rfl : i = j := Subsingleton.elim _ _
    simp [r]
  obtain ⟨E, hE, hm⟩ := GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem l Γ 1 r
    (fun i j => by simp only [hr]; exact hc)
  refine ⟨E, hE, fun g => ⟨hr g 0 0 ▸ hm g 0 0, ?_⟩⟩
  obtain ⟨C, hC⟩ := (isCompact_range hc.norm).bddAbove
  by_contra hg
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt C (not_le.1 hg)
  have := hC ⟨g ^ N, rfl⟩
  simp only [map_pow, Units.val_pow_eq_pow_val, norm_pow] at this
  exact absurd hN (not_lt.2 this)

private theorem ce_fin {l : ℕ} [Fact l.Prime] (s : Set (PadicAlgCl l)) (hs : s.Finite) :
    FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] s) := by
  haveI := hs.to_subtype
  exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x

private theorem ce_coef {l : ℕ} [Fact l.Prime] (c : Coef l) :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧ ∀ x : c.O, x.1 ∈ E := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ_[l]) (M := c.O)
  refine ⟨IntermediateField.adjoin ℚ_[l] (Subtype.val '' (s : Set c.O)), ce_fin _ (s.finite_toSet.image _), fun x => ?_⟩
  have hx : x ∈ Submodule.span ℤ_[l] (s : Set c.O) := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact IntermediateField.subset_adjoin _ _ ⟨y, hy, rfl⟩
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul a b _ hb =>
    rw [SetLike.val_smul, ← algebraMap_smul ℚ_[l] a]
    exact IntermediateField.smul_mem _ hb

private theorem ce_large {l : ℕ} [Fact l.Prime] (L : Type) [Field L] [NumberField L] :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧
      ∀ (τ : L →+* PadicAlgCl l) (x : L), τ x ∈ E := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℚ) (M := L)
  refine ⟨IntermediateField.adjoin ℚ_[l] (⋃ τ : L →+* PadicAlgCl l, τ '' (s : Set L)),
    ce_fin _ (Set.finite_iUnion fun τ => s.finite_toSet.image _), fun τ x => ?_⟩
  have hx : x ∈ Submodule.span ℚ (s : Set L) := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact IntermediateField.subset_adjoin _ _ (Set.mem_iUnion.2 ⟨τ, y, hy, rfl⟩)
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul a b _ hb =>
    rw [Rat.smul_def, map_mul, map_ratCast]
    exact mul_mem (SubfieldClass.ratCast_mem _ a) hb

theorem UpperTheory.V.Pr.coefEx :
    UpperTheory.V.Pr.CoefEx := by
  intro l _ c L Ω _ _ _ _ _ ka ka' h h'
  haveI : CompactSpace (G L Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[L] Ω))
  haveI : T2Space (G L Ω) := inferInstanceAs (T2Space (Ω ≃ₐ[L] Ω))
  obtain ⟨E₁, f₁, m₁⟩ := ce_char (G L Ω) ka h
  obtain ⟨E₂, f₂, m₂⟩ := ce_char (G L Ω) ka' h'
  obtain ⟨E₃, f₃, m₃⟩ := ce_coef c
  obtain ⟨E₄, f₄, m₄⟩ := ce_large (l := l) L
  obtain ⟨c₁, hc⟩ := UpperTheory.V.X.So.coefOf l ((E₁ ⊔ E₂) ⊔ (E₃ ⊔ E₄))
  haveI : Algebra.IsIntegral ℤ_[l] c.O := Algebra.IsIntegral.of_finite ℤ_[l] c.O
  haveI : Algebra.IsIntegral ℤ_[l] c₁.O := Algebra.IsIntegral.of_finite ℤ_[l] c₁.O
  have l₁ : E₁ ≤ (E₁ ⊔ E₂) ⊔ (E₃ ⊔ E₄) := le_sup_of_le_left le_sup_left
  have l₂ : E₂ ≤ (E₁ ⊔ E₂) ⊔ (E₃ ⊔ E₄) := le_sup_of_le_left le_sup_right
  have l₃ : E₃ ≤ (E₁ ⊔ E₂) ⊔ (E₃ ⊔ E₄) := le_sup_of_le_right le_sup_left
  have l₄ : E₄ ≤ (E₁ ⊔ E₂) ⊔ (E₃ ⊔ E₄) := le_sup_of_le_right le_sup_right
  have hle : c.O ≤ c₁.O := fun x hx => (hc x).2 ⟨l₃ (m₃ ⟨x, hx⟩),
    ce_norm x ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val)⟩
  refine ⟨c₁, hle, fun τ x => (hc _).2 ⟨l₄ (m₄ τ x), ce_norm _ ?_⟩, fun g => (hc _).2 ⟨l₁ (m₁ g).1, (m₁ g).2⟩,
    fun g => (hc _).2 ⟨l₂ (m₂ g).1, (m₂ g).2⟩, ?_⟩
  · exact (x.isIntegral_coe.map τ.toIntAlgHom).tower_top
  · let φ : c.O →+* c₁.O := (Subalgebra.inclusion hle).toRingHom
    have hint : φ.IsIntegral := by
      refine RingHom.IsIntegral.tower_top (algebraMap ℤ_[l] c.O) φ ?_
      have e : φ.comp (algebraMap ℤ_[l] c.O) = algebraMap ℤ_[l] c₁.O := (Subalgebra.inclusion hle).comp_algebraMap
      rw [e]
      exact fun x => Algebra.IsIntegral.isIntegral x
    haveI : IsLocalHom φ := hint.isLocalHom (Subalgebra.inclusion_injective hle)
    refine ⟨ResidueField.map φ, fun a b hab => ?_⟩
    rw [ResidueField.map_residue]
    exact congrArg _ (Subtype.ext hab)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CoefIs
section
theorem UpperTheory.V.Pr.coefIs :
    UpperTheory.V.Pr.CoefIs := by
  intro l hl c
  obtain ⟨hc, hf, hlm, -, -, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  refine ⟨hc, hf, ?_⟩
  have h0 : (l : IsLocalRing.ResidueField c.O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue c.O), IsLocalRing.residue_eq_zero_iff]
    exact hlm
  exact (CharP.charP_iff_prime_eq_zero hl.out).2 h0
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CrDefs
section
noncomputable section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg

namespace UpperTheory.V.Pr

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
  {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
  {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField O)}

structure Ad (k : GalLink η Ψ σ g₁ B M L Φ) (s : W.HidaSetting l L Ω) where
  lM : l ∣ M
  unr : ∀ A : ValuationSubring Ω, ¬ A.valuation (M : Ω) < 1 → Ine (F := ℚ) A ≤ Ψ.ker
  c : galEmb ℚ (W.Lp L) Ω s.c = σ
  St : ∀ u, u ∈ s.St ↔ ((M : ℕ) : 𝓞 (W.Lp L)) ∈ u.asIdeal ∧ ((l : ℕ) : 𝓞 (W.Lp L)) ∉ u.asIdeal
  e : W.Vl l L ≃ Φ.V
  A_pl : ∀ v : W.Vl l L, s.A v = k.pl (e v)
  v0M : ¬ (s.A s.v0).valuation (M : Ω) < 1
  v0Ψ : ∀ g ∈ Dec (F := L) (s.A s.v0), Φ.Ψ (k.p0 g) = 1
  v0ω : ∃ g ∈ Dec (F := L) (s.A s.v0), PadicInt.toZMod ((cycZ L Ω l g : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1


variable (Ω L) in
def toUpl : G (W.Lp L) Ω →* upl Ω L :=
  (galEmb ℚ (W.Lp L) Ω).codRestrict _ fun g x hx => g.commutes ⟨x, hx⟩

theorem toUpl_surj : Function.Surjective (toUpl Ω L) := by
  rintro ⟨s, hs⟩
  refine ⟨AlgEquiv.ofRingEquiv (f := s.toRingEquiv) (fun x => hs x.1 x.2), ?_⟩
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  rfl

theorem toUpl_inj : Function.Injective (toUpl Ω L) := by
  intro g h hgh
  apply AlgEquiv.ext
  intro x
  have := congrArg (fun u : upl Ω L => (u : G ℚ Ω) x) hgh
  exact this

theorem galEmb_resP (g : G L Ω) : galEmb ℚ (W.Lp L) Ω (W.resP L Ω g) = galEmb ℚ L Ω g := rfl

theorem GalLink.galois_link_projection_coe (k : GalLink η Ψ σ g₁ B M L Φ) (g : G L Ω) : (k.p0 g).1 = k.p (toUpl Ω L (W.resP L Ω g)) := rfl

theorem GalLink.mem_range_resP (k : GalLink η Ψ σ g₁ B M L Φ) (g : G (W.Lp L) Ω) :
    g ∈ (W.resP L Ω).range ↔ η (galEmb ℚ (W.Lp L) Ω g) = 1 := by
  constructor
  · rintro ⟨h, rfl⟩
    rw [galEmb_resP]
    have hm : galEmb ℚ L Ω h ∈ galOf ℚ L Ω := fun x => h.commutes x
    rw [k.2] at hm
    exact hm.2
  · intro hη
    have hm : galEmb ℚ (W.Lp L) Ω g ∈ upl Ω L ⊓ η.ker := ⟨(toUpl Ω L g).2, hη⟩
    rw [← k.2] at hm
    refine ⟨AlgEquiv.ofRingEquiv (f := (galEmb ℚ (W.Lp L) Ω g).toRingEquiv) (fun x => hm x), ?_⟩
    apply AlgEquiv.ext
    intro x
    rfl

def GalLink.p0h (k : GalLink η Ψ σ g₁ B M L Φ) : G L Ω →* Φ.G0 where
  toFun := k.p0
  map_one' := Subtype.ext (by rw [k.galois_link_projection_coe, map_one, map_one, map_one]; rfl)
  map_mul' g h := Subtype.ext (by rw [Subgroup.coe_mul, k.galois_link_projection_coe, k.galois_link_projection_coe, k.galois_link_projection_coe, map_mul, map_mul, map_mul])

theorem GalLink.surjective_levelChangeBaseGroupHom (k : GalLink η Ψ σ g₁ B M L Φ) : Function.Surjective k.p0 := by
  rintro ⟨y, hy⟩
  obtain ⟨s, hs⟩ := k.p_surj y
  have hη : η s = 1 := by
    rw [← k.del s, hs]
    exact hy
  obtain ⟨g', hg'⟩ := toUpl_surj s
  have hη' : η (galEmb ℚ (W.Lp L) Ω g') = 1 := by
    rw [← hg'] at hη
    exact hη
  obtain ⟨g, rfl⟩ := (k.mem_range_resP g').2 hη'
  refine ⟨g, Subtype.ext ?_⟩
  rw [k.galois_link_projection_coe, hg', hs]

end

section

variable {k E Ω : Type} [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k Ω] [Algebra E Ω] [Algebra k E]
  [IsScalarTower k E Ω]

theorem galEmb_mem_Dec (A : ValuationSubring Ω) (g : G E Ω) : galEmb k E Ω g ∈ Dec (F := k) A ↔ g ∈ Dec (F := E) A := Iff.rfl

theorem galEmb_mem_Ine (A : ValuationSubring Ω) (g : G E Ω) : galEmb k E Ω g ∈ Ine (F := k) A ↔ g ∈ Ine (F := E) A := Iff.rfl

theorem natCast_place {A : ValuationSubring Ω} {v : W.Plc E} (h : IsPlaceOver A v) (m : ℕ) :
    A.valuation (m : Ω) < 1 ↔ ((m : ℕ) : 𝓞 E) ∈ v.asIdeal := by
  unfold IsPlaceOver at h
  rw [← h (m : 𝓞 E)]
  simp only [map_natCast]

end

theorem pr_surj {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev) : Function.Surjective V.pr := by
  rintro ⟨y, hy⟩
  have hs : Function.Surjective (toGS Ω V.S') := by
    unfold toGS
    exact QuotientGroup.mk'_surjective _
  obtain ⟨g', rfl⟩ := hs y
  obtain ⟨g, rfl⟩ := (V.6 g').1 hy
  exact ⟨g, rfl⟩

def CrE : Prop :=
  ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
    {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
    {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField O)}
    (k : GalLink η Ψ σ g₁ B M L Φ), B.valuation (l : Ω) < 1 →
    ∃ e : W.Vl l L ≃ Φ.V, ∀ v : W.Vl l L, IsPlaceOver (k.pl (e v)) v.1

def ExistsPrimeSplitInKernelWithNontrivialCyclotomic : Prop :=
  ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
    {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
    {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField O)}
    (k : GalLink η Ψ σ g₁ B M L Φ), IsOpen (Φ.Ψ.ker : Set Φ.Γ) →
    ∀ g : G L Ω, Φ.Ψ (k.p0 g) = 1 → PadicInt.toZMod ((cycZ L Ω l g : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1 → ∀ M' : ℕ, M' ≠ 0 →
    ∃ (v : W.Plc (W.Lp L)) (A : ValuationSubring Ω) (p : ℕ), p.Prime ∧ ¬ p ∣ M' ∧ normV v = p ∧
      ((p : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal ∧ IsPlaceOver A v ∧ Dec (F := W.Lp L) A ≤ (W.resP L Ω).range ∧
      (∀ t ∈ Dec (F := L) A, Φ.Ψ (k.p0 t) = 1) ∧
      ∃ t ∈ Dec (F := L) A, PadicInt.toZMod ((cycZ L Ω l t : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1

def CrLam : Prop :=
  ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
    {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
    {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField O)}
    (k : GalLink η Ψ σ g₁ B M L Φ) (v : Φ.V) (A : ValuationSubring Ω),
    A = k.pl v → A.valuation (M : Ω) < 1 →
    ∃ lam : Dec (F := L) A ≃ₜ* Φ.Gv v, ∀ g : Dec (F := L) A, (k.j v (lam g)).1 = galEmb ℚ L Ω g

def CrPi : Prop :=
  ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
    {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
    {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField O)}
    (k : GalLink η Ψ σ g₁ B M L Φ) (s : W.HidaSetting l L Ω) (_ : Ad k s) (V : s.Lev), V.S' = s.S →
    ∃ π : V.frame.G₀ →* Φ.G0, Continuous π ∧ (∀ g, π (V.pr g) = k.p0 g) ∧
      (∀ g, π (V.frame.conj g) = Φ.conj (π g)) ∧ ∀ g : V.frame.G₀, Φ.eps (π g) = V.frame.ε g

def CrKer : Prop :=
  ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
    {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
    {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField O)}
    (k : GalLink η Ψ σ g₁ B M L Φ) (s : W.HidaSetting l L Ω) (_ : Ad k s) (V : s.Lev), V.S' = s.S →
    ∀ π : V.frame.G₀ →* Φ.G0, (∀ g, π (V.pr g) = k.p0 g) →
    ∀ N : Subgroup V.frame.G₀, N.Normal → IsClosed (N : Set V.frame.G₀) → (∀ g ∈ N, V.frame.conj g ∈ N) →
      (∀ u, ∀ g ∈ V.frame.Iu u, Φ.Ψ (π g) = 1 → g ∈ N) → V.frame.I0 ≤ N → π.ker ≤ N

def CrKap : Prop :=
  ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
    {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
    {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField O)}
    (k : GalLink η Ψ σ g₁ B M L Φ) (s : W.HidaSetting l L Ω) (_ : Ad k s) (V : s.Lev), V.S' = s.S →
    ∀ (c₁ : Coef l) (ι : Qbar l ≃+* ℂ) (n : ℕ) (ka : G L Ω →* (Qbar l)ˣ), IsKa σ M ι n ka → (∀ g, (ka g).val ∈ c₁.O) →
    ∃ κ : V.frame.G₀ →* c₁.Oˣ, (∀ g, (κ (V.pr g)).val.1 = (ka g).val) ∧
      (AdicCont (maximalIdeal c₁.O) fun g => (κ g : c₁.O)) ∧
      ∀ g, κ g * κ (V.frame.conj g) = V.frame.eps c₁.O c₁.O g ^ (1 - (n : ℤ))

def CrResid : Prop :=
  ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (F : Fr.Frame l (ResidueField O))
    (G : W.GFrame l) (n : ℕ), n = 2 ∨ n = 3 → IsOpen (F.Ψ.ker : Set F.Γ) → F.Ψ F.g0 ^ 2 ≠ 1 →
    ∀ π : G.G₀ →* F.G0, Continuous π → Function.Surjective π → (∀ g, π (G.conj g) = F.conj (π g)) →
    ∀ κ : G.G₀ →* Oˣ, (AdicCont (maximalIdeal O) fun g => (κ g : O)) →
    (∀ g, κ g * κ (G.conj g) = G.eps O O g ^ (1 - (n : ℤ))) →
    ∃ r : W.Resid G O n, (∀ i g, r.chib i g = F.Ψ (π g) ^ Fr.w n i * W.pushCh (residue O) κ g) ∧
      ∀ v i g, r.psib v i g = r.chib i (G.φ v g)

end UpperTheory.V.Pr

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.DiagonalCharactersRegularAlgebraicOfInertiaWeigh
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr
open scoped Matrix

private theorem cyc_ine {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {v : W.Plc F} {A : ValuationSubring Ω} (hl : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal)
    (hA : IsPlaceOver A v) {n : ℤ} (hn : n ≠ 0) : ∃ g ∈ Ine (F := F) A, cycBar F Ω l g ^ n ≠ 1 := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsAlgClosure ℚ Ω := ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.trans ℚ F Ω⟩
  have hval : A.valuation (l : Ω) < 1 := by
    have h1 := (hA (l : 𝓞 F)).2 hl
    simpa only [map_natCast] using h1
  obtain ⟨u, hu⟩ := GlobalTheory.CycDec.exists_unit_infinite_order l
  obtain ⟨σ, hσI, hσu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hval u
  let f : ℕ → (F →ₐ[ℚ] Ω) := fun k =>
    ((σ ^ k : Ω ≃ₐ[ℚ] Ω) : Ω →ₐ[ℚ] Ω).comp (IsScalarTower.toAlgHom ℚ F Ω)
  obtain ⟨a, b, hab, hfab⟩ := Finite.exists_ne_map_eq_of_infinite f
  have key : ∀ a b : ℕ, a < b → f a = f b →
      ∃ k : ℕ, 0 < k ∧ ∀ x : F, (σ ^ k) (algebraMap F Ω x) = algebraMap F Ω x := by
    intro a b hlt he
    refine ⟨b - a, by omega, fun x => ?_⟩
    have hx : (σ ^ a) (algebraMap F Ω x) = (σ ^ b) (algebraMap F Ω x) :=
      congrArg (fun φ : F →ₐ[ℚ] Ω => φ x) he
    have hb : σ ^ b = σ ^ a * σ ^ (b - a) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hb, AlgEquiv.mul_apply] at hx
    exact ((σ ^ a).injective hx).symm
  obtain ⟨k, hk0, hk⟩ : ∃ k : ℕ, 0 < k ∧ ∀ x : F, (σ ^ k) (algebraMap F Ω x) = algebraMap F Ω x := by
    rcases Nat.lt_or_gt_of_ne hab with h | h
    · exact key a b h hfab
    · exact key b a h hfab.symm
  let g : G F Ω := { (σ ^ k : Ω ≃ₐ[ℚ] Ω) with commutes' := hk }
  have hgI : g ∈ Ine (F := F) A := pow_mem hσI k
  refine ⟨g, hgI, fun heq => ?_⟩
  have hr : MulSemiringAction.toRingAut (G F Ω) Ω g =
      MulSemiringAction.toRingAut (G ℚ Ω) Ω (σ ^ k) := RingEquiv.ext fun x => rfl
  have hz : cycZ F Ω l g = u ^ k := by
    show cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G F Ω) Ω g) = u ^ k
    rw [hr, ← hσu, ← map_pow]
    rfl
  have hinj : Function.Injective
      (Units.map (((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom : ℤ_[l] →+* Qbar l) : ℤ_[l] →* Qbar l)) :=
    Units.map_injective ((algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective)
  have h1 : (u ^ k) ^ n = 1 := by
    apply hinj
    rw [map_zpow, map_one]
    have : cycBar F Ω l g = Units.map (((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom : ℤ_[l] →+* Qbar l) : ℤ_[l] →* Qbar l) (cycZ F Ω l g) := rfl
    rw [← hz, ← this]
    exact heq
  rw [← zpow_natCast, ← zpow_mul] at h1
  exact hu _ (mul_ne_zero (by exact_mod_cast hk0.ne') hn) h1

private theorem w_anti (n : ℕ) : StrictAnti (Fr.w n) := by
  intro i j hij
  have : (i : ℕ) < j := hij
  unfold Fr.w
  split_ifs <;> omega

theorem UpperTheory.diagonal_characters_regular_algebraic_of_inertia_weights :
    GlobalTheory.Published.GlobalArtinReciprocity → ∀ {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : W.Plc L} (h : IsPlaceOver A w), ((l : ℕ) : 𝓞 L) ∈ w.asIdeal → ∀ (ka : G L Ω →* (Qbar l)ˣ), Sd.IsAlgChar ι ka → ∀ (n m : ℕ), 2 ≤ m → ∀ κ : Fin n → ↥(Dec (F := L) A) →* (Qbar l)ˣ, (∀ i (s : ↥(Dec (F := L) A)), (s : G L Ω) ∈ Ine (F := L) A → κ i s = cycBar L Ω l s ^ ((m : ℤ) * Fr.w n i)) → (∃ wt : Fin n → W.Emb l w → ℤ, (∀ τ, StrictMono fun j => wt j τ) ∧ ∀ j, W.IsLocAlg h (κ j * ka.comp (Dec (F := L) A).subtype) (wt j)) ∧ ∀ i j, κ i * ka.comp (Dec (F := L) A).subtype ≠ κ j * ka.comp (Dec (F := L) A).subtype * (cycBar L Ω l).comp (Dec (F := L) A).subtype := by
  intro hGAR L Ω _ _ _ _ _ l _ ι A w h hl ka hka n m hm κ hκ
  let cyc : ↥(Dec (F := L) A) →* (Qbar l)ˣ := (cycBar L Ω l).comp (Dec (F := L) A).subtype
  let kaD : ↥(Dec (F := L) A) →* (Qbar l)ˣ := ka.comp (Dec (F := L) A).subtype
  obtain ⟨_, art, χ, a, hart, _, hlad⟩ := hka
  let wk : W.Emb l w → ℤ := fun τ =>
    -a ((ι.toRingHom.comp ↑τ).comp (algebraMap L (IsDedekindDomain.HeightOneSpectrum.adicCompletion L w)))
  have hone : IsOpen (((1 : ↥(Ine (F := L) A) →* (Qbar l)ˣ).ker : Set ↥(Ine (F := L) A))) := by
    rw [MonoidHom.ker_one, Subgroup.coe_top]
    exact isOpen_univ
  have hkaW : W.IsLocAlg h kaD wk := by
    by_cases hex : ∃ a, GlobalTheory.LocLanglands.IsLocalArtin h a
    · exact Loc.laHecke h art hart ι χ a ka hlad hex
    · exact ⟨1, hone, fun a' ha' => absurd ⟨a', ha'⟩ hex⟩
  obtain ⟨phk, hphk⟩ := hkaW
  have hc := Loc.laCyc hGAR h hl
  obtain ⟨hmul, hpow, hzero⟩ := Loc.laMul (l := l) h
  have hm0 : (0 : ℤ) < m := by exact_mod_cast (show 0 < m by omega)
  have hwt : ∀ j, W.IsLocAlg h (κ j * kaD) (fun τ => -((m : ℤ) * Fr.w n j) + wk τ) := by
    intro j
    let x : ℤ := (m : ℤ) * Fr.w n j
    have h0 : W.IsWtPart h (κ j * cyc ^ (-x)) 0 1 := by
      refine hzero _ _ hone fun σ => ?_
      have hs := hκ j (Subgroup.inclusion (GlobalTheory.WeilDeligne.Weil_le_Dec h) (GlobalTheory.WeilDeligne.ineIncl h σ)) σ.2
      rw [MonoidHom.one_apply, mul_one, MonoidHom.mul_apply, MonoidHom.zpow_apply, hs]
      show cycBar L Ω l σ ^ x * cycBar L Ω l σ ^ (-x) = 1
      rw [← zpow_add, add_neg_cancel, zpow_zero]
    have h1 := (hmul _ _ _ _ _ _ h0 (hpow _ _ _ x hc)).1
    have h2 := (hmul _ _ _ _ _ _ h1 hphk).1
    have he : κ j * cyc ^ (-x) * cyc ^ x * kaD = κ j * kaD := by
      rw [mul_assoc (κ j), ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
    rw [he] at h2
    refine ⟨1 * 1 ^ x * phk, ?_⟩
    convert h2 using 2
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, x]
    ring
  refine ⟨⟨fun j τ => -((m : ℤ) * Fr.w n j) + wk τ, fun τ i j hij => ?_, hwt⟩, ?_⟩
  · have := w_anti n hij
    simp only
    nlinarith
  · intro i j heq
    have hcomm : κ j * kaD * cyc = κ j * cyc * kaD := by
      rw [mul_assoc, mul_comm kaD, ← mul_assoc]
    rw [hcomm] at heq
    have heq' : κ i = κ j * cyc := mul_right_cancel heq
    have hN : (m : ℤ) * Fr.w n i - (m : ℤ) * Fr.w n j - 1 ≠ 0 := by
      intro h0
      have h1 : (m : ℤ) * (Fr.w n i - Fr.w n j) = 1 := by linarith
      have := Int.eq_one_of_mul_eq_one_right hm0.le h1
      omega
    obtain ⟨g, hg, hne⟩ := cyc_ine hl h hN
    apply hne
    let s := Subgroup.inclusion (GlobalTheory.WeilDeligne.Weil_le_Dec h) (GlobalTheory.WeilDeligne.ineIncl h ⟨g, hg⟩)
    have hi := hκ i s hg
    have hj := hκ j s hg
    have hs := congrArg (fun f => f s) heq'
    simp only [MonoidHom.mul_apply] at hs
    rw [hi, hj] at hs
    have hs' : cycBar L Ω l g ^ ((m : ℤ) * Fr.w n i) = cycBar L Ω l g ^ ((m : ℤ) * Fr.w n j) * cycBar L Ω l g := hs
    rw [zpow_sub, zpow_sub, hs', zpow_one]
    group
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.DimOf
section
theorem UpperTheory.V.Pr.dimOf :
    UpperTheory.V.Pr.DimOf := by
  intro O Λ B _ _ _ _ _ _ _ φ J m ⟨e⟩ hfin htf Z hZ
  haveI : NoZeroDivisors O := IsDomain.to_noZeroDivisors O
  haveI : IsPrincipalIdealRing O := IsDiscreteValuationRing.toIsPrincipalIdealRing
  haveI : IsNoetherianRing O := PrincipalIdealRing.isNoetherianRing
  haveI : IsLocalRing O := IsDiscreteValuationRing.toIsLocalRing
  haveI : NoZeroDivisors (MvPowerSeries (Fin m) O) := inferInstance
  haveI : Nontrivial (MvPowerSeries (Fin m) O) := inferInstance
  haveI : IsDomain (MvPowerSeries (Fin m) O) := NoZeroDivisors.to_isDomain _
  haveI : IsDomain Λ := e.toMulEquiv.isDomain
  letI : Algebra Λ (B ⧸ J) := ((Ideal.Quotient.mk J).comp φ).toAlgebra
  haveI : Module.Finite Λ (B ⧸ J) := hfin
  haveI : Algebra.IsIntegral Λ (B ⧸ J) := Algebra.IsIntegral.of_finite Λ (B ⧸ J)
  have hJZ : J ≤ Z := hZ.1.2
  have hZ' := hZ
  rw [Ideal.minimalPrimes_eq_comap] at hZ'
  obtain ⟨P, hP, rfl⟩ := hZ'
  have hnz : ∀ a : Λ, a ≠ 0 → algebraMap Λ (B ⧸ J) a ∈ nonZeroDivisors (B ⧸ J) := by
    intro a ha
    rw [mem_nonZeroDivisors_iff_left]
    intro x hx
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.eq_zero_iff_mem]
    refine htf a ha b ?_
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
    exact hx
  have h := (UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.component Λ (B ⧸ J) hnz P hP).2.2
  have hq : ringKrullDim (B ⧸ P.comap (Ideal.Quotient.mk J)) = ringKrullDim ((B ⧸ J) ⧸ P) := by
    have hs : Function.Surjective ((Ideal.Quotient.mk P).comp (Ideal.Quotient.mk J)) :=
      Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
    have hk : P.comap (Ideal.Quotient.mk J)
        = RingHom.ker ((Ideal.Quotient.mk P).comp (Ideal.Quotient.mk J)) := by
      ext x
      rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_comap]
    rw [hk]
    exact ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hs)
  show ringKrullDim _ = _
  rw [hq, h, ringKrullDim_eq_of_ringEquiv e.toRingEquiv,
    GlobalTheory.FormalIsogeny.ringKrullDim_mvPowerSeries, IsDiscreteValuationRing.ringKrullDim_eq_one]
  rw [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
end

