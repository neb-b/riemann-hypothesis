module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2093
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3154
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2274
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3153

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePIsogenySourcesAtCharPPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.UPel.HT.ES.SourceFin

open GlobalTheory.UPel.HT.ESDual GlobalTheory.UPel.HT.ES.CorrQF

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

def scaleMap {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o : Obj b N s} {o' : Obj b N s'} {f : S' ⟶ S}
    (m : ObjMap o' o f) (e : ℕ) : ObjMap (scale o' e rfl) (scale o e rfl) f where
  φ := m.φ
  φ₂ := m.φ₂
  cart := m.cart
  sq := m.sq
  act := m.act
  pol := m.pol
  eta y := m.eta _

theorem exists_scale_mono (hN : 0 < N) (hp : N.Coprime p) (M : Model b N) (e : ℕ) :
    ∃ τ : M.X ⟶ M.X, Mono τ ∧ τ ≫ M.s = M.s ∧ Nonempty (ObjMap (scale M.univ e rfl) M.univ τ) := by
  obtain ⟨f, hf⟩ := exists_inv_exp hN hp e
  obtain ⟨τ, ⟨hτ, ⟨m⟩⟩, -⟩ := M.rep _ _ (scale M.univ e rfl)
  obtain ⟨τ', ⟨hτ', ⟨m'⟩⟩, -⟩ := M.rep _ _ (scale M.univ f rfl)
  have n : ObjMap (scale (scale M.univ e rfl) f rfl) M.univ (𝟙 M.X) :=
    { φ := (idMap M.univ).φ
      φ₂ := (idMap M.univ).φ₂
      cart := (idMap M.univ).cart
      sq := (idMap M.univ).sq
      act := (idMap M.univ).act
      pol := (idMap M.univ).pol
      eta := fun y => by
        have h : (scale (scale M.univ e rfl) f rfl).eta y = M.univ.eta y := by
          show M.univ.eta (p ^ e • p ^ f • y) = _
          rw [smul_smul, ← pow_add, eta_congr M.univ hf (pow_pos (Fact.out : p.Prime).pos _)]
        rw [h]
        exact (idMap M.univ).eta y }
  have h1 : τ ≫ τ' = 𝟙 M.X :=
    (M.rep _ _ (scale (scale M.univ e rfl) f rfl)).unique
      ⟨by rw [Category.assoc, hτ', hτ], ⟨compMap (scaleMap m f) m'⟩⟩ ⟨Category.id_comp _, ⟨n⟩⟩
  exact ⟨τ, mono_of_mono_fac h1, hτ, ⟨m⟩⟩

theorem exists_isPIsog_scale {S : Scheme.{0}} {s : S ⟶ Sp R} {e : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A}
    (hψ : IsPIsog (p ^ e) o o' ψ) : ∃ ψ' : o'.A ⟶ (scale o e rfl).A, IsPIsog (p ^ e) o' (scale o e rfl) ψ' := by
  obtain ⟨ψ', hm, h₁, h₂⟩ := hψ.2.2.2.2.2
  obtain ⟨a, l, P⟩ := dual_clauses hψ h₁ h₂
  exact ⟨ψ', ⟨e, rfl⟩, hm, a, l, P, ψ, hψ.2.1, h₂, h₁⟩

theorem not_mem_basicOpen {X : Scheme.{0}} (z : X) {k : Type} [Field k] [CharP k p]
    (h : X.residueField z →+* k) : z ∉ X.basicOpen ((p : ℕ) : Γ(X, ⊤)) := by
  rw [Scheme.mem_basicOpen_top, map_natCast]
  intro hu
  have := hu.map (h.comp (X.residue z).hom)
  rw [map_natCast, CharP.cast_eq_zero] at this
  exact not_isUnit_zero this

theorem exists_residueField_hom {X : Scheme.{0}} {k : Type} [Field k] (ζ : Sp k ⟶ X) {z : X}
    (hz : ζ (IsLocalRing.closedPoint k) = z) :
    ∃ h : X.residueField z →+* k, spMap h ≫ X.fromSpecResidueField z = ζ := by
  subst hz
  exact ⟨(X.descResidueField (Scheme.stalkClosedPointTo ζ)).hom,
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k X ζ⟩

theorem finite_isogSource : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (c : ℕ), D.m = 1 → ∀ (M : Model b N) (z : M.X), {u : M.X | ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : CharP k p) (ζ υ : Sp k ⟶ M.X) (ou oz : Obj b N (ζ ≫ M.s)) (_ : ObjMap ou M.univ υ) (_ : ObjMap oz M.univ ζ) (ψ : ou.A ⟶ oz.A), υ ≫ M.s = ζ ≫ M.s ∧ IsPIsog c ou oz ψ ∧ ζ (IsLocalRing.closedPoint k) = z ∧ υ (IsLocalRing.closedPoint k) = u}.Finite := by
  intro p _ D R _ _ _ _ b N hN hNp _ c hm M z
  set Z := {u : M.X | ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : CharP k p) (ζ υ : Sp k ⟶ M.X) (ou oz : Obj b N (ζ ≫ M.s)) (_ : ObjMap ou M.univ υ) (_ : ObjMap oz M.univ ζ) (ψ : ou.A ⟶ oz.A), υ ≫ M.s = ζ ≫ M.s ∧ IsPIsog c ou oz ψ ∧ ζ (IsLocalRing.closedPoint k) = z ∧ υ (IsLocalRing.closedPoint k) = u} with hZ
  rcases Z.eq_empty_or_nonempty with h0 | ⟨u₀, k₀, _, _, _, ζ₀, _, _, _, -, -, _, -, hψ₀, hz₀, -⟩
  · rw [h0]; exact Set.finite_empty
  obtain ⟨e, rfl⟩ := hψ₀.1
  obtain ⟨h₀, -⟩ := exists_residueField_hom ζ₀ hz₀
  have hz := not_mem_basicOpen (p := p) z h₀
  obtain ⟨τ, hmono, hτ, ⟨mτ⟩⟩ := exists_scale_mono (by omega) hNp M e
  have key : ∀ u : Z, ∃ (k : Type) (_ : Field k) (σ : M.X.residueField z →+* k) (υ : Sp k ⟶ M.X),
      (∀ q, υ q = u.1) ∧ IsogTarget M (p ^ e) (spMap σ ≫ M.X.fromSpecResidueField z) (υ ≫ τ) := by
    rintro ⟨u, k, _, _, _, ζ, υ, ou, oz, mu, mz, ψ, hs, hψ, hζ, hu⟩
    obtain ⟨σ, hσ⟩ := exists_residueField_hom ζ hζ
    obtain ⟨ψ', hψ'⟩ := exists_isPIsog_scale hψ
    refine ⟨k, inferInstance, σ, υ, fun q => ?_, ?_⟩
    · rw [Subsingleton.elim q (IsLocalRing.closedPoint k)]
      exact hu
    · rw [hσ]
      exact ⟨by rw [Category.assoc, hτ, hs], oz, scale ou e rfl, ψ', ⟨mz⟩, ⟨compMap (scaleMap mu e) mτ⟩, hψ'⟩
  choose k hk σ υ hυ hT using key
  obtain ⟨L, _, _, g, h, hg⟩ := GlobalTheory.T.exists_isAlgClosed_compatible_embeddings_of_family (M.X.residueField z) Z k σ
  have hfin := (GlobalTheory.T.finite_pIsogenyTargets_at_charP_point p D R b N hN hNp hm (p ^ e) M z hz L h).preimage
    (f := fun υ' : Sp L ⟶ M.X => υ' ≫ τ) (fun x _ y _ hxy => (cancel_mono τ).1 hxy)
  refine (Set.Finite.biUnion hfin fun υ' _ => Set.finite_range (fun q : Sp L => υ' q)).subset ?_
  intro u hu
  have h1 := isogTarget_spMap p D R b N M (p ^ e) (k ⟨u, hu⟩) L (g ⟨u, hu⟩) _ _ (hT ⟨u, hu⟩)
  have e1 : spMap (g ⟨u, hu⟩) ≫ spMap (σ ⟨u, hu⟩) ≫ M.X.fromSpecResidueField z =
      spMap h ≫ M.X.fromSpecResidueField z := by
    rw [← Category.assoc, ← hg ⟨u, hu⟩]
    simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  rw [e1, ← Category.assoc] at h1
  simp only [Set.mem_iUnion, Set.mem_range]
  refine ⟨spMap (g ⟨u, hu⟩) ≫ υ ⟨u, hu⟩, h1, Classical.arbitrary _, ?_⟩
  rw [Scheme.Hom.comp_apply, hυ ⟨u, hu⟩ _]

end GlobalTheory.UPel.HT.ES.SourceFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsClosureGenericCorrespondenceFst
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES
open GlobalTheory.UPel.HT.ES.CorrQF

theorem closure_points_finite_fst : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∀ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ → IsFinite gs → Etale gs → IsFinite gt → Etale gt → IsPIsog c o₀ o₀' ψ₀ → IsTj r w j o₀ o₀' ψ₀ → ∀ u : M.X, {z : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
  intro p _ D R _ _ _ _ b N hN hNp hpR r w j c hw huw hj hc hm M Y₀ s₀ t₀ gs gt o₀ o₀' ms₀ mt₀ ψ₀ hst hgs hgt hfs hes hft het hψ htj u
  by_cases hu : u ∈ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))
  · exact GlobalTheory.T.finite_section_over_ordinary_locus p D R b N M Y₀ s₀ t₀ gs hgs hfs u hu
  · set Z := {z : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z} with hZ
    have key := fun (z : Z) => GlobalTheory.T.exists_pIsogenyTarget_of_dvr_specialisation p D R b N hN hNp c M Y₀ s₀ t₀ o₀ o₀' ms₀ mt₀ ψ₀ hst hψ u z.1 z.2
    choose k hk _ σ ζ hζ hT using key
    obtain ⟨L, _, _, g, h, hg⟩ := GlobalTheory.T.exists_isAlgClosed_compatible_embeddings_of_family (M.X.residueField u) Z k σ
    refine (Set.Finite.biUnion (GlobalTheory.T.finite_pIsogenyTargets_at_charP_point p D R b N hN hNp hm c M u hu L h) fun ζ' _ => Set.finite_range (fun q : Sp L => ζ' q)).subset ?_
    intro z hz
    have h1 := GlobalTheory.T.isPIsogenyTargetOfPointPair_field_extension p D R b N M c (k ⟨z, hz⟩) L (g ⟨z, hz⟩) _ _ (hT ⟨z, hz⟩)
    have e : spMap (g ⟨z, hz⟩) ≫ spMap (σ ⟨z, hz⟩) ≫ M.X.fromSpecResidueField u = spMap h ≫ M.X.fromSpecResidueField u := by
      rw [← Category.assoc, ← hg ⟨z, hz⟩]
      simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    rw [← Category.assoc] at h1
    simp only [Set.mem_iUnion, Set.mem_range]
    refine ⟨spMap (g ⟨z, hz⟩) ≫ ζ ⟨z, hz⟩, ?_, Classical.arbitrary _, ?_⟩
    · simpa [e] using h1
    · rw [Scheme.Hom.comp_apply, hζ ⟨z, hz⟩ _]

end GlobalTheory.UPel.HT.ES
end

