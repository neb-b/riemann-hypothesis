module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimitiveDerivationPairing
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ValAtRestrict
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0017

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsVBOnDualAndBidual
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.LatDual

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem mem_span_basis_iff (p : Cpt ξ) {r : ℕ} (B : Module.Basis (Fin r) Ω E) (e : E) :
    e ∈ Submodule.span (regAt ξ p) (Set.range B) ↔ ∀ i, B.repr e i ∈ regAt ξ p := by
  constructor
  · intro he
    let N : Submodule (regAt ξ p) E :=
      { carrier := {x | ∀ i, B.repr x i ∈ regAt ξ p}
        add_mem' := fun ha hb i => by simpa using add_mem (ha i) (hb i)
        zero_mem' := fun i => by simp
        smul_mem' := fun c x hx i => by
          show B.repr ((c : Ω) • x) i ∈ regAt ξ p
          simpa using mul_mem c.2 (hx i) }
    have hle : Submodule.span (regAt ξ p) (Set.range B) ≤ N := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      show ∀ i, B.repr (B j) i ∈ regAt ξ p
      intro i
      rw [B.repr_self, Finsupp.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    exact hle he
  · intro h
    rw [← B.sum_repr e]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hc : B.repr e i • B i = (⟨B.repr e i, h i⟩ : regAt ξ p) • B i := rfl
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem mem_dual_iff (L : Lat ξ E) (p : Cpt ξ) {r : ℕ} (b : Fin r → E)
    (h : L p = Submodule.span (regAt ξ p) (Set.range b)) (w : Module.Dual Ω E) :
    w ∈ L.dual p ↔ ∀ i, w (b i) ∈ regAt ξ p := by
  show (∀ e ∈ L p, w e ∈ regAt ξ p) ↔ _
  rw [h]
  constructor
  · intro hw i
    exact hw _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro hw
    let N : Submodule (regAt ξ p) E :=
      { carrier := {x | w x ∈ regAt ξ p}
        add_mem' := fun {a c} ha hc => by
          show w (a + c) ∈ regAt ξ p
          rw [map_add (f := _)]
          exact add_mem ha hc
        zero_mem' := by
          show w 0 ∈ regAt ξ p
          simp
        smul_mem' := fun c x hx => by
          show w ((c : Ω) • x) ∈ regAt ξ p
          rw [map_smul, smul_eq_mul]
          exact mul_mem c.2 hx }
    have hle : Submodule.span (regAt ξ p) (Set.range b) ≤ N := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hw i
    intro e he
    exact hle he

theorem dual_eq_span (L : Lat ξ E) (p : Cpt ξ) {r : ℕ} (B : Module.Basis (Fin r) Ω E)
    (h : L p = Submodule.span (regAt ξ p) (Set.range B)) :
    L.dual p = Submodule.span (regAt ξ p) (Set.range B.dualBasis) := by
  ext w
  rw [mem_dual_iff L p B h w, mem_span_basis_iff p B.dualBasis w]
  simp only [Module.Basis.dualBasis_repr]

end GlobalTheory.CompanionTheory.Ar.LatDual

namespace GlobalTheory.CompanionTheory.Ar

open LatDual

theorem Lat.isVBOn_dual_and_bidual :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (T : Set (Cpt ξ)) (r : ℕ), L.IsVBOn T r ⊤ → L.dual.IsVBOn T r ⊤ ∧ ∀ p ∈ T, ∀ e : E, e ∈ L p ↔ ∀ w ∈ L.dual p, w e ∈ regAt ξ p := by
  intro X Ω _ ξ E _ _ L T r hL
  refine ⟨?_, ?_⟩
  · intro p hp
    obtain ⟨U, hpU, b, hspan, hfr⟩ := hL p hp
    obtain ⟨hli, -⟩ := hfr p hp hpU
    obtain ⟨B, hB⟩ : ∃ B : Module.Basis (Fin r) Ω E, ⇑B = b :=
      ⟨Module.Basis.mk hli hspan.ge, Module.Basis.coe_mk hli _⟩
    refine ⟨U, hpU, ⇑B.dualBasis, B.dualBasis.span_eq, ?_⟩
    intro q hq hqU
    obtain ⟨-, hLq⟩ := hfr q hq hqU
    refine And.intro B.dualBasis.linearIndependent ?_
    exact LatDual.dual_eq_span L q B (by rw [hB]; exact hLq)
  · intro p hp e
    obtain ⟨U, hpU, b, hspan, hfr⟩ := hL p hp
    obtain ⟨hli, hLp0⟩ := hfr p hp hpU
    obtain ⟨B, hB⟩ : ∃ B : Module.Basis (Fin r) Ω E, ⇑B = b :=
      ⟨Module.Basis.mk hli hspan.ge, Module.Basis.coe_mk hli _⟩
    have hLp : L p = Submodule.span (regAt ξ p) (Set.range B) := by rw [hB]; exact hLp0
    constructor
    · intro he w hw
      exact hw e he
    · intro h
      rw [hLp, LatDual.mem_span_basis_iff p B e]
      intro i
      have hmem : B.dualBasis i ∈ L.dual p := by
        rw [LatDual.dual_eq_span L p B hLp]
        exact Submodule.subset_span ⟨i, rfl⟩
      have hi := h _ hmem
      rwa [Module.Basis.dualBasis_apply] at hi

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsVBOneOfChartGenerators
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

variable {E : Type} [AddCommGroup E] [Module Ω E]

section Units

variable {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ}

theorem unitAt.zpow {u : Ω} (hu : unitAt ξ p u) (n : ℤ) : unitAt ξ p (u ^ n) := by
  obtain ⟨h0, h1, h2⟩ := hu
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · refine ⟨zpow_ne_zero _ h0, ?_, ?_⟩
    · rw [zpow_natCast]; exact pow_mem h1 n
    · rw [zpow_natCast, ← inv_pow]; exact pow_mem h2 n
  · refine ⟨zpow_ne_zero _ h0, ?_, ?_⟩
    · rw [zpow_neg, zpow_natCast, ← inv_pow]; exact pow_mem h2 n
    · rw [zpow_neg, zpow_natCast, inv_inv]; exact pow_mem h1 n

theorem unitAt.prod {K : Type} (s : Finset K) {u : K → Ω} (hu : ∀ k ∈ s, unitAt ξ p (u k)) :
    unitAt ξ p (∏ k ∈ s, u k) := by
  refine ⟨Finset.prod_ne_zero_iff.2 fun k hk => (hu k hk).1, prod_mem fun k hk => (hu k hk).2.1, ?_⟩
  rw [← Finset.prod_inv_distrib]
  exact prod_mem fun k hk => (hu k hk).2.2

theorem span_singleton_eq_of_unitAt {u : Ω} (hu : unitAt ξ p u) {e e' : E} (h : e' = u • e) :
    Submodule.span (regAt ξ p) {e'} = Submodule.span (regAt ξ p) {e} := by
  obtain ⟨h0, h1, h2⟩ := hu
  apply le_antisymm
  · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
    exact ⟨⟨u, h1⟩, h.symm⟩
  · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
    refine ⟨⟨u⁻¹, h2⟩, ?_⟩
    show u⁻¹ • e' = e
    rw [h, smul_smul, inv_mul_cancel₀ h0, one_smul]

end Units

namespace Lat

variable {ξ : Spec (CommRingCat.of Ω) ⟶ X}

end Lat

section Pull

variable {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X} {i : Ω →+* Ω'}

theorem Dominates.map_genPt (h : Dominates ξ' ξ f i) : f (genPt ξ') = genPt ξ := by
  let pt' : Spec (CommRingCat.of Ω') := IsLocalRing.closedPoint Ω'
  let pt : Spec (CommRingCat.of Ω) := IsLocalRing.closedPoint Ω
  have h1 : (ξ' ≫ f) pt' = (Spec.map (CommRingCat.ofHom i) ≫ ξ) pt' :=
    congrArg (fun g : Spec (CommRingCat.of Ω') ⟶ X => g pt') h
  have h2 : (Spec.map (CommRingCat.ofHom i)) pt' = pt :=
    (inferInstance : Subsingleton (PrimeSpectrum Ω)).elim _ _
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h2] at h1
  exact h1

theorem Dominates.specializes (h : Dominates ξ' ξ f i) (p' : Cpt ξ') : genPt ξ ⤳ f p'.1 := by
  rw [← h.map_genPt]
  exact p'.2.map f.continuous

theorem Lat.pull_apply {F : Type} [AddCommGroup F] [Module Ω' F] (L : Lat ξ E) (h : Dominates ξ' ξ f i)
    (j : E →+ F) (p' : Cpt ξ') :
    L.pull ξ' f j p' = Submodule.span (regAt ξ' p') (j '' (L ⟨f p'.1, h.specializes p'⟩ : Set E)) := by
  show Submodule.span _ _ = _
  congr 1
  ext e'
  constructor
  · rintro ⟨_, e, he, rfl⟩
    exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨h.specializes p', e, he, rfl⟩

end Pull

namespace Lat

variable {ξ : Spec (CommRingCat.of Ω) ⟶ X}

section Multi

variable {K : Type} [Fintype K] {ι : K → Type} {y : (Σ k, ι k) → Ω}

theorem block_ratio_mem {p : Cpt ξ} {c : (k : K) → ι k}
    (h : InChart ξ (fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩) c p) (k : K) (i : ι k) :
    y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ regAt ξ p := by
  classical
  have h2 := h.2 (Function.update c k i)
  have e1 : ∏ k', y ⟨k', c k'⟩ = y ⟨k, c k⟩ * ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩ :=
    (Finset.mul_prod_erase _ (fun k' => y ⟨k', c k'⟩) (Finset.mem_univ k)).symm
  have e2 : ∏ k', y ⟨k', Function.update c k i k'⟩ = y ⟨k, i⟩ * ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩ := by
    rw [← Finset.mul_prod_erase _ (fun k' => y ⟨k', Function.update c k i k'⟩) (Finset.mem_univ k)]
    simp only [Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun k' hk' => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk')]
  have hP : ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩ ≠ 0 := by
    intro h0
    exact h.1 (by show ∏ k', y ⟨k', c k'⟩ = 0; rw [e1, h0, mul_zero])
  simp only [e1, e2] at h2
  rwa [mul_div_mul_right _ _ hP] at h2

theorem block_coord_ne_zero {p : Cpt ξ} {c : (k : K) → ι k}
    (h : InChart ξ (fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩) c p) (k : K) : y ⟨k, c k⟩ ≠ 0 :=
  Finset.prod_ne_zero_iff.1 h.1 k (Finset.mem_univ k)

end Multi

section Single

variable {κ : Type} {x : κ → Ω}

end Single

end Lat

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatRestrictComapSpan
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem lat_restrict_comap_span {Ω R E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] [Semiring R] [SMul R Ω]
    [Module R E] [IsScalarTower R Ω E] (V : Submodule Ω E) {r : ℕ} (b : Fin r → V) :
    (Submodule.span R (Set.range fun i => (b i : E))).comap (V.subtype.restrictScalars R) =
      Submodule.span R (Set.range b) := by
  have h : (Set.range fun i => (b i : E)) = (V.subtype.restrictScalars R) '' Set.range b := by
    rw [← Set.range_comp]; rfl
  rw [h, ← Submodule.map_span, Submodule.comap_map_eq_of_injective]
  exact Subtype.val_injective

theorem Lat.restrict_isVBOn : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type)
    [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (T : Set (Cpt ξ)) (r : ℕ) (V : Submodule Ω E),
    L.IsVBOn T r V → (L.comap V.subtype).IsVBOn T r ⊤ ∧
      ∀ p ∈ T, ((L.comap V.subtype).map V.subtype) p = L p := by
  intro X Ω _ ξ E _ _ L T r V h
  refine ⟨?_, ?_⟩
  · intro p hp
    obtain ⟨U, hpU, b, hb, hq⟩ := h p hp
    have hbV : ∀ i, b i ∈ V := fun i => hb ▸ Submodule.subset_span ⟨i, rfl⟩
    let b' : Fin r → V := fun i => ⟨b i, hbV i⟩
    have hval : (fun i => (b' i : E)) = b := rfl
    refine ⟨U, hpU, b', ?_, ?_⟩
    · apply Submodule.map_injective_of_injective (f := V.subtype) Subtype.val_injective
      have h1 : (Set.range b) = V.subtype '' Set.range b' := by
        rw [← Set.range_comp]; rfl
      rw [Submodule.map_span, ← h1, hb, Submodule.map_top, Submodule.range_subtype]
    · intro q hqT hqU
      obtain ⟨hli, hsp⟩ := hq q hqT hqU
      refine ⟨?_, ?_⟩
      · exact LinearIndependent.of_comp V.subtype hli
      · show (L q).comap (V.subtype.restrictScalars (regAt ξ q)) = _
        rw [hsp, ← hval]
        exact lat_restrict_comap_span V b'
  · intro p hp
    obtain ⟨U, hpU, b, hb, hq⟩ := h p hp
    obtain ⟨_, hsp⟩ := hq p hp hpU
    have hle : ∀ e ∈ L p, e ∈ V := by
      intro e he
      rw [hsp] at he
      have : Submodule.span (regAt ξ p) (Set.range b) ≤ V.restrictScalars (regAt ξ p) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact hb ▸ Submodule.subset_span ⟨i, rfl⟩
      exact this he
    show ((L p).comap (V.subtype.restrictScalars (regAt ξ p))).map (V.subtype.restrictScalars (regAt ξ p)) = L p
    ext e
    simp only [Submodule.mem_map, Submodule.mem_comap]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · intro he
      exact ⟨⟨e, hle e he⟩, he, rfl⟩

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimitiveDerivationPairingStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_derivation_pairing : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type) [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A]
    (P : Submodule k A) (W : Submodule k (A →ₗ[k] k)),
    (∀ f ∈ P, Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) →
    (∀ v ∈ W, ∀ f g : A, v (f * g) = v f * Coalgebra.counit (R := k) g + Coalgebra.counit (R := k) f * v g) →
    (∀ v ∈ W, ∀ f ∈ P, v f = 0) →
    p ^ (Module.finrank k P + Module.finrank k W) ∣ Module.finrank k A := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HopfCount.primitive_tangent_dvd_finrank | exact GlobalTheory.CompanionTheory.Ar.HopfCount.primitive_tangent_dvd_finrank | (intros; apply GlobalTheory.CompanionTheory.Ar.HopfCount.primitive_tangent_dvd_finrank <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularFunctionIffSection
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem regularAt_forall_iff_exists_section : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (f : T → FractionRing R), (∀ g ∈ U, Γ.RegularAt f g) ↔ ∃ s : Γ(Γ.G.left, U), ∀ (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U), valAt (Γ.pt t).left U h s = f t :=
  PositivityTheory.HtPt.Unc.reg_iff

end GlobalTheory.CompanionTheory.Ar.BT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionEqZeroOfValues
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem section_eq_zero_of_val_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (s : Γ(Γ.G.left, U)), (∀ (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U), valAt (Γ.pt t).left U h s = 0) → s = 0 :=
  PositivityTheory.HtPt.Unc.sec_inj

end GlobalTheory.CompanionTheory.Ar.BT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncPts
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GeoModel

open AlgebraicGeometry CategoryTheory
open GlobalTheory.CompanionTheory.Ar.SncBase

def SncPts {X : Scheme.{0}} {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (e : ℕ)
    (B : Set (Cpt ξ)) : Prop :=
  ∀ p, Char0 ξ p → ∃ (A : Subalgebra ℚ Ω) (z : Fin e → A) (n : ℕ) (q : Ideal A),
    IsSncPatch (Pts ξ) (regAt ξ '' B) e A z n ∧ q.IsPrime ∧ IsLocAt A q (regAt ξ p)

end GlobalTheory.CompanionTheory.Ar.GeoModel
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.WedgeEqSpanOfIsFrameAt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem Lat.wedge_eq_span_of_isFrameAt :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E]
      [Module Ω E] (L : Lat ξ E) (r : ℕ) (b : Fin r → E) (p : Cpt ξ), L.IsFrameAt b p →
      L.wedge r p = Submodule.span (regAt ξ p) {exteriorPower.ιMulti Ω r b} := by
  intro X Ω _ ξ E _ _ L r b p h
  classical
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro w ⟨v, hv, rfl⟩
    have hc : ∀ i, ∃ c : Fin r → regAt ξ p, ∑ j, c j • b j = v i := fun i => by
      have := hv i
      rw [h.2] at this
      exact (Submodule.mem_span_range_iff_exists_fun _).1 this
    choose c hc using hc
    have hv' : v = fun i => ∑ j, ((c i j : Ω)) • b j := by
      funext i
      rw [← hc i]
      rfl
    have hsum : exteriorPower.ιMulti Ω r v =
        ∑ f : Fin r → Fin r, (∏ i, c i (f i)) • exteriorPower.ιMulti Ω r (fun i => b (f i)) := by
      rw [hv']
      have := (exteriorPower.ιMulti Ω r (M := E)).toMultilinearMap.map_sum
        (fun i j => ((c i j : Ω)) • b j)
      refine this.trans (Finset.sum_congr rfl fun f _ => ?_)
      have h2 := (exteriorPower.ιMulti Ω r (M := E)).toMultilinearMap.map_smul_univ
        (fun i => (c i (f i) : Ω)) (fun i => b (f i))
      simp only [RingHom.id_apply] at h2
      refine h2.trans ?_
      have h3 : ((∏ i, c i (f i) : regAt ξ p) : Ω) = ∏ i, (c i (f i) : Ω) := by simp
      rw [← h3]
      rfl
    rw [SetLike.mem_coe, hsum]
    refine Submodule.sum_mem _ fun f _ => Submodule.smul_mem _ _ ?_
    by_cases hf : Function.Injective f
    · let σ : Equiv.Perm (Fin r) := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf)
      have h4 := (exteriorPower.ιMulti Ω r (M := E)).map_perm b σ
      have h5 : (fun i => b (f i)) = b ∘ σ := rfl
      rw [h5, h4]
      have hm := Submodule.mem_span_singleton_self (R := regAt ξ p) (exteriorPower.ιMulti Ω r b)
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
      · rw [hs, one_smul]
        exact hm
      · rw [hs, Units.neg_smul, one_smul]
        exact neg_mem hm
    · have h6 : ¬ Function.Injective (fun i => b (f i)) := fun hh =>
        hf (Function.Injective.of_comp (f := b) hh)
      rw [(exteriorPower.ιMulti Ω r (M := E)).map_eq_zero_of_not_injective _ h6]
      exact zero_mem _
  · refine Submodule.span_mono ?_
    rintro w rfl
    refine ⟨b, fun i => ?_, rfl⟩
    rw [h.2]
    exact Submodule.subset_span ⟨i, rfl⟩

end GlobalTheory.CompanionTheory.Ar
end

