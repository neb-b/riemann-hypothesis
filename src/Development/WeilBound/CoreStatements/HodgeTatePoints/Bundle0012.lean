module

public import GroundTheory.FunctionField.PlaceBridge
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0004
public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.IsMaximalOfNeBot
section
namespace PositivityTheory.HtPt.Plen

open GroundTheory.FunctionField IsLocalRing

theorem finite_closure (k K A : Type) [Field k] [Field K] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra A K] [IsFractionRing A K] [Algebra.EssFiniteType k A] :
    Module.Finite A (integralClosure A K) := by
  classical
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hR : ∀ r : Algebra.EssFiniteType.subalgebra k A, algebraMap _ K r = algebraMap A K (r : A) :=
    fun _ => rfl
  have hfs : FaithfulSMul (Algebra.EssFiniteType.subalgebra k A) K := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b h
    exact Subtype.ext (hinj h)
  have hfr : IsFractionRing (Algebra.EssFiniteType.subalgebra k A) K := by
    refine IsFractionRing.of_field _ K fun z => ?_
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) z
    obtain ⟨⟨a₁, s⟩, ha⟩ := IsLocalization.surj (Algebra.EssFiniteType.submonoid k A) a
    obtain ⟨⟨b₁, t⟩, hb'⟩ := IsLocalization.surj (Algebra.EssFiniteType.submonoid k A) b
    have hs : IsUnit ((s.1 : Algebra.EssFiniteType.subalgebra k A) : A) := s.2
    have ht : IsUnit ((t.1 : Algebra.EssFiniteType.subalgebra k A) : A) := t.2
    have hs0 : algebraMap A K (s.1 : A) ≠ 0 := (hs.map _).ne_zero
    have ht0 : algebraMap A K (t.1 : A) ≠ 0 := (ht.map _).ne_zero
    have hb0 : algebraMap A K b ≠ 0 :=
      (map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hb)
    have ha2 : a * (s.1 : A) = (a₁ : A) := ha
    have hb2 : b * (t.1 : A) = (b₁ : A) := hb'
    refine ⟨a₁ * t.1, b₁ * s.1, ?_⟩
    rw [map_mul, map_mul, hR, hR, hR, hR, ← ha2, ← hb2, map_mul, map_mul]
    field_simp
  have hfin := GroundTheory.Heights₂.Heights.FieldNumbers.NoetherIntegralClosureFinite.proof k
    (Algebra.EssFiniteType.subalgebra k A) K K
  have hfg : (integralClosure (Algebra.EssFiniteType.subalgebra k A) K).toSubmodule.FG :=
    Module.Finite.iff_fg.1 hfin
  obtain ⟨t, ht⟩ := hfg
  have hmem : ∀ x : K, IsIntegral (Algebra.EssFiniteType.subalgebra k A) x ↔
      x ∈ Submodule.span (Algebra.EssFiniteType.subalgebra k A) (t : Set K) := by
    intro x
    rw [ht]
    rfl
  have : (integralClosure A K).toSubmodule.FG := by
    refine ⟨t, le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le]
      intro x hx
      exact ((hmem x).2 (Submodule.subset_span hx)).tower_top
    · intro x hx
      have hx' : IsIntegral A x := hx
      obtain ⟨m, hm⟩ := hx'.exists_multiple_integral_of_isLocalization
        (Algebra.EssFiniteType.submonoid k A)
      have h1 := Submodule.span_le_restrictScalars (Algebra.EssFiniteType.subalgebra k A) A
        (t : Set K) ((hmem _).1 hm)
      have hu : IsUnit ((m.1 : Algebra.EssFiniteType.subalgebra k A) : A) := m.2
      obtain ⟨u, hu⟩ := hu
      have h2 : (u : A) • x ∈ Submodule.span A (t : Set K) := by
        rw [hu]
        exact h1
      have h3 := Submodule.smul_mem _ ((u⁻¹ : Aˣ) : A) h2
      rwa [smul_smul, Units.inv_mul, one_smul] at h3
  exact Module.Finite.iff_fg.2 this

variable {k K : Type} [Field k] [Field K] [Algebra k K] [IsFunctionField k K]

noncomputable def resHom (A : Type) [CommRing A] [Algebra k A] [Algebra A K] [IsScalarTower k A K]
    (v : Place k K) (hv : ∀ a : A, algebraMap A K a ∈ v.ring) : A →ₐ[k] v.ResidueField where
  toRingHom := (residue v.ring).comp (RingHom.codRestrict (algebraMap A K) v.ring hv)
  commutes' c := by
    change residue v.ring _ = residue v.ring (algebraMap k v.ring c)
    congr 1
    exact Subtype.ext (IsScalarTower.algebraMap_apply k A K c).symm

omit [IsFunctionField k K] in
theorem resHom_eq_zero (A : Type) [CommRing A] [Algebra k A] [Algebra A K] [IsScalarTower k A K]
    (v : Place k K) (hv : ∀ a : A, algebraMap A K a ∈ v.ring) (a : A) :
    resHom A v hv a = 0 ↔ v.ring.valuation (algebraMap A K a) < 1 := by
  change residue v.ring ⟨algebraMap A K a, hv a⟩ = 0 ↔ _
  rw [residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]

theorem isMaximal_center (A : Type) [CommRing A] [Algebra k A] [Algebra A K] [IsScalarTower k A K]
    (v : Place k K) (hv : ∀ a : A, algebraMap A K a ∈ v.ring) (p : Ideal A)
    (hp : ∀ a, a ∈ p ↔ v.ring.valuation (algebraMap A K a) < 1) : p.IsMaximal := by
  have hker : p = RingHom.ker (resHom A v hv) := by
    ext a
    rw [hp, RingHom.mem_ker, resHom_eq_zero]
  subst hker
  have hinj := Ideal.kerLiftAlg_injective (resHom A v hv)
  have : Module.Finite k (A ⧸ RingHom.ker (resHom A v hv)) :=
    Module.Finite.of_injective (Ideal.kerLiftAlg (resHom A v hv)).toLinearMap hinj
  have : IsArtinianRing (A ⧸ RingHom.ker (resHom A v hv)) := IsArtinianRing.of_finite k _
  have : (RingHom.ker (resHom A v hv)).IsPrime := RingHom.ker_isPrime _
  exact Ideal.Quotient.maximal_of_isField _ (IsArtinianRing.isField_of_isDomain _)

theorem isMaximal_of_ne_bot (A : Type) [CommRing A] [Algebra k A] [Algebra A K]
    [IsScalarTower k A K] (hinj : Function.Injective (algebraMap A K)) (p : Ideal A) (hp0 : p ≠ ⊥)
    (hp : p.IsPrime) : p.IsMaximal := by
  have hu : ∀ y : p.primeCompl, IsUnit (algebraMap A K y) := fun y => by
    refine IsUnit.mk0 _ ((map_ne_zero_iff _ hinj).2 fun h => y.2 ?_)
    rw [h]
    exact p.zero_mem
  let g : Localization.AtPrime p →+* K := IsLocalization.lift (M := p.primeCompl) hu
  have hg : ∀ a, g (algebraMap A _ a) = algebraMap A K a := fun a => IsLocalization.lift_eq hu a
  obtain ⟨V, hV, hloc⟩ := IsLocalRing.exists_factor_valuationRing g
  have hA : ∀ a, algebraMap A K a ∈ V := fun a => hg a ▸ hV (algebraMap A _ a)
  have key : ∀ a, a ∈ p ↔ V.valuation (algebraMap A K a) < 1 := by
    intro a
    have h1 : IsUnit (g.codRestrict V.toSubring hV (algebraMap A _ a)) ↔
        IsUnit (algebraMap A (Localization.AtPrime p) a) := isUnit_map_iff _ _
    have h2 : IsUnit (g.codRestrict V.toSubring hV (algebraMap A _ a)) ↔
        V.valuation (g (algebraMap A _ a)) = 1 :=
      V.valuation_eq_one_iff ⟨g (algebraMap A _ a), hV _⟩
    rw [IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime p) p, h2, hg] at h1
    have h3 : V.valuation (algebraMap A K a) ≤ 1 := (V.valuation_le_one_iff _).2 (hA a)
    rw [lt_iff_le_and_ne, and_iff_right h3, Ne, h1]
    exact not_not.symm
  have hne : V ≠ ⊤ := by
    rintro rfl
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp0
    have h1 := (key a).1 ha
    have h0 : algebraMap A K a ≠ 0 := (map_ne_zero_iff _ hinj).2 ha0
    have h2 := ((⊤ : ValuationSubring K).valuation_le_one_iff (algebraMap A K a)⁻¹).2
      (ValuationSubring.mem_top _)
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 h0))] at h2
    exact absurd h1 (not_lt.2 h2)
  let v : Place k K := ⟨V, hne, fun c => by
    rw [IsScalarTower.algebraMap_apply k A K]
    exact hA _⟩
  exact isMaximal_center A v hA p key

end PositivityTheory.HtPt.Plen
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.McCramer
section
noncomputable section

namespace PositivityTheory.HtPt.Mc

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

theorem cramer_sub : ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (A : Subring Ω) (r : ℕ) (b : Module.Basis (Fin r) Ω E) (κ : Type) (z : κ → E) (c₀ : Fin r → κ), b.det (z ∘ c₀) ≠ 0 → (∀ c : Fin r → κ, b.det (z ∘ c) / b.det (z ∘ c₀) ∈ A) → LinearIndependent Ω (z ∘ c₀) ∧ Submodule.span A (Set.range z) = Submodule.span A (Set.range (z ∘ c₀)) := by
  intro Ω _ E _ _ A r b κ z c₀ h0 h
  classical
  obtain ⟨li, sp⟩ := (Module.Basis.is_basis_iff_det b).2 (isUnit_iff_ne_zero.2 h0)
  refine ⟨li, le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)⟩
  · rintro _ ⟨k, rfl⟩
    let B := Module.Basis.mk li sp.ge
    have hc : ∀ l, B.repr (z k) l ∈ A := by
      intro l
      have e := LinearMap.congr_fun (b.det_smul_mk_coord_eq_det_update li sp.ge l) (z k)
      have e2 : b.det (z ∘ c₀) * B.repr (z k) l = b.det (z ∘ Function.update c₀ l k) := by
        rw [Function.comp_update]
        exact e
      have e3 : B.repr (z k) l = b.det (z ∘ Function.update c₀ l k) / b.det (z ∘ c₀) := by
        rw [← e2, mul_div_cancel_left₀ _ h0]
      rw [e3]
      exact h _
    refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun l => ⟨_, hc l⟩, ?_⟩
    have := B.sum_repr (z k)
    simp only [B, Module.Basis.mk_apply] at this
    exact this
  · rintro _ ⟨i, rfl⟩
    exact ⟨c₀ i, rfl⟩

section
variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] (A : Subring Ω) {r : ℕ}

theorem repr_mem {ι : Type} (B : Module.Basis ι Ω E) {v : E} (hv : v ∈ Submodule.span A (Set.range B)) (j : ι) :
    B.repr v j ∈ A := by
  classical
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [B.repr_self, Finsupp.single_apply]
    split_ifs
    exacts [A.one_mem, A.zero_mem]
  | zero => simp
  | add x y _ _ hx hy => simpa using A.add_mem hx hy
  | smul a x _ hx =>
    have : B.repr (a • x) j = (a : Ω) * B.repr x j := by
      show B.repr ((a : Ω) • x) j = _
      simp
    rw [this]
    exact A.mul_mem a.2 hx

theorem det_mem (B : Module.Basis (Fin r) Ω E) (v : Fin r → E)
    (hv : ∀ i, v i ∈ Submodule.span A (Set.range B)) : B.det v ∈ A := by
  rw [Module.Basis.det_apply, Matrix.det_apply']
  refine A.sum_mem fun s _ => A.mul_mem (intCast_mem _ _) (A.prod_mem fun i _ => ?_)
  exact repr_mem A B (hv _) _

theorem det_mem_span (B : Module.Basis (Fin r) Ω E) {κ : Type} (z : κ → E) (v : Fin r → E)
    (hv : ∀ i, v i ∈ Submodule.span A (Set.range z)) :
    B.det v ∈ Submodule.span A (Set.range fun c : Fin r → κ => B.det (z ∘ c)) := by
  classical
  choose c hc using fun i => Finsupp.mem_span_range_iff_exists_finsupp.1 (hv i)
  have e : v = fun i => ∑ k ∈ (c i).support, ((c i k : A) : Ω) • z k := funext fun i => (hc i).symm
  have e2 := B.det.toMultilinearMap.map_sum_finset (fun i k => ((c i k : A) : Ω) • z k) fun i => (c i).support
  rw [e]
  refine (show B.det _ = _ from e2) ▸ Submodule.sum_mem _ fun s _ => ?_
  rw [MultilinearMap.map_smul_univ]
  simp only [RingHom.id_apply]
  have : (∏ i, ((c i (s i) : A) : Ω)) = ((∏ i, c i (s i) : A) : Ω) := by simp
  rw [this]
  exact Submodule.smul_mem _ (∏ i, c i (s i)) (Submodule.subset_span ⟨s, rfl⟩)

end

theorem frame_plucker : ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (A : Subring Ω) [IsLocalRing A] (r : ℕ) (b : Module.Basis (Fin r) Ω E) (κ : Type) (z : κ → E) (f : Fin r → E), LinearIndependent Ω f → Submodule.span A (Set.range z) = Submodule.span A (Set.range f) → ∃ c₀ : Fin r → κ, b.det (z ∘ c₀) ≠ 0 ∧ ∀ c : Fin r → κ, b.det (z ∘ c) / b.det (z ∘ c₀) ∈ A := by
  intro Ω _ E _ _ A _ r b κ z f li h
  classical
  haveI := Module.Finite.of_basis b
  have sp : Submodule.span Ω (Set.range f) = ⊤ :=
    li.span_eq_top_of_card_eq_finrank' (by rw [Module.finrank_eq_card_basis b])
  let B := Module.Basis.mk li sp.ge
  have hB : (B : Fin r → E) = f := Module.Basis.coe_mk _ _
  have hd : b.det f ≠ 0 := ((Module.Basis.is_basis_iff_det b).1 ⟨li, sp⟩).ne_zero
  have hbB : ∀ v, b.det v = b.det f * B.det v := fun v => by
    conv_lhs => rw [b.det.eq_smul_basis_det B, hB]
    rfl
  have hA : ∀ c : Fin r → κ, B.det (z ∘ c) ∈ A := fun c =>
    det_mem A B _ fun i => by rw [hB, ← h]; exact Submodule.subset_span ⟨c i, rfl⟩
  have h1 := det_mem_span A B z f fun i => by rw [h]; exact Submodule.subset_span ⟨i, rfl⟩
  rw [← hB, B.det_self] at h1
  have : ∃ c₀, IsUnit (⟨_, hA c₀⟩ : A) := by
    by_contra hn
    push Not at hn
    have : Submodule.span A (Set.range fun c : Fin r → κ => B.det (z ∘ c)) ≤
        Submodule.map (Algebra.linearMap A Ω) (IsLocalRing.maximalIdeal A) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨c, rfl⟩
      exact ⟨⟨_, hA c⟩, hn c, rfl⟩
    obtain ⟨y, hy, e⟩ := this h1
    have : y = 1 := Subtype.ext e
    exact hy (this ▸ isUnit_one)
  obtain ⟨c₀, hu⟩ := this
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have hw' : B.det (z ∘ c₀) * (w : Ω) = 1 := congrArg Subtype.val hw
  refine ⟨c₀, by rw [hbB]; exact mul_ne_zero hd (left_ne_zero_of_mul_eq_one hw'), fun c => ?_⟩
  rw [hbB, hbB (z ∘ c₀), mul_div_mul_left _ _ hd, div_eq_mul_inv, ← eq_inv_of_mul_eq_one_right hw']
  exact A.mul_mem (hA c) w.2

end PositivityTheory.HtPt.Mc
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.NearMemSpan
section
noncomputable section

namespace PositivityTheory.HtPt.Mc

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

section
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem near_all {ι : Type} [Finite ι] (p : Cpt ξ) (P : ι → Cpt ξ → Prop)
    (h : ∀ i, ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → P i q) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → ∀ i, P i q := by
  choose U hU hP using h
  refine ⟨⟨⋂ i, (U i : Set X), isOpen_iInter_of_finite fun i => (U i).isOpen⟩, ?_, fun q hq i => hP i q ?_⟩
  · exact Set.mem_iInter.2 hU
  · exact Set.mem_iInter.1 hq i

theorem near_mem_span {n : ℕ} (g : Fin n → E) (p : Cpt ξ) (e : E)
    (h : e ∈ Submodule.span (regAt ξ p) (Set.range g)) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → e ∈ Submodule.span (regAt ξ q) (Set.range g) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h
  obtain ⟨U, hU, H⟩ := near_all p (fun i q => (c i : Ω) ∈ regAt ξ q)
    fun i => (regAt_unitAt_open X Ω ξ p (c i)).1 (c i).2
  exact ⟨U, hU, fun q hq => (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun i => ⟨c i, H q hq i⟩, hc⟩⟩

theorem near_span_eq {n m : ℕ} (g : Fin n → E) (b : Fin m → E) (p : Cpt ξ)
    (h : Submodule.span (regAt ξ p) (Set.range g) = Submodule.span (regAt ξ p) (Set.range b)) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U →
      Submodule.span (regAt ξ q) (Set.range g) = Submodule.span (regAt ξ q) (Set.range b) := by
  obtain ⟨U, hU, H⟩ := near_all p (fun i q => g i ∈ Submodule.span (regAt ξ q) (Set.range b))
    fun i => near_mem_span b p _ (h ▸ Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨U', hU', H'⟩ := near_all p (fun i q => b i ∈ Submodule.span (regAt ξ q) (Set.range g))
    fun i => near_mem_span g p _ (h ▸ Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨U ⊓ U', ⟨hU, hU'⟩, fun q hq => le_antisymm ?_ ?_⟩
  · exact Submodule.span_le.2 (Set.range_subset_iff.2 (H q hq.1))
  · exact Submodule.span_le.2 (Set.range_subset_iff.2 (H' q hq.2))

end

theorem frame_spread : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (T : Set (Cpt ξ)) (r : ℕ) (b : Fin r → E) (p : Cpt ξ), L.IsCohOn T → p ∈ T → L.IsFrameAt b p → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q ∈ T, q.1 ∈ U → L.IsFrameAt b q := by
  intro X Ω _ ξ E _ _ L T r b p hL hp hb
  obtain ⟨U, hU, n, g, hg⟩ := hL p hp
  obtain ⟨U', hU', H⟩ := near_span_eq g b p ((hg p hp hU).symm.trans hb.2)
  exact ⟨U ⊓ U', ⟨hU, hU'⟩, fun q hq hqU => ⟨hb.1, (hg q hq hqU.1).trans (H q hqU.2)⟩⟩

section
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E E' : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω E']

theorem map_of_span {L : Lat ξ E} (φ : E →ₗ[Ω] E') {q : Cpt ξ} {ι : Type} {b : ι → E}
    (h : L q = Submodule.span (regAt ξ q) (Set.range b)) :
    L.map φ q = Submodule.span (regAt ξ q) (Set.range (φ ∘ b)) := by
  unfold Lat.map
  rw [h, Submodule.map_span, Set.range_comp]
  rfl

theorem coh_map {L : Lat ξ E} {T : Set (Cpt ξ)} (φ : E →ₗ[Ω] E') (h : L.IsCohOn T) : (L.map φ).IsCohOn T := by
  intro p hp
  obtain ⟨U, hU, n, g, hg⟩ := h p hp
  exact ⟨U, hU, n, φ ∘ g, fun q hq hqU => map_of_span φ (hg q hq hqU)⟩

theorem vb_of_coh {L : Lat ξ E} {T : Set (Cpt ξ)} {r : ℕ} {V : Submodule Ω E} (h : L.IsCohOn T)
    (hb : ∀ p ∈ T, ∃ b : Fin r → E, Submodule.span Ω (Set.range b) = V ∧ L.IsFrameAt b p) : L.IsVBOn T r V := by
  intro p hp
  obtain ⟨b, hV, hb⟩ := hb p hp
  obtain ⟨U, hU, H⟩ := frame_spread X Ω ξ E L T r b p h hp hb
  exact ⟨U, hU, b, hV, H⟩

theorem span_smul_fam {ι : Type} (b : ι → E) {a : Ω} (ha : a ≠ 0) :
    Submodule.span Ω (Set.range fun i => a • b i) = Submodule.span Ω (Set.range b) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨i, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rintro _ ⟨i, rfl⟩
    have : b i = a⁻¹ • a • b i := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem li_smul_fam {ι : Type} {b : ι → E} (hb : LinearIndependent Ω b) {a : Ω} (ha : a ≠ 0) :
    LinearIndependent Ω fun i => a • b i :=
  hb.units_smul fun _ => Units.mk0 a ha

end

theorem coh_ops : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (E' : Type) [AddCommGroup E'] [Module Ω E'] (L L' : Lat ξ E) (T : Set (Cpt ξ)), (∀ r V, L.IsVBOn T r V → L.IsCohOn T) ∧ (∀ φ : E →ₗ[Ω] E', L.IsCohOn T → (L.map φ).IsCohOn T) ∧ (L.IsCohOn T → L'.IsCohOn T → Lat.IsCohOn (fun p => L p ⊔ L' p : Lat ξ E) T) ∧ (∀ (r : ℕ) (V : Submodule Ω E) (a : Ω), a ≠ 0 → L.IsVBOn T r V → (L.scale a).IsVBOn T r V) ∧ (∀ (r : ℕ) (V : Submodule Ω E), L.IsCohOn T → (∀ p ∈ T, ∃ b : Fin r → E, Submodule.span Ω (Set.range b) = V ∧ L.IsFrameAt b p) → L.IsVBOn T r V) := by
  intro X Ω _ ξ E _ _ E' _ _ L L' T
  refine ⟨fun r V h => Lat.IsCohOn.of_isVBOn h, fun φ h => coh_map φ h, fun h h' p hp => ?_,
    fun r V a ha h p hp => ?_, fun r V h hb => vb_of_coh h hb⟩
  · obtain ⟨U, hU, n, g, hg⟩ := h p hp
    obtain ⟨U', hU', n', g', hg'⟩ := h' p hp
    refine ⟨U ⊓ U', ⟨hU, hU'⟩, n + n', Fin.append g g', fun q hq hqU => ?_⟩
    have e : Set.range (Fin.append g g') = Set.range g ∪ Set.range g' := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        induction i using Fin.addCases with
        | left i => exact Or.inl ⟨i, by simp⟩
        | right i => exact Or.inr ⟨i, by simp⟩
      · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
        · exact ⟨Fin.castAdd n' i, by simp⟩
        · exact ⟨Fin.natAdd n i, by simp⟩
    rw [e, Submodule.span_union, ← hg q hq hqU.1, ← hg' q hq hqU.2]
  · obtain ⟨U, hU, b, hV, hb⟩ := h p hp
    refine ⟨U, hU, fun i => a • b i, (span_smul_fam b ha).trans hV, fun q hq hqU =>
      ⟨li_smul_fam (hb q hq hqU).1 ha, ?_⟩⟩
    exact map_of_span _ (hb q hq hqU).2

end PositivityTheory.HtPt.Mc
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.OfMem
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.HtPt.Ci.Val

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {R : Type} [CommRing R]
  [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X}

theorem one (h : genPt ξ ⤳ centre z) : ValAt ξ z 1 1 := ⟨h, 1, map_one _, map_one _⟩

theorem mul {a b : Ω} {r s : R} (ha : ValAt ξ z a r) (hb : ValAt ξ z b s) : ValAt ξ z (a * b) (r * s) := by
  obtain ⟨h, u, rfl, rfl⟩ := ha
  obtain ⟨_, v, rfl, rfl⟩ := hb
  exact ⟨h, u * v, map_mul _ _ _, map_mul _ _ _⟩

theorem pow {a : Ω} {r : R} (ha : ValAt ξ z a r) (n : ℕ) : ValAt ξ z (a ^ n) (r ^ n) := by
  obtain ⟨h, u, rfl, rfl⟩ := ha
  exact ⟨h, u ^ n, map_pow _ _ _, map_pow _ _ _⟩

theorem prod (h : genPt ξ ⤳ centre z) {ι : Type} (T : Finset ι) {a : ι → Ω} {r : ι → R}
    (ha : ∀ k, ValAt ξ z (a k) (r k)) : ValAt ξ z (∏ k ∈ T, a k) (∏ k ∈ T, r k) := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty]; exact one h
  | insert k T hk ih => rw [Finset.prod_insert hk, Finset.prod_insert hk]; exact mul (ha k) ih

theorem mem {a : Ω} {r : R} (ha : ValAt ξ z a r) (h : genPt ξ ⤳ centre z) : a ∈ regAt ξ ⟨centre z, h⟩ := by
  obtain ⟨_, u, rfl, -⟩ := ha
  exact ⟨u, rfl⟩

theorem of_mem {a : Ω} {h : genPt ξ ⤳ centre z} (ha : a ∈ regAt ξ ⟨centre z, h⟩) : ∃ r, ValAt ξ z a r := by
  obtain ⟨u, rfl⟩ := ha
  exact ⟨_, h, u, rfl, rfl⟩

theorem zpow {K : Type} [Field K] {z : Spec (CommRingCat.of K) ⟶ X} {a : Ω} {r : K} (ha : ValAt ξ z a r)
    (ha' : ValAt ξ z a⁻¹ r⁻¹) (n : ℤ) : ValAt ξ z (a ^ n) (r ^ n) := by
  cases n with
  | ofNat n => simpa using pow ha n
  | negSucc n => simpa only [zpow_negSucc, inv_pow] using pow ha' (n + 1)

end PositivityTheory.HtPt.Ci.Val
end
end

