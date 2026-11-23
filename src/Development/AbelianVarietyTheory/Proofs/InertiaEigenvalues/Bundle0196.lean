module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0188
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0189
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0190
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormExtensionAcris
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0191
public import Formalism.GaloisCohomology.LocalTateDualityK

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsPtPrimitiveRoot
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory

theorem exists_isPt_primitiveRoot {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P)
    {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL)
    (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) :
    ∃ (ζ : ↥LL.1) (τ : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1), H.IsPt h i ζ τ ∧ IsPrimitiveRoot ζ (l ^ s) := by
  have hs : 1 ≤ s := h.1
  have hLL := h.2.2.2
  have hprim : IsPrimitiveRoot (P.ζQ s) (l ^ s) := by
    obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
    have hpow : ∀ k, P.ζQ (k + 1) ^ l ^ k = P.ζQ 1 := by
      intro k
      induction k with
      | zero => simp
      | succ j ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]
    have h1 : ¬ P.ζQ (m + 1) ^ l ^ m = 1 := by rw [hpow]; exact P.ζQ_one
    have h2 : P.ζQ (m + 1) ^ l ^ (m + 1) = 1 := by
      rw [pow_succ, pow_mul, hpow, P.ζQ_succ, P.ζQ_zero]
    have h3 := orderOf_eq_prime_pow h1 h2
    rw [← h3]
    exact IsPrimitiveRoot.orderOf _
  have hmem : P.ζQ s ∈ Ks K s :=
    (le_sup_right : IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ l ^ s = 1} ≤ Ks K s)
      (IntermediateField.subset_adjoin _ _ hprim.pow_eq_one)
  let Φ : Om l →ₐ[ℚ_[l]] Om l := ((H.W K s LL h).emb i).liftNormal (Om l)
  have hΦ : ∀ x : ↥(K0 K), Φ (x : Om l) = (((H.W K s LL h).emb i x : ↥LL.1) : Om l) := fun x =>
    AlgHom.liftNormal_commutes ((H.W K s LL h).emb i) (Om l) x
  let τ₀ : ↥(Ks K s) →ₐ[ℚ_[l]] Om l := Φ.comp (Ks K s).val
  let τ : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1 := τ₀.codRestrict LL.1.toSubalgebra (hLL τ₀)
  have hτ : ∀ y : ↥(Ks K s), ((τ y : ↥LL.1) : Om l) = Φ (y : Om l) := fun _ => rfl
  refine ⟨τ ⟨P.ζQ s, hmem⟩, τ, ⟨?_, ?_⟩, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    rw [hτ, hxy, hΦ]
  · intro y hy
    congr 1
    exact Subtype.ext hy
  · have h1 : IsPrimitiveRoot (⟨P.ζQ s, hmem⟩ : ↥(Ks K s)) (l ^ s) :=
      IsPrimitiveRoot.of_map_of_injective (f := (Ks K s).val) hprim (Ks K s).val.injective
    exact h1.map_of_injective τ.injective

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtendOfLocallyCauchy
section
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

open Filter Topology

namespace GlobalTheory.Cong

theorem extend_of_locallyCauchy : ∀ (l : ℕ) [Fact l.Prime] (Γ J : Type) [TopologicalSpace Γ] (x : J → Γ), DenseRange x → ∀ (θ : J → PadicAlgCl l) (L : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] L → (∀ j, θ j ∈ L) → (∀ ε : ℝ, 0 < ε → ∀ g : Γ, ∃ V ∈ nhds g, ∀ i j, x i ∈ V → x j ∈ V → ‖θ i - θ j‖ ≤ ε) → ∃ T : Γ → PadicAlgCl l, Continuous T ∧ ∀ j, T (x j) = θ j := by
  intro l _ Γ J _ x hx θ L hL hθL hC
  have hLc : IsComplete (L : Set (PadicAlgCl l)) := by
    haveI : FiniteDimensional ℚ_[l] (Subalgebra.toSubmodule L.toSubalgebra) := hL
    exact Submodule.complete_of_finiteDimensional (Subalgebra.toSubmodule L.toSubalgebra)
  have hnb : ∀ g : Γ, (comap x (𝓝 g)).NeBot := by
    intro g
    refine comap_neBot_iff.2 fun t ht => ?_
    obtain ⟨_, hyt, j, rfl⟩ := mem_closure_iff_nhds.1 (hx g) t ht
    exact ⟨j, hyt⟩
  have hex : ∀ g : Γ, ∃ t : PadicAlgCl l, Tendsto θ (comap x (𝓝 g)) (𝓝 t) := by
    intro g
    haveI : (comap x (𝓝 g)).NeBot := hnb g
    have hcau : Cauchy (map θ (comap x (𝓝 g))) := by
      rw [Metric.cauchy_iff]
      refine ⟨inferInstance, fun ε hε => ?_⟩
      obtain ⟨V, hV, hVc⟩ := hC (ε / 2) (by positivity) g
      refine ⟨θ '' (x ⁻¹' V), image_mem_map (preimage_mem_comap hV), ?_⟩
      rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
      rw [dist_eq_norm]
      exact lt_of_le_of_lt (hVc i j hi hj) (by linarith)
    have hle : map θ (comap x (𝓝 g)) ≤ 𝓟 (L : Set (PadicAlgCl l)) :=
      le_principal_iff.2 (mem_map.2 (univ_mem' fun j => hθL j))
    obtain ⟨t, -, ht⟩ := hLc _ hcau hle
    exact ⟨t, ht⟩
  choose T hT using hex
  refine ⟨T, ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun g => ?_
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨V, hV, hVc⟩ := hC (ε / 2) (by positivity) g
    filter_upwards [interior_mem_nhds.2 hV] with g' hg'
    have hV' : V ∈ 𝓝 g' := mem_interior_iff_mem_nhds.1 hg'
    haveI : (comap x (𝓝 g')).NeBot := hnb g'
    haveI : (comap x (𝓝 g)).NeBot := hnb g
    have hlim : Tendsto (fun p : J × J => dist (θ p.1) (θ p.2))
        (comap x (𝓝 g') ×ˢ comap x (𝓝 g)) (𝓝 (dist (T g') (T g))) :=
      ((hT g').comp tendsto_fst).dist ((hT g).comp tendsto_snd)
    have hev : ∀ᶠ p : J × J in comap x (𝓝 g') ×ˢ comap x (𝓝 g), dist (θ p.1) (θ p.2) ≤ ε / 2 := by
      filter_upwards [prod_mem_prod (preimage_mem_comap hV') (preimage_mem_comap hV)] with p hp
      rw [dist_eq_norm]
      exact hVc p.1 p.2 hp.1 hp.2
    have := le_of_tendsto hlim hev
    linarith
  · intro j
    haveI : (comap x (𝓝 (x j))).NeBot := hnb (x j)
    refine tendsto_nhds_unique (hT (x j)) ?_
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨V, hV, hVc⟩ := hC (ε / 2) (by positivity) (x j)
    filter_upwards [preimage_mem_comap hV] with i hi
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (hVc i j hi (mem_of_mem_nhds hV)) (by linarith)

end GlobalTheory.Cong
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLengthOfSmulEqZero
section
noncomputable section

namespace GlobalTheory.AdmLoc

open Formalism.WeaklyAdmissibleFiltrations
open scoped Pointwise

section Sub

variable {O G : Type} [CommRing O] [Group G] {M : Type} [AddCommGroup M] [Module O M]

def IsStab (π : Representation O G M) (X : Submodule O M) : Prop := ∀ g, ∀ x ∈ X, π g x ∈ X

variable {π : Representation O G M}

theorem IsStab.smul {X : Submodule O M} (h : IsStab π X) (c : O) : IsStab π (c • X) := by
  intro g x hx
  obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x c X).mp hx
  rw [map_smul]
  exact Submodule.smul_mem_pointwise_smul _ _ _ (h g y hy)

theorem IsStab.sup {X Y : Submodule O M} (h : IsStab π X) (h' : IsStab π Y) : IsStab π (X ⊔ Y) := by
  intro g x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add (f := _)]
  exact Submodule.add_mem_sup (h g y hy) (h' g z hz)

def subquotRep {X Y : Submodule O M} (hX : IsStab π X) (hY : IsStab π Y) :
    Representation O G (↥Y ⧸ X.comap Y.subtype) :=
  (π.subrepresentation Y hY).quotient (X.comap Y.subtype) (fun g x hx => hX g x hx)

theorem subquot_sameSS_prod {X Y Z : Submodule O M} (hX : IsStab π X) (hY : IsStab π Y) (hZ : IsStab π Z)
    (hXY : X ≤ Y) (hYZ : Y ≤ Z) (h : IsFiniteLength O (↥Z ⧸ X.comap Z.subtype)) :
    SameSS (subquotRep hX hZ) ((subquotRep hX hY).prod (subquotRep hY hZ)) := by
  refine SameSS.of_exact
    (f := Submodule.mapQ _ _ (Submodule.inclusion hYZ) (fun _ hx => hx))
    (p := Submodule.mapQ _ _ LinearMap.id (fun _ hx => hXY hx)) ?_ ?_ ?_ ?_ ?_ h
  · intro g x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  · intro g x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : Submodule.inclusion hYZ x ∈ X.comap Z.subtype := (Submodule.Quotient.mk_eq_zero _).mp hx
    exact (Submodule.Quotient.mk_eq_zero _).mpr h1
  · intro x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  · intro x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    constructor
    · intro hx
      have h1 : x ∈ Y.comap Z.subtype := (Submodule.Quotient.mk_eq_zero _).mp hx
      exact ⟨Submodule.Quotient.mk ⟨x, h1⟩, rfl⟩
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [← hy]
      exact (Submodule.Quotient.mk_eq_zero (Y.comap Z.subtype) (x := Submodule.inclusion hYZ y)).mpr y.2

def smulEquiv {c : O} (hc : IsSMulRegular M c) (Y : Submodule O M) : ↥Y ≃ₗ[O] ↥(c • Y) :=
  Submodule.equivMapOfInjective (DistribSMul.toLinearMap O M c) hc Y

theorem subquot_sameSS_smul {c : O} (hc : IsSMulRegular M c) {X Y : Submodule O M} (hX : IsStab π X)
    (hY : IsStab π Y) (h : IsFiniteLength O (↥Y ⧸ X.comap Y.subtype)) :
    SameSS (subquotRep hX hY) (subquotRep (hX.smul c) (hY.smul c)) := by
  refine SameSS.of_equiv h (Submodule.Quotient.equiv _ _ (smulEquiv hc Y) ?_) ?_
  · ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact Submodule.smul_mem_pointwise_smul _ _ _ hx
    · intro hz
      obtain ⟨y, rfl⟩ := (smulEquiv hc Y).surjective z
      obtain ⟨x, hx, hxy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ c X).mp hz
      have hxy' : x = (y : M) := hc hxy
      exact ⟨y, (hxy' ▸ hx : (y : M) ∈ X), rfl⟩
  · intro g x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
    exact (map_smul (π g) c (x : M)).symm

theorem SameSS.prod_comm {A C : Type} [AddCommGroup A] [Module O A] [AddCommGroup C] [Module O C]
    (α : Representation O G A) (γ : Representation O G C) (hA : IsFiniteLength O A) (hC : IsFiniteLength O C) :
    SameSS (α.prod γ) (γ.prod α) :=
  ((SameSS.refl α hA).prod (SameSS.refl γ hC)).congr_right (LinearEquiv.prodComm O A C) (fun _ _ => rfl)

variable [IsDomain O] [IsDiscreteValuationRing O]

theorem finiteLength_of_smul_eq_zero {N : Type} [AddCommGroup N] [Module O N] [Module.Finite O N] {c : O}
    (hc : c ≠ 0) (h : ∀ x : N, c • x = 0) : IsFiniteLength O N := by
  have hfl := isFiniteLength_quotient_span_singleton O (mem_nonZeroDivisors_of_ne_zero hc)
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at hfl ⊢
  refine ⟨inferInstance, ?_⟩
  have ht : Module.IsTorsionBySet O N (Ideal.span {c}) :=
    (Module.isTorsionBySet_span_singleton_iff c).mpr (fun x => h x)
  letI := ht.module
  haveI : IsScalarTower O (O ⧸ Ideal.span {c}) N := ht.isScalarTower
  haveI : IsArtinianRing (O ⧸ Ideal.span {c}) := isArtinian_of_tower O hfl.2
  haveI : Module.Finite (O ⧸ Ideal.span {c}) N := Module.Finite.of_restrictScalars_finite O _ _
  exact isArtinian_of_surjective_algebraMap (R := O ⧸ Ideal.span {c}) Ideal.Quotient.mk_surjective

theorem finiteLength_subquot {c : O} (hc : c ≠ 0) {X Y : Submodule O M} (hY : Y.FG) (h : c • Y ≤ X) :
    IsFiniteLength O (↥Y ⧸ X.comap Y.subtype) := by
  haveI : Module.Finite O ↥Y := Module.Finite.iff_fg.mpr hY
  refine finiteLength_of_smul_eq_zero hc fun x => ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact h (Submodule.smul_mem_pointwise_smul _ _ _ x.2)

theorem fg_smul {Y : Submodule O M} (hY : Y.FG) (c : O) : (c • Y).FG := hY.map _

theorem red_sameSS_step {c : O} (hc0 : c ≠ 0) (hc : IsSMulRegular M c) {A B : Submodule O M} (hA : IsStab π A)
    (hB : IsStab π B) (fA : A.FG) (fB : B.FG) (h1 : c • A ≤ B) (h2 : B ≤ A) :
    SameSS (subquotRep (hA.smul c) hA) (subquotRep (hB.smul c) hB) := by
  have h3 : c • B ≤ c • A := Submodule.map_mono h2
  have e1 := subquot_sameSS_prod (hA.smul c) hB hA h1 h2 (finiteLength_subquot hc0 fA le_rfl)
  have e2 := subquot_sameSS_prod (hB.smul c) (hA.smul c) hB h3 h1 (finiteLength_subquot hc0 fB le_rfl)
  have l1 := finiteLength_subquot hc0 fB h3
  have l2 := finiteLength_subquot hc0 fA h1
  have e3 := subquot_sameSS_smul hc hB hA l2
  exact (e1.trans (SameSS.prod_comm _ _ l1 l2)).trans ((e3.prod (SameSS.refl _ l1)).trans e2.symm)

theorem red_sameSS_of_pow {c : O} (hc0 : c ≠ 0) (hc : IsSMulRegular M c) {B : Submodule O M} (hB : IsStab π B)
    (fB : B.FG) (n : ℕ) : ∀ {A : Submodule O M} (hA : IsStab π A), A.FG → c ^ n • A ≤ B → B ≤ A →
      SameSS (subquotRep (hA.smul c) hA) (subquotRep (hB.smul c) hB) := by
  induction n with
  | zero =>
    intro A hA fA h1 h2
    rw [pow_zero, one_smul] at h1
    obtain rfl : A = B := le_antisymm h1 h2
    exact SameSS.refl _ (finiteLength_subquot hc0 fA le_rfl)
  | succ n ih =>
    intro A hA fA h1 h2
    have fA' : (B ⊔ c • A).FG := fB.sup (fg_smul fA c)
    refine (red_sameSS_step hc0 hc hA (hB.sup (hA.smul c)) fA fA' le_sup_right
      (sup_le h2 (Submodule.smul_le_self_of_tower c A))).trans (ih _ fA' ?_ le_sup_left)
    rw [Submodule.smul_sup', smul_smul, ← pow_succ]
    exact sup_le (Submodule.smul_le_self_of_tower _ B) h1

theorem red_sameSS_of_commensurable {c : O} (hc0 : c ≠ 0) (hc : IsSMulRegular M c) {A B : Submodule O M}
    (hA : IsStab π A) (hB : IsStab π B) (fA : A.FG) (fB : B.FG) {m n : ℕ} (h1 : c ^ m • A ≤ B)
    (h2 : c ^ n • B ≤ A) : SameSS (subquotRep (hA.smul c) hA) (subquotRep (hB.smul c) hB) := by
  have fS : (A ⊔ B).FG := fA.sup fB
  refine (red_sameSS_of_pow hc0 hc hA fA n (hA.sup hB) fS ?_ le_sup_left).symm.trans
    (red_sameSS_of_pow hc0 hc hB fB m (hA.sup hB) fS ?_ le_sup_right)
  · rw [Submodule.smul_sup']
    exact sup_le (Submodule.smul_le_self_of_tower _ A) h2
  · rw [Submodule.smul_sup']
    exact sup_le h1 (Submodule.smul_le_self_of_tower _ B)

end Sub

section Lat

variable {G : Type} [Group G] {LL O : Type} [Field LL] [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]

def resScal (O : Type) [CommRing O] [Algebra O LL] [Module O V] [IsScalarTower O LL V]
    (ρ : Representation LL G V) : Representation O G V where
  toFun g := (ρ g).restrictScalars O
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp

variable {ρ : Representation LL G V}

theorem isStab_lattice (L : Lattice (O := O) ρ) : IsStab (resScal O ρ) L.T := L.stable

variable [IsDomain O] [IsDiscreteValuationRing O]

theorem modRep_sameSS_subquot (L : Lattice (O := O) ρ) {c : O} (hc : c ≠ 0) :
    SameSS (subquotRep ((isStab_lattice L).smul c) (isStab_lattice L)) (modRep (latRep L) c) := by
  refine SameSS.of_equiv (finiteLength_subquot hc L.fg le_rfl) (Submodule.quotEquivOfEq _ _ ?_) ?_
  · ext x
    constructor
    · intro hx
      obtain ⟨y, hy, hxy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ c L.T).mp hx
      exact (Submodule.mem_smul_pointwise_iff_exists _ c ⊤).mpr ⟨⟨y, hy⟩, trivial, Subtype.ext hxy⟩
    · intro hx
      obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ c ⊤).mp hx
      exact Submodule.smul_mem_pointwise_smul _ _ _ y.2
  · intro g x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl

variable [IsFractionRing O LL]

theorem exists_pow_smul_mem (L : Lattice (O := O) ρ) {lam : O} (hlam : Irreducible lam) (v : V) :
    ∃ n : ℕ, lam ^ n • v ∈ L.T := by
  have hv : v ∈ Submodule.span LL (L.T : Set V) := by rw [L.span]; trivial
  obtain ⟨s, hs⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) LL (L.T : Set V) v hv
  rw [Submodule.span_eq] at hs
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero s.2) hlam
  refine ⟨n, ?_⟩
  have h := L.T.smul_mem ((u⁻¹ : Oˣ) : O) hs
  rwa [Submonoid.smul_def, smul_smul, hu, Units.inv_mul_cancel_left] at h

theorem exists_pow_smul_le (L : Lattice (O := O) ρ) {lam : O} (hlam : Irreducible lam) {A : Submodule O V}
    (hA : A.FG) : ∃ n : ℕ, lam ^ n • A ≤ L.T := by
  induction A, hA using Submodule.fg_induction with
  | singleton x =>
    obtain ⟨n, hn⟩ := exists_pow_smul_mem L hlam x
    refine ⟨n, ?_⟩
    rw [Submodule.smul_span, Set.smul_set_singleton, Submodule.span_singleton_le_iff_mem]
    exact hn
  | sup A B _ _ hA hB =>
    obtain ⟨m, hm⟩ := hA
    obtain ⟨n, hn⟩ := hB
    refine ⟨m + n, ?_⟩
    rw [Submodule.smul_sup']
    refine sup_le ?_ ?_
    · rw [pow_add, mul_comm, ← smul_smul]
      exact (Submodule.smul_le_self_of_tower _ _).trans hm
    · rw [pow_add, ← smul_smul]
      exact (Submodule.smul_le_self_of_tower _ _).trans hn

theorem lattice_reduction_sameSS {lam : O} (hlam : Irreducible lam) (L L' : Lattice (O := O) ρ) :
    SameSS (modRep (latRep L) lam) (modRep (latRep L') lam) := by
  have h0 : lam ≠ 0 := hlam.ne_zero
  have hreg : IsSMulRegular V lam := by
    intro x y hxy
    have h1 : algebraMap O LL lam ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O LL)).mpr h0
    have h2 : algebraMap O LL lam • x = algebraMap O LL lam • y := by
      rw [algebraMap_smul, algebraMap_smul]; exact hxy
    exact smul_right_injective V h1 h2
  obtain ⟨m, hm⟩ := exists_pow_smul_le L' hlam L.fg
  obtain ⟨n, hn⟩ := exists_pow_smul_le L hlam L'.fg
  exact ((modRep_sameSS_subquot L h0).symm.trans
    (red_sameSS_of_commensurable h0 hreg (isStab_lattice L) (isStab_lattice L') L.fg L'.fg hm hn)).trans
    (modRep_sameSS_subquot L' h0)

end Lat

end GlobalTheory.AdmLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisTeichmullerTiltSubEqOne
section
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon.Gauss

lemma gA_term_le_one (l : ℕ) [Fact l.Prime] (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (a : Formalism.Per.Ainf l) (n : ℕ) :
    ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * ρ ^ n ≤ 1 := by
  have hx0 : 0 ≤ ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ := norm_nonneg _
  have hx1 : ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ≤ 1 := (GlobalTheory.RingBasics.mem_OC _).1 ((a.coeff n).untilt).2
  have he : 0 ≤ (1 : ℝ) / (l : ℝ) ^ n := by positivity
  have h2 : ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) ≤ 1 :=
    Real.rpow_le_one hx0 hx1 he
  have h3 : ρ ^ n ≤ 1 := pow_le_one₀ h0 h1
  calc _ ≤ 1 * 1 := mul_le_mul h2 h3 (pow_nonneg h0 n) zero_le_one
    _ = 1 := one_mul 1

theorem gC_teich_sub_eq_one : ∀ (l : ℕ) [Fact l.Prime] (ζ ζ' : Formalism.Per.Fl l),
    ‖(((ζ - ζ').untilt : Formalism.Per.OC l) : ℂ_[l])‖ = 1 →
      ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ (tc l ζ - tc l ζ') = 1 := by
  intro l _ ζ ζ' hζ ρ hρ hρ1
  have hex : ∃ N, IsGauss l ρ N := GlobalTheory.GaussExt.exists_gauss_acris l ρ hρ hρ1
  have hg : IsGauss l ρ (Classical.choose hex) := Classical.choose_spec hex
  have hC : gC l ρ (tc l ζ - tc l ζ') = Classical.choose hex (tc l ζ - tc l ζ') := by
    unfold gC; rw [dite_eq_left hex]
  have hsub : tc l ζ - tc l ζ' =
      algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (Formalism.Per.tm ζ - Formalism.Per.tm ζ') := by
    unfold tc; rw [map_sub]
  rw [hC, hsub, hg.2.2.2.2]
  have hl : (0 : ℝ) < (l : ℝ)⁻¹ := by
    have : (0 : ℝ) < (l : ℝ) := by exact_mod_cast (Fact.out : l.Prime).pos
    positivity
  have h0 : 0 ≤ ρ := le_of_lt (lt_of_lt_of_le hl hρ)
  have hc0 : (Formalism.Per.tm ζ - Formalism.Per.tm ζ').coeff 0 = ζ - ζ' := by
    have := map_sub (WittVector.constantCoeff (p := l) (R := Formalism.Per.Fl l)) (Formalism.Per.tm ζ) (Formalism.Per.tm ζ')
    simpa [Formalism.Per.tm] using this
  unfold gA
  apply le_antisymm
  · exact ciSup_le (fun n => gA_term_le_one l ρ h0 hρ1.le _ n)
  · have hb : BddAbove (Set.range fun n : ℕ =>
        ‖((((Formalism.Per.tm ζ - Formalism.Per.tm ζ').coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^
          ((1 : ℝ) / (l : ℝ) ^ n) * ρ ^ n) :=
      ⟨1, by rintro _ ⟨n, rfl⟩; exact gA_term_le_one l ρ h0 hρ1.le _ n⟩
    refine le_trans ?_ (le_ciSup hb 0)
    simp [hc0, hζ]

end GlobalTheory.PMon.Gauss

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPseudoCharacterOfApproximatedByTraces
section
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

noncomputable section

namespace GlobalTheory.PsChar

open MvPolynomial

theorem aeval_eq_zero_of_polyApprox {k : Type} [NormedField k] [IsUltrametricDist k] {J : Type} {θ : J → k}
    {S : Set (J → k)} (h : PolyApprox θ S) (P : MvPolynomial J ℤ) (hP : ∀ η ∈ S, aeval η P = 0) :
    aeval θ P = 0 := by
  refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_)
  obtain ⟨s, c, hs, hb⟩ := h ε hε
  have hz : ∑ η ∈ s, c η * aeval η P = 0 :=
    Finset.sum_eq_zero fun η hη => by rw [hP η (hs hη), mul_zero]
  have := hb P
  rw [hz, sub_zero] at this
  simpa using this

theorem isPsChar_trc {Γ A : Type} [Group Γ] [CommRing A] (a : ℕ) (ρ : Γ →* GL (Fin a) A) : IsPsChar a (trc ρ) :=
  isPsChar_trace Γ A a ((Units.coeHom (Matrix (Fin a) (Fin a) A)).comp ρ)

theorem isPsChar_of_polyApprox_trc : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a : ℕ) (T : Γ → PadicAlgCl l)
    (C : Set (Γ →* GL (Fin a) (PadicAlgCl l))), PolyApprox T (trc '' C) → IsPsChar a T := by
  intro l _ Γ _ a T C h
  have key : ∀ P : MvPolynomial Γ ℤ, (∀ ρ ∈ C, aeval (trc ρ) P = 0) → aeval T P = 0 := fun P hP =>
    aeval_eq_zero_of_polyApprox h P (by rintro η ⟨ρ, hρ, rfl⟩; exact hP ρ hρ)
  have hm : ∀ (η : Γ → PadicAlgCl l) (x : Fin (a + 1) → Γ),
      aeval η (alt (fun g => (X g : MvPolynomial Γ ℤ)) (a + 1) x) = alt η (a + 1) x := fun η x => by
    have := map_alt (aeval η).toRingHom (fun g => (X g : MvPolynomial Γ ℤ)) (a + 1) x
    simpa using this
  refine ⟨?_, ?_, ?_⟩
  · have := key (X 1 - (a : MvPolynomial Γ ℤ)) fun ρ _ => by simp [(isPsChar_trc a ρ).one]
    simpa [sub_eq_zero] using this
  · intro x y
    have := key (X (x * y) - X (y * x)) fun ρ _ => by simp [(isPsChar_trc a ρ).comm x y]
    simpa [sub_eq_zero] using this
  · intro x
    have := key _ fun ρ _ => by rw [hm]; exact (isPsChar_trc a ρ).alt_eq_zero x
    rwa [hm] at this

end GlobalTheory.PsChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeTwistExactSequenceCohomologyStatement
section
open GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Filter Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_twist_exact_sequence_cohomology : ∀ (G LL O V : Type) [Group G] [TopologicalSpace G] [Field LL] [CommRing O] [Algebra O LL] [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] (ρ : Representation LL G V) (L : Lattice (O := O) ρ) (χ : G →* Oˣ) (S X Y : Type) [AddCommGroup S] [Module O S] [AddCommGroup X] [Module O X] [AddCommGroup Y] [Module O Y] (i : S →ₗ[O] X) (p : X →ₗ[O] Y), Function.Injective i → Function.Exact i p → Function.Surjective p → (∀ c x, tensCoc L χ X c x ∈ ReciprocityTheory.Def.Z1 (twCoef (latRep L) χ X) ⊤) → (∀ m, IsLocallyConstant fun g => twCoef (latRep L) χ X g m) → (twCoef (latRep L) χ Y).invariants = ⊥ → TensIso L χ S → TensIso L χ Y → TensIso L χ X := by
  first | exact @GlobalTheory.TensIsoExt.tensIso_of_exact | exact GlobalTheory.TensIsoExt.tensIso_of_exact | (intros; apply GlobalTheory.TensIsoExt.tensIso_of_exact <;> assumption)
end

