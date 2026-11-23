module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1403
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2356
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2383
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2465
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2468
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2469
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2467

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointClosureDimLeAndResidueDegreeNeZeroIff
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.DimDeg

def DimFormula (R : Type) [CommRing R] (c : ℕ) : Prop :=
  ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra R B] [FaithfulSMul R B] [Algebra.FiniteType R B] (e : ℕ),
    Algebra.trdeg R B = e → ringKrullDim B = (e + c : ℕ)

theorem dimFormula_field (F : Type) [Field F] : DimFormula F 0 := by
  intro B _ _ _ _ _ e he
  obtain ⟨d, h₁, h₂⟩ := exists_ringKrullDim_eq_and_trdeg_eq F B
  have : d = e := by exact_mod_cast h₂.symm.trans he
  rw [h₁, this, add_zero]

theorem dimFormula_int : DimFormula ℤ 1 := by
  intro B _ _ _ _ _ e he
  have : CharZero B := charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective ℤ B)
  refine le_antisymm ?_ (PrimeDivDim.succ_trdeg_le_ringKrullDim B he)
  have hZ1 : ringKrullDim ℤ ≤ 1 := by
    exact_mod_cast Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 ℤ)
  refine (IntModel.ringKrullDim_le_add (O := ℤ) ℚ).trans ?_
  rw [ringKrullDim_genericFibre_eq ℤ ℚ he]
  refine (add_le_add hZ1 (le_refl ((e : ℕ) : WithBot ℕ∞))).trans_eq ?_
  push_cast
  exact add_comm _ _

theorem exists_dim_quotient_ker {R : Type} [CommRing R] [IsDomain R] {c : ℕ} (hR : DimFormula R c)
    (hs : Function.Surjective (Int.cast : ℤ → R)) {A K : Type} [CommRing A] (hA : (Int.castRingHom A).FiniteType)
    [Field K] [Algebra R K] [FaithfulSMul R K] (φ : A →+* K) (hφ : ∀ z : K, ∃ a b : A, z = φ a / φ b) :
    ∃ e : ℕ, Algebra.trdeg R K = e ∧ ringKrullDim (A ⧸ RingHom.ker φ) = (e + c : ℕ) := by
  let B : Subalgebra R K :=
    { φ.range.toSubsemiring with
      algebraMap_mem' := fun r => by
        obtain ⟨n, rfl⟩ := hs r
        exact ⟨n, by simp⟩ }
  let ψ : A →+* B := φ.codRestrict B fun a => ⟨a, rfl⟩
  have hψ : Function.Surjective ψ := by
    rintro ⟨_, a, rfl⟩
    exact ⟨a, rfl⟩
  have hft : Algebra.FiniteType R B := by
    have h1 : (ψ.comp (Int.castRingHom A)).FiniteType := (RingHom.FiniteType.of_surjective ψ hψ).comp hA
    rw [Subsingleton.elim (ψ.comp (Int.castRingHom A)) ((algebraMap R B).comp (Int.castRingHom R))] at h1
    exact RingHom.finiteType_algebraMap.1 h1.of_comp_finiteType
  have : FaithfulSMul R B := (faithfulSMul_iff_algebraMap_injective _ _).2 fun a b h =>
    FaithfulSMul.algebraMap_injective R K (by
      rw [IsScalarTower.algebraMap_apply R B K, IsScalarTower.algebraMap_apply R B K, h])
  have : IsFractionRing B K := IsFractionRing.of_field B K fun z => by
    obtain ⟨a, b, h⟩ := hφ z
    exact ⟨ψ a, ψ b, h⟩
  have : Algebra.IsAlgebraic B K := IsLocalization.isAlgebraic K (nonZeroDivisors B)
  obtain ⟨e, he⟩ := exists_trdeg_eq_natCast R (A := B)
  refine ⟨e, (trdeg_eq_of_isAlgebraic_top R B K).trans he, ?_⟩
  have hk : RingHom.ker φ = RingHom.ker ψ := Ideal.ext fun a => by
    simp only [RingHom.mem_ker]
    exact (Subtype.ext_iff (a1 := ψ a) (a2 := 0)).symm
  rw [← hR B e he, hk]
  exact ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hψ)

theorem exists_dim_inter {R : Type} [CommRing R] [IsDomain R] {c : ℕ} (hR : DimFormula R c)
    (hs : Function.Surjective (Int.cast : ℤ → R)) {X : Scheme.{0}} (t : X ⟶ Sp ℤ) [LocallyOfFiniteType t] (x : X)
    [Algebra R (X.residueField x)] [FaithfulSMul R (X.residueField x)] {U : X.Opens} (hU : IsAffineOpen U) (hx : x ∈ U) :
    ∃ e : ℕ, Algebra.trdeg R (X.residueField x) = e ∧
      topologicalKrullDim ((U : Set X) ∩ closure {x} : Set X) = (e + c : ℕ) := by
  have hA : (Int.castRingHom Γ(X, U)).FiniteType := by
    let φ := Spec.preimage (hU.fromSpec ≫ t)
    have hφ : Spec.map φ = hU.fromSpec ≫ t := Spec.map_preimage _
    have h := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp (hφ ▸ inferInstance)
    rwa [Subsingleton.elim (Int.castRingHom Γ(X, U)) φ.hom]
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hx⟩
  obtain ⟨e, h₁, h₂⟩ := exists_dim_quotient_ker hR hs hA (X.evaluation U x hx).hom (by
    intro z
    obtain ⟨w, rfl⟩ := X.residue_surjective x z
    obtain ⟨⟨a, b⟩, h⟩ := IsLocalization.surj (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (S := X.presheaf.stalk x) w
    have hu := (IsLocalization.map_units (X.presheaf.stalk x) b).map (X.residue x).hom
    refine ⟨a, b, (eq_div_iff hu.ne_zero).2 ?_⟩
    exact (map_mul (X.residue x).hom _ _).symm.trans (congrArg (X.residue x).hom h))
  refine ⟨e, h₁, ?_⟩
  have hk : RingHom.ker (X.evaluation U x hx).hom = (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
    ext f
    rw [RingHom.mem_ker]
    refine (X.evaluation_eq_zero_iff_notMem_basicOpen x hx f).trans ?_
    have h := hU.fromSpec_preimage_basicOpen f
    have h' : hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen f ↔ f ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
      SetLike.ext_iff.1 h (hU.primeIdealOf ⟨x, hx⟩)
    rw [hU.fromSpec_primeIdealOf] at h'
    exact h'.not.trans not_not
  have h := topologicalKrullDim_range_inter_closure_eq (B := Γ(X, U)) hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩)
  rw [← h₂, hk, ← h]
  have h3 := hU.fromSpec_primeIdealOf ⟨x, hx⟩
  have h4 := hU.range_fromSpec
  exact congrArg (fun s : Set X => topologicalKrullDim s)
    (congrArg₂ (· ∩ ·) h4.symm (congrArg (fun z => closure {z}) h3.symm))

theorem exists_hasDim {R : Type} [CommRing R] [IsDomain R] {c : ℕ} (hR : DimFormula R c)
    (hs : Function.Surjective (Int.cast : ℤ → R)) {X : Scheme.{0}} (t : X ⟶ Sp ℤ) [LocallyOfFiniteType t] (x : X)
    [Algebra R (X.residueField x)] [FaithfulSMul R (X.residueField x)] :
    ∃ e : ℕ, Algebra.trdeg R (X.residueField x) = e ∧ HasDim x (e + c) := by
  obtain ⟨U, hU, hxU, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (Opens.mem_top x)
  obtain ⟨e, h₁, h₂⟩ := exists_dim_inter hR hs t x hU hxU
  refine ⟨e, h₁, le_antisymm ?_ ?_⟩
  · refine topologicalKrullDim_le_of_forall_exists_isOpen fun z => ?_
    obtain ⟨V, hV, hzV, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (Opens.mem_top z.1)
    have hxV : x ∈ V := (specializes_iff_mem_closure.2 z.2).mem_open V.isOpen hzV
    obtain ⟨e', h₁', h₂'⟩ := exists_dim_inter hR hs t x hV hxV
    obtain rfl : e = e' := by exact_mod_cast h₁.symm.trans h₁'
    refine ⟨Subtype.val ⁻¹' (V : Set X), V.isOpen.preimage continuous_subtype_val, hzV, ?_⟩
    rw [← h₂']
    refine (topologicalKrullDim_eq_of_isEmbedding
      (Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal) ?_).ge
    rw [Set.range_comp, Subtype.range_val, Subtype.image_preimage_val, Set.inter_comm]
  · rw [← h₂]
    exact (Topology.IsEmbedding.inclusion Set.inter_subset_right).isInducing.topologicalKrullDim_le

theorem locallyOfFiniteType_of_isAmb {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (h : IsAmb p) :
    LocallyOfFiniteType p := by
  obtain ⟨N, jN, _, hjN⟩ := h.isProjOver
  have := isProper_str k N
  have : IsProper p := hjN ▸ inferInstance
  infer_instance

theorem le_and_iff_of_dimFormula {R : Type} [CommRing R] [IsDomain R] {c : ℕ} (hR : DimFormula R c)
    (hs : Function.Surjective (Int.cast : ℤ → R)) {X Y : Scheme.{0}} (t : X ⟶ Sp ℤ) [LocallyOfFiniteType t]
    (π : Y ⟶ X) [LocallyOfFiniteType π] (y : Y) [Algebra R (X.residueField (π y))]
    [FaithfulSMul R (X.residueField (π y))] (d d' : ℕ) (hd : HasDim y d) (hd' : HasDim (π y) d') :
    d' ≤ d ∧ (π.residueDegree y ≠ 0 ↔ d = d') := by
  letI := (π.residueFieldMap y).hom.toAlgebra
  letI : Algebra R (Y.residueField y) := ((π.residueFieldMap y).hom.comp (algebraMap R _)).toAlgebra
  haveI : IsScalarTower R (X.residueField (π y)) (Y.residueField y) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : FaithfulSMul R (Y.residueField y) := (faithfulSMul_iff_algebraMap_injective _ _).2
    ((π.residueFieldMap y).hom.injective.comp (FaithfulSMul.algebraMap_injective R _))
  haveI : Algebra.EssFiniteType (X.residueField (π y)) (Y.residueField y) :=
    RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap π y)
  obtain ⟨e, h₁, h₂⟩ := exists_hasDim hR hs (π ≫ t) y
  obtain ⟨e', h₁', h₂'⟩ := exists_hasDim hR hs t (π y)
  obtain rfl : d = e + c := by exact_mod_cast hd.symm.trans h₂
  obtain rfl : d' = e' + c := by exact_mod_cast hd'.symm.trans h₂'
  have hadd := trdeg_add_eq R (X.residueField (π y)) (A := Y.residueField y)
  rw [h₁, h₁'] at hadd
  have hle : e' ≤ e := by exact_mod_cast (self_le_add_right _ _).trans_eq hadd
  refine ⟨by omega, ?_⟩
  change Module.finrank (X.residueField (π y)) (Y.residueField y) ≠ 0 ↔ _
  constructor
  · intro h
    have : Module.Finite (X.residueField (π y)) (Y.residueField y) := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero h)
    rw [trdeg_eq_zero, add_zero] at hadd
    have : e' = e := by exact_mod_cast hadd
    rw [this]
  · intro h
    obtain rfl : e = e' := by omega
    have h0 : Algebra.trdeg (X.residueField (π y)) (Y.residueField y) = 0 := by
      rcases (Cardinal.add_eq_left_iff).1 hadd with h | h
      · exact absurd (le_trans (le_max_left _ _) h) (not_le.2 Cardinal.natCast_lt_aleph0)
      · exact h
    have : Algebra.IsAlgebraic (X.residueField (π y)) (Y.residueField y) := trdeg_eq_zero_iff.1 h0
    have : Module.Finite (X.residueField (π y)) (Y.residueField y) := Algebra.finite_of_essFiniteType_of_isAlgebraic
    exact Module.finrank_pos.ne'

theorem dim_le_and_residueDegree_ne_zero_iff : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsAmb p → IsAmb q → ∀ (π : Y ⟶ X), π ≫ p = q → ∀ (y : Y) (d d' : ℕ), HasDim y d → HasDim (π y) d' → d' ≤ d ∧ (π.residueDegree y ≠ 0 ↔ d = d') := by
  intro k _ X Y p q hp hq π hπ y d d' hd hd'
  have := locallyOfFiniteType_of_isAmb hp
  have : LocallyOfFiniteType (π ≫ p) := hπ ▸ locallyOfFiniteType_of_isAmb hq
  have : LocallyOfFiniteType π := locallyOfFiniteType_of_comp π p
  have : IsFinite (spMap (Int.castRingHom k)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hp.finite)
  obtain ⟨l, hl⟩ := CharP.exists (X.residueField (π y))
  rcases CharP.char_is_prime_or_zero (X.residueField (π y)) l with h | rfl
  · haveI : Fact l.Prime := ⟨h⟩
    letI := ZMod.algebra (X.residueField (π y)) l
    exact le_and_iff_of_dimFormula (dimFormula_field (ZMod l)) (ZMod.intCast_surjective)
      (p ≫ spMap (Int.castRingHom k)) π y d d' hd hd'
  · haveI := CharP.charP_to_charZero (X.residueField (π y))
    exact le_and_iff_of_dimFormula dimFormula_int (fun n => ⟨n, rfl⟩)
      (p ≫ spMap (Int.castRingHom k)) π y d d' hd hd'

end GlobalTheory.DimDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesPresentationUpToOrderTensorProduct
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.TensPres

variable {k : Type} [CommRing k]

def ordIdeal (ρ : Type) (N : ℕ) : Ideal (MvPowerSeries ρ k) where
  carrier := {f | (N : ℕ∞) ≤ f.order}
  add_mem' {f g} hf hg := MvPowerSeries.le_order fun d hd => by
    rw [map_add (f := _), MvPowerSeries.coeff_of_lt_order (hd.trans_le hf),
      MvPowerSeries.coeff_of_lt_order (hd.trans_le hg), add_zero]
  zero_mem' := by simp
  smul_mem' c f hf := by
    change (N : ℕ∞) ≤ (c * f).order
    exact hf.trans (le_add_self.trans (MvPowerSeries.le_order_mul (f := c) (g := f)))

theorem mem_ordIdeal_order {ρ : Type} {N : ℕ} {f : MvPowerSeries ρ k} :
    f ∈ ordIdeal (k := k) ρ N ↔ (N : ℕ∞) ≤ f.order := Iff.rfl

theorem mem_ordIdeal {ρ : Type} {N : ℕ} {f : MvPowerSeries ρ k} :
    f ∈ ordIdeal (k := k) ρ N ↔ ∀ α : ρ →₀ ℕ, α.degree < N → coeff α f = 0 := by
  constructor
  · intro h α hα
    exact MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le (Nat.cast_lt.2 hα) ((mem_ordIdeal_order).1 h))
  · intro h
    exact (mem_ordIdeal_order).2 (MvPowerSeries.nat_le_order h)

theorem one_le_order_X {ρ : Type} (t : ρ) : (1 : ℕ∞) ≤ (X t : MvPowerSeries ρ k).order := by
  have := MvPowerSeries.nat_le_order (f := (X t : MvPowerSeries ρ k)) (n := 1) fun d hd => by
    have : d = 0 := by
      rw [← Finsupp.degree_eq_zero_iff]; omega
    subst this; simp
  exact_mod_cast this

theorem subst_mem_ordIdeal {ρ ρ' : Type} [Finite ρ] (e : ρ → ρ') {N : ℕ}
    {f : MvPowerSeries ρ k} (hf : f ∈ ordIdeal (k := k) ρ N) :
    subst (fun i => (X (e i) : MvPowerSeries ρ' k)) f ∈ ordIdeal (k := k) ρ' N := by
  have ha : HasSubst (fun i => (X (e i) : MvPowerSeries ρ' k)) :=
    hasSubst_of_constantCoeff_zero fun i => constantCoeff_X _
  have h1 : (1 : ℕ∞) ≤ ⨅ i, ((fun i => (X (e i) : MvPowerSeries ρ' k)) i).order :=
    le_iInf fun i => one_le_order_X (e i)
  have h2 := MvPowerSeries.le_order_subst ha f
  refine (mem_ordIdeal_order).2 ?_
  calc (N : ℕ∞) ≤ f.order := (mem_ordIdeal_order).1 hf
    _ = 1 * f.order := (one_mul _).symm
    _ ≤ _ := by gcongr
    _ ≤ _ := h2

end GlobalTheory.TensPres


open GlobalTheory.TensPres in
theorem GlobalTheory.evA_tensor_presents : ∀ (k : Type) [CommRing k] (σ τ : Type) [Finite σ] [Finite τ] (A B : Type) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] (x : σ → A) (hx : ∀ i, IsNilpotent (x i)) (y : τ → B) (hy : ∀ i, IsNilpotent (y i)) (hz : ∀ i, IsNilpotent (Sum.elim (fun i => x i ⊗ₜ[k] (1 : B)) (fun j => (1 : A) ⊗ₜ[k] y j) i)), Function.Surjective (evA k x hx) → Function.Surjective (evA k y hy) → Function.Surjective (evA k _ hz) ∧ ∀ N : ℕ, (∀ f, evA k x hx f = 0 → ∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → (∀ f, evA k y hy f = 0 → ∀ α : τ →₀ ℕ, α.degree < N → coeff α f = 0) → ∀ f, evA k _ hz f = 0 → ∀ α : (σ ⊕ τ) →₀ ℕ, α.degree < N → coeff α f = 0 := by
  intro k _ σ τ _ _ A B _ _ _ _ x hx y hy hz hsx hsy
  have hX : ∀ t, evA k _ hz (X t) =
      Sum.elim (fun i => x i ⊗ₜ[k] (1 : B)) (fun j => (1 : A) ⊗ₜ[k] y j) t :=
    fun t => GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate k (σ ⊕ τ) (A ⊗[k] B) _ hz t
  have hzX : ∀ t, IsNilpotent (evA k _ hz (X t)) := fun t => by rw [hX]; exact hz t
  have hxl : ∀ i, IsNilpotent (x i ⊗ₜ[k] (1 : B)) := fun i => hz (Sum.inl i)
  have hyr : ∀ j, IsNilpotent ((1 : A) ⊗ₜ[k] y j) := fun j => hz (Sum.inr j)
  have hL : ∀ f : MvPowerSeries σ k,
      evA k _ hz (subst (fun i => (X (Sum.inl i) : MvPowerSeries (σ ⊕ τ) k)) f) =
        evA k x hx f ⊗ₜ[k] (1 : B) := by
    intro f
    rw [(_root_.GlobalTheory.evA_subst_and_map k σ (A ⊗[k] B)).1 (σ ⊕ τ) (evA k _ hz) hzX _
      (fun i => constantCoeff_X _) _ hxl (fun i => by rw [hX]; rfl) f]
    exact ((_root_.GlobalTheory.evA_subst_and_map k σ A).2 (A ⊗[k] B) (Algebra.TensorProduct.includeLeft (S := k))
      x hx _ hxl (fun i => rfl) f).symm
  have hR : ∀ g : MvPowerSeries τ k,
      evA k _ hz (subst (fun j => (X (Sum.inr j) : MvPowerSeries (σ ⊕ τ) k)) g) =
        (1 : A) ⊗ₜ[k] evA k y hy g := by
    intro g
    rw [(_root_.GlobalTheory.evA_subst_and_map k τ (A ⊗[k] B)).1 (σ ⊕ τ) (evA k _ hz) hzX _
      (fun j => constantCoeff_X _) _ hyr (fun j => by rw [hX]; rfl) g]
    exact ((_root_.GlobalTheory.evA_subst_and_map k τ B).2 (A ⊗[k] B) Algebra.TensorProduct.includeRight
      y hy _ hyr (fun j => rfl) g).symm
  refine ⟨?_, ?_⟩
  · intro w
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul a b =>
      obtain ⟨f, rfl⟩ := hsx a
      obtain ⟨g, rfl⟩ := hsy b
      refine ⟨subst (fun i => (X (Sum.inl i) : MvPowerSeries (σ ⊕ τ) k)) f *
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (σ ⊕ τ) k)) g, ?_⟩
      rw [map_mul, hL, hR, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add u v hu hv =>
      obtain ⟨f, rfl⟩ := hu
      obtain ⟨g, rfl⟩ := hv
      exact ⟨f + g, map_add _ _ _⟩
  · intro N hNx hNy f hf α hα
    let J := ordIdeal (k := k) (σ ⊕ τ) N
    let mk := Ideal.Quotient.mkₐ k J
    have haL : HasSubst (fun i => (X (Sum.inl i) : MvPowerSeries (σ ⊕ τ) k)) :=
      hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
    have haR : HasSubst (fun j => (X (Sum.inr j) : MvPowerSeries (σ ⊕ τ) k)) :=
      hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
    let φA : MvPowerSeries σ k →ₐ[k] _ := mk.comp (substAlgHom haL)
    let φB : MvPowerSeries τ k →ₐ[k] _ := mk.comp (substAlgHom haR)
    have hkA : ∀ g ∈ RingHom.ker (evA k x hx), φA g = 0 := by
      intro g hg
      rw [RingHom.mem_ker] at hg
      simp only [φA, mk, AlgHom.comp_apply, coe_substAlgHom, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem]
      exact subst_mem_ordIdeal Sum.inl (mem_ordIdeal.2 (hNx g hg))
    have hkB : ∀ g ∈ RingHom.ker (evA k y hy), φB g = 0 := by
      intro g hg
      rw [RingHom.mem_ker] at hg
      simp only [φB, mk, AlgHom.comp_apply, coe_substAlgHom, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem]
      exact subst_mem_ordIdeal Sum.inr (mem_ordIdeal.2 (hNy g hg))
    let ΨA : A →ₐ[k] _ := (Ideal.Quotient.liftₐ _ φA hkA).comp
      (Ideal.quotientKerAlgEquivOfSurjective hsx).symm.toAlgHom
    let ΨB : B →ₐ[k] _ := (Ideal.Quotient.liftₐ _ φB hkB).comp
      (Ideal.quotientKerAlgEquivOfSurjective hsy).symm.toAlgHom
    have hΨA : ∀ g, ΨA (evA k x hx g) = φA g := by
      intro g
      have : (Ideal.quotientKerAlgEquivOfSurjective hsx).symm (evA k x hx g) =
          Ideal.Quotient.mk _ g := by
        rw [AlgEquiv.symm_apply_eq]; rfl
      change Ideal.Quotient.liftₐ _ φA hkA ((Ideal.quotientKerAlgEquivOfSurjective hsx).symm (evA k x hx g)) = _
      rw [this]
      rfl
    have hΨB : ∀ g, ΨB (evA k y hy g) = φB g := by
      intro g
      have : (Ideal.quotientKerAlgEquivOfSurjective hsy).symm (evA k y hy g) =
          Ideal.Quotient.mk _ g := by
        rw [AlgEquiv.symm_apply_eq]; rfl
      change Ideal.Quotient.liftₐ _ φB hkB ((Ideal.quotientKerAlgEquivOfSurjective hsy).symm (evA k y hy g)) = _
      rw [this]
      rfl
    let Ψ := Algebra.TensorProduct.lift ΨA ΨB (fun _ _ => Commute.all _ _)
    have hnil : ∀ t, IsNilpotent (mk (X t)) := by
      intro t
      refine ⟨N, ?_⟩
      rw [← map_pow]
      simp only [mk, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      refine (mem_ordIdeal_order).2 ?_
      calc (N : ℕ∞) = N • (1 : ℕ∞) := by simp
        _ ≤ N • (X t : MvPowerSeries (σ ⊕ τ) k).order := by gcongr; exact one_le_order_X t
        _ ≤ _ := MvPowerSeries.le_order_pow _
    have huniq := _root_.GlobalTheory.mvPowerSeries_algHom_ext_of_isNilpotent k (σ ⊕ τ) _ mk (Ψ.comp (evA k _ hz)) hnil (by
      intro t
      rw [AlgHom.comp_apply, hX]
      cases t with
      | inl i =>
        simp only [Sum.elim_inl, Ψ, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
        rw [← GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate k σ A x hx i, hΨA]
        simp only [φA, AlgHom.comp_apply, coe_substAlgHom, subst_X haL]
      | inr j =>
        simp only [Sum.elim_inr, Ψ, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
        rw [← GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate k τ B y hy j, hΨB]
        simp only [φB, AlgHom.comp_apply, coe_substAlgHom, subst_X haR])
    have hmk : mk f = 0 := by
      rw [huniq, AlgHom.comp_apply, hf, map_zero]
    simp only [mk, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at hmk
    exact mem_ordIdeal.1 hmk α hα
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveDegreeTwoExtensionStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_degree_two_extension : PrimitiveStructureSheafDegTwoVanish → PrimitiveExtendedDegTwoVanish := by
  first | exact @GlobalTheory.Obs.primE2_of_primO2 | exact GlobalTheory.Obs.primE2_of_primO2 | (intros; apply GlobalTheory.Obs.primE2_of_primO2 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedGenericFibreUniformisedTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.UMin.UnifPolFib

theorem polFib_of_unif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (χ : Sp V ⟶ S) (t' : SAB H (Sp V)), Nonempty (SABMap t' t χ) → Nonempty (PELUnif (IsLocalRing.maximalIdeal V) t') → ∃ g : ℕ, ∀ (R : Type) [CommRing R] (e : FractionRing V →+* R), PolFib t.G t.PP.L g (spMap e ≫ jK V ≫ χ) := by
  intro E _ _ _ H S t V _ _ _ _ χ t' ⟨hm⟩ ⟨P⟩
  refine ⟨P.A.g, fun R _ e => ?_⟩
  have hL : t.PP.L.IsLB := RigLB.isLB _
  have hL' : t'.PP.L.IsLB := RigLB.isLB _
  have hF : LBIso t'.PP.L (t.PP.L.pull hm.cm.F) := by
    obtain ⟨w, hw, -, -⟩ := hm.lin
    exact ⟨w, hw⟩
  have hα : IsGrpPullback P.A.A t'.G (jK V) (P.U.gen.inv.left ≫ pullback.fst t'.G.hom (jK V)) :=
    GlobalTheory.NeutralLevel.isGrpPullback_of_iso_inv (jK V) t'.G P.U.gen P.U.gen_hom
  have hLα : LBIso P.A.L (t'.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t'.G.hom (jK V))) := by
    obtain ⟨w, hw⟩ := P.U.ext
    have hA := P.A.isLB
    have hB : LBIso P.A.L ((P.A.L.pull P.U.gen.hom.left).pull P.U.gen.inv.left) := by
      have e : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
        rw [← Over.comp_left, P.U.gen.inv_hom_id, Over.id_left]
      have h1 := GlobalTheory.UMin.FibMove.lbIso_pull_comp hA P.U.gen.hom.left P.U.gen.inv.left
      rw [e] at h1
      exact LBIso.trans hA (pull_isLB hA _) (pull_isLB (pull_isLB hA _) _)
        (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hA) h1
    have hLG : P.U.LG.L.IsLB := RigLB.isLB _
    have h2 := GlobalTheory.ThetaAffineGlue.lbIso_comp hA (pull_isLB hA _) hLG hB ⟨w, hw⟩
    rw [P.bundle] at h2
    exact h2
  have h0 : PolFib t'.G t'.PP.L P.A.g (jK V) := ⟨P.A, _, rfl, hα, hLα⟩
  have h1 := (GlobalTheory.UMin.FibMove.polFib_move S (Sp V) t.G t.PP.L t'.G t'.PP.L χ hm.cm.F hL hL' hm.cart hF P.A.g
    (FractionRing V) (jK V)).2 R e h0
  have h2 := (GlobalTheory.UMin.FibMove.polFib_move S (Sp V) t.G t.PP.L t'.G t'.PP.L χ hm.cm.F hL hL' hm.cart hF P.A.g
    R (spMap e ≫ jK V)).1.mp h1
  rwa [Category.assoc] at h2

end GlobalTheory.UMin.UnifPolFib
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithAmbientVerticalOrArithmeticVariety
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

namespace GlobalTheory.MixHt

theorem isEmpty_cxPts_of_algebra_zmod {k : Type} [CommRing k] {Y : Scheme.{0}} (q : Y ⟶ Sp k)
    (l : ℕ) [Fact l.Prime] (_ : Algebra (ZMod l) Γ(Y, ⊤)) (σ : k →+* ℂ) : IsEmpty (CxPts q σ) := by
  refine ⟨fun y => ?_⟩
  let f : ZMod l →+* ℂ := (Scheme.ΓSpecIso (.of ℂ)).hom.hom.comp
    (y.1.appTop.hom.comp (algebraMap (ZMod l) Γ(Y, ⊤)))
  have h := map_natCast f l
  rw [ZMod.natCast_self, map_zero] at h
  exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h.symm

theorem amb_vertical_or_arithVar : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsAmb q → ∀ d : ℕ, topologicalKrullDim Y = d → (∃ (l : ℕ) (_ : Fact l.Prime), Nonempty (Algebra (ZMod l) Γ(Y, ⊤)) ∧ ∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)) ∨ ∃ e : ℕ, d = e + 1 ∧ IsArithVar q e := by
  intro k _ Y _ q hq d hd
  obtain ⟨ℓ, _⟩ := CharP.exists Γ(Y, ⊤)
  rcases CharP.char_is_prime_or_zero Γ(Y, ⊤) ℓ with hℓ | rfl
  · have : Fact ℓ.Prime := ⟨hℓ⟩
    exact .inl ⟨ℓ, this, ⟨ZMod.algebra _ ℓ⟩, fun σ => isEmpty_cxPts_of_algebra_zmod q ℓ (ZMod.algebra _ ℓ) σ⟩
  · have hc := CharP.charP_to_charZero Γ(Y, ⊤)
    obtain _ | e := d
    · exact absurd (by simpa using hd) (dim_ne_zero_of_isProjOver q hq.isProjOver hq.finite hc)
    · exact .inr ⟨e, rfl, hq.isDomain, hq.finite, ‹_›, hq.isProjOver,
        (flat_int_iff_charZero _).2 hc, hd⟩

end GlobalTheory.MixHt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedThetaSystemSectionGeneratesFieldFibresStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realisedThetaSystem_section_generates_field_fibres : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (K : Type) [Field K] (i : S.R →+* K), IsGenSec ρ.P.A ρ.P.L _ (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ i) := by
  intro o Ω _ _ _ _ S ρ K _ i
  exact GlobalTheory.UMin.isGenSec_real_pull o Ω S ρ K i
end

