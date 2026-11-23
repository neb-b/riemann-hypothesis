module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2164
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0117
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2158
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GmEqMapGm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Mum

def IsFrameOver {X : Scheme.{0}} (L : LB X) (W : X.Opens) (T : ∀ k, Γ(X, W ⊓ L.U k)ˣ) : Prop :=
  ∀ k k', res (inf_le_left : W ⊓ L.U k ⊓ (W ⊓ L.U k') ≤ W ⊓ L.U k) (T k) =
    res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
      W ⊓ L.U k ⊓ (W ⊓ L.U k') ≤ L.U k ⊓ L.U k') (L.g k k') *
    res (inf_le_right : W ⊓ L.U k ⊓ (W ⊓ L.U k') ≤ W ⊓ L.U k') (T k')

def FrameCarried {X : Scheme.{0}} (L : LB X) (W : X.Opens) (T : ∀ k, Γ(X, W ⊓ L.U k)ˣ) (f : X ⟶ X)
    (w : LB.Iso L (L.pull f)) : Prop :=
  ∀ (z : X) (j k : L.ι), z ∈ W → f z ∈ W → z ∈ L.U k → f z ∈ L.U j →
    gm f z (W ⊓ L.U j) (T j) = gw w (𝟙 X) z j k * gm (𝟙 X) z (W ⊓ L.U k) (T k)

theorem gm_eq_map_gm {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)ˣ) :
    gm f y U a = Units.map (f.stalkMap y).hom.toMonoidHom (gm (𝟙 X) (f y) U a) := by
  apply Units.ext
  rw [gm_val f y U h, Units.coe_map, gm_val (𝟙 X) (f y) U h]
  have := congrArg (fun q => q.hom a.val) (f.germ_stalkMap U y h)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  exact this.symm

end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem FrameCarried.ratio_fixed {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {W W' O : X.Opens}
    {T : ∀ k, Γ(X, W ⊓ L.U k)ˣ} {T' : ∀ k, Γ(X, W' ⊓ L.U k)ˣ} {f : X ⟶ X} {w : LB.Iso L (L.pull f)}
    (hT : FrameCarried L W T f w) (hT' : FrameCarried L W' T' f w) (hOW : O ≤ W) (hOW' : O ≤ W') (r : Γ(X, O)ˣ)
    (hr : ∀ (z : X) (k : L.ι), z ∈ O → z ∈ L.U k →
      gm (𝟙 X) z O r = gm (𝟙 X) z _ (T' k) * (gm (𝟙 X) z _ (T k))⁻¹)
    (h : O ≤ f ⁻¹ᵁ O) : (f.appLE O O h).hom r.val = r.val := by
  apply TopCat.Presheaf.section_ext X.sheaf O
  intro x hx
  obtain ⟨k, hk⟩ := exists_chart hL x
  have hfx : f x ∈ O := h hx
  obtain ⟨j, hj⟩ := exists_chart hL (f x)
  have key : gm f x O r = gm (𝟙 X) x O r := by
    rw [gm_eq_map_gm f x O hfx, hr (f x) j hfx hj, map_mul, map_inv,
      ← gm_eq_map_gm f x (W' ⊓ L.U j) (show f x ∈ W' ⊓ L.U j from ⟨hOW' hfx, hj⟩),
      ← gm_eq_map_gm f x (W ⊓ L.U j) (show f x ∈ W ⊓ L.U j from ⟨hOW hfx, hj⟩),
      hT' x j k (hOW' hx) (hOW' hfx) hk hj, hT x j k (hOW hx) (hOW hfx) hk hj, hr x k hx hk, _root_.mul_inv,
      _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul]
  have e1 := congrArg Units.val key
  rw [gm_val f x O hfx, gm_val (𝟙 X) x O hx] at e1
  refine Eq.trans ?_ (e1.trans ?_)
  · simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
    exact TopCat.Presheaf.germ_res_apply X.presheaf _ x hx _
  · rfl

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GraphLocalRingRegularParamsAndDim
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DiagLoc

theorem ennreal_volume_ratio_step_cancel (d : WithBot ℕ∞) (m n : ℕ) (hd : d + m = ((n + m : ℕ) : WithBot ℕ∞)) : d = n := by
  induction d using WithBot.recBotCoe with
  | bot =>
    exfalso
    simp at hd
    exact absurd hd.symm (by simp [WithBot.add_eq_bot])
  | coe e =>
    have h1 : e + (m : ℕ∞) = (n : ℕ∞) + (m : ℕ∞) := by exact_mod_cast hd
    have h2 : e = n := WithTop.add_right_cancel (ENat.natCast_ne_top m) h1
    subst h2
    rfl

theorem isLocModel_top {K : Type} [Field K] [Algebra ℂ K] [Algebra.EssFiniteType ℂ K] :
    IsLocModel (algebraMap ℂ K) (⊤ : Subring K) :=
  { const_mem := fun _ => Subring.mem_top _
    isLocalRing := (Subring.topEquiv (R := K)).symm.isLocalRing
    essFiniteType := by
      let e := (Subring.topEquiv (R := K)).symm
      exact RingHom.EssFiniteType.comp (RingHom.essFiniteType_algebraMap.mpr inferInstance)
        (RingHom.FiniteType.of_surjective e.toRingHom e.surjective).essFiniteType
    frac := fun f => ⟨f, Subring.mem_top _, 1, Subring.mem_top _, one_ne_zero, mul_one f⟩ }

variable {K κ' : Type} [Field K] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ']
  (L : Type) [Field L] [Algebra (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]

theorem maximalIdeal_eq_span (σ : K →ₐ[ℂ] κ') (n : ℕ) (x : Fin n → K)
    [Algebra.EssFiniteType ℂ K] (hx : TrBasis (algebraMap ℂ K) x) :
    IsLocalRing.maximalIdeal (loc L σ) =
      Ideal.span (Set.range fun i => toLoc L σ (x i ⊗ₜ[ℂ] 1 - 1 ⊗ₜ[ℂ] σ (x i))) := by
  obtain ⟨e, he1, he⟩ := GlobalTheory.FieldPair.exists_mul_ker_mem_span_trBasis_diff n x σ (⊤ : Subring K) hx
    isLocModel_top
  haveI hP : (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).IsPrime :=
    RingHom.ker_isPrime _
  have heP : e ∈ (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).primeCompl := by
    rw [Ideal.mem_primeCompl_iff]
    intro h
    rw [RingHom.mem_ker] at h
    rw [h] at he1
    exact zero_ne_one he1
  haveI : IsDomain (K ⊗[ℂ] κ') :=
    Function.Injective.isDomain (algebraMap (K ⊗[ℂ] κ') L) (IsFractionRing.injective (K ⊗[ℂ] κ') L)
  letI : Algebra (K ⊗[ℂ] κ') ↥(loc L σ) := Subalgebra.algebra (Localization.subalgebra.ofField L
    (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).primeCompl
    (Ideal.primeCompl_le_nonZeroDivisors _))
  haveI hloc : IsLocalization (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).primeCompl
      ↥(loc L σ) := by
    exact Localization.subalgebra.isLocalization_ofField (A := K ⊗[ℂ] κ') L _ _
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal
    (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))) ↥(loc L σ)]
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap]
    obtain ⟨u, hu⟩ := IsLocalization.map_units
      (M := (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).primeCompl)
      (S := ↥(loc L σ)) ⟨e, heP⟩
    have h1 := Ideal.mem_map_of_mem (algebraMap (K ⊗[ℂ] κ') ↥(loc L σ)) (he a ha)
    rw [Ideal.map_span, ← Set.range_comp] at h1
    have h2 : algebraMap (K ⊗[ℂ] κ') ↥(loc L σ) a =
        ((u⁻¹ : (↥(loc L σ))ˣ) : ↥(loc L σ)) * algebraMap (K ⊗[ℂ] κ') ↥(loc L σ) (e * a) := by
      rw [map_mul, show algebraMap (K ⊗[ℂ] κ') ↥(loc L σ) e = (u : ↥(loc L σ)) from hu.symm,
        ← mul_assoc, Units.inv_mul, one_mul]
    rw [h2]
    exact Ideal.mul_mem_left _ _ h1
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    refine Ideal.mem_map_of_mem (algebraMap (K ⊗[ℂ] κ') ↥(loc L σ)) ?_
    rw [RingHom.mem_ker]
    simp

theorem ringKrullDim_loc (σ : K →ₐ[ℂ] κ') (n : ℕ) (x : Fin n → K)
    [Algebra.EssFiniteType ℂ K] [Algebra.EssFiniteType ℂ κ'] (hx : TrBasis (algebraMap ℂ K) x) :
    ringKrullDim (loc L σ) = n := by
  haveI hP : (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).IsPrime := RingHom.ker_isPrime _
  haveI : IsDomain (K ⊗[ℂ] κ') :=
    Function.Injective.isDomain (algebraMap (K ⊗[ℂ] κ') L) (IsFractionRing.injective (K ⊗[ℂ] κ') L)
  letI : Algebra (K ⊗[ℂ] κ') ↥(loc L σ) := Subalgebra.algebra (Localization.subalgebra.ofField L
    (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).primeCompl (Ideal.primeCompl_le_nonZeroDivisors _))
  haveI hloc : IsLocalization (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).primeCompl ↥(loc L σ) :=
    Localization.subalgebra.isLocalization_ofField (A := K ⊗[ℂ] κ') L _ _
  letI : Algebra ℂ ↥(loc L σ) :=
    ((algebraMap (K ⊗[ℂ] κ') ↥(loc L σ)).comp (algebraMap ℂ (K ⊗[ℂ] κ'))).toAlgebra
  haveI : IsScalarTower ℂ (K ⊗[ℂ] κ') ↥(loc L σ) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.EssFiniteType ℂ (K ⊗[ℂ] κ') := Algebra.EssFiniteType.comp ℂ K (K ⊗[ℂ] κ')
  haveI : Algebra.EssFiniteType (K ⊗[ℂ] κ') ↥(loc L σ) :=
    Algebra.EssFiniteType.of_isLocalization _ (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).primeCompl
  haveI : Algebra.EssFiniteType ℂ ↥(loc L σ) := Algebra.EssFiniteType.comp ℂ (K ⊗[ℂ] κ') ↥(loc L σ)
  have hg : ∀ y : (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).primeCompl,
      IsUnit ((Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ')).toRingHom (y : K ⊗[ℂ] κ')) := by
    intro y
    rw [isUnit_iff_ne_zero]
    intro h
    exact y.2 (RingHom.mem_ker.mpr h)
  letI : Algebra ↥(loc L σ) κ' := (IsLocalization.lift hg).toAlgebra
  haveI : IsScalarTower ℂ ↥(loc L σ) κ' := IsScalarTower.of_algebraMap_eq fun c =>
    ((IsLocalization.lift_eq hg (algebraMap ℂ (K ⊗[ℂ] κ') c)).trans
      ((Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ')).commutes c)).symm
  have hsurj : Function.Surjective (algebraMap ↥(loc L σ) κ') := fun b =>
    ⟨algebraMap (K ⊗[ℂ] κ') ↥(loc L σ) (1 ⊗ₜ b), by
      show IsLocalization.lift hg _ = b
      rw [IsLocalization.lift_eq]
      simp⟩
  have hx' : IsTranscendenceBasis ℂ x := by
    unfold TrBasis at hx
    rwa [toAlgebra_algebraMap] at hx
  have hK : Algebra.trdeg ℂ K = n := by
    rw [← hx'.cardinalMk_eq_trdeg, Cardinal.mk_fin]
  have hfin : Algebra.trdeg ℂ κ' < Cardinal.aleph0 := by
    exact trdeg_lt_aleph0 ℂ κ'
  have hm : Algebra.trdeg ℂ κ' = ((Algebra.trdeg ℂ κ').toNat : Cardinal) :=
    (Cardinal.cast_toNat_of_lt_aleph0 hfin).symm
  haveI : FaithfulSMul ℂ K :=
    (faithfulSMul_iff_algebraMap_injective ℂ K).mpr (algebraMap ℂ K).injective
  haveI : FaithfulSMul K (K ⊗[ℂ] κ') :=
    (faithfulSMul_iff_algebraMap_injective K (K ⊗[ℂ] κ')).mpr (algebraMap K (K ⊗[ℂ] κ')).injective
  haveI : FaithfulSMul ℂ (K ⊗[ℂ] κ') :=
    (faithfulSMul_iff_algebraMap_injective ℂ (K ⊗[ℂ] κ')).mpr (algebraMap ℂ (K ⊗[ℂ] κ')).injective
  haveI : FaithfulSMul (K ⊗[ℂ] κ') ↥(loc L σ) :=
    (faithfulSMul_iff_algebraMap_injective (K ⊗[ℂ] κ') ↥(loc L σ)).mpr
      (IsLocalization.injective ↥(loc L σ) (Ideal.primeCompl_le_nonZeroDivisors (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ')))))
  haveI : Algebra.IsAlgebraic (K ⊗[ℂ] κ') ↥(loc L σ) :=
    IsLocalization.isAlgebraic ↥(loc L σ) (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).primeCompl
  have hR : Algebra.trdeg ℂ ↥(loc L σ) = ((n + (Algebra.trdeg ℂ κ').toNat : ℕ) : Cardinal) := by
    have h0 : Algebra.trdeg (K ⊗[ℂ] κ') ↥(loc L σ) = 0 := trdeg_eq_zero
    rw [← trdeg_add_eq ℂ (K ⊗[ℂ] κ') (A := ↥(loc L σ)), h0, add_zero,
      ← trdeg_add_eq ℂ K (A := K ⊗[ℂ] κ'), _root_.GlobalTheory.trdeg_complex_baseChange_eq, hK, hm]
    push_cast
    rfl
  exact ennreal_volume_ratio_step_cancel _ _ _
    (GlobalTheory.LocModelDim.ringKrullDim_add_trdeg (k := ℂ) (R := ↥(loc L σ)) (Ω := κ') hsurj hm hR)

theorem maximalIdeal_eq_span_and_ringKrullDim : ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K]
  [Algebra ℂ κ'] [Algebra ℂ L] [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L]
  [IsFractionRing (K ⊗[ℂ] κ') L] (σ : K →ₐ[ℂ] κ') (n : ℕ) (x : Fin n → K),
  Algebra.EssFiniteType ℂ K → Algebra.EssFiniteType ℂ κ' → TrBasis (algebraMap ℂ K) x →
  IsLocalRing.maximalIdeal (GlobalTheory.DiagLoc.loc L σ) =
      Ideal.span (Set.range fun i => GlobalTheory.DiagLoc.toLoc L σ (x i ⊗ₜ[ℂ] 1 - 1 ⊗ₜ[ℂ] σ (x i))) ∧
    ringKrullDim (GlobalTheory.DiagLoc.loc L σ) = n := by
  intro K κ' L _ _ _ _ _ _ _ _ _ σ n x hK hκ hx
  exact ⟨maximalIdeal_eq_span L σ n x hx, ringKrullDim_loc L σ n x hx⟩

end GlobalTheory.DiagLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLawDescendsGaloisInvariantOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.LawDesc

section

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S} (N : Near π G)

theorem pt_unique {T : Scheme.{0}} {s : T ⟶ S} {a : T ⟶ N.U.left} {x x' : T ⟶ G.left}
    (h : N.Pt s a x) (h' : N.Pt s a x') : x = x' := by
  obtain ⟨x₀, h₁, h₂, rfl⟩ := h
  obtain ⟨x₁, h₃, h₄, rfl⟩ := h'
  rw [pullback.hom_ext (h₁.trans h₃.symm) (h₂.trans h₄.symm)]

theorem pt_unique_left {T : Scheme.{0}} {s s' : T ⟶ S} {a a' : T ⟶ N.U.left} {x : T ⟶ G.left}
    (h : N.Pt s a x) (h' : N.Pt s' a' x) : a = a' := by
  obtain ⟨x₀, rfl, -, h₂⟩ := h
  obtain ⟨x₁, rfl, -, h₄⟩ := h'
  have := N.isOpen
  rw [(cancel_mono N.u).1 (h₂.trans h₄.symm)]

theorem pt_comp {T T' : Scheme.{0}} (k : T' ⟶ T) {s : T ⟶ S} {a : T ⟶ N.U.left} {x : T ⟶ G.left}
    (h : N.Pt s a x) : N.Pt (k ≫ s) (k ≫ a) (k ≫ x) := by
  obtain ⟨x₀, rfl, rfl, rfl⟩ := h
  exact ⟨k ≫ x₀, Category.assoc _ _ _, Category.assoc _ _ _, Category.assoc _ _ _⟩

theorem pt_over {T : Scheme.{0}} {s : T ⟶ S} {a : T ⟶ N.U.left} {x : T ⟶ G.left}
    (h : N.Pt s a x) : s ≫ π = a ≫ N.U.hom := by
  obtain ⟨x₀, rfl, rfl, -⟩ := h
  rw [Category.assoc, Category.assoc, pullback.condition]

theorem pt_exists {T : Scheme.{0}} {s : T ⟶ S} {a : T ⟶ N.U.left} (h : s ≫ π = a ≫ N.U.hom) :
    ∃ x : Over.mk s ⟶ G, N.Pt s a x.left :=
  ⟨Over.homMk (pullback.lift a s h.symm ≫ N.u) (by
      change (pullback.lift a s h.symm ≫ N.u) ≫ G.hom = s
      rw [Category.assoc, N.u_over, pullback.lift_snd]),
    pullback.lift a s h.symm, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, rfl⟩

variable [GrpObj G]

def Prod {T : Scheme.{0}} (s : T ⟶ S) (v : T ⟶ (N.U ⊗ N.U).left) (z : T ⟶ G.left) : Prop :=
  ∃ x y : Over.mk s ⟶ G, N.Pt s (v ≫ (fst N.U N.U).left) x.left ∧ N.Pt s (v ≫ (snd N.U N.U).left) y.left ∧
    (x * y).left = z

theorem prod_exists {T : Scheme.{0}} {s : T ⟶ S} {v : T ⟶ (N.U ⊗ N.U).left} (h : s ≫ π = v ≫ (N.U ⊗ N.U).hom) :
    ∃ z, Prod N s v z := by
  obtain ⟨x, hx⟩ := pt_exists N (s := s) (a := v ≫ (fst N.U N.U).left)
    (by rw [h, Category.assoc]; exact congrArg (v ≫ ·) (Over.w (fst N.U N.U)).symm)
  obtain ⟨y, hy⟩ := pt_exists N (s := s) (a := v ≫ (snd N.U N.U).left)
    (by rw [h, Category.assoc]; exact congrArg (v ≫ ·) (Over.w (snd N.U N.U)).symm)
  exact ⟨_, x, y, hx, hy, rfl⟩

theorem prod_unique {T : Scheme.{0}} {s : T ⟶ S} {v : T ⟶ (N.U ⊗ N.U).left} {z z' : T ⟶ G.left}
    (h : Prod N s v z) (h' : Prod N s v z') : z = z' := by
  obtain ⟨x, y, hx, hy, rfl⟩ := h
  obtain ⟨x', y', hx', hy', rfl⟩ := h'
  obtain rfl : x = x' := Over.OverMorphism.ext (pt_unique N hx hx')
  obtain rfl : y = y' := Over.OverMorphism.ext (pt_unique N hy hy')
  rfl

theorem prod_over {T : Scheme.{0}} {s : T ⟶ S} {v : T ⟶ (N.U ⊗ N.U).left} {z : T ⟶ G.left}
    (h : Prod N s v z) : z ≫ G.hom = s := by
  obtain ⟨x, y, -, -, rfl⟩ := h
  exact Over.w (x * y)

theorem prod_comp {T T' : Scheme.{0}} (k : T' ⟶ T) {s : T ⟶ S} {v : T ⟶ (N.U ⊗ N.U).left} {z : T ⟶ G.left}
    (h : Prod N s v z) : Prod N (k ≫ s) (k ≫ v) (k ≫ z) := by
  obtain ⟨x, y, hx, hy, rfl⟩ := h
  let k' : Over.mk (k ≫ s) ⟶ Over.mk s := Over.homMk k rfl
  refine ⟨k' ≫ x, k' ≫ y, ?_, ?_, ?_⟩
  · rw [Category.assoc]; exact pt_comp N k hx
  · rw [Category.assoc]; exact pt_comp N k hy
  · rw [← comp_mul]; rfl

theorem prod_act {c : S ⟶ S} {φ : G.left ⟶ G.left} (hφ : IsGrpPullback G G c φ)
    (hN : ∀ (T : Scheme.{0}) (s : T ⟶ S) (u : T ⟶ N.U.left) (x : T ⟶ G.left),
      N.Pt s u x → N.Pt (s ≫ c) u (x ≫ φ))
    {T : Scheme.{0}} {s : T ⟶ S} {v : T ⟶ (N.U ⊗ N.U).left} {z : T ⟶ G.left}
    (h : Prod N s v z) : Prod N (s ≫ c) v (z ≫ φ) := by
  obtain ⟨x, y, hx, hy, rfl⟩ := h
  have hx' := hN _ _ _ _ hx
  have hy' := hN _ _ _ _ hy
  obtain ⟨x₀, hx₀⟩ := pt_exists N (pt_over N hx')
  obtain ⟨y₀, hy₀⟩ := pt_exists N (pt_over N hy')
  exact ⟨x₀, y₀, hx₀, hy₀, hφ.2 (Over.mk s) x y x₀ y₀ (pt_unique N hx₀ hx') (pt_unique N hy₀ hy')⟩

theorem law_of_isAffineQuotient {Γ : Type} [Group Γ] [Finite Γ] {α : Γ →* Aut S} (hq : IsAffineQuotient α π)
    (φ : Γ → (G.left ⟶ G.left)) (hφ : ∀ g, IsGrpPullback G G (α g).asIso.hom (φ g))
    (hN : ∀ g (T : Scheme.{0}) (s : T ⟶ S) (u : T ⟶ N.U.left) (x : T ⟶ G.left),
      N.Pt s u x → N.Pt (s ≫ (α g).asIso.hom) u (x ≫ φ g)) : N.Law := by
  have := N.smooth
  have := N.isOpen
  have hy : Flat (N.U ⊗ N.U).hom := by
    change Flat (pullback.fst N.U.hom N.U.hom ≫ N.U.hom)
    infer_instance
  have quot : ∀ {Y : Scheme.{0}} (y : Y ⟶ Sp R) [Flat y],
      IsAffineQuotient (pullbackAction α π hq.comp_eq y) (pullback.snd π y) := fun y _ =>
    hq.of_isPullback (IsPullback.of_hasPullback π y) (pullbackAction_fst α π hq.comp_eq y)
      (pullbackAction_snd α π hq.comp_eq y)
  have equiv : ∀ {Y : Scheme.{0}} (y : Y ⟶ Sp R) (j : Y ⟶ (N.U ⊗ N.U).left) (z : pullback π y ⟶ G.left),
      Prod N (pullback.fst π y) (pullback.snd π y ≫ j) z →
      ∀ g, (pullbackAction α π hq.comp_eq y g).asIso.hom ≫ z = z ≫ φ g := fun y j z hz g => by
    have h₁ := prod_comp N (pullbackAction α π hq.comp_eq y g).asIso.hom hz
    rw [pullbackAction_fst, pullbackAction_snd_assoc] at h₁
    exact prod_unique N h₁ (prod_act N (hφ g) (hN g) hz)
  obtain ⟨z₀, hz₁⟩ := prod_exists N (pullback.condition (f := π) (g := (N.U ⊗ N.U).hom))
  have hrange : ∀ g, pullback.map N.U.hom π N.U.hom π (𝟙 _) (α g).asIso.hom (𝟙 _) (by simp) (by simp [hq.comp_eq]) ≫ N.u
      = N.u ≫ φ g := fun g => by
    refine pt_unique N (s := pullback.snd N.U.hom π ≫ (α g).asIso.hom) (a := pullback.fst N.U.hom π)
      ⟨_, ?_, pullback.lift_snd _ _ _, rfl⟩
      (hN g _ _ _ _ ⟨𝟙 _, Category.id_comp _, Category.id_comp _, Category.id_comp _⟩)
    exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  obtain ⟨V, hV⟩ := (quot (N.U ⊗ N.U).hom).exists_preimage_eq (U := z₀ ⁻¹ᵁ N.u.opensRange) fun g w hw => by
    obtain ⟨w', hw'⟩ := hw
    change ((pullbackAction α π hq.comp_eq (N.U ⊗ N.U).hom g).asIso.hom ≫ z₀) w ∈ Set.range N.u
    rw [equiv _ (𝟙 _) z₀ (by rw [Category.comp_id]; exact hz₁) g, Scheme.Hom.comp_apply, ← hw',
      ← Scheme.Hom.comp_apply, ← hrange g, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  let y : V.toScheme ⟶ Sp R := V.ι ≫ (N.U ⊗ N.U).hom
  let k : pullback π y ⟶ pullback π (N.U ⊗ N.U).hom :=
    pullback.lift (pullback.fst π y) (pullback.snd π y ≫ V.ι) (by rw [pullback.condition, Category.assoc])
  have hk : k ≫ pullback.snd _ _ = pullback.snd π y ≫ V.ι := pullback.lift_snd _ _ _
  have hz : Prod N (pullback.fst π y) (pullback.snd π y ≫ V.ι) (k ≫ z₀) := by
    have := prod_comp N k hz₁
    rwa [hk, pullback.lift_fst] at this
  have hsub : Set.range (k ≫ z₀) ⊆ Set.range N.u := by
    rintro _ ⟨w, rfl⟩
    have : k w ∈ pullback.snd π (N.U ⊗ N.U).hom ⁻¹ᵁ V := by
      change (k ≫ pullback.snd π (N.U ⊗ N.U).hom) w ∈ V
      rw [hk, Scheme.Hom.comp_apply]
      exact (pullback.snd π y w).2
    rw [hV] at this
    exact this
  let l := IsOpenImmersion.lift N.u (k ≫ z₀) hsub
  have hl : l ≫ N.u = k ≫ z₀ := IsOpenImmersion.lift_fac _ _ _
  have hf : N.Pt (pullback.fst π y) (l ≫ pullback.fst _ _) (k ≫ z₀) :=
    ⟨l, rfl, by rw [← N.u_over, ← Category.assoc, hl, prod_over N hz], hl⟩
  obtain ⟨m, hm⟩ := (quot y).exists_comp_eq (l ≫ pullback.fst _ _) fun g => by
    have h₁ := pt_comp N (pullbackAction α π hq.comp_eq y g).asIso.hom hf
    rw [equiv y V.ι _ hz g] at h₁
    exact pt_unique_left N h₁ (hN g _ _ _ _ hf)
  refine ⟨V, m, fun z hz₀ => ?_, (quot y).hom_ext ?_, fun T v s a b ha hb => ?_⟩
  · obtain ⟨w, rfl⟩ := (quot (N.U ⊗ N.U).hom).surjective.surj z
    change w ∈ pullback.snd π (N.U ⊗ N.U).hom ⁻¹ᵁ V
    rw [hV]
    refine N.all (z₀ w) ?_
    rw [← hz₀, ← Scheme.Hom.comp_apply z₀, prod_over N hz₁, ← Scheme.Hom.comp_apply, pullback.condition,
      Scheme.Hom.comp_apply]
  · rw [← Category.assoc, hm, ← pt_over N hf, pullback.condition]
  · have hs : s ≫ π = v ≫ y := by
      rw [pt_over N ha, Category.assoc, Category.assoc]
      exact congrArg (fun t => v ≫ V.ι ≫ t) (Over.w (fst N.U N.U))
    have h₁ := pt_comp N (pullback.lift s v hs) hf
    have h₂ := prod_comp N (pullback.lift s v hs) hz
    rw [pullback.lift_fst, pullback.lift_snd_assoc] at h₂
    have h₃ : Prod N s (v ≫ V.ι) (a * b).left :=
      ⟨a, b, by rw [Category.assoc]; exact ha, by rw [Category.assoc]; exact hb, rfl⟩
    rw [← hm, pullback.lift_fst, pullback.lift_snd_assoc, prod_unique N h₂ h₃] at h₁
    exact h₁

end

end GlobalTheory.Mum.LawDesc

namespace GlobalTheory.Mum

theorem law_of_galAct_invariant : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∀ N : Near (spMap ρ) G', (∀ σ (T : Scheme.{0}) (s : T ⟶ Sp R') (u : T ⟶ N.U.left) (x : T ⟶ G'.left), N.Pt s u x → N.Pt (s ≫ spMap (Gal.hom σ)) u (x ≫ a.act σ)) → N.Law := by
  intro R _ _ _ _ R' _ _ _ ρ hρ hG D D' hD A' G' _ _ _ U' a N hN
  have := hG.1
  let _ : Algebra R R' := ρ.toAlgebra
  let _ : MulSemiringAction (R' ≃+* R') R' := RingAut.applyMulSemiringAction
  let _ : MulSemiringAction (Gal ρ) R' := Subgroup.mulSemiringAction _
  have : SMulCommClass (Gal ρ) R R' := ⟨fun σ r x => by
    change σ.1 (ρ r * x) = ρ r * σ.1 x
    rw [map_mul, σ.2 r]⟩
  have : FaithfulSMul R R' := (faithfulSMul_iff_algebraMap_injective _ _).2 hρ.2.1
  have : Algebra.IsInvariant R R' (Gal ρ) := ⟨fun x hx => hG.2 x fun σ hσ => hx ⟨σ, hσ⟩⟩
  have hq : IsAffineQuotient (specAction (Gal ρ) R') (spMap ρ) := isAffineQuotient_spec R R'
  have e : ∀ σ : Gal ρ, (specAction (Gal ρ) R' σ).asIso.hom = spMap (Gal.hom σ⁻¹) := fun σ => by
    rw [specAction_hom]; rfl
  refine LawDesc.law_of_isAffineQuotient N hq (fun σ => a.act σ⁻¹) (fun σ => ?_) fun σ => ?_
  · rw [e]; exact a.cart σ⁻¹
  · rw [e]; exact hN σ⁻¹

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RMDeform

theorem exists_lift_abelian (GD : GlobalTheory.Published.GrothendieckDeformation) (ADR : GlobalTheory.Published.AbelianDeRham)
    {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} (κ : DividedPowers I) (hκ : IsNilDP κ) (π : R →+* R₀)
    (hπ : Function.Surjective π) (hI : RingHom.ker π = I) {g : ℕ}
    {A₀ : Over (Sp R₀)} [GrpObj A₀] {A : Over (Sp R)} [GrpObj A] {i : A₀.left ⟶ A.left}
    (h : IsGrpPullback A₀ A (spMap π) i) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (E : Submodule R (Crys κ (spMap π) A₀)) (hE : ∃ N, IsCompl E N)
    (hF : ∀ y : HdR A₀, y ∈ Fil A₀ ↔ ∃ d ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor κ hI A₀).Corr d y) :
    ∃ (A' : Over (Sp R)) (_ : GrpObj A') (i' : A₀.left ⟶ A'.left) (h' : IsGrpPullback A₀ A' (spMap π) i'),
      IsAbelianScheme A' ∧ SmoothOfRelativeDimension g A'.hom ∧ liftFil κ h' = E := by
  obtain ⟨HC, HL, -⟩ := GD R I κ hκ R₀ π hπ hI
  have b := (HC g A₀ A i h hA hg).1
  have c := HC.crysToDR_bijective h hA hg
  obtain ⟨N, hN⟩ := hE
  have adm : GlobalTheory.Published.GrothendieckMessing.IsAdmissible h (E.map (crysToDR κ h)) := by
    refine ⟨⟨N.map (crysToDR κ h), (Submodule.orderIsoMapComap (LinearEquiv.ofBijective _ c)).isCompl hN⟩,
      fun y ↦ ?_⟩
    rw [hF]
    constructor
    · rintro ⟨d, hd, e⟩
      exact ⟨_, ⟨d, hd, rfl⟩, (GlobalTheory.Published.GrothendieckMessing.corr_crysToDR_iff hI h b.2 d y).2 e⟩
    · rintro ⟨_, ⟨d, hd, rfl⟩, e⟩
      exact ⟨d, hd, (GlobalTheory.Published.GrothendieckMessing.corr_crysToDR_iff hI h b.2 d y).1 e⟩
  obtain ⟨A', _, i', h', hA', hg', e⟩ := HL g A₀ A i h hA hg _ adm
  exact ⟨A', inferInstance, i', h', hA', hg', by rw [e, Submodule.comap_map_eq_of_injective c.1]⟩

theorem lbIso_pull_square {X₀ X Y₀ Y : Scheme.{0}} {P : LB X} {P₀ : LB X₀} (hP : P.IsLB) (hP₀ : P₀.IsLB)
    {l : X₀ ⟶ X} (e : LBIso (P.pull l) P₀) (a₀ : Y₀ ⟶ X₀) (a : Y ⟶ X) (y : Y₀ ⟶ Y) (w : a₀ ≫ l = y ≫ a) :
    LBIso (P₀.pull a₀) ((P.pull a).pull y) := by
  refine (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hP₀ _) (pull_isLB (pull_isLB hP _) _)).1 ?_
  rw [GlobalTheory.CechPic.cls_pull hP₀, ← (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hP l) hP₀).2 e, GlobalTheory.CechPic.cls_pull hP,
    GlobalTheory.CechPic.cls_pull (pull_isLB hP a), GlobalTheory.CechPic.cls_pull hP, ← GlobalTheory.CechPic.pull_comp,
    ← GlobalTheory.CechPic.pull_comp, w]

end GlobalTheory.RMDeform
end
end

