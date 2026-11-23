module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1044
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1112
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBigLineBundlePullbackFieldExtensionIff
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

namespace GlobalTheory.BigFieldChange

theorem isBig_pull_iff : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k)
    (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → IsProjOver q →
    topologicalKrullDim X = topologicalKrullDim Y → ∀ L : LB Y, L.IsLB →
    ((letI := algebraΓOfHom q; IsBig E (L.pull π)) ↔ (letI := algebraΓOfHom p; IsBig k L)) := by
  intro k E _ _ _ Y X p q π H hp hq hd L hL
  letI := algebraΓOfHom p
  letI := algebraΓOfHom q
  have : IsProper p := by
    obtain ⟨N, i, hi, e⟩ := hp
    have := isProper_str k N
    rw [← e]
    infer_instance
  have hL' := LB.isLB_pull hL π
  have e : ∀ m : ℕ, lbH0 E (lbPow (L.pull π) m) = lbH0 k (lbPow L m) := fun m => by
    rw [lineBundleGlobalSectionsDim_congr_picardClass (isLB_lbPow hL' m) (LB.isLB_pull (isLB_lbPow hL m) π)
      (by rw [cls_lbPow hL', cls_pull hL, cls_pull (isLB_lbPow hL m), cls_lbPow hL, map_nsmul])]
    exact FieldChangeInter.hdim_pull H (isLB_lbPow hL m) 0
  constructor
  · intro h
    obtain ⟨D, hD, c, hc, hm⟩ := h.3
    exact ⟨hL, fun m => finite_coh_zero_twist_of_isProjOver (f := p) (fun _ => rfl) hp (isLB_lbPow hL m),
      D, hd.symm.trans hD, c, hc, hm.mono fun m hm => hm.trans_eq (congrArg _ (e m))⟩
  · intro h
    obtain ⟨D, hD, c, hc, hm⟩ := h.3
    exact ⟨hL', fun m => finite_coh_zero_twist_of_isProjOver (f := q) (fun _ => rfl) hq (isLB_lbPow hL' m),
      D, hd.trans hD, c, hc, hm.mono fun m hm => hm.trans_eq (congrArg _ (e m).symm)⟩

end GlobalTheory.BigFieldChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBirationalModelIdAndComp
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem isModel_id (X : Scheme.{0}) [IsIntegral X] : IsModel (𝟙 X) (RingHom.id X.functionField) := by
  refine { gen := rfl, deg := Scheme.Hom.residueDegree_id _, compat := ?_ }
  intro y a
  simp only [RingHom.id_apply, Scheme.Hom.stalkMap_id]
  rfl

theorem IsModel.comp {X Y Z : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z] {π : Y ⟶ X} {π' : Z ⟶ Y}
    {φ : X.functionField →+* Y.functionField} {φ' : Y.functionField →+* Z.functionField}
    (h : IsModel π φ) (h' : IsModel π' φ') : IsModel (π' ≫ π) (φ'.comp φ) := by
  refine { gen := ?_, deg := ?_, compat := ?_ }
  · show π (π' (genericPoint Z)) = genericPoint X
    rw [h'.gen, h.gen]
  · rw [GlobalTheory.CurveDegreesCompare.residueDegree_comp π' π (genericPoint Z), h'.deg]
    rw [h'.gen, h.deg]
  · intro z a
    refine (congrArg φ' (h.compat (π' z) a)).trans ((h'.compat z _).trans ?_)
    rw [Scheme.Hom.stalkMap_comp]
    rfl

theorem isModel_id_and_comp : ∀ (X Y Z : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsIntegral Z] (π : Y ⟶ X) (π' : Z ⟶ Y)
    (φ : X.functionField →+* Y.functionField) (φ' : Y.functionField →+* Z.functionField),
    IsModel (𝟙 X) (RingHom.id _) ∧ (IsModel π φ → IsModel π' φ' → IsModel (π' ≫ π) (φ'.comp φ)) :=
  fun X _ _ _ _ _ _ _ _ _ => ⟨isModel_id X, fun h h' => h.comp h'⟩

end GlobalTheory.HSNef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDomainTensorComplex
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.TensorFields

theorem exists_finset_lift {k κ K : Type} [Field k] [Field κ] [Field K] [Algebra k κ] [Algebra k K]
    (x : κ ⊗[k] K) : ∃ S : Finset K, ∀ T : Finset K, S ⊆ T →
      ∃ x' : κ ⊗[k] (Algebra.adjoin k (T : Set K)),
        Algebra.TensorProduct.map (AlgHom.id k κ) (Algebra.adjoin k (T : Set K)).val x' = x := by
  classical
  obtain ⟨P, rfl⟩ := TensorProduct.exists_finset x
  refine ⟨P.image Prod.snd, fun T hT => ?_⟩
  refine ⟨∑ i ∈ P.attach, i.1.1 ⊗ₜ[k] (⟨i.1.2, Algebra.subset_adjoin
    (hT (Finset.mem_image_of_mem Prod.snd i.2))⟩ : Algebra.adjoin k (T : Set K)), ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, Subalgebra.coe_val]
  exact Finset.sum_attach P (fun i => i.1 ⊗ₜ[k] i.2)

theorem isDomain_tensor_complex : ∀ (K κ : Type) [Field K] [Field κ] [Algebra ℂ K] [Algebra ℂ κ],
    IsDomain (K ⊗[ℂ] κ) := by
  classical
  intro K κ _ _ _ _
  suffices h : IsDomain (κ ⊗[ℂ] K) from (Algebra.TensorProduct.comm ℂ K κ).toMulEquiv.isDomain
  haveI : Nontrivial (κ ⊗[ℂ] K) := inferInstance
  refine @NoZeroDivisors.to_isDomain _ _ _ ⟨fun {x y} hxy => ?_⟩
  obtain ⟨S₁, h₁⟩ := exists_finset_lift (k := ℂ) x
  obtain ⟨S₂, h₂⟩ := exists_finset_lift (k := ℂ) y
  let A := Algebra.adjoin ℂ ((S₁ ∪ S₂ : Finset K) : Set K)
  obtain ⟨x', hx'⟩ := h₁ (S₁ ∪ S₂) Finset.subset_union_left
  obtain ⟨y', hy'⟩ := h₂ (S₁ ∪ S₂) Finset.subset_union_right
  haveI : Algebra.FiniteType ℂ A := ⟨(Subalgebra.fg_top _).mpr (Subalgebra.fg_adjoin_finset _)⟩
  haveI : IsDomain A := inferInstance
  haveI : IsDomain (κ ⊗[ℂ] A) := GlobalTheory.GeomComp.isDomain_tensor_of_isAlgClosed ℂ A κ
  let φ := Algebra.TensorProduct.map (AlgHom.id ℂ κ) A.val
  have hφ : Function.Injective φ :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := κ) A.val.toLinearMap Subtype.val_injective
  have h0 : x' * y' = 0 := hφ (by rw [map_mul, hx', hy', hxy, map_zero])
  rcases mul_eq_zero.mp h0 with h | h
  · left; rw [← hx', h, map_zero]
  · right; rw [← hy', h, map_zero]

end GlobalTheory.TensorFields
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEffQDivAddOfIsQCart
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem isEffQDiv_add {X : Scheme.{0}} {Δ D : X → ℚ} (hΔ : IsEffQDiv Δ) (hD : IsEffQDiv D) :
    IsEffQDiv (Δ + D) := by
  refine ⟨(hΔ.finite.union hD.finite).subset (Function.support_add _ _), ?_, ?_⟩
  · intro z hz
    by_cases h : Δ z = 0
    · exact hD.coheight z fun h' => hz (by simp [h, h'])
    · exact hΔ.coheight z h
  · intro z
    exact add_nonneg (hΔ.nonneg z) (hD.nonneg z)

theorem isEffQDiv_add_of_isQCart : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (Δ D : X → ℚ), IsEffQDiv Δ → IsQCart D → IsEffQDiv (Δ + D) := by
  intro X _ _ p hp Δ D hΔ hD
  have : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hp
  obtain ⟨m, D₀, -, hD₀, rfl⟩ := hD
  exact isEffQDiv_add hΔ (isEffQDiv_qWeil hD₀ m)

end GlobalTheory.PairStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEffectiveQCartierDivisorConvexCone
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.QCartCone

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]

theorem mult_zero' (z : X) : (0 : CartierDiv X).mult z = 0 := by
  have := CartierDiv.mult_add (0 : CartierDiv X) 0 z
  rw [add_zero] at this
  omega

theorem mult_nsmul' (D : CartierDiv X) (n : ℕ) (z : X) : (n • D).mult z = n * D.mult z := by
  induction n with
  | zero => rw [zero_nsmul, mult_zero']; simp
  | succ n ih => rw [succ_nsmul, CartierDiv.mult_add, ih]; push_cast; ring

theorem eff_nsmul' {D : CartierDiv X} (h : D.Eff) (n : ℕ) : (n • D).Eff := by
  induction n with
  | zero => rw [zero_nsmul]; exact CartierDiv.eff_zero
  | succ n ih => rw [succ_nsmul]; exact ih.add h

theorem isQCart_cone : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (D B : X → ℚ) (c : ℚ),
    IsQCart D → IsQCart B → 0 ≤ c → IsQCart (D + B) ∧ IsQCart (c • D) ∧ IsQCart (0 : X → ℚ) := by
  intro X _ _ D B c hD hB hc
  obtain ⟨m, D₀, hm, hD₀, rfl⟩ := hD
  obtain ⟨n, B₀, hn, hB₀, rfl⟩ := hB
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨⟨m * n, n • D₀ + m • B₀, Nat.mul_pos hm hn, (eff_nsmul' hD₀ n).add (eff_nsmul' hB₀ m), ?_⟩,
    ⟨c.den * m, c.num.toNat • D₀, Nat.mul_pos c.den_pos hm, eff_nsmul' hD₀ _, ?_⟩,
    ⟨1, 0, one_pos, CartierDiv.eff_zero, ?_⟩⟩
  · funext z
    simp only [Pi.add_apply, qWeil, CartierDiv.mult_add, mult_nsmul']
    push_cast
    field_simp
  · funext z
    have hnum : ((c.num.toNat : ℕ) : ℚ) = (c.num : ℚ) := by
      have h1 : ((c.num.toNat : ℤ) : ℚ) = (c.num : ℚ) := by
        rw [Int.toNat_of_nonneg (Rat.num_nonneg.2 hc)]
      exact_mod_cast h1
    have hden : (c.den : ℚ) ≠ 0 := by exact_mod_cast c.den_pos.ne'
    simp only [Pi.smul_apply, smul_eq_mul, qWeil, mult_nsmul']
    push_cast
    rw [hnum]
    conv_lhs => rw [← Rat.num_div_den c]
    field_simp
  · funext z
    simp [qWeil, mult_zero']

end GlobalTheory.QCartCone
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFractionRingOfInjective
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.TensorTower

theorem isFractionRing_of_injective {A F : Type} [CommRing A] [Field F] [Algebra A F]
    (hi : Function.Injective (algebraMap A F))
    (hs : ∀ z : F, ∃ x y : A, algebraMap A F y ≠ 0 ∧ z * algebraMap A F y = algebraMap A F x) :
    IsFractionRing A F := by
  haveI : IsDomain A := hi.isDomain (algebraMap A F)
  refine ⟨fun y => ?_, fun z => ?_, fun {x y} e => ⟨1, by simp [hi e]⟩⟩
  · exact (map_ne_zero_iff _ hi).2 (nonZeroDivisors.ne_zero y.2) |>.isUnit
  · obtain ⟨x, y, hy, e⟩ := hs z
    exact ⟨⟨x, y, mem_nonZeroDivisors_of_ne_zero fun h => hy (by simp [h])⟩, e⟩

theorem isFractionRing_subring {K : Type} [Field K] (R : Subring K)
    (h : ∀ f : K, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ f * b = a) : IsFractionRing R K :=
  isFractionRing_of_injective Subtype.val_injective fun z => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := h z
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hb0, e⟩

theorem exists_residue {κ : Type} [Field κ] [Algebra ℂ κ] (B : Subring κ)
    (hB : IsLocModel (algebraMap ℂ κ) B) (hr : RatRes (algebraMap ℂ κ) B) :
    ∃ ev : B →+* ℂ, ∀ (b : B) (a : ℂ), NonUnit B ((b : κ) - algebraMap ℂ κ a) ↔ ev b = a := by
  haveI := hB.isLocalRing
  let c0 : ℂ →+* B := (algebraMap ℂ κ).codRestrict B hB.const_mem
  let g : ℂ →+* IsLocalRing.ResidueField B := (IsLocalRing.residue B).comp c0
  have key : ∀ (b : B) (a : ℂ), NonUnit B ((b : κ) - algebraMap ℂ κ a) ↔
      IsLocalRing.residue B b = g a := fun b a => by
    rw [show (b : κ) - algebraMap ℂ κ a = ((b - c0 a : B) : κ) from rfl, nonUnit_iff,
      ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]
    show _ ↔ Ideal.Quotient.mk _ b = Ideal.Quotient.mk _ (c0 a)
    rw [Ideal.Quotient.eq]
  have hbij : Function.Bijective g := ⟨g.injective, fun y => by
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨a, ha⟩ := hr b b.2
    exact ⟨a, ((key b a).1 ha).symm⟩⟩
  let e := RingEquiv.ofBijective g hbij
  refine ⟨e.symm.toRingHom.comp (IsLocalRing.residue B), fun b a => ?_⟩
  rw [key]
  show _ ↔ e.symm _ = a
  rw [e.symm_apply_eq]
  rfl

theorem exists_isEtTower_tensor : ∀ {K κ L : Type} [Field K] [Field κ] [Field L] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ) L] [IsScalarTower ℂ (K ⊗[ℂ] κ) L] [IsFractionRing (K ⊗[ℂ] κ) L]
    (R : Subring K) (B : Subring κ) (hB : IsLocModel (algebraMap ℂ κ) B) (r : ℕ) (τ : Fin r → B),
  IsLocModel (algebraMap ℂ K) R → IsIntegrallyClosed R → RatRes (algebraMap ℂ K) R →
  RatRes (algebraMap ℂ κ) B → (letI := hB.isLocalRing; IsLocalRing.maximalIdeal B = Ideal.span (Set.range τ)) →
  (MvPolynomial.eval₂Hom ((algebraMap ℂ κ).codRestrict B hB.const_mem) τ).FormallyEtale →
  ∃ (T : Subring L) (ι : R →+* T) (ψ : T →+* R) (j : B →+* T),
    IsEtTower (algebraMap ℂ K) R (algebraMap ℂ L) T ι ψ (fun i => j (τ i)) ∧
    (∀ a : R, (ι a : L) = algebraMap (K ⊗[ℂ] κ) L ((a : K) ⊗ₜ 1)) ∧
    (∀ b : B, (j b : L) = algebraMap (K ⊗[ℂ] κ) L (1 ⊗ₜ (b : κ))) ∧
    (∀ (b : B) (a : ℂ), NonUnit B ((b : κ) - algebraMap ℂ κ a) → ((ψ (j b) : R) : K) = algebraMap ℂ K a) ∧
    (∀ t : T, ∃ s s' : T, s ∈ Subring.closure (Set.range ι ∪ Set.range j) ∧
      s' ∈ Subring.closure (Set.range ι ∪ Set.range j) ∧ IsUnit (ψ s') ∧ (t : L) * s' = s) := by
  intro K κ L _ _ _ _ _ _ _ _ _ R B hB r τ hR hRn hRr hBr hm he
  haveI := hR.isLocalRing
  haveI := hB.isLocalRing
  letI iR : Algebra ℂ R := ((algebraMap ℂ K).codRestrict R hR.const_mem).toAlgebra
  letI iB : Algebra ℂ B := ((algebraMap ℂ κ).codRestrict B hB.const_mem).toAlgebra
  haveI : IsScalarTower ℂ R K := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower ℂ B κ := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsFractionRing R K := isFractionRing_subring R hR.frac
  haveI : IsFractionRing B κ := isFractionRing_subring B hB.frac
  obtain ⟨hinj, hsurj⟩ := _root_.GlobalTheory.tensor_fractionRing_of_tensor (k := ℂ) (R := R) (B := B) (K := K) (κ := κ) (L := L)
  set f := (algebraMap (K ⊗[ℂ] κ) L).comp (Algebra.TensorProduct.map
    (IsScalarTower.toAlgHom ℂ R K) (IsScalarTower.toAlgHom ℂ B κ)).toRingHom with hf
  letI iA : Algebra (R ⊗[ℂ] B) L := f.toAlgebra
  haveI : IsFractionRing (R ⊗[ℂ] B) L := isFractionRing_of_injective hinj hsurj
  haveI : IsDomain (R ⊗[ℂ] B) := hinj.isDomain f
  haveI : Nontrivial (R ⊗[ℂ] B) := IsDomain.toNontrivial
  have hft : ∀ (a : R) (b : B), algebraMap (R ⊗[ℂ] B) L (a ⊗ₜ b) =
      algebraMap (K ⊗[ℂ] κ) L ((a : K) ⊗ₜ (b : κ)) := fun a b => rfl

  obtain ⟨ev, hev⟩ := exists_residue B hB hBr
  have hevc : ∀ a : ℂ, ev (algebraMap ℂ B a) = a := fun a =>
    (hev _ a).1 (by
      rw [show ((algebraMap ℂ B a : B) : κ) = algebraMap ℂ κ a from rfl, sub_self]
      exact nonUnit_zero B)
  let ev' : B →ₐ[ℂ] ℂ := { ev with commutes' := hevc }
  let φ : R ⊗[ℂ] B →ₐ[ℂ] R := Algebra.TensorProduct.lift (AlgHom.id ℂ R)
    ((Algebra.ofId ℂ R).comp ev') (fun _ _ => Commute.all _ _)
  have hφ : ∀ (a : R) (b : B), φ (a ⊗ₜ b) = a * algebraMap ℂ R (ev b) := fun a b => by
    simp [φ, ev']
  let q : Ideal (R ⊗[ℂ] B) := (IsLocalRing.maximalIdeal R).comap φ
  haveI : q.IsPrime := Ideal.comap_isPrime _ _
  have hq : q.primeCompl ≤ nonZeroDivisors (R ⊗[ℂ] B) := q.primeCompl_le_nonZeroDivisors
  let A : Subalgebra (R ⊗[ℂ] B) L := Localization.subalgebra.ofField L q.primeCompl hq
  haveI hA : IsLocalization q.primeCompl A := Localization.subalgebra.isLocalization_ofField L _ hq
  have hu : ∀ y : q.primeCompl, IsUnit (φ.toRingHom y) := fun y => by
    by_contra hy
    exact y.2 (show (y : R ⊗[ℂ] B) ∈ q from (IsLocalRing.mem_maximalIdeal _).2 hy)
  let ψ : A →+* R := IsLocalization.lift hu
  have hψ : ∀ x, ψ (algebraMap _ A x) = φ x := IsLocalization.lift_eq hu
  let a : R ⊗[ℂ] B →+* A := algebraMap _ A
  have ha : ∀ x, (a x : L) = algebraMap (R ⊗[ℂ] B) L x := fun x => rfl
  let ι : R →+* A := a.comp Algebra.TensorProduct.includeLeftRingHom
  let j : B →+* A := a.comp Algebra.TensorProduct.includeRight.toRingHom
  have hcL : ∀ z : ℂ, algebraMap (R ⊗[ℂ] B) L (algebraMap ℂ _ z) = algebraMap ℂ L z := fun z => by
    rw [Algebra.TensorProduct.algebraMap_apply, hft, IsScalarTower.algebraMap_apply ℂ (K ⊗[ℂ] κ) L,
      Algebra.TensorProduct.algebraMap_apply]
    rfl
  have hcl : ∀ x, a x ∈ Subring.closure (Set.range ι ∪ Set.range j) := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      have e : a (x ⊗ₜ y) = ι x * j y := by
        simp [ι, j, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul]
      rw [e]
      exact Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨x, rfl⟩))
        (Subring.subset_closure (Or.inr ⟨y, rfl⟩))
    | add x y hx hy => rw [map_add (f := _)]; exact Subring.add_mem _ hx hy
  have hmem : ∀ z : ℂ, algebraMap ℂ L z ∈ A.toSubring := fun z => by
    rw [← hcL]; exact A.algebraMap_mem _
  have hevτ : ∀ i, ev (τ i) = 0 := fun i => by
    refine (hev _ 0).1 ?_
    rw [map_zero, sub_zero]
    refine (nonUnit_iff (τ i)).2 fun hu => ?_
    have : τ i ∈ IsLocalRing.maximalIdeal B := by
      rw [hm]; exact Ideal.subset_span ⟨i, rfl⟩
    exact (IsLocalRing.mem_maximalIdeal _).1 this hu
  refine ⟨A.toSubring, ι, ψ, j, ⟨hR, hRn, ⟨hmem, IsLocalization.AtPrime.isLocalRing A q, ?_, ?_⟩,
    fun z => ?_, fun x => ?_, fun i => ?_, ?_⟩, fun x => rfl, fun y => rfl, fun b z hbz => ?_,
    fun t => ?_⟩
  · have e : (algebraMap ℂ L).codRestrict A.toSubring hmem = a.comp (algebraMap ℂ (R ⊗[ℂ] B)) :=
      RingHom.ext fun z => Subtype.ext (hcL z).symm
    rw [e]
    haveI : Algebra.EssFiniteType ℂ R := RingHom.essFiniteType_algebraMap.1 hR.essFiniteType
    haveI : Algebra.EssFiniteType ℂ B := RingHom.essFiniteType_algebraMap.1 hB.essFiniteType
    haveI : Algebra.EssFiniteType ℂ (R ⊗[ℂ] B) := Algebra.EssFiniteType.comp ℂ R _
    have h1 : (algebraMap (R ⊗[ℂ] B) A).EssFiniteType :=
      RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization A q.primeCompl)
    have h2 : (algebraMap ℂ (R ⊗[ℂ] B)).EssFiniteType := RingHom.essFiniteType_algebraMap.2 inferInstance
    exact h2.comp h1
  · intro z
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := R ⊗[ℂ] B) z
    have hy' : algebraMap (R ⊗[ℂ] B) L y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
    exact ⟨_, A.algebraMap_mem x, _, A.algebraMap_mem y, hy', div_mul_cancel₀ _ hy'⟩
  · exact (ha _).trans (hcL z)
  · show ψ (a (x ⊗ₜ 1)) = x
    rw [hψ, hφ, map_one, map_one, mul_one]
  · show ψ (a (1 ⊗ₜ τ i)) = 0
    rw [hψ, hφ, hevτ, map_zero, mul_zero]
  · have e : MvPolynomial.eval₂Hom ι (fun i => j (τ i)) =
        a.comp (MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[ℂ] B)
          (fun i => (1 : R) ⊗ₜ[ℂ] τ i)) := by
      ext x <;> simp [ι, j]
    rw [e]
    have h1 : (algebraMap (R ⊗[ℂ] B) A).FormallyEtale :=
      RingHom.formallyEtale_algebraMap.2 (Algebra.FormallyEtale.of_isLocalization q.primeCompl)
    exact (GlobalTheory.T.formallyEtale_baseChange_eval_hom τ he).comp h1
  · show ((ψ (a (1 ⊗ₜ b)) : R) : K) = _
    rw [hψ, hφ, one_mul, (hev b z).1 hbz]
    rfl
  · obtain ⟨⟨x, y⟩, e⟩ := IsLocalization.surj q.primeCompl (S := A) t
    refine ⟨a x, a y, hcl x, hcl y, ?_, congrArg Subtype.val e⟩
    rw [hψ]; exact hu y

end GlobalTheory.FieldPair.TensorTower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFubiniStudyRatFnsMemPairSections
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem isFS_mem_pair : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (M : HermLB p) (J : Type) [Fintype J] (f : J → X.functionField) (w : J → ℝ), IsFS M f w → ∃ P : Pair p, P.L = M ∧ ∀ j, f j ∈ P.H 1 0 := by
  intro k _ X _ p M J _ f w h
  obtain ⟨ρ, hρ, hreg, -⟩ := h
  refine ⟨⟨M, M, ρ, ρ, hρ, hρ⟩, rfl, fun j x i c hi _ => ?_⟩
  have e : Pair.loc ⟨M, M, ρ, ρ, hρ, hρ⟩ 1 0 (f j) i c = f j * (ρ i : X.functionField) := by
    simp [Pair.loc]
  rw [e]
  exact (hreg x i hi).1 j

end GlobalTheory.HSNef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegrallyClosedPointLocalRingNormalScheme
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

theorem isIntegrallyClosed_locRing : ∀ (X : Scheme.{0}) [IsIntegral X] [GlobalTheory.IsNormalScheme X] (x : X),
    IsIntegrallyClosed (locRing x) := by
  intro X _ _ x
  let e : X.presheaf.stalk x ≃+* locRing x := RingEquiv.ofBijective
    (algebraMap (X.presheaf.stalk x) X.functionField).rangeRestrict
    ⟨fun _ _ h => IsFractionRing.injective _ X.functionField (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩
  haveI : IsIntegrallyClosed (X.presheaf.stalk x) := GlobalTheory.IsNormalScheme.isIntegrallyClosed_stalk x
  exact IsIntegrallyClosed.of_equiv e

end GlobalTheory.FieldPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormAlternatingOfAdjacentSwapBlocksStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearForm_alternating_of_adjacent_swap_blocks : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (L : MvPolynomial (Root m) ℝ →ₗ[ℝ] ℝ), (∀ (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ Q, L (rename (Equiv.swap (⟨τ, a⟩ : Root m) ⟨τ, b⟩) Q) = - L Q) → ∀ (w : ∀ τ, Equiv.Perm (Fin (m τ))) (Q : MvPolynomial (Root m) ℝ), L (rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) Q) = (((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : ℝ) * L Q := by
  first | exact @GlobalTheory.FlagPush.alternating_of_adjacent_swap | exact GlobalTheory.FlagPush.alternating_of_adjacent_swap | (intros; apply GlobalTheory.FlagPush.alternating_of_adjacent_swap <;> assumption)
end

