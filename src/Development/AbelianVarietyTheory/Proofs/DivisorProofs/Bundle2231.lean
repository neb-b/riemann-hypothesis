module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2186
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0539
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChernExistsUniqueAndIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2208
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2146
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2213
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2221
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2195
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AxesO1OfProjectiveRankCup
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2135
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0138

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFamilyOfTrivialModEpsilon
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen

theorem isLocalRing_dualNumber_field (k : Type) [Field k] : IsLocalRing (DualNumber k) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x ↦ by
    by_cases h : TrivSqZeroExt.fst x = 0
    · right
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
      simp [h]
    · left
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
      exact isUnit_iff_ne_zero.2 h

theorem pic_sp_local_eq_zero (R : Type) [CommRing R] [IsLocalRing R] (c : Pic (Sp R)) : c = 0 := by
  obtain ⟨V, hV, h⟩ := exists_pull_eq_zero c (IsLocalRing.closedPoint R)
  have hV' : V = ⊤ := (IsLocalRing.closedPoint_mem_iff V).1 hV
  have e := pull_eq_zero_of_mem V (𝟙 _) (fun z ↦ by rw [hV']; trivial) h
  rwa [pull_id] at e

theorem ringHom_dualNumber_factor {k K : Type} [CommRing k] [Field K] (φ : DualNumber k →+* K) :
    φ = (φ.comp (dnInl k)).comp (dnFst k) := by
  have hε : φ DualNumber.eps = 0 := by
    have e : φ DualNumber.eps * φ DualNumber.eps = 0 := by rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
    exact mul_self_eq_zero.1 e
  refine RingHom.ext fun x ↦ ?_
  have hx : x = TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inr x.snd := by ext <;> simp
  conv_lhs => rw [hx]
  rw [map_add (f := _), DualNumber.inr_eq_smul_eps, Algebra.smul_def, map_mul, hε, mul_zero, add_zero]
  rfl

theorem fam_of_triv_mod_eps : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (k : Type) [Field k]
    (s : Sp (DualNumber k) ⟶ S) (D : LB (A ⊗ Over.mk s).left) (hD : D.IsLB),
    GlobalTheory.CechPic.pull (A ◁ ptMap s (dnFst k)).left (cls D hD) = 0 → Fam A D := by
  intro S A _ hA k _ s D hD h0
  haveI := isLocalRing_dualNumber_field k
  haveI : Module.Finite k (DualNumber k) := inferInstanceAs (Module.Finite k (k × k))
  haveI : IsNoetherianRing (DualNumber k) := IsNoetherianRing.of_finite k (DualNumber k)
  haveI : IsLocallyNoetherian (Over.mk s).left := (inferInstance : IsLocallyNoetherian (Sp (DualNumber k)))
  refine ⟨hD, GlobalTheory.T.isAdditive_lineBundleFamily_of_geometricFibres S A (Over.mk s) hA D hD ?_ ?_⟩
  · rw [triv_ev_iff hD]
    exact pic_sp_local_eq_zero _ _
  · intro K _ _ s' t
    obtain ⟨φ, hφ⟩ := Spec.map_surjective t.left
    set ψ : k →+* K := φ.hom.comp (dnInl k)
    have ht : t.left = spMap ψ ≫ spMap (dnFst k) := by
      rw [← hφ, ← Spec.map_comp]
      congr 1
      ext1
      exact ringHom_dualNumber_factor φ.hom
    have hN : (ev D (fst A (Over.mk s')) (snd A (Over.mk s') ≫ t)).IsLB := pull_isLB hD _
    refine (isAdditive_iff hN).2 fun Y a a' y ↦ ?_
    have key : ∀ b : Y ⟶ A, evc hN b y = 0 := fun b ↦ by
      rw [evc_ev hD, lift_fst, lift_snd_assoc]
      let u : Y ⟶ Over.mk (spMap (dnFst k) ≫ s) := Over.homMk (y.left ≫ spMap ψ) (by
        have e1 : y.left ≫ s' = Y.hom := by simpa using Over.w y
        have e2 : t.left ≫ s = s' := by simpa using Over.w t
        simp only [Over.mk_hom]
        rw [Category.assoc, ← Category.assoc (spMap ψ), ← ht, e2, e1])
      have hu : y ≫ t = u ≫ ptMap s (dnFst k) := by
        refine Over.OverMorphism.ext ?_
        simp only [Over.comp_left, ptMap_left, ht]
        rfl
      rw [hu, evc, ← lift_whiskerLeft, Over.comp_left, pull_comp, h0, map_zero]
    rw [key, key, key, add_zero]

end GlobalTheory.DualOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicSumMaximalIdealUniqueNoetherianLocal
section
open IsLocalRing GlobalTheory.UT

namespace GlobalTheory.Poinc

theorem sumI_maximalIdeal_unique :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (Ix : Type) (x : Ix → R) (s s' : R),
      SumI (maximalIdeal R) x s → SumI (maximalIdeal R) x s' → s = s' := by
  classical
  intro R _ _ _ Ix x s s' ⟨N, _, _, _, h⟩ ⟨N', _, _, _, h'⟩
  have key : ∀ n : ℕ, s - s' ∈ maximalIdeal R ^ n := by
    intro n
    obtain ⟨S, hS⟩ := h n
    obtain ⟨S', hS'⟩ := h' n
    have le : ∀ M : Submodule R R, maximalIdeal R ^ n • M ≤ maximalIdeal R ^ n := fun M =>
      Submodule.smul_le.2 fun a ha b _ => Ideal.mul_mem_right b _ ha
    have h1 := le _ (hS (S ∪ S') Finset.subset_union_left)
    have h2 := le _ (hS' (S ∪ S') Finset.subset_union_right)
    have h3 := Ideal.sub_mem _ h1 h2
    rwa [sub_sub_sub_cancel_right] at h3
  have hb : ⨅ n : ℕ, maximalIdeal R ^ n = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top
  have : s - s' ∈ ⨅ n : ℕ, maximalIdeal R ^ n := Ideal.mem_iInf.2 key
  rw [hb, Ideal.mem_bot] at this
  exact sub_eq_zero.1 this

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenSmoothSchemeIsSpecSmoothAlgebra
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem affineChart_smooth : ∀ (R : Type) [CommRing R] (Y : Over (Sp R)), Smooth Y.hom → ∀ (W : Y.left.Opens), IsAffineOpen W → ∃ (O : Type) (_ : CommRing O) (_ : Algebra R O) (k : Sp O ⟶ Y.left) (_ : IsOpenImmersion k), k.opensRange = W ∧ k ≫ Y.hom = spMap (algebraMap R O) ∧ Algebra.Smooth R O := by
  intro R _ Y hY W hW
  let alg : R →+* Γ(Y.left, W) :=
    (Y.hom.appLE ⊤ W (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  letI : Algebra R Γ(Y.left, W) := alg.toAlgebra
  have s₀ : hW.fromSpec ≫ Y.hom = spMap alg := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec Y.hom (isAffineOpen_top _) hW (fun _ _ => trivial),
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]; rfl
  have h1 : RingHom.Smooth (Y.hom.appLE ⊤ W (fun _ _ => trivial)).hom :=
    HasRingHomProperty.appLE @Smooth Y.hom hY ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ (fun _ _ => trivial)
  have h2 : RingHom.Smooth alg :=
    RingHom.Smooth.respectsIso.2 _ (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv h1
  exact ⟨Γ(Y.left, W), inferInstance, inferInstance, hW.fromSpec, inferInstance, hW.opensRange_fromSpec, s₀, h2⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgClosurePointFactorsThroughFiniteLocalSubalgeb
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem finpt_factor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (Z : Scheme.{0}) (π : Z ⟶ Sp R) [IsFinite π] (k : Sp (Kb R) ⟶ Z), k ≫ π = (TF (R := R) (Kb R)).hom → ∃ S : Subalgebra R (Kb R), Module.Finite R S ∧ IsLocalRing S ∧ ∃ k₀ : Sp S ⟶ Z, k₀ ≫ π = spMap (algebraMap R S) ∧ spMap (S.val : S →+* Kb R) ≫ k₀ = k := by
  intro R _ _ _ hR Z π _ k hk
  obtain ⟨⟨hN, -, -, hC⟩, -⟩ := hR
  haveI := hN
  haveI := hC
  haveI : IsAffine Z := isAffine_of_isAffineHom π
  let i : Spec Γ(Z, ⊤) ≅ Z := Z.isoSpec.symm
  obtain ⟨θ, hθ⟩ := Spec.map_surjective (i.hom ≫ π)
  have h₁ : θ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hθ]
    infer_instance
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (k ≫ i.inv)
  have hc : θ ≫ ψ = CommRingCat.ofHom (algebraMap R (Kb R)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, hθ, Category.assoc, i.inv_hom_id_assoc, hk]
    simp only [TF, jFK, jK, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [← IsScalarTower.algebraMap_eq]
  let _ : Algebra R Γ(Z, ⊤) := θ.hom.toAlgebra
  have : Module.Finite R Γ(Z, ⊤) := h₁
  let φ : Γ(Z, ⊤) →ₐ[R] Kb R := ⟨ψ.hom, fun r => congr(($hc).hom r)⟩
  let S : Subalgebra R (Kb R) := φ.range
  have hfin : Module.Finite R S :=
    Module.Finite.of_surjective φ.rangeRestrict.toLinearMap φ.rangeRestrict_surjective
  have hloc : IsLocalRing S := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := R) S
  refine ⟨S, hfin, hloc, spMap (φ.rangeRestrict : Γ(Z, ⊤) →+* S) ≫ i.hom, ?_, ?_⟩
  · rw [Category.assoc, ← hθ, ← Spec.map_comp]
    congr 1
    ext r
    exact congrArg Subtype.val (φ.rangeRestrict.commutes r)
  · rw [← Category.assoc, ← Spec.map_comp]
    have : CommRingCat.ofHom (φ.rangeRestrict : Γ(Z, ⊤) →+* S) ≫ CommRingCat.ofHom (S.val : S →+* Kb R) = ψ := by
      ext b; rfl
    rw [this, hψ, Category.assoc, i.inv_hom_id, Category.comp_id]

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationBoundOfMulSqIntegral
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

noncomputable section

namespace GlobalTheory.SizeSqIntegral

theorem sz_nat_val (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (D : ℕ) :
    Sz l lam (-(padicValNat l D : ℝ)) (D : ℂ) := by
  have h := GlobalTheory.SizeRat.sz_ratCast l lam (D : ℚ) (-(padicValNat l D : ℝ)) (by
    rw [padicValRat.of_nat, Nat.padicValNat_def]; simp)
  simpa using h

theorem sz_zero_of_isIntegral (l : ℕ) [hl : Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (x : ℂ)
    (h : IsIntegral ℤ x) : Sz l lam 0 x :=
  GlobalTheory.SzRules.sz_of_isIntegral 1 x (fun hd => hl.out.one_lt.ne' (Nat.dvd_one.1 hd)) (by simpa using h)

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (D M : ℕ) (x : ℂ), 0 < D → IsIntegral ℤ ((D : ℂ) * x ^ 2) → Sz l lam (-(padicValNat l D : ℝ) / 2) ((D : ℂ) * x) ∧ Sz l lam (-(padicValNat l D : ℝ) / 2) ((M * l ^ padicValNat l D : ℕ) : ℂ) := by
  intro l hl lam D M x _ hx
  constructor
  · apply GlobalTheory.SzRules.sz_of_sq
    have h := GlobalTheory.SzRules.sz_mul (sz_nat_val l lam D) (sz_zero_of_isIntegral l lam _ hx)
    rw [add_zero] at h
    convert h using 1
    ring
  · have h1 := sz_nat_val l lam (l ^ padicValNat l D)
    rw [Nat.padicValNat_def, Nat.multiplicity_prime_pow] at h1
    have h2 : Sz l lam 0 (M : ℂ) := sz_zero_of_isIntegral l lam _ (by simpa using (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (M : ℤ))))
    have h := GlobalTheory.SzRules.sz_mul h2 h1
    rw [zero_add, ← Nat.cast_mul] at h
    refine GlobalTheory.SzRules.sz_mono ?_ h
    have : (0 : ℝ) ≤ (padicValNat l D : ℝ) := Nat.cast_nonneg _
    linarith

end GlobalTheory.SizeSqIntegral
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertDiagonalReal
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM
open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RiemInt

open GlobalTheory.AppellHumbertTrivial

theorem im_hermForm_int {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (hL : L.IsLB) (u : HolUnif A L g)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (h : IsFactorAH u Hm χ) (l m : u.Λ) :
    ∃ n : ℤ, (hermForm Hm l m).im = n := by
  have hper : ∀ (l : u.Λ) z, u.ex (z + l) = u.ex z := fun l z => by
    rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]
  obtain ⟨i, hi⟩ := PullHermitian.exists_chart (u.ex 0).left hL
  have hil : ⊤ ≤ (u.ex (0 + l)).left ⁻¹ᵁ L.U i := by rwa [hper]
  have him : ⊤ ≤ (u.ex (0 + m)).left ⁻¹ᵁ L.U i := by rwa [hper]
  have hlm : ⊤ ≤ (u.ex (0 + l + m)).left ⁻¹ᵁ L.U i := by rwa [hper]
  have h1 := h.2.2 l i 0 hi
  have h2 := h.2.2 m i _ hil
  have h3 := h.2.2 m i 0 hi
  have h4 := h.2.2 l i _ him
  have hne := u.fr_ne i _ hlm
  have hs : hermForm Hm m l = star (hermForm Hm l m) := by
    unfold hermForm
    rw [← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star, h.1.eq, Matrix.dotProduct_mulVec]
  have hχl : χ l ≠ 0 := norm_ne_zero_iff.1 (by rw [h.2.1]; exact one_ne_zero)
  have hχm : χ m ≠ 0 := norm_ne_zero_iff.1 (by rw [h.2.1]; exact one_ne_zero)
  rw [h2] at h1
  rw [h4, h1] at h3
  simp only [zero_add, zero_dotProduct, mul_zero] at h3 hne
  rw [add_comm (m : Fin g → ℂ) l] at h3
  unfold hermForm at hs ⊢
  rw [hs] at h3
  generalize (l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)) = a at h3
  generalize (m : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ)) = b at h3
  generalize (l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ)) = c at h3 ⊢
  simp only [Complex.exp_add] at h3
  have he : Complex.exp (Real.pi * c) = Complex.exp (Real.pi * star c) := by
    refine mul_right_cancel₀ (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hχl hχm)
      (Complex.exp_ne_zero (Real.pi / 2 * a))) (Complex.exp_ne_zero (Real.pi / 2 * b))) hne) ?_
    linear_combination h3
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 he
  refine ⟨n, ?_⟩
  have := congrArg Complex.im hn
  simp at this
  have hp := Real.pi_pos
  refine mul_left_cancel₀ (a := 2 * Real.pi) (by positivity) ?_
  linear_combination this

variable {g : ℕ}

end GlobalTheory.RiemInt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertExistsLineBundlePosDefHermitian
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AHPos

theorem smoothOfRelativeDimension_of_holUnif {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A] (hA : IsAbelianScheme A)
    {L : LB A.left} (u : HolUnif A L g) : SmoothOfRelativeDimension g A.hom := by
  obtain ⟨D, hD⟩ := GlobalTheory.AbelianDim.exists_relDim ℂ A hA
  obtain ⟨c, hc⟩ := GlobalTheory.AlgChart.exists_mem_source (p := A.hom) (σ := RingHom.id ℂ) (D := D)
    (GlobalTheory.HolUnifSec.pt u 0)
  have h1 : D ≤ g := GlobalTheory.HolUnifSec.dim_le u c hc
  have h2 : g ≤ D := by
    have hi : Function.Injective (fderiv ℂ (c.e ∘ GlobalTheory.HolUnifSec.pt u) 0).toLinearMap := by
      rw [ContinuousLinearMap.coe_coe]
      exact GlobalTheory.HolUnifSec.injective_fderiv u c hc
    have := LinearMap.finrank_le_finrank_of_injective hi
    simpa using this
  obtain rfl : D = g := le_antisymm h1 h2
  exact hD

end GlobalTheory.AHPos

theorem GlobalTheory.AHPos.exists_lb_of_posDef : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (L₀ : LB A.left) (u₀ : HolUnif A L₀ g) (H₀ : Matrix (Fin g) (Fin g) ℂ) (χ₀ : u₀.Λ → ℂ), L₀.IsLB → u₀.IsAH H₀ χ₀ →
    ∀ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) →
    (∀ l ∈ u₀.Λ, ∀ l' ∈ u₀.Λ, ∃ n : ℤ, (l ⬝ᵥ Hm.mulVec (star l')).im = n) →
    ∃ (M : LB A.left) (u : HolUnif A M g) (χ : u.Λ → ℂ), M.IsLB ∧ u.ex = u₀.ex ∧ u.IsAH Hm χ := by
  intro g A _ hA L₀ u₀ H₀ χ₀ hL₀ hAH Hm hHm hpos hint
  obtain ⟨A', _, hA', hsm, L', u', χ', hL', hΛ, hAH'⟩ :=
    _root_.GlobalTheory.riemann_polarised_torus g u₀.Λ Hm u₀.discrete u₀.full hHm hpos hint
  obtain ⟨f, -, hf⟩ := GlobalTheory.HolUnifHom.exists_isMonHom_of_map_lattice A A' g hA hA'
    (GlobalTheory.AHPos.smoothOfRelativeDimension_of_holUnif hA u₀) hsm L₀ L' u₀ u' LinearMap.id
    (fun x hx => (hΛ x).2 hx)
  obtain ⟨u₁, hex, hΛ₁, hfr⟩ := GlobalTheory.exists_holUnif_linComb A A' L₀ L' g g u₀ u' PUnit (fun _ => f)
    (fun _ => LinearMap.id) (fun _ => 1) (fun _ z => hf z)
  have hmem : ∀ l : u₁.Λ, (l : Fin g → ℂ) ∈ u'.Λ := fun l => (hΛ _).2 (hΛ₁ ▸ l.2)
  refine ⟨_, u₁, fun l => χ' ⟨l.1, hmem l⟩, LB.isLB_linComb hL' _ _, hex, hHm, hpos,
    fun l => hAH'.2.2.1 _, ?_⟩
  intro l j z hz
  rw [hex] at hz
  have hz' : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L'.U (j PUnit.unit) := by
    rw [← LinearMap.id_apply (R := ℂ) z, hf z]
    exact (CubeValues.le_preimage_wchart (u₀.ex z).left L' (fun _ => f.left) j).1 hz PUnit.unit
  have e1 : u₁.fr j z = u'.fr (j PUnit.unit) z := by simpa using hfr j z
  have e2 : u₁.fr j (z + l) = u'.fr (j PUnit.unit) (z + l) := by simpa using hfr j (z + l)
  rw [e1, e2]
  exact hAH'.2.2.2 ⟨l.1, hmem l⟩ (j PUnit.unit) z hz'
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithVarietyRelativeDimDrop
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

namespace GlobalTheory

theorem dim_ne_zero_of_isProjOver {k : Type} [CommRing k] {Z : Scheme.{0}} (q : Z ⟶ Sp k)
    [IsIntegral Z] (hq : IsProjOver q) (hfin : Module.Finite ℤ k) (hc : CharZero Γ(Z, ⊤)) :
    topologicalKrullDim Z ≠ 0 := fun h0 => by
  obtain ⟨N, j, _, hj⟩ := hq
  have := isProper_str k N
  have : IsProper q := hj ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom k)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hfin)
  let t := q ≫ spMap (Int.castRingHom k)
  have : Flat t := (flat_int_iff_charZero t).2 hc
  obtain ⟨z, -, hz⟩ := Flat.generalizingMap t (genericPoint_specializes (t (genericPoint Z)))
  have hs : Set.range t = Set.univ := by
    rw [← t.isClosedMap.isClosed_range.closure_eq]
    exact Set.eq_univ_of_univ_subset ((genericPoint_spec (Sp ℤ)).def.ge.trans
      (closure_mono (Set.singleton_subset_iff.2 ⟨z, hz⟩)))
  have hu (w : Z) : w = genericPoint Z := by
    have := Order.krullDim_nonpos_iff_forall_isMax.1 (show Order.krullDim (TopologicalSpace.IrreducibleCloseds Z) ≤ 0
      from h0.le) ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩
    exact IsGenericPoint.eq (Set.eq_univ_of_univ_subset (@this
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩ (Set.subset_univ _))) (genericPoint_spec Z)
  have hs' := Set.range_eq_univ.1 hs
  obtain ⟨a, ha⟩ := hs' (⊥ : PrimeSpectrum ℤ)
  obtain ⟨b, hb⟩ := hs' (⟨Ideal.span {2}, (Ideal.span_singleton_prime two_ne_zero).2
    Int.prime_two⟩ : PrimeSpectrum ℤ)
  have e := congrArg PrimeSpectrum.asIdeal (hb.symm.trans (((hu b).trans (hu a).symm) ▸ ha))
  exact two_ne_zero (Ideal.span_singleton_eq_bot.1 e)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AxesO1OfProjectiveRankCupStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.axesO1_of_projective_rank_cup : (∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → (Module.Finite R (HO1 A.hom) ∧ Module.Projective R (HO1 A.hom) ∧ ∀ p : PrimeSpectrum R, Module.rankAtStalk (HO1 A.hom) p = g) ∧ ∃ e : ⋀[R]^2 (HO1 A.hom) ≃ₗ[R] GlobalTheory.CatCoh.H2 (OAff A.hom), ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = GlobalTheory.CatCoh.cup (OAff A.hom) a b) → AxesVanishingStructureSheafDegOne := by
  first | exact @GlobalTheory.Obs.axesO1_of_cohomology_structure | exact GlobalTheory.Obs.axesO1_of_cohomology_structure | (intros; apply GlobalTheory.Obs.axesO1_of_cohomology_structure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeBisStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChangeBis : ∀ (S : Scheme.{0}) (A S' S'' : Over S) [GrpObj A] (g : ℕ) (_ : S'' ⟶ S'), HasRep A g S' → HasRep A g S'' := by
  first | exact @GlobalTheory.DualCon.HasRep.baseChange | exact GlobalTheory.DualCon.HasRep.baseChange | (intros; apply GlobalTheory.DualCon.HasRep.baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubschemeModLProjectiveStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_subscheme_mod_l_projective : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] (l : ℕ) [Fact l.Prime] [Algebra (ZMod l) Γ(Z, ⊤)], IsProjOver (strHom (ZMod l) (X := Z)) := by
  first | exact @GlobalTheory.VertProj.isProjOver_strHom_zmod | exact GlobalTheory.VertProj.isProjOver_strHom_zmod | (intros; apply GlobalTheory.VertProj.isProjOver_strHom_zmod <;> assumption)
end

