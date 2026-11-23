module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0333
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1300
public import GroundTheory.IdeleRoots.ConstantFrames.GaugeExistence.QdetSub
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0528
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0960
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0538
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0549
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0424
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0529
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0349
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0372
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0425

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CofiniteOfCapelliMonic
section
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin Polynomial

namespace GlobalTheory.CompanionTheory.CTFin.MonicCofin

theorem exists_finiteDimensional_sub_mem {C : Type*} [CommRing C] [Algebra ℂ C] (I : Ideal C) {s : Set C}
    (hs : s.Finite) (hgen : Algebra.adjoin ℂ s = ⊤) (hq : ∀ x ∈ s, ∃ q : ℂ[X], q.Monic ∧ aeval x q ∈ I) :
    ∃ V : Submodule ℂ C, FiniteDimensional ℂ V ∧ ∀ z : C, ∃ v ∈ V, z - v ∈ I := by
  let π : C →ₐ[ℂ] C ⧸ I := Ideal.Quotient.mkₐ ℂ I
  have hπ : Function.Surjective π := Ideal.Quotient.mkₐ_surjective ℂ I
  have hint : ∀ y ∈ π '' s, IsIntegral ℂ y := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨q, hm, hqI⟩ := hq x hx
    refine ⟨q, hm, ?_⟩
    rw [← aeval_def, aeval_algHom_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hqI
  have htop : Algebra.adjoin ℂ (π '' s) = ⊤ := by
    rw [← AlgHom.map_adjoin, hgen, Algebra.map_top, AlgHom.range_eq_top]
    exact hπ
  have hfg := fg_adjoin_of_finite (hs.image π) hint
  rw [htop, Algebra.top_toSubmodule] at hfg
  obtain ⟨t, ht⟩ := hfg
  refine ⟨Submodule.span ℂ (Function.surjInv hπ '' (t : Set (C ⧸ I))),
    FiniteDimensional.span_of_finite ℂ (t.finite_toSet.image _), fun z => ?_⟩
  have hmap : (Submodule.span ℂ (Function.surjInv hπ '' (t : Set (C ⧸ I)))).map π.toLinearMap = ⊤ := by
    rw [Submodule.map_span, ← Set.image_comp, ← ht]
    congr 1
    convert Set.image_id _
    funext y
    exact Function.surjInv_eq hπ y
  have hz : π z ∈ (Submodule.span ℂ (Function.surjInv hπ '' (t : Set (C ⧸ I)))).map π.toLinearMap := by
    rw [hmap]; exact Submodule.mem_top
  obtain ⟨v, hv, hvz⟩ := hz
  refine ⟨v, hv, ?_⟩
  rw [← Ideal.Quotient.eq]
  exact hvz.symm

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

theorem cap_mem_span_coeffs (τ : E →+* ℂ) (u : ℂ) :
    cap (a := n) τ u ∈ Submodule.span ℂ
      ((GroundTheory.BlockD.FourierDecayAlt.GaugeExists.qdetPoly (Eop (a := n) τ)).coeffs : Set (Module.End ℂ (Sm E n))) := by
  rw [cap, ← GroundTheory.BlockD.FourierDecayAlt.GaugeExists.evU_qdetPoly, GroundTheory.BlockD.FourierDecayAlt.GaugeExists.evU_apply, eval₂_eq_sum,
    Polynomial.sum]
  refine Submodule.sum_mem _ fun k hk => ?_
  rw [RingHom.id_apply, ← map_pow, ← Algebra.commutes, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (coeff_mem_coeffs (by simpa using hk)))

theorem exists_finite_subset_span_cap :
    ∃ b : Set (Module.End ℂ (Sm E n)), b.Finite ∧ b ⊆ {z | ∃ τ u, z = cap (a := n) τ u} ∧
      Submodule.span ℂ b = Submodule.span ℂ {z | ∃ (τ : E →+* ℂ) (u : ℂ), z = cap (a := n) τ u} := by
  obtain ⟨b, hb, hspan, hli⟩ := exists_linearIndependent ℂ {z | ∃ (τ : E →+* ℂ) (u : ℂ), z = cap (a := n) τ u}
  have hF : (⋃ τ : E →+* ℂ, ((GroundTheory.BlockD.FourierDecayAlt.GaugeExists.qdetPoly (Eop (a := n) τ)).coeffs :
      Set (Module.End ℂ (Sm E n)))).Finite := Set.finite_iUnion fun τ => Finset.finite_toSet _
  haveI := FiniteDimensional.span_of_finite ℂ hF
  have hle : Submodule.span ℂ {z | ∃ (τ : E →+* ℂ) (u : ℂ), z = cap (a := n) τ u} ≤ Submodule.span ℂ
      (⋃ τ : E →+* ℂ, ((GroundTheory.BlockD.FourierDecayAlt.GaugeExists.qdetPoly (Eop (a := n) τ)).coeffs :
      Set (Module.End ℂ (Sm E n)))) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨τ, u, rfl⟩
    exact Submodule.span_mono (Set.subset_iUnion (fun τ : E →+* ℂ =>
      ((GroundTheory.BlockD.FourierDecayAlt.GaugeExists.qdetPoly (Eop (a := n) τ)).coeffs : Set (Module.End ℂ (Sm E n)))) τ)
      (cap_mem_span_coeffs τ u)
  haveI := Submodule.finiteDimensional_of_le hle
  have hfin : b.Finite := by
    have hli' : LinearIndependent ℂ (fun x : b => (⟨x.1, hspan ▸ Submodule.subset_span x.2⟩ :
        Submodule.span ℂ {z | ∃ (τ : E →+* ℂ) (u : ℂ), z = cap (a := n) τ u})) :=
      LinearIndependent.of_comp (Submodule.subtype _) hli
    have := hli'.finite
    exact Set.toFinite b
  exact ⟨b, hfin, hb, hspan⟩

theorem cofin_of_algHom {C : Type} [CommRing C] [Algebra ℂ C] (ι : C →ₐ[ℂ] Module.End ℂ (Sm E n))
    (hι : Function.Injective ι) (hr : ι.range = Zalg E n) (J : Set (Module.End ℂ (Sm E n))) (hJ : J ⊆ Zalg E n)
    (hq : ∀ (τ : E →+* ℂ) (u : ℂ), ∃ q : Polynomial ℂ, q.Monic ∧ Polynomial.aeval (cap (a := n) τ u) q ∈ J) :
    Cofin J := by
  have hZ : ∀ c : C, ι c ∈ Zalg E n := fun c => hr ▸ AlgHom.mem_range_self ι c
  have hZ' : ∀ z ∈ Zalg E n, ∃ c : C, ι c = z := fun z hz => by
    rw [← hr] at hz
    exact hz
  obtain ⟨b, hbfin, hbT, hspan⟩ := exists_finite_subset_span_cap (E := E) (n := n)
  have hbZ : b ⊆ Zalg E n := fun x hx => Algebra.subset_adjoin (hbT hx)
  let s : Set C := ι ⁻¹' b
  have hs : s.Finite := hbfin.preimage hι.injOn
  have himg : ι '' s = b := Set.image_preimage_eq_of_subset fun x hx => hZ' x (hbZ hx)
  have hgen : Algebra.adjoin ℂ s = ⊤ := by
    refine Subalgebra.map_injective hι ?_
    rw [AlgHom.map_adjoin, himg, Algebra.map_top, hr]
    refine le_antisymm (Algebra.adjoin_le hbZ) (Algebra.adjoin_le ?_)
    intro x hx
    have h1 : x ∈ Submodule.span ℂ b := hspan ▸ Submodule.subset_span hx
    exact (Submodule.span_le.2 Algebra.subset_adjoin :
      Submodule.span ℂ b ≤ Subalgebra.toSubmodule (Algebra.adjoin ℂ b)) h1
  let I : Ideal C := Ideal.span (ι ⁻¹' J)
  have hI : ∀ w ∈ I, ι w ∈ Submodule.span ℂ {y | ∃ x ∈ Zalg E n, ∃ j ∈ J, y = x * j} := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => exact Submodule.subset_span ⟨1, Subalgebra.one_mem _, ι w, hw, (one_mul _).symm⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [smul_eq_mul, map_mul]
      exact GlobalTheory.CompanionTheory.HCFin.mul_mem_span_zalg_mul (hZ a) hx
  have hrel : ∀ x ∈ s, ∃ q : ℂ[X], q.Monic ∧ aeval x q ∈ I := by
    intro x hx
    obtain ⟨τ, u, hτ⟩ := hbT hx
    obtain ⟨q, hm, hqJ⟩ := hq τ u
    refine ⟨q, hm, Ideal.subset_span ?_⟩
    change ι (aeval x q) ∈ J
    rw [← aeval_algHom_apply, hτ]
    exact hqJ
  obtain ⟨V, hV, hz⟩ := exists_finiteDimensional_sub_mem I hs hgen hrel
  refine ⟨hJ, V.map ι.toLinearMap, inferInstance, fun z hzZ => ?_⟩
  obtain ⟨c, rfl⟩ := hZ' z hzZ
  obtain ⟨v, hv, hvI⟩ := hz c
  refine Submodule.mem_sup.2 ⟨ι v, Submodule.mem_map_of_mem hv, ι (c - v), hI _ hvI, ?_⟩
  rw [map_sub]
  abel

theorem cofin_of_monic (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ)
    (J : Set (Module.End ℂ (Sm E n))) (hJ : J ⊆ Zalg E n)
    (hq : ∀ (τ : E →+* ℂ) (u : ℂ), ∃ q : Polynomial ℂ, q.Monic ∧ Polynomial.aeval (cap (a := n) τ u) q ∈ J) :
    Cofin J := by
  letI : CommRing (Zalg E n) := { (inferInstance : Ring (Zalg E n)) with
    mul_comm := fun x y => Subtype.ext (GlobalTheory.AutGrowth.KilledFin.Zalg_commute x.property y.property).eq }
  exact @cofin_of_algHom E _ _ _ n (Zalg E n) inferInstance (Subalgebra.algebra _)
    (Zalg E n).val Subtype.val_injective (Subalgebra.range_val _) J hJ hq

end GlobalTheory.CompanionTheory.CTFin.MonicCofin

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactElementEigenvaluesUnitsStatement
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_element_eigenvalues_units : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n : ℕ) (H : Subgroup (GLw n w)) (g : H) (p : GLw n w) (s : Fin n → (w.adicCompletion E)ˣ), g.1 = p * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s * p⁻¹ → IsCompact (closure (Subgroup.zpowers g : Set H)) → ∀ i, Valued.v (s i : w.adicCompletion E) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.DiagBd.valued_eq_one_of_isCompact_closure_zpowers | exact GlobalTheory.CompanionTheory.DiagBd.valued_eq_one_of_isCompact_closure_zpowers | (intros; apply GlobalTheory.CompanionTheory.DiagBd.valued_eq_one_of_isCompact_closure_zpowers <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexPointLiftsToMulticone
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

noncomputable section

namespace GlobalTheory.CompanionTheory.MPDict.UnderIdeal

section Alg

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {A Ω : Type*} [CommRing A] [Field Ω]

theorem eval_eq_zero_of_mem_mCoordIdeal (e : A →+* Ω) (he : Function.Injective e) (ρ : (Σ k, ι k) → A)
    {f : Geo.MRing ι} (hf : f ∈ Geo.mCoordIdeal fun p => e (ρ p)) (ε : A →+* ℂ) (t : K → ℂ) :
    eval (fun p => t p.1 * ε (ρ p)) (MvPolynomial.map (Int.castRingHom ℂ) f) = 0 := by
  let q : Geo.MRing ι →+* MvPolynomial K A := eval₂Hom (Int.castRingHom _) fun p => C (ρ p) * X p.1
  have h1 : (MvPolynomial.map e).comp q =
      (Geo.mConeMap (fun p => e (ρ p)) : Geo.MRing ι →ₐ[ℤ] MvPolynomial K Ω).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
    · simp [q]
    · simp [q, Geo.mConeMap]
  have h0 : q f = 0 := by
    refine map_injective e he ?_
    rw [map_zero]
    have := congrArg (fun g => g f) h1
    refine this.trans ?_
    exact hf
  have h2 : (eval₂Hom ε t).comp q =
      (eval (fun p => t p.1 * ε (ρ p))).comp (MvPolynomial.map (Int.castRingHom ℂ)) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
    · simp [q]
    · simp [q, mul_comm]
  have := congrArg (fun g => g f) h2
  simp only [RingHom.comp_apply, h0, map_zero] at this
  exact this.symm

end Alg

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem ptCoord_eq_mul (x : MP ℤ m n) (c : ∀ k, Bk n k) (hx : x ∈ mchart c) :
    ∃ b : Fin (m + 1) → (MP ℤ m n).residueField x, (∀ k, b k ≠ 0) ∧ ∀ p : Σ k, Bk n k,
      ptCoord x p = b p.1 * (MP ℤ m n).evaluation (mchart c) x hx
        (resG _ (mchart_le c p.1) (pullRatio (prB n p.1) _ (c p.1) le_rfl p.2)) := by
  have key : ∀ k, ∃ b : (MP ℤ m n).residueField x, b ≠ 0 ∧ ∀ j : Bk n k,
      ptCoord x ⟨k, j⟩ = b * (MP ℤ m n).evaluation (blockChart n k (c k)) x (mchart_le c k hx)
        (pullRatio (prB n k) _ (c k) le_rfl j) := by
    intro k
    let W₀ := blockChart n k (ptChart x k)
    let W₁ := blockChart n k (c k)
    let V := W₀ ⊓ W₁
    have hxV : x ∈ V := ⟨mem_ptChart x k, mchart_le c k hx⟩
    have hV₀ : V ≤ prB n k ⁻¹ᵁ chart ℤ (n k) (ptChart x k) := inf_le_left
    have hV₁ : V ≤ prB n k ⁻¹ᵁ chart ℤ (n k) (c k) := inf_le_right
    have e₀ : ∀ j : Bk n k, ptCoord x ⟨k, j⟩ =
        (MP ℤ m n).evaluation V x hxV (pullRatio (prB n k) V (ptChart x k) hV₀ j) := by
      intro j
      show (MP ℤ m n).evaluation W₀ x (mem_ptChart x k) (pullRatio (prB n k) W₀ (ptChart x k) le_rfl j) = _
      rw [← ProjImage.evaluation_resG (inf_le_left : V ≤ W₀) x hxV]
      exact congrArg _ (resG_pullRatio (φ := prB n k) (hi := le_rfl) inf_le_left)
    have e₁ : ∀ j : Bk n k, (MP ℤ m n).evaluation W₁ x (mchart_le c k hx)
        (pullRatio (prB n k) W₁ (c k) le_rfl j) =
        (MP ℤ m n).evaluation V x hxV (pullRatio (prB n k) V (c k) hV₁ j) := by
      intro j
      rw [← ProjImage.evaluation_resG (inf_le_right : V ≤ W₁) x hxV]
      exact congrArg _ (resG_pullRatio (φ := prB n k) (hi := le_rfl) inf_le_right)
    refine ⟨(MP ℤ m n).evaluation V x hxV (pullRatio (prB n k) V (ptChart x k) hV₀ (c k)), ?_, fun j => ?_⟩
    · intro h0
      have e := congrArg ((MP ℤ m n).evaluation V x hxV)
        ((pullRatio_mul_pullRatio (φ := prB n k) (hi := hV₀) (hj := hV₁) (k := ptChart x k)).trans pullRatio_self)
      rw [map_mul, h0, zero_mul, map_one] at e
      exact zero_ne_one e
    · refine (e₀ j).trans ?_
      rw [e₁ j, ← map_mul]
      exact congrArg _ (pullRatio_mul_pullRatio (φ := prB n k) (hi := hV₀) (hj := hV₁) (k := j)).symm
  choose b hb hbe using key
  refine ⟨b, hb, fun p => ?_⟩
  rw [ProjImage.evaluation_resG]
  exact hbe p.1 p.2

theorem evaluation_genericPoint_injective {X : Scheme.{0}} [IsIntegral X] (U : X.Opens) (h : genericPoint X ∈ U) :
    Function.Injective (X.evaluation U (genericPoint X) h) := by
  have h1 : Function.Injective (X.residue (genericPoint X)).hom :=
    RingHom.injective (R := X.functionField) (X.residue (genericPoint X)).hom
  exact h1.comp (fnOf_injective U h)

end GlobalTheory.CompanionTheory.MPDict.UnderIdeal

namespace GlobalTheory.CompanionTheory.MPDict


open UnderIdeal in
theorem exists_mem_mcPts_isUnder : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀), ∃ z ∈ mcPts (ptIdeal (i (genericPoint X))), IsUnder (PtsOver.map i rfl _ y) z := by
  intro m n X _ i _ y
  obtain ⟨z, hz, hu⟩ := exists_isUnder_of_cxPt m n (PtsOver.map i rfl _ y)
  refine ⟨z, ⟨hz, fun f hf => ?_⟩, hu⟩
  choose c hc using hz
  have hwk : ∀ k, PtsOver.map i rfl _ y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k (c k)) :=
    fun k => (hu k (c k)).1.2 (hc k)
  have hwV : PtsOver.map i rfl _ y ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) :=
    CxPts.mem_ptsIn.2 (Set.mem_iInter.2 fun k => CxPts.mem_ptsIn.1 (hwk k))
  have hyV : y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart c) := hwV
  have hη : genericPoint X ∈ i ⁻¹ᵁ mchart c :=
    ((genericPoint_spec X).mem_open_set_iff (i ⁻¹ᵁ mchart c).isOpen).2 ⟨_, trivial, CxPts.mem_ptsIn.1 hyV⟩
  obtain ⟨b, hb, hbe⟩ := ptCoord_eq_mul (i (genericPoint X)) c hη
  let r : (Σ k, Bk n k) → Γ(MP ℤ m n, mchart c) := fun p =>
    resG _ (mchart_le c p.1) (pullRatio (prB n p.1) _ (c p.1) le_rfl p.2)
  let ρ : (Σ k, Bk n k) → Γ(X, i ⁻¹ᵁ mchart c) := fun p => (i.app (mchart c)).hom (r p)
  let φ := (i.residueFieldMap (genericPoint X)).hom
  have hf' : f ∈ Geo.mCoordIdeal fun p => (X.evaluation _ _ hη).hom (ρ p) := by
    have e := ProjImage.imageZ_mCoordIdeal_of_eq (ι := Bk n) (ι' := Bk n) id Function.injective_id id (fun _ => rfl) φ
      (fun k => φ (b k)) (fun k => (map_ne_zero φ).2 (hb k))
      (ptCoord (i (genericPoint X))) (fun p => (X.evaluation _ _ hη).hom (ρ p)) (fun p => by
        rw [hbe p, map_mul]
        congr 1
        exact Scheme.evaluation_naturality_apply _ _ _ _)
    rw [ptIdeal, ← e] at hf
    simpa [ReciprocityTheory.ChartRestriction.G.AI.I4.imageZ] using hf
  have h := eval_eq_zero_of_mem_mCoordIdeal (X.evaluation _ _ hη).hom
    (evaluation_genericPoint_injective _ hη) ρ hf' (evHom hyV) (fun k => z ⟨k, c k⟩)
  have hz' : (fun p : Σ k, Bk n k => z ⟨p.1, c p.1⟩ * evHom hyV (ρ p)) = z := by
    funext ⟨k, j⟩
    have e1 : evHom hyV (ρ ⟨k, j⟩) = z ⟨k, j⟩ / z ⟨k, c k⟩ := by
      rw [← CxPts.ev_eq hyV]
      refine Eq.trans ?_ ((hu k (c k)).2 j (hwk k))
      refine Eq.trans ?_ (CxPts.ev_res (mchart_le c k) hwV _)
      exact (valR_comp y.1 i (mchart c) (r ⟨k, j⟩)).symm
    show z ⟨k, c k⟩ * evHom hyV (ρ ⟨k, j⟩) = z ⟨k, j⟩
    rw [e1, mul_div_cancel₀ _ (hc k)]
  rw [hz'] at h
  exact h

end GlobalTheory.CompanionTheory.MPDict
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOrbitalIntegralUnipotent
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem jn_firstCols {D : D7} {a r t n : ℕ} (hn : r + t = n) (w : Mx D a r) (v : Mx D a t) :
    (jn hn w v).submatrix id (fun j : Fin r => finCongr hn (Fin.castAdd t j)) = w := by
  ext i j
  have e : (finSumFinEquiv.trans (finCongr hn)).symm (finCongr hn (Fin.castAdd t j)) = Sum.inl j := by
    rw [Equiv.symm_apply_eq]
    simp
  simp only [jn, Matrix.submatrix_apply, id, e, Matrix.fromCols_apply_inl]

theorem continuous_jn_pair {D : D7} {a r t n : ℕ} (hn : r + t = n) :
    Continuous fun p : Mx D a r × Mx D a t => jn hn p.1 p.2 := by
  refine continuous_matrix fun i j => ?_
  simp only [jn, Matrix.submatrix_apply, id]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm j with k | k
  · simpa using (continuous_fst.matrix_elem i k)
  · simpa using (continuous_snd.matrix_elem i k)

theorem continuous_orb_shear : IkSch → Dom → OrbFin → Shift → JnBl → Ext0 → ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t)
    (hn : W.rank + t = n) (I : IkD d n) θ, IsInfFam θ → ∀ (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E), x₀.det ≠ 0 →
    ∀ Φ ∈ schwartzA θ B.rank n,
      Continuous (fun y : Mx D W.rank t => orb W I.m (ikp I fun X => Φ (mm X (bl hn 1 y 0 1))) (ext0 hn x₀)) := by
  intro hIk hDom hOrb hShift hJn hExt D n t B W d hn I θ hθ x₀ hx Φ hΦ
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨hT, -, hS, -, -⟩ := top_mx (D := D) W.rank t
  obtain ⟨hT', -, -, -, -⟩ := top_mx (D := D) W.rank W.rank
  obtain ⟨-, g2, g3, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have hBor : BorelSpace (GA D W) := ⟨rfl⟩
  have hΨ : ikp I Φ ∈ schwartzA θ W.rank n := (hIk D n t B W d I θ hθ Φ hΦ).2
  have hcΨ : Continuous (ikp I Φ) := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ _ hΨ).1
  have hinj : Function.Injective fun j : Fin W.rank => finCongr hn (Fin.castAdd t j) := by
    intro a b h
    exact Fin.castAdd_injective _ _ ((finCongr hn).injective h)
  obtain ⟨M, hM, -, hMd⟩ := hDom D θ hθ W.rank n W.rank _ hinj _ hΨ
  have hcM : Continuous M := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ M hM).1
  have hform : ∀ (y : Mx D W.rank t) (h : GA D W),
      (ikp I fun X => Φ (mm X (bl hn 1 y 0 1))) (mm (mt W h⁻¹) (rat (ext0 hn x₀))) =
        ikp I Φ (jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0)) := by
    intro y h
    rw [hShift D n t B W d hn I Φ y, hExt D n t W hn x₀ h, hJn D n t W.rank W.rank hn]
  have hfun : (fun y : Mx D W.rank t => orb W I.m (ikp I fun X => Φ (mm X (bl hn 1 y 0 1))) (ext0 hn x₀)) =
      fun y => ∫ h, ikp I Φ (jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0)) ∂I.m := by
    funext y
    exact integral_congr_ae (Eventually.of_forall fun h => hform y h)
  rw [hfun]
  have hcw := continuous_ww (D := D) (W := W) x₀
  have hb : Integrable (fun h => M (ww W x₀ h)) I.m :=
    ⟨(hcM.comp hcw).aestronglyMeasurable, hOrb D θ hθ W I.m I.haar x₀ hx M hM⟩
  have hpt : ∀ (h : GA D W), Continuous fun y : Mx D W.rank t => ikp I Φ (jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0)) := by
    intro h
    refine hcΨ.comp ((continuous_jn_pair hn).comp (continuous_const.prodMk ?_))
    exact (continuous_const.matrix_mul continuous_id).add continuous_const
  have hmeas : ∀ y : Mx D W.rank t, Continuous fun h : GA D W => ikp I Φ (jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0)) := by
    intro y
    refine hcΨ.comp ((continuous_jn_pair hn).comp (hcw.prodMk ?_))
    exact (hcw.matrix_mul continuous_const).add continuous_const
  have hF : FirstCountableTopology (Mx D W.rank t) :=
    @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ hS
  refine continuous_of_dominated (bound := fun h => ‖M (ww W x₀ h)‖)
    (fun y => (hmeas y).aestronglyMeasurable) (fun y => Eventually.of_forall fun h => ?_) hb.norm
    (Eventually.of_forall hpt)
  have h1 := hMd (jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0))
  rw [jn_firstCols] at h1
  exact h1.trans (Complex.re_le_norm _)

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientSegmentProductEquiv
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegIncDual

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_equiv_prodIrr_of_cast {h h' N : ℕ} (e : h = h') (x : Fin h → IrrGL (k := k)) (y : Fin h' → IrrGL (k := k))
    (hxy : ∀ a, x a = y (Fin.cast e a)) (hd : ∑ a, (x a).1 = N) :
    ∃ hd' : ∑ a, (y a).1 = N, Nonempty ((prodIrr x hd).Equiv (prodIrr y hd')) := by
  subst e
  obtain rfl : x = y := funext fun a => by simpa using hxy a
  exact ⟨hd, ⟨Representation.Equiv.refl _⟩⟩

theorem nonempty_contra_trans {h h' N : ℕ} {x y : Fin h → IrrGL (k := k)} {z : Fin h' → IrrGL (k := k)} {hd : ∑ a, (x a).1 = N}
    {hy : ∑ a, (y a).1 = N} {hz : ∑ a, (z a).1 = N} (H₁ : Nonempty ((contra (prodIrr x hd)).Equiv (prodIrr y hy)))
    (H₂ : Nonempty ((prodIrr y hy).Equiv (prodIrr z hz))) :
    Nonempty ((contra (prodIrr x hd)).Equiv (prodIrr z hz)) :=
  H₁.elim fun φ => H₂.elim fun ψ => ⟨φ.trans ψ⟩

theorem dualCl_term (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) (hl : Δ.len = (segDual Δ).len)
    (a : Fin Δ.len) : dualCl (Δ.term a) = dec (segDual Δ) (Fin.cast hl a) := by
  have hc : ∀ x : IrrGL (k := k), x.IsCusp → (dualCl x).IsCusp := fun x hx =>
    (GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp hA x hx).1
  have hv : ((Fin.rev (Fin.cast hl a) : Fin (segDual Δ).len) : ℕ) = Δ.len - (a + 1) := by
    have h0 : ((Fin.cast hl a : Fin (segDual Δ).len) : ℕ) = a := rfl
    rw [Fin.val_rev, h0]; omega
  have ha : (a : ℕ) + 1 ≤ Δ.len := a.2
  change dualCl (Δ.first.nu ((a : ℕ) : ℂ)) =
    (segDual Δ).first.nu (((Fin.rev (Fin.cast hl a) : Fin (segDual Δ).len) : ℕ) : ℂ)
  rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_nu hA, GlobalTheory.CompanionTheory.SegDualPrec.first_segDual hc, IrrGL.nu_nu, hv, Nat.cast_sub ha]
  congr 1
  push_cast
  ring

theorem contra_prodIrr_term : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ}
    (hd : ∑ a, (Δ.term a).1 = N), ∃ hd' : ∑ a, (dec (segDual Δ) a).1 = N,
      Nonempty ((contra (prodIrr Δ.term hd)).Equiv (prodIrr (dec (segDual Δ)) hd')) := by
  intro k _ _ _ _ hA Δ N hd
  have hl : Δ.len = (segDual Δ).len :=
    (GlobalTheory.CompanionTheory.SegDualPrec.len_segDual (fun x hx => (GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp hA x hx).1) Δ).symm
  have H := @GlobalTheory.CompanionTheory.ContraProd.contra_prodIrr k _ _ _ _ hA Δ.len N Δ.term hd
  obtain ⟨hd₁, H₁⟩ := H
  have H' := exists_equiv_prodIrr_of_cast hl (fun a => dualCl (Δ.term a)) (dec (segDual Δ))
    (dualCl_term hA Δ hl) hd₁
  obtain ⟨hd₂, H₂⟩ := H'
  exact ⟨hd₂, nonempty_contra_trans H₁ H₂⟩

end GlobalTheory.CompanionTheory.SegIncDual

end
end

