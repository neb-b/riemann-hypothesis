module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2753
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2857
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2862
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1575
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0799
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2861
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2447
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2834
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2814
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2302
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2647
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2685
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2790
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2852
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentApproximation.AddDense

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColengthRangeMapGe
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem colength_range_map_ge (p : ℕ) [Fact p.Prime] (T : GlobalTheory.Dieu.Theory p) (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H) :
    (Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G H q)) : ℕ∞) ≤
        Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) ∧
      (Module.finrank k (G.dual.Lie ⧸ LinearMap.range (lieMap H.dual G.dual (dualHom G H q))) : ℕ∞) ≤
        Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) := by
  have hp : (p : k) = 0 := CharP.cast_eq_zero k p
  haveI : Module.Finite k G.RigExt := (_root_.GlobalTheory.PDivGroup.finrank_rigExt_omega p k hp G).2.1
  obtain ⟨θ, hθ⟩ := GlobalTheory.Dieu.theta_exists p T k
  have hred : ∀ m : T.M H, T.red G (T.map q m) = rigExtMap q (T.red H m) := fun m => by
    show T.base.red G trivial (T.base.smap trivial trivial (SemiHom.ofHom q) m) = _
    rw [T.base.red_smap, SemiHom.ofHom_rig]
  constructor
  · haveI : Module.Finite k G.omega :=
      Module.Finite.of_injective G.rigOfOmega (G.rigOfOmega_injective_of_eq_zero hp)
    obtain ⟨-, hsurj, -, hsemi, hnat⟩ := hθ G
    let Q := LinearMap.range (omegaMap G H q)
    refine (_root_.GlobalTheory.Dieu.length_ge_finrank_of_semilinear_surj p k (T.M G) (G.omega ⧸ Q) (WittVector.frobeniusEquiv p k)
      (Q.mkQ.toAddMonoidHom.comp (θ G)) (Q.mkQ_surjective.comp hsurj) (fun a n => ?_)
      (LinearMap.range (T.map q))).1 ?_
    · show Q.mkQ (θ G (WittVector.frobenius a • n)) = WittVector.constantCoeff a • Q.mkQ (θ G n)
      exact (congrArg Q.mkQ (hsemi a n)).trans (Q.mkQ.map_smul _ _)
    · rintro _ ⟨m, rfl⟩
      show Q.mkQ (θ G (T.map q m)) = 0
      rw [hnat, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨_, rfl⟩
  · haveI : Module.Finite k G.dual.Lie := Module.Finite.of_surjective (G.rigToLie hp) (G.rigToLie_surjective hp)
    let Q := LinearMap.range (lieMap H.dual G.dual (dualHom G H q))
    refine (_root_.GlobalTheory.Dieu.length_ge_finrank_of_semilinear_surj p k (T.M G) (G.dual.Lie ⧸ Q) (RingEquiv.refl _)
      ((Q.mkQ ∘ₗ G.rigToLie hp).toAddMonoidHom.comp (T.red G).toAddMonoidHom)
      ((Q.mkQ_surjective.comp (G.rigToLie_surjective hp)).comp (T.base.red_surjective G trivial))
      (fun a n => ?_) (LinearMap.range (T.map q))).1 ?_
    · show Q.mkQ (G.rigToLie hp (T.red G (a • n))) = WittVector.constantCoeff a • Q.mkQ (G.rigToLie hp (T.red G n))
      rw [LinearMap.map_smulₛₗ]
      exact (congrArg Q.mkQ ((G.rigToLie hp).map_smul _ _)).trans (Q.mkQ.map_smul _ _)
    · rintro _ ⟨m, rfl⟩
      show Q.mkQ (G.rigToLie hp (T.red G (T.map q m))) = 0
      rw [hred]
      have heq := rigToLie_rigExtMap hp q (T.red H m)
      apply (congrArg Q.mkQ heq).trans
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨_, rfl⟩

end GlobalTheory.Dieu
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugatePlaceValuationCountUnder
section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

noncomputable section

namespace GlobalTheory.ConjPlace

open GlobalTheory.IdemSupport (cP cO mem_cP cO_cO cO_coe)

theorem conj_smul_eq (D : D7) (x : 𝓞 D.host.E) : D.host.conj • x = cO D x := by
  apply RingOfIntegers.ext
  rw [cO_coe, Formalism.BasicNotions.Examples₂.star_eq_conj]
  rfl

theorem mem_conj_smul (D : D7) (I : Ideal (𝓞 D.host.E)) (x : 𝓞 D.host.E) :
    x ∈ (D.host.conj • I : Ideal (𝓞 D.host.E)) ↔ cO D x ∈ I := by
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  have : D.host.conj⁻¹ • x = cO D x := by
    rw [inv_smul_eq_iff, conj_smul_eq, cO_cO]
  rw [this]

theorem count_conj (D : D7) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : (cP w).asIdeal = D.host.conj • w.asIdeal)
    (𝔞 : Ideal (𝓞 D.host.E)) (h : 𝔞 ≠ ⊥) :
    FractionalIdeal.count D.host.E (cP w)
      ((D.host.conj • 𝔞 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
      FractionalIdeal.count D.host.E w (𝔞 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
  have h' : (D.host.conj • 𝔞 : Ideal (𝓞 D.host.E)) ≠ 0 := fun e => h (by
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) e
    simpa using this)
  rw [FractionalIdeal.count_coe _ _ h', FractionalIdeal.count_coe _ _ h]
  congr 1
  refine eq_of_forall_le_iff fun k => ?_
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 h') (cP w).associates_irreducible,
    ← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 h) w.associates_irreducible,
    ← Associates.mk_pow, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Associates.mk_le_mk_iff_dvd,
    Ideal.dvd_iff_le, Ideal.dvd_iff_le, hw, ← smul_pow', Ideal.pointwise_smul_le_pointwise_smul_iff]

theorem exists_norm (D : D7) (x : 𝓞 D.host.E) :
    ∃ y : 𝓞 D.host.F, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) y = x * cO D x := by
  have hm : ((x * cO D x : 𝓞 D.host.E) : D.host.E) ∈ maximalRealSubfield D.host.E := by
    rw [← IsCMField.complexConj_eq_self_iff]
    change star ((x * cO D x : 𝓞 D.host.E) : D.host.E) = _
    rw [← cO_coe, map_mul, cO_cO, mul_comm]
  refine ⟨⟨⟨_, hm⟩, ?_⟩, rfl⟩
  exact (isIntegral_algebraMap_iff ).1 (x * cO D x).isIntegral_coe

theorem cO_algebraMap (D : D7) (y : 𝓞 D.host.F) :
    cO D (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) y) = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) y := by
  apply RingOfIntegers.ext
  rw [cO_coe]
  exact (IsCMField.complexConj_eq_self_iff D.host.E _).2 (y : D.host.F).2

theorem under_cP (D : D7) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    (cP w).under (𝓞 D.host.F) = w.under (𝓞 D.host.F) := by
  ext y
  change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) y ∈ (cP w).asIdeal ↔ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) y ∈ w.asIdeal
  rw [mem_cP, cO_algebraMap]

theorem under_eq_iff (D : D7) (w w'' : HeightOneSpectrum (𝓞 D.host.E)) :
    w''.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) ↔ w'' = w ∨ w'' = cP w := by
  refine ⟨fun h => ?_, ?_⟩
  · have hs : (w''.asIdeal : Set (𝓞 D.host.E)) ⊆ w.asIdeal ∪ (cP w).asIdeal := fun x hx => by
      obtain ⟨y, hy⟩ := exists_norm D x
      have h1 : y ∈ (w''.under (𝓞 D.host.F)).asIdeal := by
        change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) y ∈ w''.asIdeal
        rw [hy]; exact Ideal.mul_mem_right _ _ hx
      rw [h] at h1
      change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) y ∈ w.asIdeal at h1
      rw [hy] at h1
      exact w.isPrime.mem_or_mem h1
    exact (Ideal.subset_union.1 hs).imp GlobalTheory.IdemSupport.eq_of_le GlobalTheory.IdemSupport.eq_of_le
  · rintro (rfl | rfl)
    · rfl
    · exact under_cP D w

theorem conj_place : ∀ (D : D7), ∀ w : HeightOneSpectrum (𝓞 D.host.E), ∃ w' : HeightOneSpectrum (𝓞 D.host.E), w'.asIdeal = D.host.conj • w.asIdeal ∧
    (∀ x : Formalism.MainNotions.StandardLatticesGL3.AE D, Valued.v (GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.sgA D x) w') = Valued.v (GlobalTheory.BotFormula.toFinE D x w)) ∧
    (∀ 𝔞 : Ideal (𝓞 D.host.E), 𝔞 ≠ ⊥ → FractionalIdeal.count D.host.E w' ((D.host.conj • 𝔞 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
      FractionalIdeal.count D.host.E w (𝔞 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) ∧
    ∀ w'' : HeightOneSpectrum (𝓞 D.host.E), w''.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) ↔ w'' = w ∨ w'' = w' := by
  intro D w
  have hw : (cP w).asIdeal = D.host.conj • w.asIdeal := by
    ext x
    rw [mem_cP, mem_conj_smul]
  refine ⟨cP w, hw, fun x => ?_, count_conj D w hw, under_eq_iff D w⟩
  have hc : w = GlobalTheory.CuspRep.conjSrc (D.host.conj : D.host.E ≃+* D.host.E) (cP w) :=
    GlobalTheory.CuspRep.eq_conjSrc fun y => by
      have := GlobalTheory.ConjVal.valuation_cP w y
      rw [Formalism.BasicNotions.Examples₂.star_eq_conj] at this
      exact this
  rw [GlobalTheory.BotFormula.toFinE_sgA]
  refine ((GlobalTheory.CuspRep.conjLoc_spec (D.host.conj : D.host.E ≃+* D.host.E) (cP w)).2.2
    (GlobalTheory.BotFormula.toFinE D x (GlobalTheory.CuspRep.conjSrc (D.host.conj : D.host.E ≃+* D.host.E) (cP w)))).trans ?_
  rw [← hc]

end GlobalTheory.ConjPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamPolarizationFormPrimitive
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.ConjSeq GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt
open GlobalTheory.Cris (dp0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HodgeWeil

theorem triv_theta (hC : GlobalTheory.Published.CubeTheorem) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {L : LB A.left} (hL : L.IsLB) : AbLaw.Triv (Theta A L) := by
  have := hA.comm
  have h := hC S A hA L hL (G3 A) (x3 A 0) (x3 A 1) (x3 A 2)
  have e := (CechPic.cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 h
  rw [CechPic.cls_linComb hL _ _ _, Fin.sum_univ_eight] at e
  refine (CechPic.cls_eq_zero_iff (LB.isLB_linComb hL _ _)).1 ?_
  rw [CechPic.cls_linComb hL _ _ _, ← e, ← Equiv.ulift.symm.sum_comp]
  have u : (Finset.univ : Finset (Finset (Fin 3))) = {{0, 1, 2}, {0, 1}, {0, 2}, {1, 2}, {0}, {1}, {2}, ∅} := by
    decide
  rw [u]
  iterate 7 rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  have k0 : psum A (x3 A) {0, 1, 2} = x3 A 0 * x3 A 1 * x3 A 2 :=
    (show _ = x3 A 0 * (x3 A 1 * (x3 A 2 * 1)) from rfl).trans (by rw [_root_.mul_one, _root_.mul_assoc])
  have k1 : psum A (x3 A) {0, 1} = x3 A 0 * x3 A 1 :=
    (show _ = x3 A 0 * (x3 A 1 * 1) from rfl).trans (by rw [_root_.mul_one])
  have k2 : psum A (x3 A) {0, 2} = x3 A 0 * x3 A 2 :=
    (show _ = x3 A 0 * (x3 A 2 * 1) from rfl).trans (by rw [_root_.mul_one])
  have k3 : psum A (x3 A) {1, 2} = x3 A 1 * x3 A 2 :=
    (show _ = x3 A 1 * (x3 A 2 * 1) from rfl).trans (by rw [_root_.mul_one])
  have k4 : psum A (x3 A) {0} = x3 A 0 := _root_.mul_one (x3 A 0)
  have k5 : psum A (x3 A) {1} = x3 A 1 := _root_.mul_one (x3 A 1)
  have k6 : psum A (x3 A) {2} = x3 A 2 := _root_.mul_one (x3 A 2)
  have k7 : psum A (x3 A) ∅ = 1 := rfl
  simp only [Equiv.ulift_symm_down, k0, k1, k2, k3, k4, k5, k6, k7, ← add_assoc]
  rfl

section Point

variable {R D : Type} [CommRing R] [CommRing D] [Bialgebra R D] [Module.Finite R D] [Module.Projective R D]
  [Coalgebra.IsCocomm R D]

end Point

section Tower

variable {p : ℕ} {R : Type} [CommRing R] {A B : Over (Sp R)} [GrpObj A] [GrpObj B] {𝒜 ℬ : PDivGroup p R}

end Tower

section Linear

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {𝒜 : PDivGroup p K}
  {w : 𝒜 ⟶ 𝒜.dual} {E : V ≃ₗ[K] 𝒜.RigExt} {β : V →ₗ[K] V →ₗ[K] K} {ε : ℤˣ}


end Linear

end GlobalTheory.HodgeWeil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamToRigidifiedExtensionBijectivePNilpotent
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt

theorem bijective_of_isCan_of_isNilpotent_of_hodgeDeRham : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R], IsNilpotent (p : R) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (G : PDivGroup p R) (t : G.TorsionTower A) (L : primDR A →ₗ[R] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))), (∀ c, IsCan t c (L c)) → Function.Bijective L := by
  intro hH p _ R _ hnil A _ g hA hg G t L hL
  obtain ⟨N, hN⟩ := hnil
  obtain ⟨hF, hHo, -⟩ := GlobalTheory.abelianDeRham_free_hodge_baseChange hH
  obtain ⟨hAll, -⟩ := hF R A g hA hg
  obtain ⟨hLie, hCompl, hFfin, hFproj, -⟩ := hHo R A g hA hg
  have hO : Function.Surjective (toH1O (A.hom ≫ 𝟙 _)) :=
    GlobalTheory.PtExt.toH1O_surjective_of_abelian hH R A g hA hg
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_hodgeFiltration_to_pDivOmega_linearMap p R N hN A hA G t

  haveI : Module.Finite R (Cot R (G.A N)) := .of_surjective _ (AugCot.d_surjective _)
  haveI : Module.Finite R G.omega :=
    .equiv (LinearEquiv.ofBijective _
      (PDivGroup.omegaLevel_bijective_of_pow_eq_zero p R N hN G N le_rfl)).symm
  haveI : Module.Projective R (PrimitiveSubmodule A) := hFproj

  have hψs : Function.Surjective ψ :=
    GlobalTheory.surjective_of_range_sup_smul_top_eq_top R _ G.omega ψ
      (GlobalTheory.T.primitive_hodge_to_omega_span_mod_maximal hH p R N hN A g hA hg G t ψ hψ)
  have hψi : Function.Injective ψ := by
    refine GlobalTheory.injective_of_dualMap_surjective_of_projective R _ G.omega ψ fun l => ?_
    obtain ⟨x, hx⟩ := _root_.GlobalTheory.PtExt.exists_lie_comp_psi_eq p R N hN A hA hLie hCompl G t ψ hψ l
    exact ⟨x, LinearMap.ext fun c => hx c⟩

  have hLF : ∀ c : PrimitiveSubmodule A, L c.1 = G.rigOfOmega (ψ c) := fun c =>
    GlobalTheory.PtExt.isCan_unique R A p G t c.1 hA _ _ (hL c.1) (hψ c)
  refine ⟨(injective_iff_map_eq_zero L).2 fun c hc => ?_, fun x => ?_⟩
  · have hcF : c ∈ PrimitiveSubmodule A :=
      GlobalTheory.T.mem_primitiveSubmodule_of_isCan_of_rigToExt_eq_zero p R N hN A hA G t c (L c) (hL c) (by rw [hc]; exact G.rigToExt.map_zero)
    have h1 : G.rigOfOmega (ψ ⟨c, hcF⟩) = 0 := by rw [← hLF ⟨c, hcF⟩]; exact hc
    have h2 : ψ ⟨c, hcF⟩ = 0 :=
      PDivGroup.rigOfOmega_injective_of_pow p R N hN G (by rw [h1, map_zero])
    have h3 : (⟨c, hcF⟩ : PrimitiveSubmodule A) = 0 := hψi (by rw [h2, map_zero])
    exact congrArg Subtype.val h3
  · obtain ⟨c, x', hcx', hx'⟩ := _root_.GlobalTheory.PtExt.exists_isCan_rigToExt_eq p R N hN A hA hAll hO G t x
    have hx'L : x' = L c := GlobalTheory.PtExt.isCan_unique R A p G t c hA _ _ hcx' (hL c)
    have hd : G.rigToExt (x - L c) = 0 := by
      exact (G.rigToExt.map_sub x (L c)).trans (sub_eq_zero.mpr (hx'L ▸ hx'.symm))
    obtain ⟨w, hw⟩ := (G.exact_rigOfOmega_rigToExt (x - L c)).1 hd
    obtain ⟨c₁, rfl⟩ := hψs w
    refine ⟨c + c₁.1, ?_⟩
    rw [map_add (f := _), hLF c₁, hw, add_sub_cancel]

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseAffineChartPreimageInterior
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BalProj

theorem chart_dense_interior : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens), Dense ((chart U).base ⁻¹' (interior Y : Set Y.X)) := by
  intro E _ _ _ H Dw l Xo c Y U
  have hi := IsAffineOpen.isOpenImmersion_fromSpec U.2
  have h : IsOpenMap (chart U).base := (Scheme.Hom.isOpenEmbedding (f := U.2.fromSpec)).isOpenMap
  exact (dense_interior Y).preimage h

end GlobalTheory.BalProj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseRationalHomPointsIdealCompletion
section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

noncomputable section

namespace GlobalTheory.CosetOrthDens

section General

variable {E : Type} [Field E] [NumberField E]

theorem inHat_algebraMap_iff {I : FractionalIdeal (𝓞 E)⁰ E} (hI : I ≠ 0) (x : E) :
    InHat I (algebraMap E (FiniteAdeleRing (𝓞 E) E) x) ↔ x ∈ I :=
  (GlobalTheory.Idele.mem_adelicIdeal_iff hI).symm.trans (GlobalTheory.Idele.algebraMap_mem_adelicIdeal hI x)

theorem isOpen_inHat_one : IsOpen {x : FiniteAdeleRing (𝓞 E) E | InHat 1 x} := by
  have h := RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
    (A := fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) fun v => Valued.isOpen_valuationSubring _
  have e : {x : FiniteAdeleRing (𝓞 E) E | InHat 1 x} =
      {x : FiniteAdeleRing (𝓞 E) E | ∀ v, x v ∈ (v.adicCompletionIntegers E : Set (v.adicCompletion E))} := by
    ext x
    exact inHat_one_iff x
  rw [e]
  exact h

theorem isOpen_inHat {I : FractionalIdeal (𝓞 E)⁰ E} (hI : I ≠ 0) : IsOpen {x : FiniteAdeleRing (𝓞 E) E | InHat I x} := by
  obtain ⟨c, hc0, hc⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger hI
  set a : E := algebraMap (𝓞 E) E c with ha
  have ha0 : a ≠ 0 := by simpa [ha] using hc0
  rw [isOpen_iff_mem_nhds]
  intro y hy
  have hcont : Continuous fun x : FiniteAdeleRing (𝓞 E) E => (x - y) * algebraMap E (FiniteAdeleRing (𝓞 E) E) a⁻¹ :=
    (continuous_id.sub continuous_const).mul continuous_const
  refine Filter.mem_of_superset ((isOpen_inHat_one.preimage hcont).mem_nhds ?_) fun x hx => ?_
  · show InHat 1 ((y - y) * _)
    rw [sub_self, zero_mul]
    exact inHat_zero 1
  · have h1 := InHat.mul_left hx ((inHat_algebraMap_iff hI a).2 hc)
    rw [mul_assoc, ← map_mul, inv_mul_cancel₀ ha0, map_one, mul_one] at h1
    have h2 := h1.add hy
    rwa [sub_add_cancel] at h2

end General

variable {D : D7}

def lift (D : D7) (s : FA D) : AE D :=
  GlobalTheory.LFun.extZero D.host.F D.host.E ((GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm s)

theorem continuous_lift : Continuous (lift D) :=
  GlobalTheory.LFun.continuous_extZero.comp GlobalTheory.LFun.continuous_finAdEquiv_symm

theorem infPart_lift (s : FA D) : infPart D (lift D s) = 0 := GlobalTheory.LFun.infTens_extZero _

theorem fe_lift (s : FA D) : fe D (lift D s) = s := by
  have : finPart D (lift D s) = (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm s := GlobalTheory.LFun.finTens_extZero _
  rw [fe_apply, this, RingEquiv.apply_symm_apply]

theorem lift_fe {x : AE D} (hx : infPart D x = 0) : lift D (fe D x) = x := by
  refine sub_eq_zero.1 (GlobalTheory.LatVac.eq_zero_of_parts _ ?_ ?_)
  · rw [RingHom.map_sub, infPart_lift, hx, sub_self]
  · apply (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective
    rw [map_zero, ← fe_apply, map_sub, fe_lift, sub_self]

theorem lift_algebraMap (γ : D.host.E) :
    lift D (algebraMap D.host.E (FA D) γ) = pairA D.host.F 0 1 ⊗ₜ[D.host.F] γ := by
  have h1 : infPart D (pairA D.host.F 0 1 ⊗ₜ[D.host.F] γ) = 0 := by
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] γ = 0
    exact TensorProduct.zero_tmul _ _
  have h2 : fe D (pairA D.host.F 0 1 ⊗ₜ[D.host.F] γ) = algebraMap D.host.E (FA D) γ := by
    show GlobalTheory.LFun.toFinAd D.host.F D.host.E ((1 : Af D.host.F) ⊗ₜ[D.host.F] γ) = _
    rw [GlobalTheory.LFun.toFinAd_tmul, map_one, one_mul]
  rw [← h2, lift_fe h1]

theorem exists_finPt_sub_mem : ∀ {D : D7} (S T : HSp D) (r : D.host.E) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), r ≠ 0 → I ≠ 0 →
  ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ u : WO S T, HatPt r I u →
  ∃ z : Matrix (Fin T.rank) (Fin S.rank) D.host.E, (∀ i j, z i j ∈ I) ∧ u - finPt (S := S) (T := T) rfl rfl r z ∈ U := by
  intro D S T r I hr hI U hU u hu
  haveI hg : IsTopologicalAddGroup (WO S T) := inferInstance
  haveI : ContinuousSub (WO S T) := IsTopologicalAddGroup.to_continuousSub
  let Φ : (Fin T.rank → Fin S.rank → FA D) → WO S T := fun y =>
    Matrix.of fun i j => lift D (algebraMap D.host.E (FA D) r⁻¹ * y i j)
  have hΦ : Continuous Φ := continuous_matrix fun i j =>
    continuous_lift.comp (continuous_const.mul ((continuous_apply j).comp (continuous_apply i)))
  have hd : DenseRange (Pi.map fun (_ : Fin T.rank) => Pi.map fun (_ : Fin S.rank) => algebraMap D.host.E (FA D)) :=
    DenseRange.piMap fun _ => DenseRange.piMap fun _ =>
      PI.UnipApproxD.IntegersDenseFiniteAdeles.denseRange (R := 𝓞 D.host.E) (K := D.host.E)
  have hO : IsOpen ({y | u - Φ y ∈ U} ∩ ⋂ i, ⋂ j, {y : Fin T.rank → Fin S.rank → FA D | InHat I (y i j)}) :=
    (hU.preimage (continuous_const.sub hΦ)).inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (isOpen_inHat hI).preimage (f := fun y : Fin T.rank → Fin S.rank → FA D => y i j)
        ((continuous_apply j).comp (continuous_apply i)))
  have h0 : Φ (fun i j => algebraMap D.host.E (FA D) r * fe D (u i j)) = u := by
    funext i j
    show lift D (algebraMap D.host.E (FA D) r⁻¹ * (algebraMap D.host.E (FA D) r * fe D (u i j))) = u i j
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hr, map_one, one_mul]
    exact lift_fe (congrFun (congrFun hu.1 i) j)
  obtain ⟨z, hz1, hz2⟩ := hd.exists_mem_open hO ⟨fun i j => algebraMap D.host.E (FA D) r * fe D (u i j), by
    show u - Φ _ ∈ U
    rw [h0, sub_self]
    exact U.zero_mem, Set.mem_iInter.2 fun i => Set.mem_iInter.2 fun j => hu.2 i j⟩
  refine ⟨Matrix.of fun i j => -z i j, fun i j => ?_, ?_⟩
  · have : z i j ∈ I := (inHat_algebraMap_iff hI _).1 (Set.mem_iInter.1 (Set.mem_iInter.1 hz2 i) j)
    exact (I : Submodule (𝓞 D.host.E) D.host.E).neg_mem this
  · have e : finPt (S := S) (T := T) rfl rfl r (Matrix.of fun i j => -z i j) =
        Φ (Pi.map (fun (_ : Fin T.rank) => Pi.map fun (_ : Fin S.rank) => algebraMap D.host.E (FA D)) z) := by
      funext i j
      show pairA D.host.F 0 1 ⊗ₜ[D.host.F] (-(r⁻¹ * -z i j)) =
        lift D (algebraMap D.host.E (FA D) r⁻¹ * algebraMap D.host.E (FA D) (z i j))
      rw [← map_mul, lift_algebraMap, mul_neg, neg_neg]
    rw [e]
    exact hz1

end GlobalTheory.CosetOrthDens
end
end

