module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0004
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0836
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0883
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0154
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0299
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0017
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EOpEqAsAlgebraHom
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHeckeOpFullOfLevel
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.RowsNonzero

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Abstract

variable {K G X H E : Type} [Field K] [Group G] [Fintype G] [AddCommGroup X] [Module K X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]


omit [Fintype G] in
theorem mem_range_adjoint (ρ : Representation ℂ G H) (π : Representation ℂ G E) (Θ : H →ₗ[ℂ] E)
    (hρ : ∀ g y, ‖ρ g y‖ = ‖y‖) (hΘ : ∀ g y, Θ (ρ g y) = π g (Θ y)) (g : G) {y : H}
    (hy : y ∈ LinearMap.range (LinearMap.adjoint Θ)) : ρ g y ∈ LinearMap.range (LinearMap.adjoint Θ) := by
  rw [← LinearMap.orthogonal_ker, Submodule.mem_orthogonal] at hy ⊢
  intro u hu
  have h1 : ρ g (ρ g⁻¹ u) = u := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have h2 : inner ℂ (ρ g (ρ g⁻¹ u)) (ρ g y) = inner ℂ (ρ g⁻¹ u) y := LinearIsometry.inner_map_map ⟨ρ g, hρ g⟩ _ _
  rw [← h1, h2]
  refine hy _ ?_
  rw [LinearMap.mem_ker] at hu ⊢
  rw [hΘ, hu, map_zero]

theorem exists_rational {σ : K →+* ℂ} (j : X →ₛₗ[σ] H) (r : Representation K G X) (ρ : Representation ℂ G H)
    (π : Representation ℂ G E) (Θ : H →ₗ[ℂ] E) (hj : ∀ g z, j (r g z) = ρ g (j z)) (hρ : ∀ g y, ‖ρ g y‖ = ‖y‖)
    (hΘ : ∀ g y, Θ (ρ g y) = π g (Θ y))
    (hrat : LinearMap.range (LinearMap.adjoint Θ) ≤
      Submodule.span ℂ (j '' {z | j z ∈ LinearMap.range (LinearMap.adjoint Θ)}))
    (a b : G → K) {x u : E} (hx : x ≠ 0) (hu : Θ (LinearMap.adjoint Θ u) = x)
    (ha : ∑ g, σ (a g) • π g x = x) (hb : ∑ g, σ (b g) • π g x = x) :
    ∃ z, (∑ g, a g • r g) ((∑ g, b g • r g) z) ≠ 0 ∧
      j ((∑ g, a g • r g) ((∑ g, b g • r g) z)) ∈ LinearMap.range (LinearMap.adjoint Θ) := by
  have hop : ∀ (c : G → K) z, j ((∑ g, c g • r g) z) = ∑ g, σ (c g) • ρ g (j z) := fun c z => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smulₛₗ, hj]
  have hst : ∀ (c : G → K) z, j z ∈ LinearMap.range (LinearMap.adjoint Θ) →
      j ((∑ g, c g • r g) z) ∈ LinearMap.range (LinearMap.adjoint Θ) := fun c z hz => by
    rw [hop]
    exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (mem_range_adjoint ρ π Θ hρ hΘ g hz)
  have hth : ∀ (c : G → K) z, Θ (j ((∑ g, c g • r g) z)) = (∑ g, σ (c g) • π g) (Θ (j z)) := fun c z => by
    rw [hop]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, hΘ, LinearMap.sum_apply, LinearMap.smul_apply]
  by_contra hn
  push Not at hn
  have hker : Submodule.span ℂ (j '' {z | j z ∈ LinearMap.range (LinearMap.adjoint Θ)}) ≤
      LinearMap.ker ((∑ g, σ (a g) • π g) ∘ₗ (∑ g, σ (b g) • π g) ∘ₗ Θ) := by
    rw [Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    have h0 : (∑ g, a g • r g) ((∑ g, b g • r g) z) = 0 := by
      by_contra h0
      exact hn z h0 (hst a _ (hst b z hz))
    show (∑ g, σ (a g) • π g) ((∑ g, σ (b g) • π g) (Θ (j z))) = 0
    rw [← hth, ← hth, h0, map_zero, map_zero]
  have h1 : (∑ g, σ (a g) • π g) ((∑ g, σ (b g) • π g) (Θ (LinearMap.adjoint Θ u))) = 0 := hker (hrat ⟨u, rfl⟩)
  simp only [hu, LinearMap.sum_apply, LinearMap.smul_apply, hb, ha] at h1
  exact hx h1


omit [FiniteDimensional ℂ E] in
theorem sum_lvlIdem {σ : K →+* ℂ} (π : Representation ℂ G E) (P : Subgroup G) (ψ : P →* Kˣ) {x : E}
    (hx : ∀ g : P, π (g : G) x = σ ((ψ g : Kˣ) : K) • x) : ∑ g, σ ((lvlIdem P ψ).coeff g) • π g x = x := by
  classical
  have hc : (Nat.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have h1 : ∀ (h : G) (c : K), ∑ g, σ ((MonoidAlgebra.single h c).coeff g) • π g x = σ c • π h x := fun h c => by
    rw [Finset.sum_eq_single h]
    · simp
    · intro g _ hg
      simp [Finsupp.single_eq_of_ne hg]
    · simp
  have h2 : ∀ h : P, σ ((Nat.card P : K)⁻¹ * ((ψ h⁻¹ : Kˣ) : K)) • π (h : G) x = (Nat.card P : ℂ)⁻¹ • x := fun h => by
    rw [hx h, smul_smul, ← map_mul, mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, mul_one,
      map_inv₀, map_natCast]
  unfold lvlIdem
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, map_sum, Finset.sum_smul]
  rw [Finset.sum_comm]
  simp only [h1, h2, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← Nat.card_eq_fintype_card, mul_inv_cancel₀ hc, one_smul]

end Abstract

section Hecke

open GlobalTheory.HeckeModel GlobalTheory.SphericalOps

variable {D : D7}

variable {V : HSp D} {S : D.what₂.Tau → SPar} {β : GL (Fin V.rank) (Lev.EAf D)}

end Hecke

section Rows

variable {D : D7}

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem dZ_pos {K : Type} [Field K] [NumberField K] [StarRing K] (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms)
    {z : B.S.Forms} (h0 : B.S.gaOp B.r (idemOf ℓ.X) (B.S.gaOp B.r (lvlIdem ℓ.P ℓ.ψ) z) ≠ 0)
    (hZ : B.S.gaOp B.r (idemOf ℓ.X) (B.S.gaOp B.r (lvlIdem ℓ.P ℓ.ψ) z) ∈ Z) : 0 < B.dZ ℓ Z := by
  rw [← B.gaOp_mul, ← goodAt] at h0 hZ
  have hV : LinearMap.range (B.vE ℓ).mulVecLin = LinearMap.range (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ)).mulVecLin :=
    (image_idempotent_spec K B.S.dim (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ))).2
  obtain ⟨u, hu⟩ : B.S.basis.equivFun (B.S.gaOp B.r (goodAt ℓ.X ℓ.P ℓ.ψ) z) ∈ LinearMap.range (B.vE ℓ).mulVecLin := by
    rw [hV]
    exact ⟨B.S.basis.equivFun z, by rw [Matrix.mulVecLin_apply, CSD.gaMat_mulVec_equivFun]⟩
  rw [Matrix.mulVecLin_apply] at hu
  refine Nat.pos_of_ne_zero fun h => h0 ?_
  have h1 : u ∈ B.Z0 ℓ Z := by
    rw [BlockDat.Z0, B.mem_goodPart_iff, hu, LinearEquiv.symm_apply_apply]
    exact hZ
  rw [Submodule.finrank_eq_zero.1 h, Submodule.mem_bot] at h1
  rw [h1, Matrix.mulVec_zero] at hu
  exact B.S.basis.equivFun.map_eq_zero_iff.1 hu.symm

end Rows

end GlobalTheory.RowsNonzero

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedAtPlaceIdempotentOfHeckeCharUnramifi
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Links Formalism.L2.Host GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnramOver

theorem map_eq_one_of_supp {R K : Type} [CommRing R] [CommRing K] (f : R →+* K) {e x : R}
    (hx : e * (x - 1) = x - 1) (he : f e = 0) : f x = 1 := by
  have h := congrArg f hx
  rw [map_mul, map_sub, map_one, he, zero_mul] at h
  exact sub_eq_zero.mp h.symm

theorem val_eq_one_of_unit {R K Γ : Type} [CommRing R] [CommRing K] [LinearOrderedCommMonoidWithZero Γ]
    (w : Valuation K Γ) (f : R →+* K) (x : Rˣ) (a : w (f x) ≤ 1) (b : w (f (x⁻¹ : Rˣ)) ≤ 1) : w (f x) = 1 := by

  have hprod : w (f x) * w (f (x⁻¹ : Rˣ)) = 1 := by
    rw [← Valuation.map_mul, ← map_mul f, Units.mul_inv, map_one f, Valuation.map_one]
  refine le_antisymm a ?_
  calc (1 : Γ) = w (f x) * w (f (x⁻¹ : Rˣ)) := hprod.symm
    _ ≤ w (f x) := mul_le_of_le_one_right' b

theorem unramAt_of_unrAt : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ →
    ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
    (∀ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) = v → χ.UnrAt P) → UnramAt ε c := by
  classical
  intro D c χ hce v ε hε hunr x hsupp hxi hxii
  obtain ⟨ι, hι1, hint, happ⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hmain⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι hι1 hint
    (GlobalTheory.PlaceIdem.exists_isPlIdem D ι hι1 hint happ) c χ hce
  obtain ⟨α, rfl, -, hα0⟩ := hε

  have hinf0 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
    show (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E))
      (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    rw [Algebra.TensorProduct.map_tmul]
    exact TensorProduct.zero_tmul _ _
  have hfin : finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = α ⊗ₜ[D.host.F] (1 : D.host.E) := by
    show (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E))
      (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) = _
    rw [Algebra.TensorProduct.map_tmul]
    rfl

  have hx1 : infPart D (x : AE D) = 1 := map_eq_one_of_supp (infPart D) hsupp hinf0

  have hval : ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι (finPart D (x : AE D)) P) = 1 := fun P =>
    val_eq_one_of_unit Valued.v ((GlobalTheory.CharLocProd.evalAt P).comp (ι.toRingHom.comp (finPart D))) x
      ((hint _).1 hxi P) ((hint _).1 hxii P)

  have hoff : ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) ≠ v →
      ι (finPart D (x : AE D)) P = 1 := by
    intro P hP
    refine map_eq_one_of_supp ((GlobalTheory.CharLocProd.evalAt P).comp (ι.toRingHom.comp (finPart D))) hsupp ?_
    show ι (finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α))) P = 0
    rw [hfin]
    have hα : α (P.under (𝓞 D.host.F)) = 0 := hα0 _ hP
    apply GlobalTheory.PlaceIdem.eq_zero_of_val
    intro n
    have h := happ α 0 P n (by rw [hα, map_zero, sub_zero, Valuation.map_zero]; exact zero_le')
    rwa [map_zero, map_zero, sub_zero] at h

  obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN
    (Units.map (ι.toRingHom.comp (finPart D)).toMonoidHom x)
  have hXP : ∀ P, ((Units.map (ι.toRingHom.comp (finPart D)).toMonoidHom x : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) :
      FiniteAdeleRing (𝓞 D.host.E) D.host.E) P = ι (finPart D (x : AE D)) P := fun _ => rfl
  have hS2 : ∀ P ∈ S, Valued.v (ι (finPart D (x : AE D)) P) = P.valuation D.host.E (k P : D.host.E) ∧
      Valued.v (ι (finPart D (x : AE D)) P - algebraMap D.host.E _ (k P : D.host.E)) ≤
        P.valuation D.host.E (N : D.host.E) * P.valuation D.host.E (k P : D.host.E) := by
    intro P hP
    have h := hS P hP
    rw [hXP] at h
    exact ⟨h.1, h.2.1⟩
  have hS'2 : ∀ P, P ∉ S → Valued.v (ι (finPart D (x : AE D)) P) = 1 ∧ (N : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro P hP
    have h := hS' P hP
    rwa [hXP] at h

  obtain ⟨k', hk'1, hk'2⟩ : ∃ k' : HeightOneSpectrum (𝓞 D.host.E) → D.host.Eˣ,
      (∀ P, P.under (𝓞 D.host.F) = v → k' P = k P) ∧ (∀ P, P.under (𝓞 D.host.F) ≠ v → k' P = 1) :=
    ⟨fun P => if P.under (𝓞 D.host.F) = v then k P else 1, fun _ h => if_pos h, fun _ h => if_neg h⟩
  have hcx := hmain x hx1 S k' ?_ ?_
  · have hprod : ∏ P ∈ S, ((χ.locK P (k' P) : ℂˣ) : ℂ) = 1 := by
      apply Finset.prod_eq_one
      intro P hPS
      by_cases hP : P.under (𝓞 D.host.F) = v
      · rw [hk'1 P hP]
        have hu : χ.loc P (atFin P (k P)) = 1 := by
          apply hunr P hP
          show Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) (k P : D.host.E)) = 1
          rw [GlobalTheory.CharLocProd.val_algebraMap, ← (hS2 P hPS).1]
          exact hval P
        show ((χ.loc P (atFin P (k P)) : ℂˣ) : ℂ) = 1
        rw [hu, Units.val_one]
      · rw [hk'2 P hP, map_one, Units.val_one]
    exact Circle.coe_eq_one.mp (hcx.trans hprod)
  · intro P hPS
    by_cases hP : P.under (𝓞 D.host.F) = v
    · rw [hk'1 P hP]
      exact hS2 P hPS
    · rw [hk'2 P hP, hoff P hP]
      refine ⟨?_, ?_⟩
      · rw [Units.val_one, Valuation.map_one, map_one]
      · rw [Units.val_one, map_one, sub_self, Valuation.map_zero]
        exact zero_le'
  · intro P hPS
    exact hS'2 P hPS

end GlobalTheory.UnramOver
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedEtaTildeOfOddExponentSum
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EtaTildeOddParity

theorem isEta_sq (D : D7) (η : (AF D.host.F)ˣ →* Circle) (h : IsEta D η) (a : (AF D.host.F)ˣ) : η a ^ 2 = 1 := by
  obtain ⟨-, -, hnorm, -⟩ := h
  have hn := hnorm (idF D a)
  rw [Formalism.L2.Theta.norm_idF, map_pow] at hn
  exact hn

private theorem hasInfQ_half_of_isEtaT (D : D7) (χ : Formalism.L2.Host.HChar D.host.E) (h : Formalism.L2.Host.IsEtaT D.host χ) :
    χ.HasInfQ (tauE D) (fun _ => 1 / 2) := by
  unfold Formalism.L2.Host.HChar.HasInfQ
  refine ⟨fun _ => 1, fun _ => by norm_num, ?_⟩
  intro k
  rw [h.inf k]
  symm
  exact Fintype.prod_equiv D.eTau _ _ (fun _ => rfl)

private theorem one_mem_intAE_twisted_operators (D : D7) : 1 ∈ intAE D := by
  apply AddSubgroup.subset_closure
  rw [Set.mem_setOf_eq]
  refine ⟨1, ?_, 1, ?_⟩
  · intro v
    first
      | exact one_mem _
      | (rw [map_one]; exact one_mem _)
      | simp [evalV]
  · rw [Algebra.TensorProduct.one_def]
    all_goals simp

theorem isEtaTilde_of_odd : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → Formalism.L2.Host.IsEtaT D.host χ → ∀ (μ : (AE D)ˣ →* Circle) (n m : ℕ), ResEta D μ n → ResEta D (μ * c⁻¹) m → Odd (n + m) → IsEtaTilde D c := by
  intro D c χ hc hχ μ n m hμ hμc hodd
  unfold IsEtaTilde
  refine ⟨hc.1, ?_, ?_, fun τ => GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D c χ (fun _ => 1 / 2) hc
    (hasInfQ_half_of_isEtaT D χ hχ) τ⟩
  ·
    intro x h1 h2 h3
    refine GlobalTheory.tame_heckeChar_eq_one_of_finUnit D c χ hc (fun P => ?_) 1 (fun P _ => hχ.unr P) x ⟨h1, h2, h3⟩
      ⟨finPart D (x : AE D) - 1, sub_mem h2 (one_mem_intAE_twisted_operators D), by rw [one_smul]⟩
    intro y hy _
    exact hχ.unr P y hy
  ·
    unfold ResEta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AllSome at hμ hμc ⊢
    refine ⟨hμ.1, fun η hη a => ?_⟩
    have e1 : μ (idF D a) = η a ^ n := hμ.2 η hη a
    have e2 : (μ * c⁻¹) (idF D a) = η a ^ m := hμc.2 η hη a
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, e1] at e2
    have hs : η a ^ 2 = 1 := isEta_sq D η hη a
    have hi : (η a ^ m)⁻¹ = η a ^ m := by
      rw [inv_eq_iff_mul_eq_one, ← pow_add, ← two_mul, pow_mul, hs, one_pow]
    have hc' : c (idF D a) = η a ^ n * (η a ^ m)⁻¹ := by
      rw [← e2, mul_inv_rev, inv_inv, mul_comm (c _), mul_inv_cancel_left]
    obtain ⟨k, hk⟩ := hodd
    show c (idF D a) = η a ^ 1
    rw [pow_one, hc', hi, ← pow_add, hk, pow_succ, pow_mul, hs, one_pow, one_mul]

end GlobalTheory.EtaTildeOddParity
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KernelProjectionPreservesGoodFormsBaseLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
open Formalism.IndefR.CxPass Formalism.IndefR.CxPass.LevelOperators

noncomputable section

namespace GlobalTheory.KerProjGood

theorem starProjection_comm {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (S : Submodule ℂ V) (T : V →ₗ[ℂ] V) (hT : ∀ u ∈ S, T u ∈ S) (hTa : ∀ u ∈ S, LinearMap.adjoint T u ∈ S) (z : V) :
    (S.starProjection (T z) : V) = T (S.starProjection z) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hT _ (Submodule.coe_mem _)) fun w hw => ?_
  rw [← map_sub, ← LinearMap.adjoint_inner_right]
  have h := Submodule.sub_starProjection_mem_orthogonal (K := S) z
  rw [inner_eq_zero_symm]
  exact h _ (hTa w hw)

end GlobalTheory.KerProjGood


open GlobalTheory.KerProjGood in
theorem GlobalTheory.kerProj_goodL : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → ∀ j, ∀ y ∈ U2.goodL A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 j, ((LinearMap.ker ((R.toCx3 F).θ' j A3.A.fam.μ0)).starProjection y : (R.toCx3 F).FLC j A3.A.fam.μ0) ∈ U2.goodL A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 j := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hok hC _ _ hG j y hy
  have hM := hC.base.models
  have hK := RealDat3.kFormL_of (F := F) hM
  have hJ := RealDat3.jIsoL_of (F := F) hM
  set X := R.toCx3 F with hX
  set t := A3.A.fam.μ0
  have sp := lift_embeddings_span hK j t
  have jr : ∀ (g : G) x, X.jL j t ((A3.fam3.F.L j t).r g x) = X.opLC j t (Sum.inr g) (X.jL j t x) :=
    fun g x => X.jL_opL hK j t (Sum.inr g) x

  have hker : ∀ (g : G), ∀ u ∈ LinearMap.ker (X.θ' j t), X.opLC j t (Sum.inr g) u ∈ LinearMap.ker (X.θ' j t) := by
    intro g u hu
    rw [LinearMap.mem_ker] at hu ⊢
    have h := congrArg (fun f => f u) (theta_rho (r := (A3.fam3.F.L j t).r) (ρ := fun g => X.opLC j t (Sum.inr g))
      sp jr (fun g x => hG.2 j t g x) g)
    simp only [LinearMap.comp_apply] at h
    rw [h, hu, map_zero]
  have hadj : ∀ g : G, LinearMap.adjoint (X.opLC j t (Sum.inr g)) = X.opLC j t (Sum.inr g⁻¹) := fun g =>
    (X.opLC_adjoint hK F.cv hJ j t (Sum.inr g) (Sum.inr g⁻¹)
      fun f f' => csum_act_inv (hok.ok2.lifts j t).act g f f').symm
  have hcomm : ∀ (g : G) z, ((LinearMap.ker (X.θ' j t)).starProjection (X.opLC j t (Sum.inr g) z) : X.FLC j t) =
      X.opLC j t (Sum.inr g) ((LinearMap.ker (X.θ' j t)).starProjection z) := fun g z =>
    starProjection_comm _ _ (hker g) (fun u hu => by rw [hadj]; exact hker g⁻¹ u hu) z
  have hrange : U2.goodL A3 X F.P0 F.ψ0 F.P1 F.ψ1 j = LinearMap.range (opV A3.fam3.base3.v0.embedding
      (fun g => X.opLC j t (Sum.inr g)) (goodAt (A3.fam3.F.lvlA F.P0 F.ψ0).X (A3.fam3.F.lvlA F.P0 F.ψ0).P
        (A3.fam3.F.lvlA F.P0 F.ψ0).ψ)) := by
    show X.goodPartComplexPoints F.cv false j t = _
    unfold CxData.goodPartComplexPoints
    rw [show F.cv.v0L X.zs false j t = BlockGood.goodR (A3.fam3.F.L j t) (A3.fam3.F.lvlA F.P0 F.ψ0) from rfl, goodR_eq]
    conv_rhs => rw [LinearMap.range_eq_map, ← sp, Submodule.map_span]
    congr 1
    ext u
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨X.jL j t x, ⟨x, rfl⟩, (j_opF jr _ x).symm⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨_, ⟨x, rfl⟩, j_opF jr _ x⟩
  rw [hrange] at hy ⊢
  obtain ⟨z, rfl⟩ := hy
  refine ⟨(LinearMap.ker (X.θ' j t)).starProjection z, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [opV, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hcomm]
  exact Finset.sum_congr rfl fun g _ => congrArg _ (hcomm g z).symm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftsRationalOfRatAt
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open Formalism.IndefR.Arith

namespace GlobalTheory.LiftRat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Abstract

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

end Abstract

section Forms

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
  {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL]
  {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  {G : Type} [Group G] [Fintype G] (A : FormsL LL Ks WL W G)

end Forms

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Package

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem j_eq_sum (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (y : Fin (R.nW i) → D.what₂.LL) :
    (R.FW i).j σ y = ∑ k, σ (y k) • (R.FW i).j σ (Pi.basisFun D.what₂.LL (Fin (R.nW i)) k) := by
  conv_lhs => rw [← (Pi.basisFun D.what₂.LL (Fin (R.nW i))).sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [map_smulₛₗ, Pi.basisFun_repr]

theorem span_basis (hU : R.LUnif) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) :
    Submodule.span ℂ (Set.range fun k => (R.FW i).j σ (Pi.basisFun D.what₂.LL (Fin (R.nW i)) k)) = ⊤ := by
  refine top_le_iff.1 ((hU i σ).2.1.ge.trans (Submodule.span_le.2 ?_))
  rintro _ ⟨y, rfl⟩
  rw [j_eq_sum]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

end Package

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
  (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ)

end GlobalTheory.LiftRat

end
end

