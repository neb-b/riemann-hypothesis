module

public import Formalism.SatakeDualWeyl.DefsCS
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0002
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0008
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0004

@[expose] public section

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.ClassInjectiveOfSpanRecovery
section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG.P

open Formalism.UG Formalism.UG.CS

theorem class_injective_of_span_recovery (hSpanRecover : Formalism.UG.CS.SpanRecover)
    (hGlobLatEquiv : Formalism.UG.CS.GlobLatEquiv) : Formalism.UG.CS.ClassInj := by
  intro F E _ _ _ _ _ n _ _ σ J Λ hfin hspan g g' γ hγ hlat
  set A := FiniteAdeleRing (𝓞 F) F with hA
  set L := latS (F := F) A (tensInt (F := F) A (intOE E) (intAd F)) Λ with hL
  set γA : GL n (E ⊗[F] A) := bc (inclE (F := F) A) γ with hγA

  have hsig : ∀ e : E, sigR σ A (inclE (F := F) A e) = inclE (F := F) A (σ e) := by
    intro e
    simp [sigR, inclE]
  have hγm : (γA : Matrix n n (E ⊗[F] A)) = (γ : Matrix n n E).map (inclE (F := F) A) := rfl
  have hγU : γA ∈ UPts σ J A := by
    change cT (sigR σ A) (γA : Matrix n n (E ⊗[F] A)) * J.map (inclE (F := F) A)
      * (γA : Matrix n n (E ⊗[F] A)) = J.map (inclE (F := F) A)
    have h0 : cT (σ : E →+* E) (γ : Matrix n n E) * J * (γ : Matrix n n E) = J := hγ
    have hc : cT (sigR σ A) (γA : Matrix n n (E ⊗[F] A))
        = (cT (σ : E →+* E) (γ : Matrix n n E)).map (inclE (F := F) A) := by
      ext i j
      simp [cT, hγm, hsig]
    rw [hc, hγm, ← Matrix.map_mul, ← Matrix.map_mul, h0]

  have heq : globLat (γA * (g' : GL n (E ⊗[F] A))) Λ = globLat (g : GL n (E ⊗[F] A)) Λ := by
    have h1 := hGlobLatEquiv F E n Λ γ (g' : GL n (E ⊗[F] A)) 1 (one_mem _)
    rw [mul_one] at h1
    rw [h1, hlat]
  have hR : ∀ u : n → E ⊗[F] A,
      (((g : GL n (E ⊗[F] A))⁻¹ : GL n (E ⊗[F] A)) : Matrix n n _) *ᵥ u ∈ L ↔
        (((γA * (g' : GL n (E ⊗[F] A)))⁻¹ : GL n (E ⊗[F] A)) : Matrix n n _) *ᵥ u ∈ L := by
    intro u
    have h1 := hSpanRecover F E n Λ hfin hspan (g : GL n (E ⊗[F] A)) u
    have h2 := hSpanRecover F E n Λ hfin hspan (γA * (g' : GL n (E ⊗[F] A))) u
    rw [heq] at h2
    exact h1.symm.trans h2
  set k : GL n (E ⊗[F] A) := (g : GL n (E ⊗[F] A))⁻¹ * (γA * (g' : GL n (E ⊗[F] A))) with hk
  have hkS : k ∈ stabGL L := by
    intro x
    have h := hR (((γA * (g' : GL n (E ⊗[F] A)) : GL n (E ⊗[F] A)) : Matrix n n _) *ᵥ x)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h
    exact h.symm
  have hkU : k ∈ UPts σ J A :=
    mul_mem (inv_mem g.2) (mul_mem hγU g'.2)
  rw [DoubleCoset.eq]
  refine ⟨⟨γA⁻¹, inv_mem hγU⟩, ?_, ⟨k, hkU⟩, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    exact ⟨γ⁻¹, inv_mem hγ, map_inv _ _⟩
  · rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_inf.mpr ⟨hkU, hkS⟩
  · apply Subtype.ext
    simp only [Subgroup.coe_mul, hk]
    group

end Formalism.UG.P
end
end

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsApprox
section
noncomputable section
namespace Formalism.UG.P
open Formalism.UG IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero

section CsApprox

variable {F : Type} [Field F] [NumberField F]

theorem csApprox_val_int (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) :
    Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r) = v.intValuation r := by
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]
  first
  | (rw [valuedAdicCompletion_eq_valuation' v]; exact valuation_of_algebraMap v r)
  | simp [valuedAdicCompletion_eq_valuation', valuation_of_algebraMap]
  | (erw [valuedAdicCompletion_eq_valuation']; exact valuation_of_algebraMap v r)

theorem csApprox_local (v : HeightOneSpectrum (𝓞 F)) (D : 𝓞 F) (hD : D ≠ 0)
    (x : v.adicCompletion F) (hx : x ∈ v.adicCompletionIntegers F) :
    ∃ s : 𝓞 F, Valued.v (x - algebraMap (𝓞 F) (v.adicCompletion F) s) < v.intValuation D := by
  set c := algebraMap (𝓞 F) (v.adicCompletion F) D with hcdef
  have hc : c ≠ 0 := levelaf_algebraMap_ne_zero v D hD
  have hrc : (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).restrict c ≠ 0 :=
    (Valuation.ne_zero_iff _).2 hc
  have hs : {y : v.adicCompletion F | Valued.v (y - x) < Valued.v c} ∈ nhds x := by
    refine Valued.mem_nhds.2 ⟨Units.mk0 _ hrc, fun y hy => ?_⟩
    simp only [Set.mem_ofPred_eq, Units.val_mk0] at hy ⊢
    exact lt_of_not_ge fun h => (not_le.2 hy) ((Valuation.restrict_le_iff _).2 h)
  obtain ⟨b, hb⟩ := (denseRange_algebraMap (K := F) v).mem_nhds hs
  simp only [Set.mem_ofPred_eq] at hb
  have hcv : Valued.v c = v.intValuation D := csApprox_val_int v D
  rw [hcv] at hb
  have hb1 : v.valuation F b ≤ 1 := by
    rw [← levelaf_valued_algebraMap]
    have e : algebraMap F (v.adicCompletion F) b = (algebraMap F (v.adicCompletion F) b - x) + x := by
      ring
    rw [e]
    exact Valuation.map_add_le _ (hb.le.trans (v.intValuation_le_one D)) hx
  obtain ⟨s, hs⟩ := exists_valuation_sub_lt_of_integer v hb1
    (Units.mk0 (v.intValuation D) (v.intValuation_ne_zero D hD))
  simp only [Units.val_mk0] at hs
  refine ⟨s, ?_⟩
  have hs' : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) s - algebraMap F (v.adicCompletion F) b)
      < v.intValuation D := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), ← map_sub,
      levelaf_valued_algebraMap]
    exact hs
  have e2 : x - algebraMap (𝓞 F) (v.adicCompletion F) s =
      -(algebraMap F (v.adicCompletion F) b - x) +
        -(algebraMap (𝓞 F) (v.adicCompletion F) s - algebraMap F (v.adicCompletion F) b) := by
    ring
  rw [e2]
  refine Valuation.map_add_lt _ ?_ ?_
  · rw [Valuation.map_neg]; exact hb
  · rw [Valuation.map_neg]; exact hs'

theorem csApprox_global (D : 𝓞 F) (hD : D ≠ 0) (a : FiniteAdeleRing (𝓞 F) F) (ha : a ∈ intAd F) :
    ∃ r : 𝓞 F, ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v (a v - algebraMap (𝓞 F) (v.adicCompletion F) r) ≤
        Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) := by
  classical
  have hP := levelaf_finite_places D hD
  choose s hs using fun v : HeightOneSpectrum (𝓞 F) => csApprox_local v D hD (a v) (ha v)
  obtain ⟨r, hr⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := hP.toFinset)
    (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)
    (fun v => multiplicity v.asIdeal (Ideal.span {D})) (fun v _ => v.prime)
    (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h)) (fun v => s v)
  refine ⟨r, fun v => ?_⟩
  by_cases hv : v ∈ hP.toFinset
  · have h1 := (v.intValuation_le_pow_iff_mem _ _).2 (hr v hv)
    rw [← v.intValuation_eq_exp_neg_multiplicity hD] at h1
    have e1 : a v - algebraMap (𝓞 F) (v.adicCompletion F) r =
        (a v - algebraMap (𝓞 F) (v.adicCompletion F) (s v)) +
          -(algebraMap (𝓞 F) (v.adicCompletion F) (r - s v)) := by
      rw [map_sub]; ring
    rw [e1, csApprox_val_int]
    refine Valuation.map_add_le _ (hs v).le ?_
    rw [Valuation.map_neg, csApprox_val_int]
    exact h1
  · have hv' : ¬ Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) < 1 := by simpa using hv
    have h1 : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) = 1 :=
      le_antisymm ((mem_adicCompletionIntegers _ _ _).1 (levelaf_int_mem_v v D)) (not_lt.1 hv')
    rw [h1]
    exact (mem_adicCompletionIntegers _ _ _).1 (sub_mem (ha v) (levelaf_int_mem_v v r))

end CsApprox

theorem integral_adele_approximation_holds : Formalism.UG.CS.IntAdApprox := by
  intro F _ _ D hD a ha
  obtain ⟨r, hle⟩ := csApprox_global D hD a ha
  set y : FiniteAdeleRing (𝓞 F) F := algebraMap F _ (algebraMap (𝓞 F) F D)⁻¹ *
    (a - algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r) with hy
  refine ⟨r, y, fun v => ?_, ?_⟩
  · show algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F D)⁻¹ *
        (a v - algebraMap (𝓞 F) (v.adicCompletion F) r) ∈ _
    have hne : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 (levelaf_algebraMap_ne_zero v D hD)
    rw [mem_adicCompletionIntegers, Valuation.map_mul, map_inv₀, map_inv₀,
      ← IsScalarTower.algebraMap_apply]
    calc _ ≤ (Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D))⁻¹ *
          Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) := mul_le_mul_right (hle v) _
      _ = 1 := inv_mul_cancel₀ hne
  · have hD' : algebraMap (𝓞 F) F D ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hD
    rw [hy, IsScalarTower.algebraMap_apply (𝓞 F) F (FiniteAdeleRing (𝓞 F) F) D, ← mul_assoc,
      ← map_mul, mul_inv_cancel₀ hD', map_one, one_mul]
    ring

end Formalism.UG.P
end
end

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsAsmHformSmulRight
section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG.P

open Formalism.UG Formalism.UG.CS

theorem csAsm_hform_smul_right {E : Type} [Field E] (σ : E →+* E) {n : Type} [Fintype n]
    (J : Matrix n n E) (c : E) (y x : n → E) :
    hform σ J y (c • x) = c * hform σ J y x := by
  unfold Formalism.UG.hform
  simp [Matrix.mulVec_smul, dotProduct_smul, Finset.mul_sum, smul_eq_mul, mul_left_comm]

theorem csAsm_gmap_mul {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] (a b : V ≃ₗ[K] V)
    (L : Submodule R V) :
    Formalism.HermitianLatticesTheory.gmap (a * b) L = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b L) := by
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [← Submodule.map_comp]
  first
  | rfl
  | (congr 1; ext x; simp [LinearEquiv.mul_apply])

theorem csAsm_gmap_one {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] (L : Submodule R V) :
    Formalism.HermitianLatticesTheory.gmap (1 : V ≃ₗ[K] V) L = L := by
  unfold Formalism.HermitianLatticesTheory.gmap
  simp

theorem csAsm_gmap_inv {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] (a : V ≃ₗ[K] V)
    (L : Submodule R V) :
    Formalism.HermitianLatticesTheory.gmap a⁻¹ (Formalism.HermitianLatticesTheory.gmap a L) = L := by
  rw [← csAsm_gmap_mul, inv_mul_cancel, csAsm_gmap_one]

theorem classSetFiniteL_of (hSigmaInvol : Formalism.UG.CS.SigmaInvol) (hTracePos : Formalism.UG.CS.TracePos)
    (hFormSymm : Formalism.UG.CS.FormSymm) (hIsomUJ : Formalism.UG.CS.IsomUJ)
    (hGlobLatLattice : Formalism.UG.CS.GlobLatLattice) (hClassInj : Formalism.UG.CS.ClassInj)
    (hScaleBound : Formalism.UG.CS.ScaleBound) (hDualBound : Formalism.UG.CS.DualBound)
    (hClassSetFiniteBdd : Formalism.UG.CS.ClassSetFiniteBdd) (hStdLatFull : Formalism.UG.CS.StdLatFull) :
    Formalism.UG.ClassSetFiniteL := by
  intro F E _ _ _ _ _ n _ _ σ J hσ hJ hdet hdef Λ hfin hspan
  have hinv : ∀ e, (σ : E →+* E) ((σ : E →+* E) e) = e := fun e => hSigmaInvol F E σ hσ e
  obtain ⟨c, hc0, hcpos⟩ := hTracePos F E n σ J hdef
  set cE : E := algebraMap F E (c : F) with hcE
  have hσc : (σ : E →+* E) cE = cE := by
    rw [hcE]
    exact σ.commutes _
  have hcF : ((c : 𝓞 F) : F) ≠ 0 := by
    intro h
    apply hc0
    first
    | exact_mod_cast h
    | exact RingOfIntegers.ext h
  have hcE0 : cE ≠ 0 := by
    rw [hcE]
    exact (map_ne_zero _).mpr hcF
  set cO : 𝓞 E := algebraMap (𝓞 F) (𝓞 E) c with hcO
  have hcOE : algebraMap (𝓞 E) E cO = cE := by
    rw [hcO, hcE, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E]
  have hcO0 : cO ≠ 0 := by
    intro h
    apply hcE0
    rw [← hcOE, h, map_zero]
  letI : StarRing E := starOfInv (σ : E →+* E) hinv
  obtain ⟨hsymm, hfe⟩ := hFormSymm E (σ : E →+* E) hinv n J cE hσc hJ
  obtain ⟨d, hd0, hd⟩ := hScaleBound F E n σ J Λ hfin hspan
  obtain ⟨e, he0, he⟩ := hDualBound F E n σ J Λ hdet hfin hspan
  have hpos : ∀ x : n → E, x ≠ 0 → 0 < Algebra.trace ℚ E (formJ (σ : E →+* E) hinv J cE x x) := by
    intro x hx
    rw [hfe]
    exact hcpos x hx
  obtain ⟨s, hs⟩ := hClassSetFiniteBdd E (n → E) (formJ (σ : E →+* E) hinv J cE) hsymm hpos d (e * cO) hd0
    (mul_ne_zero he0 hcO0)
  have key : ∀ g : UPts σ J (FiniteAdeleRing (𝓞 F) F), ∃ N ∈ s, ∃ φ ∈ Formalism.HermitianLatticesTheory.isom (formJ (σ : E →+* E) hinv J cE),
      Formalism.HermitianLatticesTheory.gmap φ N = globLat (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Λ := by
    intro g
    apply hs
    · exact hGlobLatLattice F E n Λ hfin hspan g
    · intro x hx y hy
      rw [hfe, Submodule.mem_one]
      obtain ⟨o, ho⟩ := hd g g.2 x hx y hy
      refine ⟨o * cO, ?_⟩
      rw [map_mul, ho, hcOE]
      show algebraMap (𝓞 E) E d * hform (σ : E →+* E) J x y * cE = algebraMap (𝓞 E) E d * (cE * hform (σ : E →+* E) J x y)
      ring
    · intro x hx
      simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
        LinearMap.restrictScalars_apply, Submodule.mem_one] at hx
      have hx' : ∀ y ∈ globLat (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Λ,
          hform (σ : E →+* E) J y (cE • x) ∈ (algebraMap (𝓞 E) E).range := by
        intro y hy
        obtain ⟨o, ho⟩ := hx y hy
        rw [hfe] at ho
        refine ⟨o, ?_⟩
        rw [csAsm_hform_smul_right]
        exact ho
      have h2 := he g g.2 (cE • x) hx'
      convert h2 using 1
      show algebraMap (𝓞 E) E (e * cO) • x = algebraMap (𝓞 E) E e • cE • x
      rw [map_mul, hcOE, smul_smul]
  classical
  choose N hN φ hφ hφN using key
  let f : ClassSet ((ratPts σ J (FiniteAdeleRing (𝓞 F) F)).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F)))
      ((levelAfL σ J Λ).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))) → s :=
    fun q => ⟨N (Quotient.out q), hN (Quotient.out q)⟩
  have hf : Function.Injective f := by
    intro q1 q2 h12
    have hNN : N (Quotient.out q1) = N (Quotient.out q2) := congrArg Subtype.val h12
    obtain ⟨γ, hγ⟩ : ∃ γ : GL n E, glEquiv γ = φ (Quotient.out q1) * (φ (Quotient.out q2))⁻¹ :=
      ⟨Matrix.GeneralLinearGroup.toLin.symm ((LinearMap.GeneralLinearGroup.generalLinearEquiv E (n → E)).symm
        (φ (Quotient.out q1) * (φ (Quotient.out q2))⁻¹)), by simp [glEquiv]⟩
    have hUJ : γ ∈ UJ (σ : E →+* E) J :=
      (hIsomUJ E (σ : E →+* E) hinv n J cE hcE0 hσc γ).mpr (by
        rw [hγ]
        exact mul_mem (hφ _) (inv_mem (hφ _)))
    have hlat : globLat ((Quotient.out q1 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Λ =
        Formalism.HermitianLatticesTheory.gmap (glEquiv γ) (globLat ((Quotient.out q2 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
          GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Λ) := by
      rw [hγ, csAsm_gmap_mul, ← hφN (Quotient.out q2), csAsm_gmap_inv, ← hNN, hφN]
    have h3 := hClassInj F E n σ J Λ hfin hspan (Quotient.out q1) (Quotient.out q2) γ hUJ hlat
    rwa [DoubleCoset.out_eq', DoubleCoset.out_eq'] at h3
  exact Finite.of_injective f hf

theorem classSetFinite_of (hSigmaInvol : Formalism.UG.CS.SigmaInvol) (hTracePos : Formalism.UG.CS.TracePos)
    (hFormSymm : Formalism.UG.CS.FormSymm) (hIsomUJ : Formalism.UG.CS.IsomUJ)
    (hGlobLatLattice : Formalism.UG.CS.GlobLatLattice) (hClassInj : Formalism.UG.CS.ClassInj)
    (hScaleBound : Formalism.UG.CS.ScaleBound) (hDualBound : Formalism.UG.CS.DualBound)
    (hClassSetFiniteBdd : Formalism.UG.CS.ClassSetFiniteBdd) (hStdLatFull : Formalism.UG.CS.StdLatFull) :
    Formalism.UG.ClassSetFinite := by
  intro F E _ _ _ _ _ n _ _ σ J hσ hJ hdet hdef
  have h := classSetFiniteL_of hSigmaInvol hTracePos hFormSymm hIsomUJ hGlobLatLattice hClassInj hScaleBound
    hDualBound hClassSetFiniteBdd hStdLatFull F E n σ J hσ hJ hdet hdef (stdLat (n := n) (A := E) (𝓞 E))
    (hStdLatFull E n).1 (hStdLatFull E n).2
  have heq : levelAfL σ J (stdLat (n := n) (A := E) (𝓞 E)) = levelAf σ J := by
    unfold Formalism.UG.levelAfL Formalism.UG.levelAf
    congr 1
    apply le_antisymm
    · unfold Formalism.UG.latS
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      simp only [SetLike.mem_coe, Formalism.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies,
        LinearMap.mem_range] at hx ⊢
      intro i
      obtain ⟨a, ha⟩ := hx i
      exact ⟨⟨inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i),
        Subring.subset_closure (Or.inl ⟨⟨x i, a, ha⟩, rfl⟩)⟩, rfl⟩
    · intro v hv
      simp only [Formalism.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies,
        LinearMap.mem_range] at hv
      unfold Formalism.UG.latS
      rw [pi_eq_sum_univ v]
      refine Submodule.sum_mem _ (fun i _ => ?_)
      obtain ⟨y, hy⟩ := hv i
      have hy' : (y : E ⊗[F] FiniteAdeleRing (𝓞 F) F) = v i := hy
      have hsm : (v i • fun j => if i = j then (1 : E ⊗[F] FiniteAdeleRing (𝓞 F) F) else 0) =
          y • (fun j => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (if i = j then (1 : E) else 0)) := by
        ext j
        simp only [Pi.smul_apply, smul_eq_mul, Subring.smul_def]
        rw [← hy']
        split_ifs <;> simp
      rw [hsm]
      refine Submodule.smul_mem _ y (Submodule.subset_span ⟨fun j => if i = j then (1 : E) else 0, ?_, rfl⟩)
      simp only [SetLike.mem_coe, Formalism.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies,
        LinearMap.mem_range]
      intro j
      split_ifs
      · exact ⟨1, by simp⟩
      · exact ⟨0, by simp⟩
  rw [heq] at h
  exact h

end Formalism.UG.P
end
end

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsEasy
section
noncomputable section

open Matrix NumberField

namespace Formalism.UG.P

theorem sigma_involution_holds : Formalism.UG.CS.SigmaInvol := by
  intro F E _ _ _ _ _ σ hσ e
  let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  have h : ∀ x, τ (σ x) = starRingEnd ℂ (τ x) := fun x => by
    simpa using RingHom.congr_fun (hσ τ) x
  apply τ.injective
  rw [h, h, Complex.conj_conj]

theorem csEasy_stdLat_eq_range (E : Type) [Field E] [NumberField E] (n : Type) [Fintype n]
    [DecidableEq n] :
    Formalism.UG.stdLat (n := n) (A := E) (𝓞 E) =
      LinearMap.range (LinearMap.pi (fun i : n =>
        (Algebra.linearMap (𝓞 E) E).comp (LinearMap.proj i))) := by
  ext x
  simp only [Formalism.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, LinearMap.mem_range]
  constructor
  · intro h
    choose y hy using h
    exact ⟨y, funext fun i => by simpa using hy i⟩
  · rintro ⟨y, rfl⟩ i
    exact ⟨y i, by simp⟩

theorem standard_lattice_full_holds : Formalism.UG.CS.StdLatFull := by
  intro E _ _ n _ _
  refine ⟨?_, ?_⟩
  · rw [csEasy_stdLat_eq_range]
    infer_instance
  · rw [eq_top_iff, ← (Pi.basisFun E n).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    show Pi.basisFun E n i ∈ Formalism.UG.stdLat (n := n) (A := E) (𝓞 E)
    simp only [Formalism.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, LinearMap.mem_range,
      Pi.basisFun_apply]
    intro j
    rw [Pi.single_apply]
    split_ifs
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩

theorem csEasy_formJ_apply {E : Type} [Field E] (σ : E →+* E) (hσ : ∀ e, σ (σ e) = e)
    {n : Type} [Fintype n] [DecidableEq n] (J : Matrix n n E) (c : E) (x y : n → E) :
    Formalism.UG.CS.formJ σ hσ J c x y = c * Formalism.UG.hform σ J x y := by
  unfold Formalism.UG.CS.formJ Formalism.UG.hform
  rw [Matrix.toLinearMapₛₗ₂'_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show σ (x i) * (y j * (c * J i j)) = c * (σ (x i) * J i j * y j)
  ring

theorem hermitian_form_symmetry_holds : Formalism.UG.CS.FormSymm := by
  intro E _ σ hσ n _ _ J c hc hJ
  have hJ' : ∀ i j, σ (J i j) = J j i := fun i j => by
    have := congrFun (congrFun hJ j) i
    simpa [Formalism.UG.cT] using this
  refine ⟨?_, fun x y => csEasy_formJ_apply σ hσ J c x y⟩
  constructor
  intro x y
  rw [csEasy_formJ_apply, csEasy_formJ_apply]
  show σ (c * Formalism.UG.hform σ J x y) = c * Formalism.UG.hform σ J y x
  rw [map_mul, hc]
  congr 1
  unfold Formalism.UG.hform
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, hσ, hJ']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma hform_mulVec_mulVec_of_cT_mul_mul_eq {E : Type} [Field E] (σ : E →+* E) {n : Type} [Fintype n]
    [DecidableEq n] (J M : Matrix n n E) (x y : n → E) :
    Formalism.UG.hform σ J (M *ᵥ x) (M *ᵥ y) = Formalism.UG.hform σ (Formalism.UG.cT σ M * J * M) x y := by
  have e : ∀ (A : Matrix n n E) (u v : n → E),
      Formalism.UG.hform σ A u v = (fun i => σ (u i)) ⬝ᵥ (A *ᵥ v) := by
    intro A u v
    simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  have hs : (fun i => σ ((M *ᵥ x) i)) = (M.map σ) *ᵥ (fun i => σ (x i)) := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [mulVec, dotProduct, map_sum]
  rw [e, e, hs, ← Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, Formalism.UG.cT]
  simp only [Matrix.mul_assoc]

private lemma hform_single_single_stabilizer_orbit_volume {E : Type} [Field E] (σ : E →+* E) {n : Type} [Fintype n]
    [DecidableEq n] (A : Matrix n n E) (i j : n) :
    Formalism.UG.hform σ A (Pi.single i 1) (Pi.single j 1) = A i j := by
  simp [Formalism.UG.hform, Pi.single_apply]

theorem unitary_isometry_lattice_holds : Formalism.UG.CS.IsomUJ := by
  intro E _ σ hσ n _ _ J c hc hcσ g
  have hg : ∀ x, Formalism.UG.glEquiv g x = (g : Matrix n n E) *ᵥ x := fun x => rfl
  show Formalism.UG.cT σ (g : Matrix n n E) * J * (g : Matrix n n E) = J ↔ _
  show _ ↔ ∀ x y, _ = _
  simp only [hg, csEasy_formJ_apply, hform_mulVec_mulVec_of_cT_mul_mul_eq, mul_right_inj' hc]
  constructor
  · intro h x y
    rw [h]
  · intro h
    ext i j
    have := h (Pi.single i 1) (Pi.single j 1)
    rwa [hform_single_single_stabilizer_orbit_volume, hform_single_single_stabilizer_orbit_volume] at this

end Formalism.UG.P
end
end

