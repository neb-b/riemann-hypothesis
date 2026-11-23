module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0002
public import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0125
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0003
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.GramLevelZeroEqReindex
public import Formalism.LocalToGlobal.HermitianForms.Bundle0007
public import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle0003
public import Formalism.LocalToGlobal.GlobalTheory.ExistsUnitaryOneDetEq
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelMoveDegree

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FacQIsPt
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.FacQPt


set_option maxHeartbeats 400000 in
theorem facQ_isPt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p} (A : LocAt F E n G) (i : G.comp) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (y : GL (Fin n) (E ⊗[F] (FiniteAdeleRing (𝓞 F) F))) : A.IsPt i g y → ∀ v, facQ A v y = bc (A.iw v) A.B * castGL A.rk (G.P.Qq v) (g v) * (bc (A.iw v) A.B)⁻¹ := by
  intro h v

  have hv := h.2 v
  have hB : bc ((A.eQ v).symm : (A.pl v).1.adicCompletion F →+* G.P.Qq v) (bc (A.phE v) A.B) = bc (A.iw v) A.B := by
    ext a b
    rfl
  have hg : bc ((A.eQ v).symm : (A.pl v).1.adicCompletion F →+* G.P.Qq v)
      (bc ((A.eQ v : G.P.Qq v →+* (A.pl v).1.adicCompletion F)) (castGL A.rk (G.P.Qq v) (g v))) =
      castGL A.rk (G.P.Qq v) (g v) := by
    apply Units.ext
    ext a b
    simp [Formalism.UG.bc]
  unfold facQ
  rw [hv, map_mul, map_mul, map_inv, hB, hg]

end GlobalTheory.TwV.FacQPt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GidxFacts
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.XdInert

theorem gidx_facts : ∀ (D : D7) (T p : ℕ), GIdx D.host T p →
    5 ≤ p ∧ GL3Theta.InertK D p ∧ Nat.Coprime T p ∧ ∀ i, p ≠ D.host.g i := by
  intro D T p h
  obtain ⟨hp, h5, hc, hn, hl, hT⟩ := h
  refine ⟨h5, ?_, ?_, ?_⟩
  · exact (GlobalTheory.TwU.Served.served_facts D p hp hc hn).2.1
  · exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hT).symm
  · intro i hi
    exact hl (hi ▸ D.host.g_level i)

end GlobalTheory.TwU.XdInert
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsFractionRingGat
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ggeo.FracLocal

theorem isFractionRing_gat : ∀ {D : D7} (Gl : G.LatInst D) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf :=
  fun {_} Gl u w hg => GlobalTheory.TwV.Lt.fracAt Gl u w hg

end GlobalTheory.Ggeo.FracLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLatAndDlEqOfIsSDLatMvL
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.OrthSelfDual

theorem toLE_mem_mvL {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ} (co : GL (Fin N) E)
    (M : Submodule (𝓞 E) (Fin N → E)) (y : Fin N → E) :
    toLE co y ∈ mvL co M ↔ y ∈ M := by
  constructor
  · rintro ⟨x, hx, hxy⟩
    have hxy' : x = y := (toLE co).injective hxy
    rw [hxy'] at hx
    exact hx
  · intro hy
    exact Submodule.mem_map.mpr ⟨y, hy, rfl⟩

theorem isLat_and_dl_eq_of_isSDLat_mvL : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (co : GL (Fin N) E) (M : Submodule (𝓞 E) (Fin N → E)), IsOrthCo (sp.cm.sig : E →+* E) J (toLE co) → IsSDLat E N (mvL co M) → Formalism.L2.GlobalTheoryTheory.Comp.IsLat M ∧ Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J M = M := by
  intro R F E _ _ _ _ _ _ sp N J co M hco hsd
  obtain ⟨hfg, hspan, hdual⟩ := hsd

  have hkey : ∀ x z : Fin N → E, Formalism.BasicNotions.stdH E N (toLE co x) (toLE co z) =
      ∑ a, ∑ b, (sp.cm.sig : E →+* E) (x a) * J a b * z b := fun x z => hco x z
  have hinj : Function.Injective
      (((toLE co : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)).restrictScalars (𝓞 E)) :=
    (toLE co).injective
  refine ⟨⟨?_, ?_⟩, ?_⟩
  ·
    have hfin : Module.Finite (𝓞 E)
        (M.map ((((toLE co : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E))).restrictScalars (𝓞 E))) :=
      Module.Finite.iff_fg.mpr hfg
    exact Module.Finite.equiv (Submodule.equivMapOfInjective _ hinj M).symm
  ·
    have himage : (↑(mvL co M) : Set (Fin N → E)) = (toLE co) '' (↑M : Set (Fin N → E)) := by
      ext x
      simp [mvL]
    rw [himage] at hspan
    apply top_unique
    intro x hx
    apply (Submodule.apply_mem_span_image_iff_mem_span
      (R := E) (R₂ := E)
      (f := ((toLE co : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)))
      (toLE co).injective).mp
    change toLE co x ∈ Submodule.span E ((toLE co) '' (↑M : Set (Fin N → E)))
    rw [hspan]
    trivial
  ·
    ext y
    rw [Formalism.L2.GlobalTheoryTheory.Comp.mem_dl, ← toLE_mem_mvL co M y, hdual (toLE co y)]
    constructor
    · intro h x' hx'
      obtain ⟨x, hx, hxx'⟩ := Submodule.mem_map.mp hx'
      have hx'' : x' = toLE co x := hxx'.symm
      rw [hx'', hkey]
      exact h x hx
    · intro h x hx
      have h1 := h (toLE co x) ((toLE_mem_mvL co M x).mpr hx)
      rw [hkey] at h1
      exact h1

end GlobalTheory.OrthSelfDual

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLatDlOfIsOrthCo
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.OrthDual

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

theorem int_mem_range {t : E} (h : IsIntegral ℤ t) : t ∈ (algebraMap (𝓞 E) E).range :=
  ⟨⟨t, h⟩, rfl⟩

theorem ringHom_mem_range (τ : E →+* E) {t : E} (h : t ∈ (algebraMap (𝓞 E) E).range) :
    τ t ∈ (algebraMap (𝓞 E) E).range := by
  obtain ⟨r, rfl⟩ := h
  exact int_mem_range (IsIntegral.map τ.toIntAlgHom r.isIntegral_coe)

theorem exists_int_smul_mem (M : Submodule (𝓞 E) (Fin N → E)) {v : Fin N → E}
    (hv : v ∈ Submodule.span E (M : Set (Fin N → E))) : ∃ n : ℤ, n ≠ 0 ∧ (n : E) • v ∈ M := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n₁, h₁, hx⟩ := hx
    obtain ⟨n₂, h₂, hy⟩ := hy
    refine ⟨n₁ * n₂, mul_ne_zero h₁ h₂, ?_⟩
    have e : ((n₁ * n₂ : ℤ) : E) • (x + y) = n₂ • ((n₁ : E) • x) + n₁ • ((n₂ : E) • y) := by
      rw [← Int.cast_smul_eq_zsmul E, ← Int.cast_smul_eq_zsmul E, smul_smul, smul_smul, smul_add]
      push_cast
      rw [mul_comm (n₂ : E)]
    rw [e]
    exact add_mem (zsmul_mem hx _) (zsmul_mem hy _)
  | smul e x _ hx =>
    obtain ⟨n, hn, hx⟩ := hx
    obtain ⟨k, hk, hki⟩ := exists_integral_multiples ℤ ℚ (L := E) {e}
    have hke := hki e (Finset.mem_singleton_self e)
    refine ⟨k * n, mul_ne_zero hk hn, ?_⟩
    have e1 : ((k * n : ℤ) : E) • (e • x) = (⟨k • e, hke⟩ : 𝓞 E) • ((n : E) • x) := by
      rw [← algebraMap_smul E (⟨k • e, hke⟩ : 𝓞 E), smul_smul, smul_smul]
      congr 1
      show ((k * n : ℤ) : E) * e = (k • e) * n
      push_cast
      rw [zsmul_eq_mul]
      ring
    rw [e1]
    exact M.smul_mem _ hx

theorem isLat_dl (σ : E →ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) (co : (Fin N → E) ≃ₗ[E] (Fin N → E))
    (hc : Formalism.L2.PairingIndexBounds.F.IsOrthCo (σ : E →+* E) J co) (M : Submodule (𝓞 E) (Fin N → E))
    (hM : Formalism.L2.GlobalTheoryTheory.Comp.IsLat M) : Formalism.L2.GlobalTheoryTheory.Comp.IsLat (Formalism.L2.GlobalTheoryTheory.Comp.dl σ J M) := by
  classical
  set v : Fin N → Fin N → E := fun a => co.symm (Pi.single a 1) with hv
  have key : ∀ x y, Formalism.UG.hform (σ : E →+* E) J x y = ∑ b, (σ : E →+* E) (co x b) * co y b :=
    fun x y => (hc x y).symm
  have hsingle : ∀ (a : Fin N) (c : E), Pi.single a c = c • (Pi.single a (1 : E) : Fin N → E) := by
    intro a c; ext j; simp [Pi.single_apply]
  have hexp : ∀ z : Fin N → E, z = ∑ a, co z a • v a := by
    intro z
    conv_lhs => rw [← co.symm_apply_apply z, ← Finset.univ_sum_single (co z)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hsingle, map_smul]
  have hcv : ∀ (c : E) a b, co (c • v a) b = if b = a then c else 0 := by
    intro c a b; simp [v, Pi.single_apply]
  have hform_v : ∀ (c : E) a x, Formalism.UG.hform (σ : E →+* E) J x (c • v a) = (σ : E →+* E) (co x a) * c := by
    intro c a x; rw [key]; simp [hcv]

  have hex : ∀ a, ∃ n : ℤ, n ≠ 0 ∧ (n : E) • v a ∈ M := fun a =>
    exists_int_smul_mem M (by rw [hM.2]; trivial)
  choose n hn0 hnM using hex
  have hle : Formalism.L2.GlobalTheoryTheory.Comp.dl σ J M ≤
      Submodule.span (𝓞 E) (Set.range fun a => ((n a : E))⁻¹ • v a) := by
    intro y hy
    rw [Formalism.L2.GlobalTheoryTheory.Comp.mem_dl] at hy
    have hr : ∀ a, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = (n a : E) * co y a := by
      intro a
      obtain ⟨r, hr⟩ := hy _ (hnM a)
      refine ⟨r, ?_⟩
      rw [hr, key, Finset.sum_eq_single a]
      · rw [hcv, if_pos rfl, map_intCast]
      · intro b _ hb
        rw [hcv, if_neg hb, map_zero, zero_mul]
      · intro h; exact absurd (Finset.mem_univ a) h
    choose r hr using hr
    rw [hexp y]
    refine Submodule.sum_mem _ fun a _ => ?_
    have e3 : co y a • v a = r a • (((n a : E))⁻¹ • v a) := by
      rw [← algebraMap_smul E (r a), smul_smul, hr a, mul_comm (n a : E), mul_assoc,
        mul_inv_cancel₀ (Int.cast_ne_zero.2 (hn0 a)), mul_one]
    rw [e3]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  haveI : Module.Finite (𝓞 E) (Submodule.span (𝓞 E) (Set.range fun a => ((n a : E))⁻¹ • v a)) :=
    Module.Finite.span_of_finite _ (Set.finite_range _)
  refine ⟨Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle), ?_⟩

  obtain ⟨s, hs⟩ := Module.Finite.iff_fg.1 hM.1
  obtain ⟨m, hm0, hmi⟩ := exists_integral_multiples ℤ ℚ (L := E)
    (s.biUnion fun x => Finset.univ.image fun b => co x b)
  have hint : ∀ a, ∀ x ∈ M, (m : E) * co x a ∈ (algebraMap (𝓞 E) E).range := by
    intro a x hx
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      apply int_mem_range
      have := hmi (co x a) (Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩⟩)
      rwa [zsmul_eq_mul] at this
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), Pi.add_apply, mul_add]; exact add_mem hx hy
    | smul t x _ hx =>
      rw [← algebraMap_smul E t x, map_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm]
      exact mul_mem ⟨t, rfl⟩ hx
  have hmem : ∀ a, (m : E) • v a ∈ Formalism.L2.GlobalTheoryTheory.Comp.dl σ J M := by
    intro a
    rw [Formalism.L2.GlobalTheoryTheory.Comp.mem_dl]
    intro x hx
    rw [hform_v]
    have e4 : (σ : E →+* E) (co x a) * (m : E) = (σ : E →+* E) ((m : E) * co x a) := by
      rw [map_mul, map_intCast, mul_comm]
    rw [e4]
    exact ringHom_mem_range _ (hint a x hx)
  rw [eq_top_iff]
  intro z _
  rw [hexp z]
  refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ?_
  have e5 : v a = ((m : E))⁻¹ • ((m : E) • v a) := by
    rw [smul_smul, inv_mul_cancel₀ (Int.cast_ne_zero.2 hm0), one_smul]
  rw [e5]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (hmem a))

end GlobalTheory.OrthDual

theorem GlobalTheory.isLat_dl_of_isOrthCo : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E), (∃ co, IsOrthCo (sp.cm.sig : E →+* E) J co) → ∀ M : Submodule (𝓞 E) (Fin N → E), Formalism.L2.GlobalTheoryTheory.Comp.IsLat M → Formalism.L2.GlobalTheoryTheory.Comp.IsLat (Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J M) := by
  rintro R F E _ _ _ _ _ _ sp N J ⟨co, hc⟩ M hM
  exact GlobalTheory.OrthDual.isLat_dl sp.cm.sig J co hc M hM

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsOrthCoToLEOfCTMulSelf
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV

open Matrix

theorem isOrthCo_toLE_of_cT_mul_self {E : Type} [Field E] [NumberField E] {N : ℕ} (σ : E →+* E)
    (J : Matrix (Fin N) (Fin N) E) (co : GL (Fin N) E) (h : cT σ co.1 * co.1 = J) :
    IsOrthCo σ J (toLE co) := by
  intro x y
  subst h
  have ht (v : Fin N → E) : toLE co v = (co : Matrix (Fin N) (Fin N) E) *ᵥ v := rfl
  rw [ht, ht]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply,
    map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, j]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

end GlobalTheory.TwV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSDLatLatK
section
noncomputable section

namespace GlobalTheory.SDCompan

section Gen

open Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.L2.GlobalTheoryTheory.Comp Formalism.L2.KerInert
open scoped TensorProduct

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {N : ℕ}

omit [StarRing E] in
theorem latAd_eq (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Lb : Submodule (𝓞 E) (Fin N → E)) :
    Formalism.L2.PairingIndexBounds.F.latAd y Lb = Formalism.UG.CS.globLat y Lb :=
  Submodule.span_eq (Formalism.UG.CS.globLat y Lb)

theorem compan_eq (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (Λ : Submodule (𝓞 E) (Fin N → E)) :
    Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J a Λ = Λ ⊔ Ideal.span {a} • dl sp.cm.sig J Λ := rfl

theorem compan_zero (J : Matrix (Fin N) (Fin N) E) (Λ : Submodule (𝓞 E) (Fin N → E)) :
    Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J 0 Λ = Λ := by
  rw [compan_eq, Ideal.span_singleton_eq_bot.2 rfl, Submodule.bot_smul, sup_bot_eq]

theorem mem_toStd (J : Matrix (Fin N) (Fin N) E) (M : Submodule (𝓞 E) (Fin N → E)) (y : Fin N → E) :
    y ∈ Formalism.L2.PairingIndexBounds.F.toStd (sp.cm.sig : E →+* E) J M ↔
      (Formalism.L2.PairingIndexBounds.F.stdCo (sp.cm.sig : E →+* E) J).symm y ∈ M := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    have : (Formalism.L2.PairingIndexBounds.F.stdCo (sp.cm.sig : E →+* E) J).symm (Formalism.L2.PairingIndexBounds.F.stdCo (sp.cm.sig : E →+* E) J x) = x :=
      LinearEquiv.symm_apply_apply _ x
    simpa using (this ▸ hx)
  · intro h
    exact ⟨_, h, by simp⟩

theorem isSD_toStd (J : Matrix (Fin N) (Fin N) E)
    (hco : ∃ co, Formalism.L2.PairingIndexBounds.F.IsOrthCo (sp.cm.sig : E →+* E) J co)
    {M : Submodule (𝓞 E) (Fin N → E)} (hM : IsLat M) (hsd : dl sp.cm.sig J M = M) :
    IsSDLat E N (Formalism.L2.PairingIndexBounds.F.toStd (sp.cm.sig : E →+* E) J M) := by
  have hc : Formalism.L2.PairingIndexBounds.F.IsOrthCo (sp.cm.sig : E →+* E) J (Formalism.L2.PairingIndexBounds.F.stdCo (sp.cm.sig : E →+* E) J) :=
    Classical.epsilon_spec hco
  set co := Formalism.L2.PairingIndexBounds.F.stdCo (sp.cm.sig : E →+* E) J with hco_def
  have key : ∀ x y, stdH E N (co x) (co y) = hform (sp.cm.sig : E →+* E) J x y := fun x y => hc x y
  refine ⟨(Module.Finite.iff_fg.1 hM.1).map _, ?_, fun y => ?_⟩
  · rw [Formalism.L2.PairingIndexBounds.F.toStd, Submodule.map_coe, LinearMap.coe_restrictScalars, ← hco_def, eq_top_iff]
    rintro v -
    have hv : co.symm v ∈ Submodule.span E (M : Set (Fin N → E)) := by rw [hM.2]; trivial
    have h1 := Submodule.apply_mem_span_image_of_mem_span (co : (Fin N → E) →ₗ[E] (Fin N → E)) hv
    simpa using h1
  · rw [mem_toStd (sp := sp), ← hco_def]
    constructor
    · intro hy x hx
      rw [mem_toStd (sp := sp), ← hco_def] at hx
      have h1 := (mem_dl sp.cm.sig J M (co.symm y)).1 (hsd.symm ▸ hy) (co.symm x) hx
      rw [← key, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1
      exact h1
    · intro h
      rw [← hsd, mem_dl]
      intro x hx
      have h1 := h (co x) ((mem_toStd (sp := sp) J M (co x)).2 (by rw [← hco_def, LinearEquiv.symm_apply_apply]; exact hx))
      rw [← LinearEquiv.apply_symm_apply co y, key] at h1
      exact h1

theorem isSD_core (J : Matrix (Fin N) (Fin N) E)
    (hJ : ∀ M : Submodule (𝓞 E) (Fin N → E), IsLat M → IsLat (dl sp.cm.sig J M))
    (hco : ∃ co, Formalism.L2.PairingIndexBounds.F.IsOrthCo (sp.cm.sig : E →+* E) J co)
    (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hy : y ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F))
    {Lb M0 : Submodule (𝓞 E) (Fin N → E)} (hLb : IsLat Lb) (a : 𝓞 E)
    (hA : Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J a Lb = M0) (hM0 : IsLat M0) (hsd : dl sp.cm.sig J M0 = M0) :
    IsSDLat E N (Formalism.L2.PairingIndexBounds.F.toStd (sp.cm.sig : E →+* E) J
      (Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J a (Formalism.L2.PairingIndexBounds.F.latAd y Lb))) := by
  have hG : Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J a (Formalism.L2.PairingIndexBounds.F.latAd y Lb) = Formalism.UG.CS.globLat y M0 := by
    rw [latAd_eq, ← hA]
    by_cases ha : a = 0
    · subst ha
      rw [compan_zero, compan_zero]
    · rw [compan_eq, compan_eq]
      exact (glob_companion sp.cm.sig J hJ hLb ha y hy).symm
  rw [hG]
  exact isSD_toStd (sp := sp) J hco (isLat_glob hM0 y) (glob_selfdual sp.cm.sig J hJ hM0 hsd y hy)

end Gen

section Main

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isSDLat_latK : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E), (∀ M : Submodule (𝓞 E) (Fin N → E), Formalism.L2.GlobalTheoryTheory.Comp.IsLat M → Formalism.L2.GlobalTheoryTheory.Comp.IsLat (Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J M)) → (∃ co, IsOrthCo (sp.cm.sig : E →+* E) J co) → ∀ y ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F), ∀ (Lb : Submodule (𝓞 E) (Fin N → E)) (a : 𝓞 E), Formalism.L2.GlobalTheoryTheory.Comp.IsLat Lb → Formalism.L2.GlobalTheoryTheory.Comp.IsLat (compan (sp := sp) J a Lb) → Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J (compan (sp := sp) J a Lb) = compan (sp := sp) J a Lb → IsSDLat E N (latK sp J a y Lb) := by
  intro R F E _ _ _ _ _ _ sp N J hJ hco y hy Lb a hLb hM hsd
  exact isSD_core (sp := sp) J hJ hco y hy hLb a rfl hM hsd

end Main

end GlobalTheory.SDCompan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolDYExpDeg
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem polDY_exp_deg : ∀ (D : D7) {N N' : ℕ} (s : D.what₂.Tau → ℂ) (ν : D.what₂.Tau → Fin N → ℕ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ), Q ∈ WtPol ℂ ν → ∀ α ∈ (polDY D s Q (N' := N')).support, ∀ τ, ∑ b, ∑ a, α (τ, b, a) = ∑ r, ν τ r := by
  intro D N N' s ν Q hQ α hα τ
  exact Formalism.L2.KerInert.SecondKernelMoveDegree.difference_polynomial_degree D N N' s ν Q hQ α hα τ

end GlobalTheory.TwV.DelA
end

