module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0020
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0008
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.CuspFormLaws
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.RightInvariantOfCovolume
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005

@[expose] public section

noncomputable section

namespace GlobalTheory.CoreLawsCompare

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct Matrix

section Gen

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
variable {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra F E] {r : ℕ} (V : ConjugateFieldNorm.HSpace E r)




end Gen

section Rec

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

instance totallyReal_host (D : D7) : IsTotallyReal D.host.F := D.sp.cm.totReal

variable {D : D7} (V : HSp D) {r : ℕ} (hr : V.rank = r)

def crdR : V.V ≃ₗ[D.host.E] (Fin r → D.host.E) := (V.frame.reindex (finCongr hr)).equivFun

def gramR : Matrix (Fin r) (Fin r) D.host.E := (Matrix.reindex (finCongr hr) (finCongr hr) V.gram)ᵀ

theorem herm_crdR (x y : V.V) : herm (gramR V hr) (crdR V hr x) (crdR V hr y) = V.hT y x := by
  subst hr
  rw [Formalism.L2.Herm.hT_crd D.sp.cm V]
  unfold herm Formalism.UG.hform
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  simp only [crdR, gramR, finCongr_refl, Matrix.reindex_refl_refl, Module.Basis.reindex_refl]
  change _ * V.gram b a * cc _ = cc _ * V.gram b a * _
  unfold Formalism.L2.Herm.crd
  ring

theorem mem_one_iff (z : D.host.E) : z ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) ↔ IsIntegral ℤ z := by
  rw [Submodule.mem_one]
  exact ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun h => ⟨⟨z, h⟩, rfl⟩⟩

def spOf : ConjugateFieldNorm.HSpace D.host.E r where
  Gm := gramR V hr
  Gm_herm a b := V.herm.eq _ _
  Gm_det h := by
    obtain ⟨v, hv, h0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h
    obtain ⟨x, rfl⟩ := (crdR V hr).surjective v
    refine hv ((congrArg _ (V.nondeg.2 x fun y => ?_)).trans (map_zero _))
    rw [← herm_crdR V hr, herm, Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [← Finset.sum_mul, show ∑ a, crdR V hr x a * gramR V hr a b = 0 from congrFun h0 b, zero_mul]
  L := V.L0.map ((crdR V hr).toLinearMap.restrictScalars (𝓞 D.host.E))
  L_fg := V.standardTuple_isLattice.fg.map _
  L_span := by
    have hspan : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      by_contra hproper
      obtain ⟨φ, hφ, hker⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hproper)
      have hinj : Function.Injective V.hT := LinearMap.ker_eq_bot.mp
        (LinearMap.separatingLeft_iff_ker_eq_bot.mp V.nondeg.1)
      let e := LinearEquiv.ofInjective V.hT hinj
      have hrank : Module.rank D.host.E V.V = Module.rank D.host.E (LinearMap.range V.hT) :=
        rank_eq_of_equiv_equiv (starRingEnd D.host.E) e.toAddEquiv
          (star_involutive.bijective) (map_smulₛₗ e)
      have hsurj : Function.Surjective V.hT := by
        rw [← LinearMap.range_eq_top]
        apply Submodule.eq_top_of_finrank_eq
        change Module.finrank D.host.E (LinearMap.range V.hT) =
          Module.finrank D.host.E (Module.Dual D.host.E V.V)
        rw [Subspace.dual_finrank_eq]
        exact congrArg Cardinal.toNat hrank.symm
      obtain ⟨x, hx⟩ := hsurj φ
      have hx0 : x ≠ 0 := by
        rintro rfl
        exact hφ (hx.symm.trans V.hT.map_zero)
      have hline (c : D.host.E) : c • x ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual,
          Submodule.mem_iInf, Submodule.mem_comap]
        intro y hy
        have hxy : V.hT x y = 0 := by
          rw [hx]
          exact hker (Submodule.subset_span hy)
        rw [LinearMap.restrictScalars_apply, map_smul, V.herm.eq_iff.mp hxy, smul_zero]
        exact Submodule.zero_mem _
      obtain ⟨y, hy⟩ : ∃ y, V.hT y x ≠ 0 := by
        simpa only [not_forall, not_not] using mt (V.nondeg.2 x) hx0
      let f := ((V.hT y).restrictScalars (𝓞 D.host.E)).comp V.L0.subtype
      let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_surjective f <| by
        intro z
        refine ⟨⟨(z / V.hT y x) • x, hline _⟩, ?_⟩
        change V.hT y ((z / V.hT y x) • x) = z
        rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hy]
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField RingOfIntegers.coe_injective (Field.toIsField _))
    rw [Submodule.map_coe]
    change Submodule.span D.host.E ((crdR V hr).toLinearMap '' (V.L0 : Set V.V)) = ⊤
    rw [Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]
  L_dual v := by
    obtain ⟨x, rfl⟩ := (crdR V hr).surjective v
    have h1 : crdR V hr x ∈ V.L0.map ((crdR V hr).toLinearMap.restrictScalars (𝓞 D.host.E)) ↔ x ∈ V.L0 :=
      ⟨fun ⟨y, hy, e⟩ => (crdR V hr).injective e ▸ hy, fun h => ⟨x, h, rfl⟩⟩
    have h2 : x ∈ V.L0 ↔ ∀ y ∈ V.L0, IsIntegral ℤ (V.hT y x) := by
      conv_lhs => rw [← V.baseLattice_isUnimodular]
      simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, mem_one_iff]
      rfl
    rw [h1, h2]
    constructor
    · rintro h _ ⟨y, hy, rfl⟩
      exact (herm_crdR V hr x y).symm ▸ h y hy
    · intro h y hy
      exact herm_crdR V hr x y ▸ h _ ⟨y, hy, rfl⟩

structure IsCoord (V' : ConjugateFieldNorm.HSpace D.host.E r) (ψ : ConjugateFieldNorm.GA D.host.F V' ≃* GA D V) : Prop where
  sp : V' = spOf V hr
  inf : ∀ g, Matrix.reindex (finCongr hr) (finCongr hr) (infHom V (ψ g)).val = g.1.1.val
  fin : ∀ g, Matrix.reindex (finCongr hr) (finCongr hr) (finHom V (ψ g)).val = g.2.1.val
  top : AutomorphismGroupTopologies.topG D.host.F V' = TopologicalSpace.induced ψ inferInstance

variable {V hr} {V' : ConjugateFieldNorm.HSpace D.host.E r} {ψ : ConjugateFieldNorm.GA D.host.F V' ≃* GA D V}

def IsCoord.quotEquiv (h : IsCoord V hr V' ψ) : AutomorphismGroupTopologies.AutQ D.host.F V' ≃ᵐ Formalism.L2.Pj.AutQ V where
  toEquiv := Quotient.congr ψ.toEquiv fun a b => by
    have mem_GQ (g : ConjugateFieldNorm.GA D.host.F V') :
        ψ g ∈ GQ V ↔ g ∈ AutomorphismGroupTopologies.ratG D.host.F V' := by
      subst hr
      let p := (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
      let q := (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
      have hInf : (matHom V (ψ g)).val.map p = g.1.1.val := h.inf g
      have hFin : (matHom V (ψ g)).val.map q = g.2.1.val := h.fin g
      constructor
      · rintro ⟨γ, -, e⟩
        have he : (matHom V (ψ g)).val = γ.val.map (inclR (AF D.host.F)) :=
          (congrArg Units.val e).symm
        refine ⟨γ, ?_, ?_⟩
        · rw [← hInf, he]
          ext i j
          simp [p, inclR, ConjugateFieldNorm.incl]
        · rw [← hFin, he]
          ext i j
          simp [q, inclR, ConjugateFieldNorm.incl]
      · rintro ⟨γ, eInf, eFin⟩
        obtain ⟨e, he, -, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
        have he' : (matHom V (ψ g)).val = γ.val.map (inclR (AF D.host.F)) := by
          ext i j
          refine e.injective (Prod.ext ?_ ?_)
          · rw [(he _).1, (he _).1]
            exact congrFun (congrFun (hInf.trans eInf) i) j
          · rw [(he _).2, (he _).2]
            exact congrFun (congrFun (hFin.trans eFin) i) j
        refine ⟨γ, ?_, Units.ext he'.symm⟩
        have hu : Formalism.UG.cT (sigR _ D.sp.cm.sig) (matHom V (ψ g)).val *
            JR _ V.gram * (matHom V (ψ g)).val = JR _ V.gram := (ψ g).2
        have hinj : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) :=
          Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)
        change Formalism.UG.cT _ γ.val * V.gram * γ.val = V.gram
        refine Matrix.map_injective hinj ?_
        change (_ : Matrix _ _ _).map _ = JR _ V.gram
        rw [← hu, he', Matrix.map_mul, Matrix.map_mul]
        congr 2
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply]
    change _ ↔ ψ b * (ψ a)⁻¹ ∈ GQ V
    rw [← map_inv, ← map_mul]
    exact (mem_GQ _).symm
  measurable_toFun s hs := by
    change MeasurableSet[@borel _ (AutomorphismGroupTopologies.topG D.host.F V')] (ψ ⁻¹' (Formalism.L2.Pj.autMk V ⁻¹' s))
    rw [h.top, borel_comap]
    exact ⟨_, hs, rfl⟩
  measurable_invFun s hs := by
    have hs' : MeasurableSet[@borel _ (AutomorphismGroupTopologies.topG D.host.F V')] (AutomorphismGroupTopologies.autMk D.host.F V' ⁻¹' s) := hs
    rw [h.top, borel_comap] at hs'
    obtain ⟨t, ht, e⟩ := hs'
    change MeasurableSet (ψ.symm ⁻¹' (AutomorphismGroupTopologies.autMk D.host.F V' ⁻¹' s))
    rw [← e, ← Set.preimage_comp]
    simpa using ht

def RightInv (V : HSp D) (ν : Measure (Formalism.L2.Pj.AutQ V)) : Prop :=
  ∀ (h : GA D V) (ρ : Formalism.L2.Pj.AutQ V → Formalism.L2.Pj.AutQ V),
    (∀ g : GA D V, ρ (Quotient.mk _ g) = Quotient.mk _ (g * h)) → ∀ s, MeasurableSet s → ν (ρ ⁻¹' s) = ν s

end Rec

end GlobalTheory.CoreLawsCompare
