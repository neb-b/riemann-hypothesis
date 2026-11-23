module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3110
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphFiltrationLieCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3106
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3101
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0675
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0126
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3076
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2121
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2427
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedMembersClassSumsDeeperLevels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2825
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2768

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentsMemOfSumMemDistinctEigencharactersMod
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory

theorem eigen_components_mod_stable {k : Type} [Field k] {H : Type 1} [AddCommGroup H] [Module k H]
    {O : Type} [CommRing O] (ρ : O →+* Module.End k H) (F : Submodule k H)
    (hF : ∀ c, ∀ x ∈ F, ρ c x ∈ F) {a : ℕ} (χ : Fin a → O → k)
    (hχ : ∀ i j, i ≠ j → ∃ c, χ i c ≠ χ j c) (S : Finset (Fin a)) :
    ∀ u : Fin a → H, (∀ i ∈ S, ∀ c, ρ c (u i) - χ i c • u i ∈ F) →
      ∑ i ∈ S, u i ∈ F → ∀ i ∈ S, u i ∈ F := by
  first
  | exact @_root_.GlobalTheory.MembershipOfSum.mem_of_sum_mem
  | exact _root_.GlobalTheory.MembershipOfSum.mem_of_sum_mem
  | (apply _root_.GlobalTheory.MembershipOfSum.mem_of_sum_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.MembershipOfSum.mem_of_sum_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MembershipOfSum.mem_of_sum_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MembershipOfSum.mem_of_sum_mem ..)

theorem eigen_mod_stable : ∀ (k : Type) [Field k] (H : Type 1) [AddCommGroup H] [Module k H] (O : Type) [CommRing O] (ρ : O →+* Module.End k H) (F : Submodule k H), (∀ c, ∀ x ∈ F, ρ c x ∈ F) → ∀ (a : ℕ) (χ : Fin a → O → k), (∀ i j, i ≠ j → ∃ c, χ i c ≠ χ j c) → ∀ u : Fin a → H, (∀ i c, ρ c (u i) - χ i c • u i ∈ F) → ∑ i, u i ∈ F → ∀ i, u i ∈ F := by
  intro k _ H _ _ O _ ρ F hF a χ hχ u hu hs i
  exact eigen_components_mod_stable ρ F hF χ hχ Finset.univ u (fun i _ c => hu i c) hs i (Finset.mem_univ i)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphFiltrationLieConditionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalGluedHodgeGraphFiltration_lie_condition : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (f j)) → (∀ e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (e)) - algebraMap k (TrivSqZeroExt k (Fin d → k)) (β b.ρ) • e ∈ (GlobalTheory.HTGlue.glueFil o₀.A f) → ∃ w : Fin D.a → Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - algebraMap k (TrivSqZeroExt k (Fin d → k)) (β (b.t i c)) • w i ∈ (GlobalTheory.HTGlue.glueFil o₀.A f)) ∧ e - ∑ i, w i ∈ (GlobalTheory.HTGlue.glueFil o₀.A f)) := by
  first | (exact @GlobalTheory.HTGlueLie.glueFil_lie) | (exact GlobalTheory.HTGlueLie.glueFil_lie) | (intros; apply GlobalTheory.HTGlueLie.glueFil_lie  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphIsotropicOfDirectionsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalGluedHodgeGraph_isotropic_of_directions : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (tk : R →+* k) (s : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s), s = spMap tk → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), ∀ (E' : Fin d → Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A)), (∀ j, ∃ M : Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A), IsCompl (E' j) M) → (∀ j, ∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ e ∈ E' j, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k k)) rfl o₀.A).Corr e y) → (∀ j, ∀ x ∈ Fil o₀.A, ∃ e ∈ E' j, ∀ c, e ((GlobalTheory.FODef.constMorV k k o₀.A).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (f j x c)) → (∀ j (c : D.O), ∀ e ∈ E' j, (haveI := o₀.act.hom (c); push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (o₀.act.act (c)) (e)) ∈ E' j) → (∀ j, ∀ φ : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A →ₗ[TrivSqZeroExt k k] Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A →ₗ[TrivSqZeroExt k k] TrivSqZeroExt k k, GlobalTheory.AbDual.IsCorrForm (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A o₀.A o₀.P φ → ∀ x ∈ E' j, ∀ y ∈ E' j, φ x y = 0) → ∀ φ : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A →ₗ[TrivSqZeroExt k (Fin d → k)] Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A →ₗ[TrivSqZeroExt k (Fin d → k)] TrivSqZeroExt k (Fin d → k), GlobalTheory.AbDual.IsCorrForm (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A o₀.A o₀.P φ → ∀ x ∈ GlobalTheory.HTGlue.glueFil o₀.A f, ∀ y ∈ GlobalTheory.HTGlue.glueFil o₀.A f, φ x y = 0 := by
  first | (exact @GlobalTheory.HTGlueIso.glueFil_isotropic) | (exact GlobalTheory.HTGlueIso.glueFil_isotropic) | (intros; apply GlobalTheory.HTGlueIso.glueFil_isotropic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalProjectiveOverTensorRingOfIntegers
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
attribute [local instance] Functor.grpObjObj

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HTSummand

theorem crys_projective : ∀ (F : Type) [Field F] [NumberField F] (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (A₀ : Over (Sp C₀)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ (O : Type) [Ring O] [Algebra (𝓞 F) O] (a : GlobalTheory.UPel.HT.OActN O A₀), letI := GlobalTheory.HTSummand.tensorModOf ((GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) a).comp (algebraMap (𝓞 F) O)); Module.Projective (C ⊗[ℤ] 𝓞 F) (Crys (divided₂ hsq) (spMap π) A₀) := by
  intro F _ _ C C₀ _ _ _ _ π hπ hsq A₀ _ _ hA O _ _ a
  haveI : Nontrivial C₀ := by
    refine ⟨⟨0, 1, fun h ↦ ?_⟩⟩
    have h1 : (1 : C) ∈ RingHom.ker π := by rw [RingHom.mem_ker, map_one]; exact h.symm
    have h2 : (1 : C) ∈ RingHom.ker π ^ 2 := by
      rw [pow_two]; simpa using Ideal.mul_mem_mul h1 h1
    rw [hsq] at h2
    exact one_ne_zero ((Submodule.mem_bot C).1 h2)
  haveI : IsLocalRing C₀ := IsLocalRing.of_surjective' π hπ
  obtain ⟨red, hfin, hproj, hsurj, hker, -, hequiv, -⟩ := _root_.GlobalTheory.CrysRed.exists_crysRed C C₀ π hπ hsq A₀ hA O a
  let a' : OAct (𝓞 F) A₀ :=
    { act := fun x ↦ a.act (algebraMap (𝓞 F) O x)
      hom := fun x ↦ a.hom _
      one := by rw [map_one]; exact a.one
      mul := fun x y ↦ by rw [mul_comm, map_mul, a.mul]
      add := fun x y ↦ by rw [map_add (f := _), a.add] }
  obtain ⟨f, fsurj, fker, fequiv⟩ := GlobalTheory.T.deRhamHomology_closedFibre_surjective_kernel C₀ A₀ hA (𝓞 F) a'
  have hB : IsAbelianScheme ((Over.pullback (spMap (algebraMap C₀ (IsLocalRing.ResidueField C₀)))).obj A₀) :=
    { comm := by have := hA.comm; infer_instance
      smooth := by have := hA.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by have := hA.proper; show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by
        have := hA.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }
  have hP := GlobalTheory.T.firstDeRhamHomology_projective_over_tensor_integers F (IsLocalRing.ResidueField C₀) _ hB (OAct.pullback _ A₀ a')
  let σ : C →+* IsLocalRing.ResidueField C₀ := (algebraMap C₀ (IsLocalRing.ResidueField C₀)).comp π
  have hσ : Function.Surjective σ := IsLocalRing.residue_surjective.comp hπ
  haveI : RingHomCompTriple π (algebraMap C₀ (IsLocalRing.ResidueField C₀)) σ := ⟨rfl⟩
  have hle : RingHom.ker π ≤ RingHom.ker σ := fun b hb ↦ by
    rw [RingHom.mem_ker] at hb ⊢
    show algebraMap C₀ (IsLocalRing.ResidueField C₀) (π b) = 0
    rw [hb, map_zero]
  refine GlobalTheory.T.projective_tensor_of_fibre_projective' C (IsLocalRing.ResidueField C₀) (𝓞 F) σ hσ _ _
    ((GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) a).comp (algebraMap (𝓞 F) O))
    (act (dp0 (IsLocalRing.ResidueField C₀)) (𝟙 _) (OAct.pullback _ A₀ a')) (f.comp red) hfin hproj
    (fsurj.comp hsurj) ?_ ?_ hP
  · intro h hh
    have h1 : red h ∈ IsLocalRing.maximalIdeal C₀ • (⊤ : Submodule C₀ (HdR A₀)) := fker _ hh
    have h2 : ∀ y ∈ IsLocalRing.maximalIdeal C₀ • (⊤ : Submodule C₀ (HdR A₀)),
        ∃ x ∈ RingHom.ker σ • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) A₀)), red x = y := by
      intro y hy
      refine Submodule.smul_induction_on hy ?_ ?_
      · intro c hc y _
        obtain ⟨b, rfl⟩ := hπ c
        obtain ⟨x, rfl⟩ := hsurj y
        refine ⟨b • x, Submodule.smul_mem_smul ?_ Submodule.mem_top, ?_⟩
        · rw [RingHom.mem_ker]
          show algebraMap C₀ (IsLocalRing.ResidueField C₀) (π b) = 0
          rw [IsLocalRing.ResidueField.algebraMap_eq]
          exact (IsLocalRing.residue_eq_zero_iff _).2 hc
        · exact LinearMap.map_smulₛₗ red b x
      · rintro y y' ⟨x, hx, rfl⟩ ⟨x', hx', rfl⟩
        exact ⟨x + x', add_mem hx hx', map_add _ _ _⟩
    obtain ⟨x, hx, hxe⟩ := h2 _ h1
    have h3 : h - x ∈ RingHom.ker π • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) A₀)) :=
      hker _ (by rw [map_sub, hxe, sub_self])
    have h4 := Submodule.smul_mono_left hle h3
    simpa using add_mem h4 hx
  · intro x h
    show f (red (GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) a (algebraMap (𝓞 F) O x) h)) = _
    rw [hequiv]
    exact fequiv x (red h)

end GlobalTheory.HTSummand
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreePowFinrankEqNatAbsNormPow
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar
open scoped CategoryTheory.Obj CategoryTheory.MonObj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.AbVar.DegNorm

open Polynomial IntermediateField

theorem deg_pow_finrank_eq_natAbs_norm_pow : ∀ (K : Type) [Field K] (B : AbVar K) (F : Type) [Field F] [NumberField F] (ψ : 𝓞 F →+* End B) (c : 𝓞 F), c ≠ 0 → deg (ψ c).asHom ^ Module.finrank ℚ F = (Algebra.norm ℤ c).natAbs ^ (2 * B.dim) := by
  intro K _ B F _ _ ψ c hc
  have hN : Algebra.norm ℤ c ≠ 0 := by
    intro h
    have h1 := Algebra.coe_norm_int c
    rw [h, Int.cast_zero, eq_comm, Algebra.norm_eq_zero_iff] at h1
    exact hc (by exact_mod_cast h1)
  by_cases hB : B.dim = 0
  · obtain ⟨y, hy⟩ := dvd_algebraMap_norm c
    have hcomp : (ψ y).asHom ≫ (ψ c).asHom = Algebra.norm ℤ c • 𝟙 B := by
      rw [← End.mul_asHom]
      rw [← map_mul, ← hy, algebraMap_int_eq, Int.coe_castRingHom, map_intCast, ← zsmul_one]
      rfl
    have h := isIsogeny_comp_iff_and_deg_comp K B B B (ψ y).asHom (ψ c).asHom rfl rfl
    obtain ⟨-, hd⟩ := GlobalTheory.MulIsogeny.mul_isogeny K B _ hN
    rw [hcomp] at h
    rw [h.2, hB, mul_zero, pow_zero] at hd
    have h1 : deg (ψ c).asHom = 1 := Nat.eq_one_of_mul_eq_one_left hd
    rw [h1, hB, mul_zero, pow_zero, one_pow]
  · classical
    obtain ⟨k, hk, hPQ⟩ := charpoly_eq_minpoly_pow B hB ψ c
    obtain ⟨⟨-, hd, -⟩, -⟩ := isCharpoly_charpoly_unique K B (ψ c)
    have hxint : IsIntegral ℚ (c : F) := Algebra.IsIntegral.isIntegral _
    have hdeg : k * Module.finrank ℚ ℚ⟮(c : F)⟯ = 2 * B.dim := by
      have e := congrArg Polynomial.natDegree hPQ
      rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int _), hd,
        Polynomial.natDegree_pow, ← IntermediateField.adjoin.finrank hxint] at e
      omega
    have hD := deg_aeval_eq_prod_aroots K B (ψ c) (AlgebraicClosure ℚ) Polynomial.X
    simp only [aeval_X, Multiset.map_id'] at hD
    rw [hPQ, Polynomial.aroots_pow, Multiset.prod_nsmul] at hD
    have hNr := Algebra.norm_eq_prod_roots (K := ℚ) (L := F) (AlgebraicClosure ℚ) (x := (c : F))
      (IsAlgClosed.splits _)
    have e : algebraMap ℚ (AlgebraicClosure ℚ) ((deg (ψ c).asHom : ℚ) ^ Module.finrank ℚ⟮(c : F)⟯ F) =
        algebraMap ℚ (AlgebraicClosure ℚ) (Algebra.norm ℚ (c : F) ^ k) := by
      rw [map_pow, map_pow, hD, hNr, ← pow_mul, ← pow_mul, mul_comm]
    have e2 := (algebraMap ℚ (AlgebraicClosure ℚ)).injective e
    rw [← Algebra.coe_norm_int] at e2
    have e3 : (deg (ψ c).asHom : ℤ) ^ Module.finrank ℚ⟮(c : F)⟯ F = Algebra.norm ℤ c ^ k := by
      exact_mod_cast e2
    have e4 := congrArg (fun t : ℤ => t ^ Module.finrank ℚ ℚ⟮(c : F)⟯) e3
    simp only [← pow_mul] at e4
    rw [hdeg, mul_comm, Module.finrank_mul_finrank] at e4
    have e5 := congrArg Int.natAbs e4
    simpa [Int.natAbs_pow] using e5

end GlobalTheory.AV.AbVar.DegNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberHodgeSummandEqGraphCoordinates
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.HTGlueLie
variable {k : Type} [Field k] {A₀ : Over (Sp k)} [GrpObj A₀]

theorem inr_one_mul (y : TrivSqZeroExt k k) :
    (TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) * y = TrivSqZeroExt.inr y.fst := by
  ext
  · simp
  · simp

theorem fstC_inr_smul (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀) :
    fstC A₀ ((TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) • e) = 0 := by
  ext c
  rw [fstC_apply]
  change ((TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) * e ((GlobalTheory.FODef.constMorV k k A₀).pull c)).fst = 0
  rw [inr_one_mul, TrivSqZeroExt.fst_inr]

theorem sndC_inr_smul (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀) :
    (sndC A₀ ((TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) • e) : HdR A₀) = fstC A₀ e := by
  ext c
  change (sndC A₀ _) c = fstC A₀ e c
  rw [sndC_apply, fstC_apply]
  change ((TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) * e ((GlobalTheory.FODef.constMorV k k A₀).pull c)).snd = _
  rw [inr_one_mul, TrivSqZeroExt.snd_inr]

theorem exists_of_coords_self (hA : IsAbelianScheme A₀) (x : HdR A₀) (y : primDR A₀ →ₗ[k] k) :
    ∃ e : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀, fstC A₀ e = x ∧ sndC A₀ e = y :=
  exists_of_coords hA x y

theorem ext_coords_self (hA : IsAbelianScheme A₀) {e e' : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀}
    (h1 : fstC A₀ e = fstC A₀ e') (h2 : (sndC A₀ e : HdR A₀) = sndC A₀ e') : e = e' :=
  ext_coords hA h1 h2


set_option maxHeartbeats 1600000 in
theorem dualNumber_hodge_summand_eq_graph_coords_of_compl (hA : IsAbelianScheme A₀) (f : HdR A₀ →ₗ[k] HdR A₀)
    (E M : Submodule (TrivSqZeroExt k k)
      (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀))
    (hEM : IsCompl E M)
    (h2 : ∀ y : HdR A₀, y ∈ Fil A₀ ↔ ∃ e ∈ E,
      (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k k)) rfl A₀).Corr e y)
    (h3 : ∀ x ∈ Fil A₀, ∃ e ∈ E, ∀ c, e ((GlobalTheory.FODef.constMorV k k A₀).pull c) =
      TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (f x c))
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀) :
    e ∈ E ↔ (fstC A₀ e ∈ Fil A₀ ∧ (sndC A₀ e : HdR A₀) - f (fstC A₀ e) ∈ Fil A₀) := by
  have hε := fun e' ↦ And.intro (fstC_inr_smul (A₀ := A₀) e') (sndC_inr_smul (A₀ := A₀) e')
  have hc : ∀ x ∈ Fil A₀, ∃ e ∈ E, fstC A₀ e = x ∧ (sndC A₀ e : HdR A₀) = f x := by
    intro x hx
    refine (h3 x hx).elim fun e₁ hh ↦ ⟨e₁, hh.1, ?_, ?_⟩
    · ext c; rw [fstC_apply, hh.2 c, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
    · ext c; show (sndC A₀ e₁) c = _; rw [sndC_apply, hh.2 c, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
  have hfil : ∀ a ∈ E, fstC A₀ a ∈ Fil A₀ := fun a ha ↦ (h2 _).2 ⟨a, ha, (corr_iff_fstC hA a _).2 rfl⟩
  constructor
  · intro he
    have hx := hfil e he
    obtain ⟨e₁, he₁, h1, h1'⟩ := hc _ hx
    refine ⟨hx, ?_⟩
    have hh := exists_of_coords_self hA ((sndC A₀ e : HdR A₀) - f (fstC A₀ e)) 0
    obtain ⟨yh, hy1, -⟩ := hh
    have hεy : (TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) • yh = e - e₁ := by
      refine ext_coords_self hA ?_ ?_
      · rw [(hε yh).1, map_sub, h1, sub_self]
      · have h5 := (hε yh).2
        rw [hy1] at h5
        show (sndC A₀ _ : HdR A₀) = sndC A₀ (e - e₁)
        rw [h5, map_sub]
        show _ = (sndC A₀ e : HdR A₀) - (sndC A₀ e₁ : HdR A₀)
        rw [h1']
    have hmem : (TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) • yh ∈ E := hεy ▸ E.sub_mem he he₁
    have hyt : yh ∈ E ⊔ M := hEM.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨a, ha, m, hm, hsum⟩ := Submodule.mem_sup.1 hyt
    have hεm : (TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) • m ∈ E := by
      have := E.sub_mem hmem (E.smul_mem (TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) ha)
      rwa [← hsum, smul_add, add_sub_cancel_left] at this
    have hm0 : (TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) • m = 0 :=
      (Submodule.disjoint_def.1 hEM.disjoint) _ hεm (M.smul_mem _ hm)
    have hm1 : fstC A₀ m = 0 := by rw [← (hε m).2, hm0, map_zero]
    rw [← hy1, ← hsum, map_add (f := _), hm1, add_zero]
    exact hfil a ha
  · rintro ⟨hx, hz⟩
    obtain ⟨e₁, he₁, h1, h1'⟩ := hc _ hx
    obtain ⟨e₂, he₂, h2a, -⟩ := hc _ hz
    have : e = e₁ + (TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) • e₂ := by
      refine ext_coords_self hA ?_ ?_
      · rw [map_add (f := _), (hε e₂).1, h1, add_zero]
      · show (sndC A₀ e : HdR A₀) = (sndC A₀ (e₁ + _) : HdR A₀)
        rw [map_add (f := _)]
        show _ = (sndC A₀ e₁ : HdR A₀) + (sndC A₀ (_ • e₂) : HdR A₀)
        rw [(hε e₂).2, h1', h2a, add_sub_cancel]
    rw [this]
    exact E.add_mem he₁ (E.smul_mem _ he₂)

theorem fo_summand_coords : ∀ (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ → ∀ (f : HdR A₀ →ₗ[k] HdR A₀) (E : Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀)), (∃ M : Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀), IsCompl E M) → (∀ y : HdR A₀, y ∈ Fil A₀ ↔ ∃ e ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k k)) rfl A₀).Corr e y) → (∀ x ∈ Fil A₀, ∃ e ∈ E, ∀ c, e ((GlobalTheory.FODef.constMorV k k A₀).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (f x c)) → ∀ e : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀, e ∈ E ↔ (GlobalTheory.HTGlueLie.fstC A₀ e ∈ Fil A₀ ∧ (GlobalTheory.HTGlueLie.sndC A₀ e : HdR A₀) - f (GlobalTheory.HTGlueLie.fstC A₀ e) ∈ Fil A₀) := fun _ _ _ _ hA f E ⟨M, hEM⟩ h2 h3 e ↦
  dualNumber_hodge_summand_eq_graph_coords_of_compl hA f E M hEM h2 h3 e

end GlobalTheory.HTGlueLie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFourierTermSystemTraitsChartThetaModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.Poinc.Sep.nonempty_uMem_trait {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    (hZ : IsNormalScheme Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (hact : IsAct X₁ act)
    (T : Trait F) (ev : X₁.M.Z.presheaf.stalk z₁ →+* T.V) (h₁ : IsLocalHom ev) (h₂ : RegAt X₁ z₁ ev)
    (h₃ : jK T.V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = T.y ≫ i) :
    Nonempty (UMem X₁ z₁ act T.V ev T.D.toPre.X ![T.ϖ] ![T.β]) := by
  haveI := X₁.imm
  obtain ⟨hτ, h0, -, -⟩ := _root_.GlobalTheory.Poinc.TraitTau.main g n _ _ F T
  have hcn : IsCN T.V := ⟨inferInstance, inferInstance, T.complete, inferInstance⟩
  obtain ⟨𝔪, -⟩ := _root_.GlobalTheory.Poinc.Sep.MkMember.exists_uMem g X₁.one_le n X₁.three_le X₁.odd F Z X₁.z i X₁.proj hZ X₁.thetaSetup_structureMap_comp X₁.dense W X₁.e8
    X₁.thetaInt X₁ z₁ act hact T.V (GlobalTheory.PolDeg.Wit.ofDeg T.D.toPre T.D.tau_bimult) 1 ![T.ϖ] ![T.β]
    (fun k => by rw [Subsingleton.elim k 0]; exact T.irr.ne_zero)
    (fun k => by rw [Subsingleton.elim k 0]; exact T.symm)
    (fun k => by rw [Subsingleton.elim k 0]; exact h0) hτ T.V (RingHom.id _) hcn Function.injective_id
    (RingHom.Finite.id _) T.D (AddEquiv.refl _) (GlobalTheory.PolDeg.Wit.refines_ofDeg _ _) T.G T.A T.U T.y T.α T.α₂ T.semi T.cart
    T.sq T.lb ev h₁ h₂ h₃
  exact ⟨𝔪⟩

theorem _root_.GlobalTheory.Poinc.Sep.exists_vPre_traits_chart : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), Module.finrank ℤ Q.X ≤ g → (∀ k, t k ∈ maximalIdeal V ∧ t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ a, a ≠ 0 → ∃ k, 0 < δ k a a) → Q.IsMonomialTau t δ → ∀ ξ : Sp V ⟶ Z, UnifOver F i ξ Q → ∀ l : ℕ, l.Prime → l ∣ n → ∀ j₀ : ℕ, ∃ (j : ℕ) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (_ : IsDomain (X₁.M.Z.presheaf.stalk z₁)) (Φ : VPre (id : ℤ → ℤ) g W (X₁.M.Z.presheaf.stalk z₁)) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃+ Q.X) (h : Fin (Φ.m y) ≃ Fin m) (c₀ : Φ.Q), j₀ ≤ j ∧ HasTraitsR X₁ z₁ Φ ∧ IsChartMemberP X₁ z₁ Φ ((l ^ j) ^ 2) Q ξ t δ y ρ e h ∧ (∀ y', IsUnit (Φ.u y' 0 c₀)) ∧ (∀ y', Φ.m y' ≠ 1 → y' = y) ∧ Φ.Exact ((l ^ j) ^ 2) ∧ Φ.ClassSums ((l ^ j) ^ 2) := by
  intro g hg n hn hodd F Z z i _ hproj hnorm hiz hdense W hW hth V _ _ _ Q m t δ hrk ht hsymm hnn hpos hτ ξ hξ l hl hln j₀
  obtain ⟨j, X₁, z₁, V₁, _, _, _, ρ, ev, D₀, e₀, hj, hN, hcn, hinj, hfin, hloc, hreg, hcomp, href⟩ :=
    _root_.GlobalTheory.Poinc.Sep.exists_setup_regAt_chart g hg n hn hodd F Z z i hproj hnorm hiz hdense W hW hth V Q m t δ hrk ht hsymm hnn hpos hτ ξ hξ l hl hln j₀
  have hdom := (GlobalTheory.Poinc.stalk_isNoetherian_normal_fractionRing g n F W Z i X₁ z₁).1
  obtain ⟨act, hact⟩ := _root_.GlobalTheory.Poinc.Sep.exists_isAct g n F W Z i X₁
  obtain ⟨x₀, hx₀⟩ := X₁.div z₁
  obtain ⟨G₀, _, _, A₀, U₀, y₀, α, α₂, hsemi, hy₀, hcart, hsq, hlb⟩ := hξ.2 V₁ ρ hcn hinj hfin D₀ e₀ href
  obtain ⟨𝔪₀, hsharp⟩ := _root_.GlobalTheory.Poinc.Sep.MkMember.exists_uMem g hg n hn hodd F Z z i hproj hnorm hiz hdense W hW hth X₁ z₁ act hact V Q m t δ
    (fun k => (ht k).2) hsymm hnn hτ V₁ ρ hcn hinj hfin D₀ e₀ href G₀ A₀ U₀ y₀ α α₂ hsemi hcart hsq hlb ev hloc hreg
    (by rw [hcomp, hy₀])
  have hζ : IsUnit (zetaAway n) := by
    rw [← cycBase_ζ (show n ≠ 0 by omega)]
    exact Units.isUnit _
  have hρ : IsLocalHom ρ := by
    letI := ρ.toAlgebra
    haveI : Module.Finite V V₁ := hfin
    haveI : FaithfulSMul V V₁ := (faithfulSMul_iff_algebraMap_injective V V₁).2 hinj
    exact (inferInstance : IsLocalHom (algebraMap V V₁))
  let Tr : Type 1 := Σ T : Trait F, {e : X₁.M.Z.presheaf.stalk z₁ →+* T.V // IsLocalHom e ∧ RegAt X₁ z₁ e ∧
    jK T.V ≫ spMap e ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = T.y ≫ i}
  let VV : Option Tr → Type := fun y => match y with | none => V₁ | some T => T.1.V
  letI iR : ∀ y, CommRing (VV y) := fun y => match y with
    | none => inferInstanceAs (CommRing V₁) | some T => inferInstanceAs (CommRing T.1.V)
  haveI iD : ∀ y, IsDomain (VV y) := fun y => match y with
    | none => inferInstanceAs (IsDomain V₁) | some T => inferInstanceAs (IsDomain T.1.V)
  haveI iL : ∀ y, IsLocalRing (VV y) := fun y => match y with
    | none => inferInstanceAs (IsLocalRing V₁) | some T => inferInstanceAs (IsLocalRing T.1.V)
  let EV : ∀ y, X₁.M.Z.presheaf.stalk z₁ →+* VV y := fun y => match y with | none => ev | some T => T.2.1
  let XX : Option Tr → Type := fun y => match y with | none => Q.X | some T => T.1.D.toPre.X
  letI iA : ∀ y, AddCommGroup (XX y) := fun y => match y with
    | none => inferInstanceAs (AddCommGroup Q.X) | some T => inferInstanceAs (AddCommGroup T.1.D.toPre.X)
  haveI iF : ∀ y, Module.Free ℤ (XX y) := fun y => match y with
    | none => inferInstanceAs (Module.Free ℤ Q.X) | some T => inferInstanceAs (Module.Free ℤ T.1.D.toPre.X)
  haveI iG : ∀ y, Module.Finite ℤ (XX y) := fun y => match y with
    | none => inferInstanceAs (Module.Finite ℤ Q.X) | some T => inferInstanceAs (Module.Finite ℤ T.1.D.toPre.X)
  let MM : Option Tr → ℕ := fun y => match y with | none => m | some _ => 1
  let tt : ∀ y, Fin (MM y) → VV y := fun y => match y with | none => fun k => ρ (t k) | some T => ![T.1.ϖ]
  let dd : ∀ y, Fin (MM y) → LinearMap.BilinForm ℤ (XX y) := fun y => match y with | none => δ | some T => ![T.1.β]
  let 𝔪 : ∀ y, UMem X₁ z₁ act (VV y) (EV y) (XX y) (tt y) (dd y) := fun y => match y with
    | none => 𝔪₀
    | some T => (nonempty_uMem_trait hnorm X₁ z₁ act hact T.1 T.2.1 T.2.2.1 T.2.2.2.1 T.2.2.2.2).some
  have hlab : Set.range (Subtype.val : X₁.S.HH X₁.M z₁ → X₁.S.Gam) = X₁.S.HH X₁.M z₁ := Subtype.range_val
  choose u hu₁ hu₂ hu₃ using fun y => _root_.GlobalTheory.Poinc.IntTerm.exists_terms g n F W Z i X₁ z₁ act x₀ hx₀ (VV y) (EV y) (XX y) (MM y) (tt y) (dd y)
    (𝔪 y) (X₁.S.HH X₁.M z₁) Subtype.val hlab
  let Φ : VPre (id : ℤ → ℤ) g W (X₁.M.Z.presheaf.stalk z₁) :=
    { posW := X₁.posW
      Y := Option Tr
      V := VV
      cn := fun y => (𝔪 y).cn
      ev := EV
      ev_loc := fun y => (𝔪 y).loc
      X := XX
      rank_le := fun y => match y with
        | none => hrk
        | some T => (_root_.GlobalTheory.Poinc.TraitTau.main g n _ _ F T.1).2.2.2 (by omega) hζ
      m := MM
      t := tt
      t_mem := fun y => match y with
        | none => fun k => ⟨map_nonunit ρ _ (ht k).1, fun h => (ht k).2 (hinj (h.trans (map_zero ρ).symm))⟩
        | some T => fun k => by
            rw [Subsingleton.elim (α := Fin 1) k 0]
            exact ⟨T.1.irr.not_isUnit, T.1.irr.ne_zero⟩
      δ := dd
      bal := fun y => match y with
        | none => fun k => mem_balForms_int.2 (hsymm k)
        | some T => fun k => by
            rw [Subsingleton.elim (α := Fin 1) k 0]
            exact mem_balForms_int.2 T.1.symm
      nonneg := fun y => match y with
        | none => hnn
        | some T => fun k => by
            rw [Subsingleton.elim (α := Fin 1) k 0]
            exact (_root_.GlobalTheory.Poinc.TraitTau.main g n _ _ F T.1).2.1
      pos := fun y => match y with
        | none => hpos
        | some T => fun x hx => ⟨(0 : Fin 1), (_root_.GlobalTheory.Poinc.TraitTau.main g n _ _ F T.1).2.2.1 x hx⟩
      Q := X₁.S.HH X₁.M z₁
      u := u
      u_unit := hu₂ }
  have hgeo : IsGeo X₁ z₁ act x₀ Φ Subtype.val := ⟨hx₀, hlab, fun y => ⟨𝔪 y, hu₁ y⟩⟩
  refine ⟨j, X₁, z₁, hdom, Φ, none, ρ, AddEquiv.refl _, Equiv.refl _, ⟨x₀, AddSubgroup.subset_closure hx₀⟩, hj, ?_, ?_,
    fun y => hu₃ y _ rfl, ?_, ?_, ?_⟩
  · intro T e h₁ h₂ h₃
    refine ⟨some ⟨T, e, h₁, h₂, h₃⟩, RingHom.id _, AddEquiv.refl _, rfl, inferInstanceAs (IsPrincipalIdealRing T.V),
      Function.injective_id, inferInstanceAs (IsLocalHom (RingHom.id T.V)), rfl, fun k => ?_⟩
    rw [Subsingleton.elim (α := Fin 1) k 0]
    exact ⟨rfl, fun _ _ => rfl⟩
  · refine ⟨hinj, hfin, hcomp, fun k => ⟨rfl, fun _ _ => rfl⟩, 𝔪₀.D.toPre, 𝔪₀.e₈, hsharp, ?_⟩
    rw [← hN]
    exact _root_.GlobalTheory.Poinc.Sep.ThetaTerms.isThetaTerms₀_of_terms g n F W Z i X₁ z₁ act x₀ hx₀ V₁ ev Q.X m _ δ 𝔪₀ _ Subtype.val hlab _ (hu₁ none)
  · rintro (_ | T) h
    · rfl
    · exact absurd rfl h
  · rw [← hN]
    exact _root_.GlobalTheory.Poinc.Sep.ExactSums.exact_of_isGeo g n F W Z i X₁ z₁ act x₀ Φ _ hgeo
  · rw [← hN]
    exact _root_.GlobalTheory.Poinc.Sep.DeepSums.classSums_deeper g hg n hn hodd F Z z i hproj hnorm hiz hdense W hW hth X₁ z₁ act hact x₀ Φ _ hgeo
end

