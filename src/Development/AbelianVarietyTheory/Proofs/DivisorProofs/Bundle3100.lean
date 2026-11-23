module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3095
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2871
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3084
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeLiftWithPrincipalLineBundle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2915
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2193
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3094
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Rosati
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0791
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3079
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0691
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0016
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PreservesFiniteLimitsTensorLeftSheafify
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2847
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2423
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2374
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2591
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0929
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2846
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2786
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3087
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2579
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1419
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2808
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2831

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphOrderStableOfDirections
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTGlueOStab

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]

theorem coord_ext (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    {e e' : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀}
    (h : ∀ c, e ((GlobalTheory.FODef.constMorV k V A₀).pull c) = e' ((GlobalTheory.FODef.constMorV k V A₀).pull c)) :
    e = e' := by
  refine LinearMap.ext fun c' => ?_
  obtain ⟨u, rfl⟩ := (GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k V A₀ hA (GlobalTheory.FODef.sqZero k V)
    (GlobalTheory.FODef.constMorV k V A₀)).2 c'
  induction u using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add u v hu hv => simp only [map_add (f := _), hu, hv]
  | tmul r c => rw [liftSemi_tmul, map_smul, map_smul, h]

theorem push_coord (A₀ : Over (Sp k)) [GrpObj A₀] (f : A₀ ⟶ A₀) [IsMonHom f]
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀)
    (c : primDR A₀) :
    push (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) f e
        ((GlobalTheory.FODef.constMorV k V A₀).pull c) =
      e ((GlobalTheory.FODef.constMorV k V A₀).pull (primPull (dp0 k) (𝟙 _) f c)) := by
  rw [push_apply]
  congr 1
  have m : GrpMor (dp0 k) (𝟙 _) A₀ (divided₂ (GlobalTheory.FODef.sqZero k V))
      (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀
      (algebraMap k (TrivSqZeroExt k V)) (𝟙 _) f.left :=
    ⟨(GlobalTheory.FODef.constMorV k V A₀).dp, (GlobalTheory.FODef.constMorV k V A₀).base,
      (homMor (dp0 k) (𝟙 _) f).w, (homMor (dp0 k) (𝟙 _) f).mul⟩
  exact (GrpMor.pull_pull (GlobalTheory.FODef.constMorV k V A₀) (homMor _ _ f) m (fun _ => rfl) (by simp) c).trans
    (GrpMor.pull_pull (homMor (dp0 k) (𝟙 _) f) (GlobalTheory.FODef.constMorV k V A₀) m (fun _ => rfl) rfl c).symm

theorem red_pull (A₀ : Over (Sp k)) [GrpObj A₀] (c : prim (dp0 k) (𝟙 _) A₀) :
    (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k V)) rfl A₀).pull
      ((GlobalTheory.FODef.constMorV k V A₀).pull c) = c := by
  rw [GrpMor.pull_pull _ _ (homMor (dp0 k) (𝟙 _) (𝟙 A₀)) (fun r => rfl) (by simp)]
  exact Subtype.ext (IsMor.pullCohomologyOne_id _ c.1)

theorem eq_of_surj {K C : Type} [Field K] [CommRing C] [Algebra K C] {M M' : Type*} [AddCommGroup M]
    [Module K M] [AddCommGroup M'] [Module C M'] (P : M →ₛₗ[algebraMap K C] M')
    (hP : Function.Surjective (liftSemi P)) (π : C →+* K)
    (Q : M' →ₛₗ[π] M) (e : M' →ₗ[C] C) (y : M →ₗ[K] K) (hQ : ∀ c, Q (P c) = c)
    (he : ∀ c, π (e (P c)) = y c) (c' : M') : y (Q c') = π (e c') := by
  obtain ⟨u, rfl⟩ := hP c'
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hu, hv]
  | tmul r c =>
    rw [liftSemi_tmul, LinearMap.map_smulₛₗ, hQ, map_smul, map_smul, smul_eq_mul, smul_eq_mul, map_mul, he]

theorem corr_of_fst (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀)
    (y : HdR A₀) (hc : ∀ c, (TrivSqZeroExt.fstHom k k V).toRingHom
      (e ((GlobalTheory.FODef.constMorV k V A₀).pull c)) = y c) :
    (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k V)) rfl A₀).Corr e y :=
  eq_of_surj _ (GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k V A₀ hA (GlobalTheory.FODef.sqZero k V)
    (GlobalTheory.FODef.constMorV k V A₀)).2 _ _ e y (red_pull A₀) hc

theorem eps_smul_eq {k : Type} [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀) (y : HdR A₀)
    (w e₃ : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀)
    (hw : ∀ c, w ((GlobalTheory.FODef.constMorV k k A₀).pull c) = (Algebra.linearMap k (TrivSqZeroExt k k) ∘ₗ y) c)
    (hy : ∀ c, e₃ ((GlobalTheory.FODef.constMorV k k A₀).pull c) = TrivSqZeroExt.inr (y c)) :
    (TrivSqZeroExt.inr 1 : TrivSqZeroExt k k) • w = e₃ := by
  refine coord_ext A₀ hA fun c => ?_
  have e1 : ((TrivSqZeroExt.inr 1 : TrivSqZeroExt k k) • w) ((GlobalTheory.FODef.constMorV k k A₀).pull c) =
      (TrivSqZeroExt.inr 1 : TrivSqZeroExt k k) * (w ((GlobalTheory.FODef.constMorV k k A₀).pull c)) := rfl
  rw [e1, hw c, hy c]
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_smul_eq_of_isCompl {C X : Type*} [CommRing C] [AddCommGroup X] [Module C X] {E M : Submodule C X}
    (hEM : IsCompl E M) (ε : C) {w e₃ : X} (h1 : ε • w = e₃) (he₃ : e₃ ∈ E) : ∃ a ∈ E, ε • a = e₃ := by
  have hw : w ∈ E ⊔ M := by rw [hEM.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨a, ha, m, hm, rfl⟩ := Submodule.mem_sup.1 hw
  have h4 : ε • m = e₃ - ε • a := by rw [← h1, smul_add]; abel
  have hmE : ε • m ∈ E := h4 ▸ E.sub_mem he₃ (E.smul_mem ε ha)
  have h2 : ε • m = 0 := (Submodule.disjoint_def.1 hEM.disjoint) _ hmE (M.smul_mem ε hm)
  exact ⟨a, ha, by rw [← h1, smul_add, h2, add_zero]⟩

theorem fil_of_eps (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    (E M : Submodule (TrivSqZeroExt k k)
      (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀))
    (hEM : IsCompl E M)
    (hred : ∀ y : HdR A₀, y ∈ Fil A₀ ↔
      ∃ e ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k k)) rfl A₀).Corr e y)
    {e₃ : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀}
    (he₃ : e₃ ∈ E) (y : HdR A₀)
    (hy : ∀ c, e₃ ((GlobalTheory.FODef.constMorV k k A₀).pull c) = TrivSqZeroExt.inr (y c)) : y ∈ Fil A₀ := by
  obtain ⟨w, hw⟩ := GlobalTheory.HTGlue.exists_coords k A₀ hA (Algebra.linearMap k (TrivSqZeroExt k k) ∘ₗ y)
  obtain ⟨a, ha, h1⟩ := exists_smul_eq_of_isCompl hEM _ (eps_smul_eq A₀ hA y w e₃ hw hy) he₃
  refine (hred y).2 ⟨a, ha, corr_of_fst A₀ hA a y fun c => ?_⟩
  have h3 := congrArg (fun u => (u ((GlobalTheory.FODef.constMorV k k A₀).pull c)).snd) h1
  have e1 : ((TrivSqZeroExt.inr 1 : TrivSqZeroExt k k) • a) ((GlobalTheory.FODef.constMorV k k A₀).pull c) =
      (TrivSqZeroExt.inr 1 : TrivSqZeroExt k k) * (a ((GlobalTheory.FODef.constMorV k k A₀).pull c)) := rfl
  simp only [e1, hy c] at h3
  simpa using h3

theorem glueFil_stable : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (tk : R →+* k) (s : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s), s = spMap tk → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), ∀ (E' : Fin d → Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A)), (∀ j, ∃ M : Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A), IsCompl (E' j) M) → (∀ j, ∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ e ∈ E' j, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k k)) rfl o₀.A).Corr e y) → (∀ j, ∀ x ∈ Fil o₀.A, ∃ e ∈ E' j, ∀ c, e ((GlobalTheory.FODef.constMorV k k o₀.A).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (f j x c)) → (∀ j (c : D.O), ∀ e ∈ E' j, (haveI := o₀.act.hom (c); push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (o₀.act.act (c)) (e)) ∈ E' j) → ∀ (c : D.O), ∀ e ∈ GlobalTheory.HTGlue.glueFil o₀.A f, (haveI := o₀.act.hom (c); push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) (o₀.act.act (c)) (e)) ∈ GlobalTheory.HTGlue.glueFil o₀.A f := by
  intro p _ D R _ b N k _ _ tk s o₀ _ d f E' hcompl hred hlift hstab c e he
  obtain ⟨x, hx, z, hz, hze⟩ := he
  haveI := o₀.act.hom c
  have key : ∀ j, ∀ x ∈ Fil o₀.A, push (dp0 k) (𝟙 _) (o₀.act.act c) (f j x) -
      f j (push (dp0 k) (𝟙 _) (o₀.act.act c) x) ∈ Fil o₀.A := by
    intro j x hx
    obtain ⟨M, hM⟩ := hcompl j
    obtain ⟨e1, he1, hc1⟩ := hlift j x hx
    obtain ⟨e2, he2, hc2⟩ := hlift j _ (push_mem_Fil (o₀.act.act c) hx)
    refine fil_of_eps o₀.A o₀.ab (E' j) M hM (hred j) (sub_mem (hstab j c e1 he1) he2) _ fun c' => ?_
    rw [LinearMap.sub_apply, push_coord, hc1, hc2]
    ext <;> simp [push_apply]
  refine ⟨_, push_mem_Fil (o₀.act.act c) hx, fun j => push (dp0 k) (𝟙 _) (o₀.act.act c) (f j x) -
      f j (push (dp0 k) (𝟙 _) (o₀.act.act c) x) + push (dp0 k) (𝟙 _) (o₀.act.act c) (z j),
    fun j => add_mem (key j x hx) (push_mem_Fil _ (hz j)), fun c' => ?_⟩
  rw [push_coord, hze]
  ext
  · simp [push_apply]
  · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, Pi.add_apply,
      LinearMap.add_apply, LinearMap.sub_apply, push_apply]
    ring

end GlobalTheory.HTGlueOStab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberGraphFiltrationExistsIsCompl
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTRealise

variable {k : Type} [Field k]

def coordSub (A₀ : Over (Sp k)) [GrpObj A₀] (S : Submodule k (HdR A₀)) :
    Submodule (DualNumber k) (Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀) where
  carrier := {d | ∃ u ∈ S, ∃ v ∈ S, ∀ c : primDR A₀,
    d ((constMor A₀).pull c) = TrivSqZeroExt.inl (u c) + TrivSqZeroExt.inr (v c)}
  add_mem' := by
    rintro d d' ⟨x, hx, y, hy, e⟩ ⟨x', hx', y', hy', e'⟩
    refine ⟨x + x', add_mem hx hx', y + y', add_mem hy hy', fun c => ?_⟩
    rw [LinearMap.add_apply, e, e']
    ext <;> simp <;> ring
  zero_mem' := ⟨0, zero_mem _, 0, zero_mem _, fun c => by
    rw [LinearMap.zero_apply]
    ext <;> simp⟩
  smul_mem' := by
    rintro r d ⟨x, hx, y, hy, e⟩
    refine ⟨r.fst • x, Submodule.smul_mem _ _ hx, r.fst • y + r.snd • x,
      add_mem (Submodule.smul_mem _ _ hy) (Submodule.smul_mem _ _ hx), fun c => ?_⟩
    rw [LinearMap.smul_apply, e, smul_eq_mul]
    ext <;> simp <;> ring

theorem coords_unique {A₀ : Over (Sp k)} [GrpObj A₀] {u v u' v' : HdR A₀}
    (h : ∀ c : primDR A₀, TrivSqZeroExt.inl (u c) + TrivSqZeroExt.inr (v c)
      = (TrivSqZeroExt.inl (u' c) + TrivSqZeroExt.inr (v' c) : DualNumber k)) : u = u' ∧ v = v' := by
  constructor
  · refine LinearMap.ext fun c => ?_
    have := congrArg TrivSqZeroExt.fst (h c)
    simpa using this
  · refine LinearMap.ext fun c => ?_
    have := congrArg TrivSqZeroExt.snd (h c)
    simpa using this

theorem graphFil_exists_isCompl : ∀ (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ →
    ∀ f : HdR A₀ →ₗ[k] HdR A₀, ∃ M : Submodule (DualNumber k) (Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀),
      IsCompl (GlobalTheory.HTRealise.graphFil A₀ f) M := by
  intro k _ A₀ _ hA f
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (Fil A₀)
  refine ⟨coordSub A₀ W, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro d ⟨x, hx, y, hy, e⟩ ⟨u, hu, v, hv, e'⟩
    obtain ⟨h1, h2⟩ := coords_unique (u := x) (v := f x + y) (u' := u) (v' := v)
      (fun c => by rw [LinearMap.add_apply]; exact (e c).symm.trans (e' c))
    subst h1
    have hx0 : x = 0 := (Submodule.disjoint_def.1 hW.disjoint) x hx hu
    subst hx0
    rw [map_zero, zero_add] at h2
    subst h2
    have hy0 : y = 0 := (Submodule.disjoint_def.1 hW.disjoint) y hy hv
    subst hy0
    refine crys_ext hA fun c => ?_
    rw [e' c]
    ext <;> simp <;> rfl
  · rw [codisjoint_iff, eq_top_iff]
    intro d _
    obtain ⟨u, v, hd⟩ := exists_coords d
    have htop : Fil A₀ ⊔ W = ⊤ := hW.sup_eq_top
    obtain ⟨x, hx, w, hw, hxw⟩ := Submodule.mem_sup.1 (htop ▸ Submodule.mem_top : u ∈ Fil A₀ ⊔ W)
    obtain ⟨y, hy, w', hw', hyw⟩ :=
      Submodule.mem_sup.1 (htop ▸ Submodule.mem_top : v - f x ∈ Fil A₀ ⊔ W)
    obtain ⟨d₁, h₁⟩ := exists_crys hA x (f x + y)
    obtain ⟨d₂, h₂⟩ := exists_crys hA w w'
    have hsum : d = d₁ + d₂ := by
      refine crys_ext hA fun c => ?_
      rw [LinearMap.add_apply, hd c, h₁ c, h₂ c, ← hxw]
      have hv : v = f x + (y + w') := by rw [hyw]; abel
      rw [hv]
      ext <;> simp <;> ring
    rw [hsum]
    exact Submodule.add_mem_sup ⟨x, hx, y, hy, h₁⟩ ⟨w, hw, w', hw', h₂⟩

end GlobalTheory.HTRealise
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberGraphFiltrationIsotropicOfSkew
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HTRealise

theorem pairing_eps_eq_zero {k : Type} [Field k] {M : Type*} [AddCommGroup M] [Module (DualNumber k) M]
    (χ : M →ₗ[DualNumber k] M →ₗ[DualNumber k] DualNumber k) {X Z X' Z' : M} {a b c e : k}
    (h₁ : χ X X' = algebraMap k (DualNumber k) a) (h₂ : χ X Z' = algebraMap k (DualNumber k) b)
    (h₃ : χ Z X' = algebraMap k (DualNumber k) c) (h₄ : χ Z Z' = algebraMap k (DualNumber k) e)
    (ha : a = 0) (hbc : b + c = 0) :
    χ (X + (DualNumber.eps : DualNumber k) • Z) (X' + (DualNumber.eps : DualNumber k) • Z') = 0 := by
  simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, h₁, h₂, h₃, h₄, smul_eq_mul]
  subst ha
  ext
  · simp [TrivSqZeroExt.algebraMap_eq_inl]
  · simp [TrivSqZeroExt.algebraMap_eq_inl]
    linear_combination hbc


set_option maxHeartbeats 1000000 in
theorem graphFil_isotropic : ∀ (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ →
    ∀ (P : LB (A₀ ⊗ A₀).left), P.IsLB → ∀ (φ : LinearMap.BilinForm k (HdR A₀)),
    GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) A₀ A₀ P φ → ∀ f : HdR A₀ →ₗ[k] HdR A₀,
    (∀ x ∈ Fil A₀, ∀ y ∈ Fil A₀, φ (f x) y + φ x (f y) = 0) →
    ∀ φ' : Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀ →ₗ[DualNumber k] Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀ →ₗ[DualNumber k] DualNumber k,
    GlobalTheory.AbDual.IsCorrForm (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀ A₀ P φ' →
    ∀ d ∈ GlobalTheory.HTRealise.graphFil A₀ f, ∀ d' ∈ GlobalTheory.HTRealise.graphFil A₀ f, φ' d d' = 0 := by
  intro k _ A₀ _ hA P hP φ hφ f hf φ' hφ' d hd d' hd'
  have := hA.smooth
  obtain ⟨g, hg⟩ := GlobalTheory.SerreDim.exists_dim_of_grpObj A₀
  have iso := GlobalTheory.PrincipalPolPairing.isotropic GlobalTheory.abelianDeRham hA hg hP hφ
  have C : GlobalTheory.AbDual.CupSquare (epsDP k) (GlobalTheory.DeRham.epsRed k) (A₀ ⊗ A₀) := by
    obtain ⟨C, _, φ, j, hφ, hic, -⟩ := exists_const (A₀ ⊗ A₀)
    have hAB := AbelianSchemeGerms.isAbelianScheme_tensor A₀ A₀ hA hA
    have hC : IsAbelianScheme C := by
      have := hAB.comm
      refine { comm := ?_, smooth := MorphismProperty.of_isPullback (P := @Smooth) hφ.1 hAB.smooth
               proper := MorphismProperty.of_isPullback (P := @IsProper) hφ.1 hAB.proper
               geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) hφ.1 hAB.geomConnected }
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (hφ.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← hφ.2 T x y (pushPt hφ.1.w x) (pushPt hφ.1.w y) rfl rfl,
        ← hφ.2 T y x (pushPt hφ.1.w y) (pushPt hφ.1.w x) rfl rfl, _root_.mul_comm]
    have gC := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hφ.1 (GlobalTheory.AbDual.smooth_prod hg hg)
    have su : Function.Surjective (TrivSqZeroExt.fstHom k k k).toRingHom := fun r => ⟨TrivSqZeroExt.inl r, rfl⟩
    exact GlobalTheory.Published.AbelianDualCrystal.cupSquare_crys GlobalTheory.abelianDeRham.1 GlobalTheory.abelianDualCrystal.2
      (isDPNilpotent_squareZero _) su rfl hC gC hic.1 (liftMor (epsDP k) hic)
  have e : LBIso (P.pull (𝟙 _)) P :=
    (CechPic.cls_eq_iff (pull_isLB hP _) hP).1 (by rw [CechPic.cls_pull hP, CechPic.pull_id])
  obtain ⟨χ, hχ, hk⟩ := hφ.pull hP (constMor A₀) (constMor A₀) (h := 𝟙 _) (by simp) (by simp) hP e
  obtain rfl := hχ.unique C hP hφ'
  have hm := isBC_constMor hA
  obtain ⟨x, hx, y, hy, ed⟩ := mem_graphFil.1 hd
  obtain ⟨x', hx', y', hy', ed'⟩ := mem_graphFil.1 hd'
  obtain ⟨X, hX⟩ := hm.exists x
  obtain ⟨Z, hZ⟩ := hm.exists (f x + y)
  obtain ⟨X', hX'⟩ := hm.exists x'
  obtain ⟨Z', hZ'⟩ := hm.exists (f x' + y')
  have dE : d = X + (DualNumber.eps : DualNumber k) • Z := crys_ext hA fun c => by
    rw [ed c, LinearMap.add_apply, LinearMap.smul_apply, hX c, hZ c]
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have dE' : d' = X' + (DualNumber.eps : DualNumber k) • Z' := crys_ext hA fun c => by
    rw [ed' c, LinearMap.add_apply, LinearMap.smul_apply, hX' c, hZ' c]
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have h₁ : φ x x' = 0 := iso x hx x' hx'
  have h₂ : φ x (f x' + y') + φ (f x + y) x' = 0 := by
    rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, iso x hx y' hy', iso y hy x' hx', add_zero, add_zero, add_comm]
    exact hf x hx x' hx'
  rw [dE, dE']
  exact pairing_eps_eq_zero χ (hk _ _ _ _ hX hX') (hk _ _ _ _ hX hZ') (hk _ _ _ _ hZ hX') (hk _ _ _ _ hZ hZ') h₁ h₂

end GlobalTheory.HTRealise
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianLiftAmpleBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.SqStep.exists_lift : ∀ (R R₀ : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R₀] [IsLocalRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (Y₀ : Over (Sp R₀)) [GrpObj Y₀], IsAbelianScheme Y₀ → ∀ L₀ : LB Y₀.left, L₀.IsLB → RelAmple Y₀ L₀ → KTriv Y₀ L₀ → ∃ (Y : Over (Sp R)) (_ : GrpObj Y) (L : LB Y.left) (i : Y₀.left ⟶ Y.left), IsAbelianScheme Y ∧ L.IsLB ∧ RelAmple Y L ∧ KTriv Y L ∧ IsGrpPullback Y₀ Y (spMap π) i ∧ LBIso L₀ (L.pull i) := by
  intro R R₀ _ _ _ _ _ π hπ hsq Y₀ _ hY₀ L₀ hL₀ hamp hK
  obtain ⟨Y, _, i, l, Q, hY, hpb, hsqr, hQ, a₁, a₂, hQi⟩ :=
    _root_.GlobalTheory.AltLift.exists_lift_lam R R₀ π hπ hsq Y₀ hY₀ L₀ hL₀ hamp hK
  obtain ⟨L, hL, hLi⟩ := _root_.GlobalTheory.Mum.exists_lift_of_lam_lift_sq R R₀ π hπ hsq Y₀ Y i l hY₀ hY hpb hsqr L₀ Q hL₀ hQ a₁ a₂ hQi
  haveI : Smooth Y.hom := hY.smooth
  have hamp' : RelAmple Y L :=
    GlobalTheory.AmpleThickening.relAmple_of_sq_zero R R₀ π hπ hsq Y Y₀ i hpb.1 inferInstance L L₀ hL hL₀ hLi hamp
  exact ⟨Y, inferInstance, L, i, hY, hL, hamp',
    _root_.GlobalTheory.KTrivSqZero.kTriv_lift R R₀ π hπ hsq Y₀ Y i hY hpb L₀ L hL₀ hL hamp' hLi hK, hpb, hLi⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBirigidifiedKthRootPullbackBundleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

open scoped CategoryTheory.Obj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_birigidified_kth_root_pullback_bundle : ∀ (Y : Scheme.{0}) (A D : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj D] (Q : LB (A ⊗ D).left) (h : A ⟶ D) (k : ℕ) (X : Scheme.{0}) (M : LB X) (c : (A ⊗ A).left ⟶ X), IsAbelianScheme A → IsAbelianScheme D → GlobalTheory.AbDual.IsDual A D Q → GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap Q) → IsMonHom h → 0 < k → IsUnit (k : Γ(Y, ⊤)) → M.IsLB → LBIso (M.pull c) (Q.pull (lift (fst A A) (snd A A ≫ h)).left) → ∀ (U : Scheme.{0}) (t : U ⟶ Y) (AU : Over U) [GrpObj AU] [IsCommMonObj AU] (φ : AU.left ⟶ A.left) (φ₂ : (G2 AU).left ⟶ (G2 A).left), IsGrpPullback AU A t φ → IsSquare φ φ₂ → (∀ (T : Over Y) (s : T.left ⟶ U), s ≫ t = T.hom → ∀ a : T ⟶ A, a ^ k = 1 → a ≫ h = 1) → ∃ P : LB (G2 AU).left, P.IsLB ∧ (∃ t : (P.pull (lift (1 : AU ⟶ AU) (𝟙 AU)).left).Gen, t.IsGen) ∧ (∃ t : (P.pull (lift (𝟙 AU) (1 : AU ⟶ AU)).left).Gen, t.IsGen) ∧ LBIso (M.pull (φ₂ ≫ c)) (lbPow P k) := by
  first | (exact @GlobalTheory.KthRoot.exists_birigid_kth_root) | (exact GlobalTheory.KthRoot.exists_birigid_kth_root) | (intros; apply GlobalTheory.KthRoot.exists_birigid_kth_root <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCrysForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open IsLocalRing GlobalTheory.AbDual GlobalTheory.Published.GrothendieckMessing

namespace GlobalTheory.HTDefLift

theorem exists_crysForm : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∃ φ₀ : Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C, GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P φ₀ ∧ (∀ φ, GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P φ → φ = φ₀) ∧ (∀ (c : D.O) x y, φ₀ (GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) o₀.act c x) y = φ₀ x (GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) o₀.act (D.star c).unop y)) ∧ ∃ φ' : HdR o₀.A →ₗ[C₀] HdR o₀.A →ₗ[C₀] C₀, GlobalTheory.AbDual.IsCorrForm (dp0 C₀) (𝟙 _) o₀.A o₀.A o₀.P φ' ∧ ∀ x x' y y', (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl o₀.A).Corr x x' → (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl o₀.A).Corr y y' → φ' x' y' = π (φ₀ x y) := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR o₀
  have hI2 : RingHom.ker π ^ 2 = ⊥ := hsq
  haveI : Nontrivial C₀ := by
    refine ⟨⟨0, 1, fun h ↦ ?_⟩⟩
    have h1 : (1 : C) ∈ RingHom.ker π := by rw [RingHom.mem_ker, map_one]; exact h.symm
    have h2 : (1 : C) ∈ RingHom.ker π ^ 2 := by
      rw [pow_two]; simpa using Ideal.mul_mem_mul h1 h1
    rw [hI2] at h2
    exact one_ne_zero ((Submodule.mem_bot C).1 h2)
  haveI : IsLocalRing C₀ := IsLocalRing.of_surjective' π hπ
  let κ := GlobalTheory.Cris.divided₂ hsq
  have hκ : GlobalTheory.Cris.IsNilDP κ := GlobalTheory.Cris.isDPNilpotent_squareZero hsq
  have ADR : GlobalTheory.Published.AbelianDeRham := GlobalTheory.abelianDeRham
  have ADC : GlobalTheory.Published.AbelianDualCrystal := GlobalTheory.abelianDualCrystal
  obtain ⟨A', _, i', h', hA'⟩ := GlobalTheory.UnobTop.abelianUnobstructed C (RingHom.ker π) hsq C₀ π hπ rfl o₀.A o₀.ab
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim C A' hA'
  have CS := GlobalTheory.Published.AbelianDualCrystal.cupSquare_crys_prod ADR.1 ADC.2 hκ hπ rfl hA' hg hA' hg h' h'
  obtain ⟨φ₀, hφ₀⟩ := exists_isCorrForm CS o₀.isLB o₀.rig₁ o₀.rig₂
  refine ⟨φ₀, hφ₀, fun φ hφ ↦ hφ.unique CS o₀.isLB hφ₀, fun c x y ↦ ?_, ?_⟩
  · haveI := o₀.act.hom c
    haveI := o₀.act.hom (D.star c).unop
    have := hφ₀.adjoint CS o₀.isLB o₀.isLB hφ₀ (o₀.act.act c) (o₀.act.act (D.star c).unop) (LBIso.symm (o₀.rosati c)) x y
    exact this.symm
  · have iso : LBIso (o₀.P.pull (Over.Hom.left (𝟙 (o₀.A ⊗ o₀.A)))) o₀.P :=
      (GlobalTheory.CechPic.cls_eq_iff (pull_isLB o₀.isLB _) o₀.isLB).1
        (by rw [GlobalTheory.CechPic.cls_pull o₀.isLB, Over.id_left, GlobalTheory.CechPic.pull_id])
    obtain ⟨φ', hφ', e'⟩ := hφ₀.pull o₀.isLB (crysRedMor κ rfl o₀.A) (crysRedMor κ rfl o₀.A)
      (h := Over.Hom.left (𝟙 (o₀.A ⊗ o₀.A))) (by simp) (by simp) o₀.isLB iso
    exact ⟨φ', hφ', e'⟩

end GlobalTheory.HTDefLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualMapEq
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.Et
open scoped TensorProduct DirectSum
open ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

namespace GlobalTheory.TateHondaBridge

open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.AV GlobalTheory.AV.AbVar ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Published.AbVarRed

def toAbVar {k : Type} [Field k] (A : Over (Spec (CommRingCat.of k))) [GrpObj A] (hA : IsAbelianScheme A) :
    AbVar k where
  X := A
  ab := hA
  dim := (GlobalTheory.T.abelianScheme_specField_smoothOfRelativeDimension k A hA).choose
  smooth := (GlobalTheory.T.abelianScheme_specField_smoothOfRelativeDimension k A hA).choose_spec

end GlobalTheory.TateHondaBridge

end
end

