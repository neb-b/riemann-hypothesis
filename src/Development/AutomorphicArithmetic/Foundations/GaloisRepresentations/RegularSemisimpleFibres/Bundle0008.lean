module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
public import Mathlib
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0005
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0017
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0002
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0015
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.FinrankK
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TameRecAll
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0056
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
public import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.ConjTorusSubApply
public import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.Bundle0002
public import Development.DiscreteGroups.GlobalIrreducibility.DzKSchur
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroSupercuspidalCuspidalModule
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0858
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1050
public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.GreenCuspLabels.GreenCuspidal

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PTameRead
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.InertialTypesAlt.TameReduction

section Res

variable {Ω : Type} [Field Ω]

private noncomputable def toRes (A : ValuationSubring Ω) (F : Type) [Field F] [NumberField F] [Algebra F Ω] :
    𝓞 F →+* IsLocalRing.ResidueField A :=
  (IsLocalRing.residue A).comp
    { toFun := fun x => ⟨algebraMap F Ω (x : F), ReciprocityTheory.Gal.mem_of_isIntegral_int A (x.2.map (algebraMap F Ω).toIntAlgHom)⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }

private theorem toRes_eq_zero_iff (A : ValuationSubring Ω) {F : Type} [Field F] [NumberField F] [Algebra F Ω] (x : 𝓞 F) :
    toRes A F x = 0 ↔ A.valuation (algebraMap F Ω (x : F)) < 1 := by
  unfold toRes
  rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
  exact A.valuation_lt_one_iff _

private theorem exists_emb {A : ValuationSubring Ω} {F : Type} [Field F] [NumberField F] [Algebra F Ω]
    {v : HeightOneSpectrum (𝓞 F)} (hv : IsPlaceOver A v) {K : Type} [Field K] (red : 𝓞 F →+* K)
    (hs : Function.Surjective red) (hk : RingHom.ker red = v.asIdeal) :
    ∃ ι : K →+* IsLocalRing.ResidueField A, ∀ x, ι (red x) = toRes A F x := by
  refine ⟨RingHom.liftOfSurjective red hs ⟨toRes A F, fun x hx => ?_⟩, fun x => ?_⟩
  · rw [hk] at hx
    rw [RingHom.mem_ker, toRes_eq_zero_iff]
    exact (hv x).2 hx
  · exact RingHom.liftOfRightInverse_comp_apply _ _ _ _ _

private theorem residue_eq_toRes {A : ValuationSubring Ω} {F : Type} [Field F] [NumberField F] [Algebra F Ω]
    (z : A) (x : 𝓞 F) (h : A.valuation ((z : Ω) - algebraMap F Ω (x : F)) < 1) :
    IsLocalRing.residue A z = toRes A F x := by
  unfold toRes
  rw [RingHom.comp_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact (A.valuation_lt_one_iff _).2 h

end Res

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem res_read {g n : ℕ} [Fact g.Prime] (hn : 0 < n) (D : UpperTheory.Zero.LLC.Ext h g n) (R : Ine (F := E) A →* D.Kˣ) (hR : D.Res R)
    (t : Ine (F := E) A) : ∃ (t' : Ine (F := D.E') A) (x : 𝓞 D.E'),
      (∀ z : Ω, (t : G E Ω) z = (t' : G D.E' Ω) z) ∧
      Valued.v ((D.a' (ineIncl D.h' t') : D.w'.adicCompletion D.E') - algebraMap D.E' (D.w'.adicCompletion D.E') (x : D.E')) < 1 ∧
      ((R t : D.Kˣ) : D.K) = D.red x := by
  obtain ⟨t', ht', e⟩ := DiscreteGroups.sglob.DzType.ine_lift g A w h D.w' D.h' n hn D.unr D.card (t : G E Ω) t.2
  obtain ⟨x, hx⟩ := DiscreteGroups.sglob.DzType.exists_int_approx_compl D.w' _ (DiscreteGroups.sglob.DzType.val_artin_ine D.ha' ⟨t', ht'⟩).le
  have hne := DiscreteGroups.sglob.DzType.red_ne_zero_of_approx D.ha' D.ker hx
  refine ⟨⟨t', ht'⟩, x, fun z => by rw [← e]; rfl, hx, ?_⟩
  have := hR t ⟨t', ht'⟩ x (Units.mk0 _ hne) e.symm rfl hx
  rw [this]; rfl

end UpperTheory.Gal.InertialTypesAlt.TameReduction

open UpperTheory.Gal.InertialTypesAlt.TameReduction in
theorem UpperTheory.Gal.InertialTypesAlt.tameRead :
    TameRead := by
  intro E Ω _ _ _ _ _ A v h g _ m hm D R hR
  obtain ⟨ι, hι⟩ := exists_emb D.h' D.red D.surj D.ker
  refine ⟨ι, fun t ϖ hϖ z hz => ?_⟩
  obtain ⟨t', x, ht, hx, hr⟩ := res_read hm D R hR t
  have hg := DiscreteGroups.sglob.DzType.natCast_mem_of_normV D.w' g m hm D.card
  have h1 := UpperTheory.Zero.LLC.tameRecAll D.E' Ω g A D.w' D.h' hg D.unr D.a' D.ha' ϖ (by rw [D.card]; exact hϖ) t' x hx
  rw [hr, hι]
  refine (residue_eq_toRes z x ?_).symm
  rw [hz, ht]
  exact h1
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PTensFix
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.Parabolic (mem_fixed)

namespace UpperTheory.Gal.InertialTypesAlt.TensorFixedVectors

section Rep

variable {Γ X : Type} [Group Γ] [AddCommGroup X] [Module ℂ X]

private theorem idem_comm [TopologicalSpace Γ] [IsTopologicalGroup Γ] {π : Representation ℂ Γ X}
    (hπ : GlobalTheory.PRep.IsSmooth π) {H : Subgroup Γ} (hH : IsCompact (H : Set Γ)) {g : Γ}
    (hg : g ∈ Subgroup.normalizer (H : Set Γ)) (v : X) :
    idem hπ hH (π g v) = π g (idem hπ hH v) := by
  have h1 : v - idem hπ hH v ∈ twKer π H 1 := by
    rw [← idem_eq_zero_iff hπ hH, map_sub, idem_of_mem hπ hH (idem_mem hπ hH v), sub_self]
  have h3 := (idem_eq_zero_iff hπ hH).2 (twKer_le_comap π H g hg h1)
  rw [map_sub, map_sub, sub_eq_zero] at h3
  rw [h3]
  refine idem_of_mem hπ hH (mem_fixed.2 fun u hu => ?_)
  have hu' : g⁻¹ * u * g ∈ H := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) u).1 hu
    simpa using this
  have h4 : π u (π g (idem hπ hH v)) = π g (π (g⁻¹ * u * g) (idem hπ hH v)) := by
    have e1 : u * g = g * (g⁻¹ * u * g) := by group
    rw [← mul_apply_eq_comp (π u), ← map_mul, e1, map_mul, mul_apply_eq_comp]
  rw [h4, mem_fixed.1 (idem_mem hπ hH v) _ hu']

end Rep

section Tensor

variable {s : ℕ} {G V : Fin s → Type} [∀ a, Group (G a)] [∀ a, AddCommGroup (V a)] [∀ a, Module ℂ (V a)]

private noncomputable def intersection_update_fsHerm_neg_one (σ : ∀ a, Representation ℂ (G a) (V a)) (a : Fin s) :
    Representation ℂ (G a) (PiTensorProduct ℂ V) :=
  (piTensor σ).comp (MonoidHom.mulSingle G a)

private theorem position_tprod (σ : ∀ a, Representation ℂ (G a) (V a)) (a : Fin s) (g : G a) (f : ∀ b, V b) :
    intersection_update_fsHerm_neg_one σ a g (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f a (σ a g (f a))) := by
  show piTensor σ (Pi.mulSingle a g) _ = _
  rw [piTensor_tprod]
  congr 1
  funext b
  by_cases h : b = a
  · subst h; simp
  · simp [h, Pi.mulSingle_eq_of_ne h]

private theorem position_smooth [∀ a, TopologicalSpace (G a)] [∀ a, IsTopologicalGroup (G a)] (σ : ∀ a, Representation ℂ (G a) (V a))
    (hσ : ∀ a, GlobalTheory.PRep.IsSmooth (σ a)) (a : Fin s) : GlobalTheory.PRep.IsSmooth (intersection_update_fsHerm_neg_one σ a) :=
  _root_.UpperTheory.Reformulated.B.SmoothTensorFactor.position_smooth σ hσ a

private noncomputable def oneMap (a : Fin s) (e : V a →ₗ[ℂ] V a) : PiTensorProduct ℂ V →ₗ[ℂ] PiTensorProduct ℂ V :=
  PiTensorProduct.map (Function.update (fun b => (LinearMap.id : V b →ₗ[ℂ] V b)) a e)

private theorem oneMap_tprod (a : Fin s) (e : V a →ₗ[ℂ] V a) (f : ∀ b, V b) :
    oneMap a e (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f a (e (f a))) := by
  rw [oneMap, PiTensorProduct.map_tprod]
  congr 1
  funext b
  by_cases h : b = a
  · subst h; simp
  · simp [h]

private theorem oneMap_fix [∀ a, TopologicalSpace (G a)] [∀ a, IsTopologicalGroup (G a)]
    (σ : ∀ a, Representation ℂ (G a) (V a)) (hσ : ∀ a, GlobalTheory.PRep.IsSmooth (σ a)) (a : Fin s)
    {H : Subgroup (G a)} (hH : IsCompact (H : Set (G a))) (e : V a →ₗ[ℂ] V a)
    (he : ∀ v, e v ∈ fixed (σ a) H) (hk : ∀ v, v - e v ∈ twKer (σ a) H 1)
    {w : PiTensorProduct ℂ V} (hw : w ∈ fixed (intersection_update_fsHerm_neg_one σ a) H) : oneMap a e w = w := by
  have h1 : ∀ x, oneMap a e x ∈ fixed (intersection_update_fsHerm_neg_one σ a) H := fun x => by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r f =>
      refine Submodule.smul_mem _ _ ?_ |> fun h => by rw [map_smul]; exact h
      rw [oneMap_tprod]
      refine mem_fixed.2 fun u hu => ?_
      rw [position_tprod, Function.update_self, mem_fixed.1 (he (f a)) u hu, Function.update_idem]
    | add x y hx hy => rw [map_add (f := _)]; exact add_mem hx hy
  have h2 : ∀ f : ∀ b, V b, (twKer (σ a) H 1).map
      ((PiTensorProduct.tprod ℂ).toLinearMap f a) ≤ twKer (intersection_update_fsHerm_neg_one σ a) H 1 := fun f => by
    rw [Submodule.map_le_iff_le_comap]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨n, v, rfl⟩
    refine Submodule.subset_span ⟨n, PiTensorProduct.tprod ℂ (Function.update f a v), ?_⟩
    simp [MultilinearMap.toLinearMap, position_tprod]
  have h3 : ∀ x, x - oneMap a e x ∈ twKer (intersection_update_fsHerm_neg_one σ a) H 1 := fun x => by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r f =>
      rw [map_smul, ← smul_sub]
      refine Submodule.smul_mem _ _ (h2 f ⟨_, hk (f a), ?_⟩)
      rw [oneMap_tprod, map_sub]
      simp [MultilinearMap.toLinearMap]
    | add x y hx hy =>
      rw [map_add (f := _), add_sub_add_comm]; exact add_mem hx hy
  have h4 := Submodule.disjoint_def.1 (isCompl_fixed_twKer (position_smooth σ hσ a) hH).disjoint
    (w - oneMap a e w) (sub_mem hw (h1 w)) (h3 w)
  exact (sub_eq_zero.1 h4).symm

private theorem map_fix (e : ∀ a, V a →ₗ[ℂ] V a) (w : PiTensorProduct ℂ V)
    (h : ∀ a, oneMap a (e a) w = w) : PiTensorProduct.map e w = w := by
  have key : ∀ S : Finset (Fin s),
      PiTensorProduct.map (fun b => if b ∈ S then e b else (LinearMap.id : V b →ₗ[ℂ] V b)) w = w := fun S => by
    induction S using Finset.induction_on with
    | empty => simp [PiTensorProduct.map_id]
    | insert a S ha ih =>
      have e1 : (fun b => if b ∈ insert a S then e b else (LinearMap.id : V b →ₗ[ℂ] V b)) =
          fun b => (if b ∈ S then e b else (LinearMap.id : V b →ₗ[ℂ] V b)) ∘ₗ
            Function.update (fun b => (LinearMap.id : V b →ₗ[ℂ] V b)) a (e a) b := by
        funext b
        by_cases hb : b = a
        · subst hb; simp [ha]
        · simp [hb]
      rw [e1, PiTensorProduct.map_comp, LinearMap.comp_apply]
      have := h a
      rw [oneMap] at this
      rw [this, ih]
  simpa using key Finset.univ

end Tensor

end UpperTheory.Gal.InertialTypesAlt.TensorFixedVectors

open UpperTheory.Gal.InertialTypesAlt.TensorFixedVectors in
theorem UpperTheory.Gal.InertialTypesAlt.tensFix :
    TensFix := by
  intro k _ _ _ _ s d V _ _ σ hσ
  have hK : ∀ a, IsCompact (KOne k (Fin (d a)) : Set (GL (Fin (d a)) k)) := fun a =>
    levelPre_bot (k := k) (n := Fin (d a)) ▸ isCompact_levelPre ⊥
  let e : ∀ a, V a →ₗ[ℂ] V a := fun a => idem (hσ a) (hK a)
  let pr : ∀ a, V a →ₗ[ℂ] fixed (σ a) (KOne k (Fin (d a))) := fun a =>
    (e a).codRestrict _ (idem_mem (hσ a) (hK a))
  refine ⟨PiTensorProduct.map pr, fun x w => ?_, fun w hw h0 => ?_⟩
  · induction w using PiTensorProduct.induction_on with
    | smul_tprod r f =>
      simp only [map_smul, piTensor_tprod, PiTensorProduct.map_tprod]
      congr 2
      funext a
      refine Subtype.ext ?_
      rw [redLevi_apply, levelZero_apply]
      exact idem_comm (hσ a) (hK a) (KO_le_normalizer (x.2 a trivial)) (f a)
    | add x' y hx hy => simp only [map_add (f := _), hx, hy]
  · have hk : ∀ a v, v - e a v ∈ twKer (σ a) (KOne k (Fin (d a))) 1 := fun a v => by
      rw [← idem_eq_zero_iff (hσ a) (hK a), map_sub, idem_of_mem (hσ a) (hK a) (idem_mem (hσ a) (hK a) v), sub_self]
    have h1 : ∀ a, oneMap a (e a) w = w := fun a =>
      oneMap_fix σ hσ a (hK a) (e a) (idem_mem (hσ a) (hK a)) (hk a) (mem_fixed.2 fun u hu =>
        mem_fixed.1 hw (Pi.mulSingle a u) fun b _ => by
          by_cases h : b = a
          · subst h; simpa using hu
          · simpa [Pi.mulSingle_eq_of_ne h] using one_mem _)
    have h2 := map_fix e w h1
    have h3 : PiTensorProduct.map e =
        PiTensorProduct.map (fun a => (fixed (σ a) (KOne k (Fin (d a)))).subtype) ∘ₗ PiTensorProduct.map pr := by
      rw [← PiTensorProduct.map_comp]
      rfl
    rw [← h2, h3, LinearMap.comp_apply, h0, map_zero]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PTypeChar
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace UpperTheory.Gal.InertialTypesAlt.TypeCharacters

open Matrix GlobalTheory.GLq GlobalTheory.SerSys GlobalTheory.IwahoriInj GlobalTheory.DepthZeroJac

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)

include hi

private def resE : 𝓀[w.adicCompletion E] ≃+* ZMod g :=
  RingEquiv.ofBijective (DiscreteGroups.sglob.DzTw.resMap i hi) ⟨RingHom.injective _, fun a => by
    obtain ⟨y, rfl⟩ := DiscreteGroups.sglob.DzIso.redO_surjective i hi a
    exact ⟨IsLocalRing.residue _ y, rfl⟩⟩

private theorem resE_redK {n : ℕ} (x : KO (w.adicCompletion E) (Fin n)) (κ : GL (Fin n) ℤ_[g])
    (hκ : GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n κ) = x) :
    GeneralLinearGroup.map (resE i hi).toRingHom (redK (w.adicCompletion E) (Fin n) x) = GlobalTheory.GLp.red g n κ := by
  ext a b
  have hx : ((x : GL (Fin n) (w.adicCompletion E)) : Matrix _ _ _) a b = i (κ a b : ℚ_[g]) := by
    rw [← hκ]; rfl
  simp only [GeneralLinearGroup.map_apply, RingHom.mapMatrix_apply, Matrix.map_apply, redK_apply]
  have key : ∀ y : 𝒪[w.adicCompletion E], (y : w.adicCompletion E) = i (κ a b : ℚ_[g]) →
      (resE i hi).toRingHom (IsLocalRing.residue _ y) = PadicInt.toZMod (κ a b) := by
    intro y hy
    show PadicInt.toZMod (DiscreteGroups.sglob.DzIso.toInt i hi y) = _
    congr 1
    apply Subtype.ext
    rw [DiscreteGroups.sglob.DzIso.coe_toInt, hy, RingEquiv.symm_apply_apply]
  exact key _ hx

private theorem finCusp_comp {n : ℕ} (τ : FDRep ℂ (Gn g n)) (hτ : IsCusp τ.character) :
    PositivityTheory.Rg.DzCount.FinCusp (τ.ρ.comp (GeneralLinearGroup.map (n := Fin n) (resE i hi).toRingHom)) := by
  intro s d e hne v hv
  have hF : PositivityTheory.Rg.DzCount.FinCusp τ.ρ :=
    PositivityTheory.Rg.DzCount.finite_cuspidal_of_isCuspidal τ (PositivityTheory.GreenCharacters.isCuspidal_of_isCusp τ hτ)
  refine hF s d e (GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff.mpr (GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff.mp hne)) v ?_
  intro u hu
  have hback : GeneralLinearGroup.map (resE i hi).toRingHom
      (GeneralLinearGroup.map (resE i hi).symm.toRingHom u) = u := by
    ext a b
    simp
  rw [← hback]
  apply hv
  rw [GlobalTheory.SmGL.CuspMax.mem_unipRad_iff_entries] at hu ⊢
  intro a b hab
  have h1 := hu a b hab
  simp only [GeneralLinearGroup.map_apply, RingHom.mapMatrix_apply, Matrix.map_apply, h1]
  by_cases hab' : a = b
  · subst hab'; simp
  · simp [Matrix.one_apply_ne hab']

private theorem fixed_eq_range {n : ℕ} (τ : FDRep ℂ (Gn g n)) (hτ : IsCusp τ.character)
    (σ : IrrRep (GL (Fin n) (w.adicCompletion E))) (ω : (w.adicCompletion E)ˣ →* ℂˣ) (hω : HasCentralChar σ.ρ ω)
    (φ : τ →ₗ[ℂ] σ.V) (h0 : φ ≠ 0)
    (hφ : ∀ (k : GL (Fin n) ℤ_[g]) (u : τ), φ (τ.ρ (GlobalTheory.GLp.red g n k) u) =
      σ.ρ (GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n k)) (φ u)) :
    Function.Injective φ ∧ fixed σ.ρ (KOne (w.adicCompletion E) (Fin n)) = LinearMap.range φ := by
  haveI hirr : Representation.IsIrreducible τ.ρ :=
    GlobalTheory.SerOSys.ZSum.isIrreducible_of_simple τ (DiscreteGroups.sglob.DzType.Kon.simple_of_isIrr τ hτ.2.1)
  let U : Subrepresentation τ.ρ := ⟨LinearMap.ker φ, fun x v hv => by
    obtain ⟨k, rfl⟩ := GlobalTheory.GLp.Model.red_surjective n x
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hφ, hv, map_zero]⟩
  have hinj : Function.Injective φ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top U with h | h
    · have hk : LinearMap.ker φ = ⊥ := congrArg Subrepresentation.toSubmodule h
      exact LinearMap.ker_eq_bot.1 hk
    · exfalso
      have hk : LinearMap.ker φ = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact h0 (LinearMap.ker_eq_top.1 hk)
  obtain ⟨u0, hu0⟩ : ∃ u, φ u ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact h0 (LinearMap.ext hcon)
  haveI : Nontrivial τ := ⟨⟨u0, 0, fun e => hu0 (by rw [e, map_zero])⟩⟩
  have hT : PositivityTheory.Rg.DzCount.IsTypeMap (τ.ρ.comp (GeneralLinearGroup.map (n := Fin n) (resE i hi).toRingHom)) σ.ρ φ :=
    ⟨hinj, fun x v => by
      obtain ⟨κ, hκ⟩ := DiscreteGroups.sglob.DzIso.exists_of_mem_KO i hi x.2
      rw [MonoidHom.comp_apply, resE_redK i hi x κ hκ, hφ, hκ]⟩
  exact ⟨hinj, PositivityTheory.Rg.DzCount.B.st6 (w.adicCompletion E) τ n _ (finCusp_comp i hi τ hτ) σ ω hω φ hT⟩

omit hi in
private theorem ringEquiv_eq {F : Type} [Field F] (r r' : F ≃+* ZMod g) : r = r' := by
  have h : (r.symm : ZMod g →+* F) = (r'.symm : ZMod g →+* F) := Subsingleton.elim _ _
  have hs : r.symm = r'.symm := RingEquiv.ext fun y => RingHom.congr_fun h y
  rw [← RingEquiv.symm_symm r, ← RingEquiv.symm_symm r', hs]

omit hi in
private theorem central (y : IrrGL (k := w.adicCompletion E)) : ∃ ω : (w.adicCompletion E)ˣ →* ℂˣ, HasCentralChar y.rep ω :=
  (GlobalTheory.T.centralCharacter_subquotient_productIrreducibles (w.adicCompletion E)).1 y

private theorem trace_eq {n : ℕ} (τ : FDRep ℂ (Gn g n)) (hτ : IsCusp τ.character)
    (σ : IrrRep (GL (Fin n) (w.adicCompletion E))) (ω : (w.adicCompletion E)ˣ →* ℂˣ) (hω : HasCentralChar σ.ρ ω)
    (φ : τ →ₗ[ℂ] σ.V) (h0 : φ ≠ 0)
    (hφ : ∀ (k : GL (Fin n) ℤ_[g]) (u : τ), φ (τ.ρ (GlobalTheory.GLp.red g n k) u) =
      σ.ρ (GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n k)) (φ u))
    (γ : GL (Fin n) 𝓀[w.adicCompletion E]) :
    τ.character (GeneralLinearGroup.map (resE i hi).toRingHom γ) = LinearMap.trace ℂ _ (levelZero σ.ρ γ) := by
  obtain ⟨hinj, hfix⟩ := fixed_eq_range i hi τ hτ σ ω hω φ h0 hφ
  obtain ⟨x, rfl⟩ := GlobalTheory.LocGL.redK_surjective γ
  obtain ⟨κ, hκ⟩ := DiscreteGroups.sglob.DzIso.exists_of_mem_KO i hi x.2
  rw [resE_redK i hi x κ hκ]
  let e : τ ≃ₗ[ℂ] fixed σ.ρ (KOne (w.adicCompletion E) (Fin n)) :=
    (LinearEquiv.ofInjective φ hinj).trans (LinearEquiv.ofEq _ _ hfix.symm)
  have he : ∀ u : τ, ((e u : fixed σ.ρ (KOne (w.adicCompletion E) (Fin n))) : σ.V) = φ u := fun u => rfl
  have hc : e.conj (τ.ρ (GlobalTheory.GLp.red g n κ)) = levelZero σ.ρ (redK (w.adicCompletion E) (Fin n) x) := by
    ext v
    rw [LinearEquiv.conj_apply]
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    rw [he, hφ, hκ, levelZero_apply]
    congr 1
    have := he (e.symm v)
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  show LinearMap.trace ℂ τ (τ.ρ (GlobalTheory.GLp.red g n κ)) = _
  rw [← hc, LinearMap.trace_conj']

end UpperTheory.Gal.InertialTypesAlt.TypeCharacters

open UpperTheory.Gal.InertialTypesAlt.TypeCharacters Matrix in
theorem UpperTheory.Gal.InertialTypesAlt.typeChar :
    TypeChar := by
  intro E _ _ v g _ i hi r y τ hτ hinf γ
  obtain ⟨φ, h0, hφ⟩ := hinf
  obtain ⟨ω, hω⟩ := central y
  have hr : r = resE i hi := ringEquiv_eq _ _
  rw [hr]
  exact trace_eq i hi τ hτ y.2.rep ω hω φ h0 hφ γ
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PUnifTower
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.unifTower :
    LiftsFix → PlaceEx → UnrOfIne → UnifTower := by
  intro hF hP hU E Ω _ _ _ n X Y hXY
  induction hXY using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro A _ v w hv hw g hg
    have hvw : v = w := by
      apply HeightOneSpectrum.ext
      ext x
      rw [← hv x, hw x]
    rw [← hvw]
    exact hg
  | @head X Z hs hZY ih =>
    intro A hI v w hv hw g hg
    obtain ⟨_, _, _, _, _⟩ := hs
    obtain ⟨u, hu, -⟩ := hP X.K Z.K Ω A v hv n Z.π
    have hfix : ∀ t ∈ Ine (F := X.K) A, UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes Z.K t := by
      intro t ht z
      obtain ⟨y, hy⟩ := hF E Ω n Z Y hZY z
      have := hI t ht y
      rwa [hy] at this
    have hgu : ((g : ℕ) : 𝓞 Z.K) ∉ u.asIdeal ^ 2 := by
      have h3 := (hU X.K Z.K Ω A v u hv hu hfix).2.2 (g : 𝓞 X.K) hg
      rwa [map_natCast] at h3
    refine ih A (fun t ht => ?_) u w hu hw g hgu
    exact hI (AlgEquiv.restrictScalars X.K t) ht
end

