module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1787
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0471
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0194
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0264
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaPointShapePrimitivityNearGeneric
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2037
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2117

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameAt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc

def SameAt {R₁ R₂ B M Γ : Type} [CommRing R₁] [CommRing R₂] [CommRing B] (P₁ : PolAV (Sp R₁)) (P₂ : PolAV (Sp R₂))
    (f₁ : R₁ →+* B) (f₂ : R₂ →+* B) (e₁ : M → (P₁.A ⟶ P₁.A)) (e₂ : M → (P₂.A ⟶ P₂.A))
    (t₁ : Γ → (baseOver (Sp R₁) ⟶ P₁.A)) (t₂ : Γ → (baseOver (Sp R₂) ⟶ P₂.A)) : Prop :=
  ∃ (P : PolAV (Sp B)) (a₁ : P.A.left ⟶ P₁.A.left) (a₂ : P.A.left ⟶ P₂.A.left),
    IsGrpPullback P.A P₁.A (spMap f₁) a₁ ∧ IsGrpPullback P.A P₂.A (spMap f₂) a₂ ∧
    LBIso P.L (P₁.L.pull a₁) ∧ LBIso P.L (P₂.L.pull a₂) ∧
    (∀ E, ∃ e : P.A ⟶ P.A, e.left ≫ a₁ = a₁ ≫ (e₁ E).left ∧ e.left ≫ a₂ = a₂ ≫ (e₂ E).left) ∧
    ∀ x, ∃ w : Sp B ⟶ P.A.left, w ≫ a₁ = spMap f₁ ≫ (t₁ x).left ∧ w ≫ a₂ = spMap f₂ ≫ (t₂ x).left

end GlobalTheory.Poinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameGenericFibreChainRescaledDeeperRealisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.SameChain

theorem spec_endo_eq_id {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω)
    (frac : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) (g : Sp Ω ⟶ Sp Ω)
    (h : g ≫ spMap R.val.toRingHom = spMap R.val.toRingHom) : g = 𝟙 _ := by
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective g
  have h2 : CommRingCat.ofHom R.val.toRingHom ≫ ψ = CommRingCat.ofHom R.val.toRingHom :=
    Spec.map_injective (by rw [Spec.map_comp]; exact h)
  have e : ∀ c ∈ R, ψ.hom c = c := fun c hc => congrArg (fun f => f.hom (⟨c, hc⟩ : R)) h2
  have hψ : ψ = 𝟙 _ := by
    ext x
    obtain ⟨a, ha, b, hb, rfl⟩ := frac x
    simp [map_div₀, e a ha, e b hb]
  rw [hψ, Spec.map_id]

theorem sec_of_pt {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real) {G : Over (Sp Ω)}
    (a : G.left ⟶ ρ.P.A.left) (h : IsPullback a G.hom ρ.P.A.hom (spMap S.R.val.toRingHom)) (w : Sp Ω ⟶ G.left)
    (x : S.Gam) (hw : w ≫ a = spMap S.R.val.toRingHom ≫ (ρ.pt x).left) : w ≫ G.hom = 𝟙 _ := by
  refine spec_endo_eq_id S.R S.frac _ ?_
  rw [Category.assoc, ← h.w, ← Category.assoc, hw, Category.assoc, Over.w (ρ.pt x)]
  simp

end GlobalTheory.Poinc.SameChain


open GlobalTheory.Poinc.SameChain in
theorem GlobalTheory.Poinc.same_chain_deep : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (D : Deep X₁ ε₁)
  (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A))
  (c₂ : D.X.Ω₁) (hc₂ : c₂ ≠ 0) (R₂ : Subalgebra D.X.o₁ D.X.Ω₁) (fg₂ : R₂.FG) (frac₂ : ∀ x : D.X.Ω₁, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b) (hth₂ : ∀ x, c₂ * D.X.S.th x ∈ R₂) (hev₂ : ∀ x k, c₂ * D.X.S.ev x k ∈ R₂) (ρ₂ : (D.X.S.rechart c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂).Real) (ε₂ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₂.P.A ⟶ ρ₂.P.A)),
  Same X₁.ρ ε₁ ρ' ε' (fun x => x) (RingHom.id _) → Same D.X.ρ D.ε ρ₂ ε₂ (fun x => x) (RingHom.id _) →
  Same ρ' ε' ρ₂ ε₂ (fun a => D.lab a) (algebraMap X₁.Ω₁ D.X.Ω₁) := by
  intro g n F W Z i X₁ ε₁ D c₀ hc R' fg frac hth hev ρ' ε' c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂ ρ₂ ε₂ h1 h3
  obtain ⟨P₁, a₁, a₁', e₁, pa₁, pa₁', L₁, L₁', E₁, T₁⟩ := h1
  obtain ⟨P₀, b, b', e₀, pb, pb', L₀, L₀', E₀, T₀⟩ := D.same
  obtain ⟨P₃, c, c', e₃, pc, pc', L₃, L₃', E₃, T₃⟩ := h3
  have pa₁c : IsGrpPullback P₁.A X₁.ρ.P.A (spMap X₁.S.R.val.toRingHom) a₁ := pa₁.congr (by rw [RingHom.id_comp]) rfl
  have pcc : IsGrpPullback P₃.A D.X.ρ.P.A (spMap D.X.S.R.val.toRingHom) c := pc.congr (by rw [RingHom.id_comp]) rfl
  have hspc := Geo.Tor.spMap_comp X₁.S.R.val.toRingHom (algebraMap X₁.Ω₁ D.X.Ω₁)
  have pbc : IsGrpPullback P₀.A X₁.ρ.P.A (spMap (algebraMap X₁.Ω₁ D.X.Ω₁) ≫ spMap X₁.S.R.val.toRingHom) b :=
    pb.congr hspc rfl
  have wm : b ≫ X₁.ρ.P.A.hom = (P₀.A.hom ≫ spMap (algebraMap X₁.Ω₁ D.X.Ω₁)) ≫ spMap X₁.S.R.val.toRingHom := by
    rw [pbc.1.w, Category.assoc]
  set m := pa₁c.1.lift b (P₀.A.hom ≫ spMap (algebraMap X₁.Ω₁ D.X.Ω₁)) wm with hmdef
  have hm1 : m ≫ a₁ = b := pa₁c.1.lift_fst _ _ wm
  have hm2 : m ≫ P₁.A.hom = P₀.A.hom ≫ spMap (algebraMap X₁.Ω₁ D.X.Ω₁) := pa₁c.1.lift_snd _ _ wm
  have pm : IsGrpPullback P₀.A P₁.A (spMap (algebraMap X₁.Ω₁ D.X.Ω₁)) m := pa₁c.cancel (pbc.congr rfl hm1.symm) hm2
  obtain ⟨e, he_mon, he⟩ := grpPullback_iso pb' pcc
  haveI := he_mon
  have pe := isGrpPullback_of_iso e
  refine ⟨P₀, m ≫ a₁', e.hom.left ≫ c', e₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (pm.comp pa₁').congr (Geo.Tor.spMap_comp R'.val.toRingHom (algebraMap X₁.Ω₁ D.X.Ω₁)).symm rfl
  · exact (pe.comp pc').congr (Category.id_comp _) rfl
  · have A : LBIso (X₁.ρ.P.L.pull b) (P₁.L.pull m) :=
      LBIso.chartPull (chartPullSame X₁.ρ.P.L (K := PUnit) (fun _ => b) (fun _ => a₁) (fun _ => 1) m
        (fun _ => hm1.symm)) (chartPullPull P₁.L m) L₁.symm
    have B : LBIso (P₁.L.pull m) (ρ'.P.L.pull (m ≫ a₁')) :=
      LBIso.chartPull (chartPullPull P₁.L m) (chartPullSame ρ'.P.L (K := PUnit) (fun _ => m ≫ a₁') (fun _ => a₁')
        (fun _ => 1) m (fun _ => rfl)) L₁'
    exact LBIso.trans P₀.isLB (pull_isLB P₁.isLB m) (pull_isLB ρ'.P.isLB _)
      (LBIso.trans P₀.isLB (pull_isLB X₁.ρ.P.isLB b) (pull_isLB P₁.isLB m) L₀ A) B
  · have A : LBIso (D.X.ρ.P.L.pull b') (P₃.L.pull e.hom.left) :=
      LBIso.chartPull (chartPullSame D.X.ρ.P.L (K := PUnit) (fun _ => b') (fun _ => c) (fun _ => 1) e.hom.left
        (fun _ => he.symm)) (chartPullPull P₃.L e.hom.left) L₃.symm
    have B : LBIso (P₃.L.pull e.hom.left) (ρ₂.P.L.pull (e.hom.left ≫ c')) :=
      LBIso.chartPull (chartPullPull P₃.L e.hom.left) (chartPullSame ρ₂.P.L (K := PUnit)
        (fun _ => e.hom.left ≫ c') (fun _ => c') (fun _ => 1) e.hom.left (fun _ => rfl)) L₃'
    exact LBIso.trans P₀.isLB (pull_isLB P₃.isLB _) (pull_isLB ρ₂.P.isLB _)
      (LBIso.trans P₀.isLB (pull_isLB D.X.ρ.P.isLB b') (pull_isLB P₃.isLB _) L₀' A) B
  · intro E
    have k1 : (e₀ E).left ≫ m = m ≫ (e₁ E).left := by
      apply pa₁c.1.hom_ext
      · rw [Category.assoc, hm1, (E₀ E).1, Category.assoc, (E₁ E).1, ← Category.assoc, hm1]
      · rw [Category.assoc, hm2, ← Category.assoc, Over.w (e₀ E), Category.assoc, Over.w (e₁ E), hm2]
    have k3 : (e₀ E).left ≫ e.hom.left = e.hom.left ≫ (e₃ E).left := by
      apply pcc.1.hom_ext
      · rw [Category.assoc, he, (E₀ E).2, Category.assoc, (E₃ E).1, ← Category.assoc, he]
      · rw [Category.assoc, Over.w e.hom, Over.w (e₀ E), Category.assoc, Over.w (e₃ E), Over.w e.hom]
    refine ⟨?_, ?_⟩
    · rw [← Category.assoc, k1, Category.assoc, (E₁ E).2, Category.assoc]
    · rw [← Category.assoc, k3, Category.assoc, (E₃ E).2, Category.assoc]
  · intro x
    obtain ⟨w, hw, hw'⟩ := T₀ x
    obtain ⟨w₁, hw₁, hw₁'⟩ := T₁ x
    obtain ⟨w₃, hw₃, hw₃'⟩ := T₃ (D.lab x)
    have s0 : w ≫ P₀.A.hom = 𝟙 _ := sec_of_pt D.X.ρ b' pb'.1 w _ hw'
    have s1 : w₁ ≫ P₁.A.hom = 𝟙 _ := sec_of_pt ρ' a₁' pa₁'.1 w₁ _ hw₁'
    have s3 : w₃ ≫ P₃.A.hom = 𝟙 _ := sec_of_pt ρ₂ c' pc'.1 w₃ _ hw₃'
    have hwm : w ≫ m = spMap (algebraMap X₁.Ω₁ D.X.Ω₁) ≫ w₁ := by
      apply pa₁c.1.hom_ext
      · rw [Category.assoc, hm1, hw, Category.assoc, hw₁, hspc, Category.assoc, RingHom.id_comp]
      · rw [Category.assoc, hm2, ← Category.assoc, s0, Category.id_comp, Category.assoc, s1, Category.comp_id]
    have hwe : w ≫ e.hom.left = w₃ := by
      apply pcc.1.hom_ext
      · rw [Category.assoc, he, hw', hw₃, RingHom.id_comp]
      · rw [Category.assoc, Over.w e.hom, s0, s3]
    refine ⟨w, ?_, ?_⟩
    · rw [← Category.assoc, hwm, Category.assoc, hw₁', Geo.Tor.spMap_comp R'.val.toRingHom (algebraMap X₁.Ω₁ D.X.Ω₁),
        Category.assoc]
    · rw [← Category.assoc, hwe, hw₃']
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarOfLaws
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RescaleForm

open GlobalTheory.TauTwist (unitAt unitAt_injective IsScalarForm)

theorem scalar_of_laws {R : Type} [CommRing R] [IsDomain R] {O : Type} [CommRing O] [StarRing O] (D : DegPre R)
    [inst : Module O D.X] (oa : D.OAct O) (w0 : O) (g : D.X → (FractionRing R)ˣ) (hB : D.TauBimult) (hW : TraceFormTwistIso D oa w0)
    (hB' : (GlobalTheory.PolDeg.rescale D g).TauBimult)
    (oa' : @DegPre.OAct R _ _ O _ _ (GlobalTheory.PolDeg.rescale D g) inst)
    (ho : @DegPre.OAct.onB R _ _ O _ _ (GlobalTheory.PolDeg.rescale D g) inst oa' = oa.onB)
    (hW' : @TraceFormTwistIso R _ _ O _ _ (GlobalTheory.PolDeg.rescale D g) inst oa' w0) :
    IsScalarForm O (fun a b => g (a + b) * (g a)⁻¹ * (g b)⁻¹) ∧
      ∀ y, g y = g (y + w0 • y) * (g y)⁻¹ * (g (w0 • y))⁻¹ := by
  letI : Module O (GlobalTheory.PolDeg.rescale D g).X := inst
  have hG := GlobalTheory.globalFns_holds
  let y : (TK R).left := IsLocalRing.closedPoint (FractionRing R)
  obtain ⟨I, hJ⟩ := GlobalTheory.DegPull.exists_good' D.P.isLB y
  have vt : ∀ a b, val ((GlobalTheory.PolDeg.rescale D g).tau a b) (𝟙 _) y I =
      unitAt (𝟙 (TK R).left) y (g (a + b) * (g a)⁻¹ * (g b)⁻¹) * val (D.tau a b) (𝟙 _) y I := fun a b => by
    rw [map_mul, map_mul, map_inv, map_inv]
    exact GlobalTheory.PolDeg.rescale_tau_val D g a b hJ
  have sy : ∀ a b, g (a + b) * (g a)⁻¹ * (g b)⁻¹ = g (b + a) * (g b)⁻¹ * (g a)⁻¹ := fun a b => by
    rw [add_comm, mul_right_comm]
  have al : ∀ a a' b, g (a + a' + b) * (g (a + a'))⁻¹ * (g b)⁻¹ =
      (g (a + b) * (g a)⁻¹ * (g b)⁻¹) * (g (a' + b) * (g a')⁻¹ * (g b)⁻¹) := fun a a' b => by
    have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB a a' b) (𝟙 _)).trans (val_mul hJ _ _ _))
    have e' := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB' a a' b) (𝟙 _)).trans (val_mul hJ _ _ _))
    have e'' := (congrArg₂ (· * ·) (vt (a + a') b).symm rfl).trans (e'.trans (congrArg₂ (· * ·) (vt a b) (vt a' b)))
    rw [_root_.mul_mul_mul_comm, ← e, _root_.mul_assoc, ← map_mul] at e''
    exact unitAt_injective y (mul_right_cancel e'')
  obtain ⟨onB', cl', tb'⟩ := oa'
  obtain rfl : onB' = oa.onB := ho
  refine ⟨⟨fun a b b' => ?_, sy, fun x a b => ?_⟩, fun a => ?_⟩
  · rw [sy, sy a b, sy a b']
    exact al b b' a
  · have hr := GlobalTheory.TorusExt.exists_isRos hG oa (star x)
    rw [star_star] at hr
    obtain ⟨u, hu, u₀⟩ := hr
    have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (oa.tau_bal x u hu u₀ a b) (𝟙 _))
    have e' := (val_mul hJ _ _ _).symm.trans (val_corr hJ (tb' x u hu u₀ a b) (𝟙 _))
    have e'' := (congrArg₂ (· * ·) (vt (x • a) b).symm rfl).trans (e'.trans (vt a (star x • b)))
    rw [← e, _root_.mul_assoc] at e''
    exact unitAt_injective y (mul_right_cancel e'')
  · obtain ⟨u, hu, u₀, h⟩ := hW
    obtain ⟨u', hu', u₀', h'⟩ := hW'
    have k := gen_unique' D.P.isLB (fun _ _ _ => rfl) D.P.A.hom (eSec D.P.A) (Over.w η[D.P.A]) (hG _ _ D.P.isAb).2 hu hu'
      (fun z J hz => by
        have a := val_corr hz u₀ (𝟙 _)
        have b := val_corr hz u₀' (𝟙 _)
        rw [val_pull hz, val_one, Category.id_comp] at a
        have b' := ((val_pull hz _ _ _).symm.trans b).trans (val_one _)
        rw [Category.id_comp] at b'
        exact a.trans b'.symm) _ (𝟙 _ ≫ D.xK a) y I hJ
    have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (h a) (𝟙 _)).trans (val_mul hJ _ _ _))
    have e' := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (h' a) (𝟙 _)).trans (val_mul hJ _ _ _))
    rw [val_pull hJ] at e
    have e'' := (congrArg₂ (· * ·) (vt a (w0 • a)).symm (k.trans (val_pull hJ _ _ _).symm)).trans (e'.trans
      (congrArg₂ (· * ·) (GlobalTheory.UU.val_scaleGen (unitOn (g a)) (D.psi a) (𝟙 _) hJ) rfl))
    rw [_root_.mul_assoc, e] at e''
    exact (unitAt_injective y (mul_right_cancel (e''.trans (_root_.mul_assoc _ _ _)))).symm

theorem main : ∀ {R : Type} [CommRing R] [IsDomain R] {O : Type} [CommRing O] [StarRing O] (D : DegPre R) [inst : Module O D.X] (oa : D.OAct O) (w0 : O) (g : D.X → (FractionRing R)ˣ), D.TauBimult → TraceFormTwistIso D oa w0 → (GlobalTheory.PolDeg.rescale D g).TauBimult → ∀ (oa' : @DegPre.OAct R _ _ O _ _ (GlobalTheory.PolDeg.rescale D g) inst), @DegPre.OAct.onB R _ _ O _ _ (GlobalTheory.PolDeg.rescale D g) inst oa' = oa.onB → @TraceFormTwistIso R _ _ O _ _ (GlobalTheory.PolDeg.rescale D g) inst oa' w0 → GlobalTheory.TauTwist.IsScalarForm O (fun a b => g (a + b) * (g a)⁻¹ * (g b)⁻¹) ∧ ∀ y, g y = g (y + w0 • y) * (g y)⁻¹ * (g (w0 • y))⁻¹ :=
  fun D _ oa w0 g a b c oa' d e => scalar_of_laws D oa w0 g a b c oa' d e

end GlobalTheory.RescaleForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatLocalApproximation
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RankCoinv


open GlobalTheory.SplitFlip in
theorem exists_soLoc_sub_mem_augAt : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v,
    X.Good v → (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) →
    ∀ t : E →ₐ[F] Fv F v, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∃ φ₀ ∈ G.M'.SoLoc B.ψ t, φ - φ₀ ∈ augAt om' v := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v hv hν t φ hφ
  obtain ⟨ι, hι⟩ := _root_.GlobalTheory.LinBarAt.exists_isLinBar_at hP F E σ B a a' G X om om' hT v hv t
  obtain ⟨ν₀, hν₀, hf⟩ := _root_.GlobalTheory.GoodPlaceAct.act_omB hP F E σ B a a' G X om om' hT v hv hν t
  have hspan : Submodule.span ℂ {Z | ∃ g : GL (Fin a') (Fv F v), ∃ Ψ' ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)),
      Z = omB ν₀ ν₀ g 1 Ψ' - Ψ'} ≤ (augAt om' v ⊓ SB _).map ι := by
    rw [Submodule.span_le]
    rintro Z ⟨g₀, Ψ', hΨ', rfl⟩
    obtain ⟨φ', hφ', rfl⟩ := hι.bij.surjOn hΨ'
    obtain ⟨g, hg, hact⟩ := hf ι hι g₀
    obtain ⟨φ₁, hφ₁, hA, hE⟩ := hact φ' hφ'
    refine ⟨φ₁ - φ', ⟨Submodule.subset_span ⟨g, hg, φ', hφ', φ₁, hφ₁, hA, rfl⟩, Submodule.sub_mem _ hφ₁ hφ'⟩, ?_⟩
    simp [map_sub, hE]
  obtain ⟨Ψ₀, -, hrk, hmem⟩ := _root_.GlobalTheory.RankStrata.exists_fullRank_sub_mem_span (Fv F v) a' (a + a') ν₀ (unifAt v)
    (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec hν₀ (ι φ) (hι.bij.mapsTo hφ)
  obtain ⟨n, ⟨hnA, hnSB⟩, hn⟩ := hspan hmem
  refine ⟨φ - n, ⟨Submodule.sub_mem _ hφ hnSB, ι, hι, fun Y hY => ?_⟩, by simpa using hnA⟩
  have : ι (φ - n) = Ψ₀ := by rw [map_sub, hn]; abel
  rw [this]; exact hrk Y hY

end GlobalTheory.RankCoinv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecIsMulOfBaseMultipleThetaSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.PsiRing

theorem secIsMul_of_mult : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (th g : GlobalTheory.UU.SecBT D (𝟙_ _) 1 0) (b : R), GlobalTheory.PsiRing.Mult D th g b → ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom b g th := by
  intro R _ _ D th g b h
  refine GlobalTheory.IndivisibleSection.secIsMul_of_sval D.P.isLB fun y J hJ => ?_
  have e := h _ (𝟙 _) y J hJ
  rwa [Category.id_comp] at e

end GlobalTheory.PsiRing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecIsMulOfTranslatedThetaCoefficientProportional
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.PsiRing

theorem secIsMul_of_coef : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (χ : D.X) (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (th : GlobalTheory.UU.SecBT D (𝟙_ _) 1 0) (g₁ g₂ : GlobalTheory.UU.SecBT D (𝟙_ _) 1 χ) (b₁ b₂ q : R), GlobalTheory.PsiRing.Coef D χ u th g₁ b₁ → GlobalTheory.PsiRing.Coef D χ u th g₂ b₂ → b₁ = q * b₂ → ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom q g₁ g₂ := by
  intro R _ _ D χ u th g₁ g₂ b₁ b₂ q h₁ h₂ hb
  refine GlobalTheory.IndivisibleSection.secIsMul_of_sval D.P.isLB fun y J hJ => ?_
  have e : lift (toUnit (𝟙_ _ ⊗ D.P.A)) (snd (𝟙_ _) D.P.A) = 𝟙 _ := by
    rw [toUnit_unique (toUnit _) (fst (𝟙_ _) D.P.A), lift_fst_snd]
  have e₁ := h₁ (𝟙_ _ ⊗ D.P.A) (snd _ _) y J hJ
  have e₂ := h₂ (𝟙_ _ ⊗ D.P.A) (snd _ _) y J hJ
  rw [e] at e₁ e₂
  refine e₁.trans (Eq.trans ?_ (congrArg (_ * ·) e₂.symm))
  rw [hb, GlobalTheory.IndivisibleSection.cst_mul', _root_.mul_assoc]

end GlobalTheory.PsiRing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionExpansionScaleBaseElement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.UU.expT_scale : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU I D A G) (k : ℕ) (q : R) (σ τ : U.SecGT (𝟙_ _) k) (f g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) k α), ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ G).hom q σ τ → (∀ α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom q (f α) (g α)) → U.ExpT (𝟙_ _) k τ g → U.ExpT (𝟙_ _) k σ f := by
  intro R _ _ I D A G _ _ U k q σ τ f g hσ hf hE e
  obtain ⟨s, hs⟩ := hE e
  refine ⟨s, fun Z x rG rB h1 h2 h3 z JG J hG hB => ?_⟩
  obtain ⟨H1, H2⟩ := hs Z x rG rB h1 h2 h3 z JG J hG hB
  have hc : cst (rB ≫ (𝟙_ _ ⊗ D.P.A).hom) z q = cst (rG ≫ (𝟙_ _ ⊗ G).hom) z q := by
    rw [← Over.w (fst (𝟙_ (Over (Spec (CommRingCat.of R)))) D.P.A), ← Over.w (fst (𝟙_ (Over (Spec (CommRingCat.of R)))) G),
      ← Category.assoc, ← Category.assoc, h3]
  have hF : ∀ α, sval (f α) rB z J = cst (rG ≫ (𝟙_ _ ⊗ G).hom) z q * sval (g α) rB z J := fun α => by
    rw [← hc]
    exact GlobalTheory.secIsMul_gs (hf α) rB z _ (hB.mem _ _)
  have hS : sval σ rG z JG = cst (rG ≫ (𝟙_ _ ⊗ G).hom) z q * sval τ rG z JG :=
    GlobalTheory.secIsMul_gs hσ rG z _ (hG.mem _ _)
  refine ⟨fun α hα => by rw [hF, H1 α hα, mul_zero], ?_⟩
  rw [hS, mul_left_comm, H2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun α _ => by rw [hF, _root_.mul_assoc]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionPowScales
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

open GlobalTheory.Points ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

namespace GlobalTheory.SelfInterPow

theorem isSelfInter_pow : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (L : HermLB p) (a : ℝ), L.IsSelfInter a → ∀ e : ℕ,
      (L.pow e).IsSelfInter ((e : ℝ) ^ (D + 1) * a) := by
  intro hC k _ X _ p D hX L a ha e
  obtain ⟨Φ, hΦ⟩ := ((hC.arExists k X p D hX).2 Unit fun _ => L).1
  have h₁ := (((hC.arIso k X p D hX).2 Unit _ Φ hΦ).1 ()).unique hX ha
  obtain ⟨H, hH, he⟩ := hΦ.1 fun _ => (e : ℤ)
  refine ⟨H, (hC.arIso k X p D hX).1 _ _ H (GlobalTheory.ArInt.isometric_comb_unit_pow k X p L e) hH, he.trans ?_⟩
  rw [← h₁, ← smul_eq_mul, ← map_smul, ArInt.lin, Fintype.sum_unique, mul_pow, ← map_pow, MvPolynomial.smul_eq_C_mul]
  simp

end GlobalTheory.SelfInterPow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegPreDataDescends
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.SiegApprox

open GlobalTheory.SiegelDescent ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison

theorem model_exists : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (F : Finset R), IsAbelianScheme A → ∀ P : LB (G2 A).left, P.IsLB → ∃ (S : Subring R) (B : Over (Sp S)) (_ : GrpObj B) (_ : IsCommMonObj B) (φ : A.left ⟶ B.left) (φ₂ : (G2 A).left ⟶ (G2 B).left) (P₀ : LB (G2 B).left), (F : Set R) ⊆ S ∧ Algebra.FiniteType ℤ S ∧ IsAbelianScheme B ∧ IsGrpPullback A B (spMap S.subtype) φ ∧ IsSquare φ φ₂ ∧ P₀.IsLB ∧ LBIso P (P₀.pull φ₂) := _root_.GlobalTheory.SiegApproxModel.model_exists

theorem rig_descends : ∀ (R : Type) [CommRing R] (S : Subring R) (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (B : Over (Sp S)) [GrpObj B] [IsCommMonObj B] (φ : A.left ⟶ B.left) (φ₂ : (G2 A).left ⟶ (G2 B).left) (P : LB (G2 A).left) (P₀ : LB (G2 B).left) (a : A ⟶ G2 A) (a₀ : B ⟶ G2 B), IsAbelianScheme B → IsGrpPullback A B (spMap S.subtype) φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → a.left ≫ φ₂ = φ ≫ a₀.left → (∃ t : (P.pull a.left).Gen, t.IsGen) → ∃ F : Finset R, ∀ (R₁ : Subring R) (h : S ≤ R₁), (F : Set R) ⊆ R₁ → ∀ a₁ : (Over.pullback (spMap (Subring.inclusion h))).obj B ⟶ G2 ((Over.pullback (spMap (Subring.inclusion h))).obj B), a₁.left ≫ pφ₂ (spMap (Subring.inclusion h)) B = pφ (spMap (Subring.inclusion h)) B ≫ a₀.left → ∃ t : ((P₀.pull (pφ₂ (spMap (Subring.inclusion h)) B)).pull a₁.left).Gen, t.IsGen := _root_.GlobalTheory.exists_finset_gen_descends

theorem symm_descends : ∀ (R : Type) [CommRing R] (S : Subring R) (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (B : Over (Sp S)) [GrpObj B] [IsCommMonObj B] (φ : A.left ⟶ B.left) (φ₂ : (G2 A).left ⟶ (G2 B).left) (P : LB (G2 A).left) (P₀ : LB (G2 B).left), IsAbelianScheme B → IsGrpPullback A B (spMap S.subtype) φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → ∃ F : Finset R, ∀ (R₁ : Subring R) (h : S ≤ R₁), (F : Set R) ⊆ R₁ → LBIso (P₀.pull (pφ₂ (spMap (Subring.inclusion h)) B)) ((P₀.pull (pφ₂ (spMap (Subring.inclusion h)) B)).pull (lift (snd ((Over.pullback (spMap (Subring.inclusion h))).obj B) ((Over.pullback (spMap (Subring.inclusion h))).obj B)) (fst ((Over.pullback (spMap (Subring.inclusion h))).obj B) ((Over.pullback (spMap (Subring.inclusion h))).obj B))).left) := _root_.GlobalTheory.symm_lbIso_descends_to_subring_containing_finset

end GlobalTheory.SiegApprox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareDecompositionDescendsToFiniteExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SqDecFinite

theorem exists_algHom_finite (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) (hR : R.FG) :
    ∃ (k₁ : Type) (_ : Field k₁) (_ : Algebra k k₁) (_ : FiniteDimensional k k₁), Nonempty (R →ₐ[k] k₁) := by
  have : Algebra.FiniteType k R := (Subalgebra.fg_iff_finiteType _).1 hR
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  have : Algebra.FiniteType k (R ⧸ m) := Algebra.FiniteType.trans (S := R) inferInstance inferInstance
  have : Module.Finite k (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (R ⧸ m)
  exact ⟨R ⧸ m, inferInstance, inferInstance, inferInstance, ⟨Ideal.Quotient.mkₐ k m⟩⟩

theorem main : ∀ (k Ω : Type) [Field k] [Field Ω] (σ : k →+* Ω) (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ → ∀ (L M : LB A₀.left), L.IsLB → M.IsLB → SqDec ((Over.pullback (spMap σ)).obj A₀) (L.pull (pullback.fst A₀.hom (spMap σ))) (M.pull (pullback.fst A₀.hom (spMap σ))) → ∃ (k₁ : Type) (_ : Field k₁) (_ : Algebra k k₁) (_ : FiniteDimensional k k₁), SqDec ((Over.pullback (spMap (algebraMap k k₁))).obj A₀) (L.pull (pullback.fst A₀.hom (spMap (algebraMap k k₁)))) (M.pull (pullback.fst A₀.hom (spMap (algebraMap k k₁)))) := by
  intro k Ω _ _ σ A₀ _ hA L M hL hM h
  letI := σ.toAlgebra
  obtain ⟨R, hR, hRd⟩ := _root_.GlobalTheory.SqDecSpread.sqDec_fg k Ω A₀ hA L M hL hM h
  obtain ⟨k₁, _, _, _, ⟨ρ⟩⟩ := exists_algHom_finite k Ω R hR
  exact ⟨k₁, inferInstance, inferInstance, inferInstance, _root_.GlobalTheory.SqDecBC.sqDec_baseChange k R k₁ ρ A₀ L M hL hM hRd⟩

end GlobalTheory.SqDecFinite
end

