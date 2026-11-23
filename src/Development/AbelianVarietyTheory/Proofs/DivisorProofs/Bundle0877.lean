module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0834
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0859
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0846
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0853
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0830
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0847
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0837
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0836
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0863
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TangentEqLcZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.LinearFormDegree.InvFun
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralChangeBaseFrameOrthonormal
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0866
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralEqOfNorms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0848
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabEqStabilizer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerEqCentralizer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0264

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueRigidifiedLineBundleClasses
section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem exists_glue_rigidified (X Y : Scheme.{0}) (p : X ⟶ Y) (e : Y ⟶ X) (hep : e ≫ p = 𝟙 Y) (hp : FnBij p)
    (Ix : Type) (X' : Ix → Scheme.{0}) (f : ∀ i, X' i ⟶ X) (V : Ix → Y.Opens) (c : ∀ i, Pic (X' i))
    (hf : ∀ i, IsOpenImmersion (f i)) (hr : ∀ i x, x ∈ Set.range (f i) ↔ p x ∈ V i) (hV : ∀ y, ∃ i, y ∈ V i)
    (hrig : ∀ (i : Ix) (T : Scheme.{0}) (t : T ⟶ X' i) (s : T ⟶ Y), t ≫ f i = s ≫ e → GlobalTheory.CechPic.pull t (c i) = 0)
    (hov : ∀ (i k : Ix) (T : Scheme.{0}) (a : T ⟶ X' i) (b : T ⟶ X' k), a ≫ f i = b ≫ f k →
      GlobalTheory.CechPic.pull a (c i) = GlobalTheory.CechPic.pull b (c k)) :
    ∃ c₀ : Pic X, GlobalTheory.CechPic.pull e c₀ = 0 ∧ ∀ i, GlobalTheory.CechPic.pull (f i) c₀ = c i := by
  have hpe : ∀ y : Y, p (e y) = y := fun y ↦ by
    rw [← Scheme.Hom.comp_apply, hep]; rfl
  have hrange : ∀ i, (f i).opensRange = p ⁻¹ᵁ V i := fun i ↦ by
    ext x; exact hr i x
  choose M hM hMc using fun i ↦ cls_surj (c i)
  choose L hL hLM using fun i ↦ _root_.GlobalTheory.PicGlue.exists_isOn_of_openImmersion X (X' i) (f i) (M i) (hM i)
  have hL' : ∀ i, IsOn (p ⁻¹ᵁ V i) (L i) := fun i ↦ hrange i ▸ hL i
  have hfm : ∀ i (z : X' i), f i z ∈ p ⁻¹ᵁ V i := fun i z ↦ (hr i _).1 ⟨z, rfl⟩
  have hfl : ∀ i, ((L i).pull (f i)).IsLB := fun i ↦ _root_.GlobalTheory.PicGlue.pull_isLB_of_isOn X _ _ (L i) (f i) (hL' i) (hfm i)
  have hcl : ∀ i, cls _ (hfl i) = c i := fun i ↦ ((cls_eq_iff (hfl i) (hM i)).2 (hLM i)).trans (hMc i)
  have lifts : ∀ i (T : Scheme.{0}) (g : T ⟶ X), (∀ z, g z ∈ p ⁻¹ᵁ V i) → ∃ t : T ⟶ X' i, t ≫ f i = g :=
    fun i T g hg ↦ ⟨IsOpenImmersion.lift (f i) g (by rintro _ ⟨z, rfl⟩; exact (hr i _).2 (hg z)),
      IsOpenImmersion.lift_fac _ _ _⟩
  have hpl : ∀ i (T : Scheme.{0}) (t : T ⟶ X' i) (g : T ⟶ X), t ≫ f i = g →
      ∃ h : ((L i).pull g).IsLB, cls _ h = GlobalTheory.CechPic.pull t (c i) := by
    rintro i T t _ rfl
    have h : ((L i).pull (t ≫ f i)).IsLB := _root_.GlobalTheory.PicGlue.pull_isLB_of_isOn X _ _ (L i) _ (hL' i) fun z ↦ by
      rw [Scheme.Hom.comp_apply]; exact hfm i _
    refine ⟨h, ?_⟩
    rw [← hcl i, ← cls_pull (hfl i) t (pull_isLB (hfl i) t)]
    exact ((cls_eq_iff _ _).2 (_root_.GlobalTheory.PicGlue.isOn_pull_comp X _ _ _ (L i) (f i) t (hL' i) (hfm i))).symm
  have hR : ∀ i, ∃ r : RigD e (L i), RigOn e (L i) r := fun i ↦ by
    refine _root_.GlobalTheory.PicGlue.rigOn_of_triv_open X Y e (V i) (L i) (fun a y hy ↦ ?_) ?_
    · have : p (e y) ∈ V i := (hL' i).le a hy
      rwa [hpe] at this
    · obtain ⟨t, ht⟩ := lifts i _ ((V i).ι ≫ e) fun z ↦ by
        rw [Scheme.Hom.comp_apply]
        change p (e _) ∈ V i
        rw [hpe]
        exact z.2
      obtain ⟨h, hc⟩ := hpl i _ t _ ht
      exact (cls_eq_zero_iff h).1 (hc.trans (hrig i _ t _ ht))
  choose r hr' using hR
  have hw : ∀ i k, ∃ w : Cmp (p ⁻¹ᵁ (V i ⊓ V k)) (L i) (L k), IsoOn (p ⁻¹ᵁ (V i ⊓ V k)) (L i) (L k) w ∧
      Norm e (p ⁻¹ᵁ (V i ⊓ V k)) (L i) (L k) w (r i) (r k) := fun i k ↦ by
    obtain ⟨a, ha⟩ := lifts i _ (p ⁻¹ᵁ (V i ⊓ V k)).ι fun z ↦ z.2.1
    obtain ⟨b, hb⟩ := lifts k _ (p ⁻¹ᵁ (V i ⊓ V k)).ι fun z ↦ z.2.2
    obtain ⟨h1, e1⟩ := hpl i _ a _ ha
    obtain ⟨h2, e2⟩ := hpl k _ b _ hb
    obtain ⟨w, hw⟩ := GlobalTheory.T.exists_isLineBundleIsoOnOpen_of_restriction_iso X (p ⁻¹ᵁ (V i ⊓ V k)) (L i) (L k)
      ((cls_eq_iff h1 h2).1 (e1.trans ((hov i k _ a b (ha.trans hb.symm)).trans e2.symm)))
    exact GlobalTheory.T.exists_lineBundleIso_normalisedAlongSection_retraction X Y p e hep (V i ⊓ V k) _ _ (L i) (L k) w (r i) (r k) (hL' i) (hL' k)
      (fun _ h ↦ h.1) (fun _ h ↦ h.2) hw (hr' i) (hr' k)
  choose w hwi hwn using hw
  obtain ⟨N, hN, hv⟩ := _root_.GlobalTheory.PicGlue.lb_glue X Ix (fun i ↦ p ⁻¹ᵁ V i) L w (fun x ↦ hV (p x)) hL' hwi
    fun i j k x a b d ha hb hd ↦ _root_.GlobalTheory.PicGlue.norm_cocycle X Y p e hep hp (V i ⊓ V j ⊓ V k) _ _ _ _ _ _ (L i) (L j) (L k)
      (w i j) (w j k) (w i k) (r i) (r j) (r k) (hL' i) (hL' j) (hL' k) (fun _ h ↦ h)
      (fun _ h ↦ ⟨⟨h.1, h.1.2, h.2⟩, h.1.1, h.2⟩) (hwi i j) (hwi j k) (hwi i k) (hwn i j) (hwn j k) (hwn i k)
      x a b d ⟨⟨(hL' i).le a ha, (hL' j).le b hb⟩, (hL' k).le d hd⟩ ha hb hd
  have hNc : ∀ i, GlobalTheory.CechPic.pull (f i) (cls N hN) = c i := fun i ↦ by
    obtain ⟨v, hv⟩ := hv i
    rw [← hcl i, ← cls_pull hN (f i) (pull_isLB hN _)]
    exact (cls_eq_iff _ _).2 (GlobalTheory.T.lineBundleIso_pull_of_isLineBundleIsoOnOpen X _ _ N (L i) v (f i) hv (hfm i))
  refine ⟨cls N hN - GlobalTheory.CechPic.pull p (GlobalTheory.CechPic.pull e (cls N hN)), ?_, fun i ↦ ?_⟩
  · rw [map_sub, ← pull_comp e p, hep, pull_id, sub_self]
  · obtain ⟨t, ht⟩ := lifts i _ ((f i ≫ p) ≫ e) fun z ↦ by
      rw [Scheme.Hom.comp_apply]
      change p (e _) ∈ V i
      rw [hpe, Scheme.Hom.comp_apply]
      exact hfm i z
    rw [map_sub, hNc, ← pull_comp (f i) p, ← pull_comp (f i ≫ p) e, ← ht, pull_comp, hNc,
      hrig i _ t _ ht, sub_zero]

end GlobalTheory.PicGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntInv
section
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

namespace GlobalTheory.IntInv

theorem exists_int_inv : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)), ∀ (d : ℕ) (Θ : Fin d → MvPowerSeries (Fin d) C), (∀ a, MvIsInt v (Θ a)) → (∀ a, constantCoeff (Θ a) = 0) → (∀ a b, coeff (Finsupp.single b 1) (Θ a) = if a = b then 1 else 0) → ∃ Ψ : Fin d → MvPowerSeries (Fin d) C, (∀ a, MvIsInt v (Ψ a)) ∧ (∀ a, constantCoeff (Ψ a) = 0) ∧ (∀ a, subst Ψ (Θ a) = MvPowerSeries.X a) ∧ ∀ a, subst Θ (Ψ a) = MvPowerSeries.X a := by
  intro C _ _ v d Θ hint h0 h1
  set S := ReciprocityTheory.ChartRestriction.G.Sh.PTb.intRing v
  let Θ' : Fin d → MvPowerSeries (Fin d) S := fun a α => ⟨coeff α (Θ a), hint a α⟩
  have hΘ' : ∀ a, map S.subtype (Θ' a) = Θ a := fun a => by ext α; rfl
  have h0' : ∀ a, constantCoeff (Θ' a) = 0 := fun a => Subtype.ext (by
    change coeff 0 (Θ a) = 0
    rw [coeff_zero_eq_constantCoeff_apply]; exact h0 a)
  have h1' : ∀ a b, coeff (Finsupp.single b 1) (Θ' a) = (1 : Matrix (Fin d) (Fin d) S) a b := by
    intro a b
    apply Subtype.ext
    change coeff (Finsupp.single b 1) (Θ a) = _
    rw [h1 a b, Matrix.one_apply]
    split_ifs <;> rfl
  have hu : IsUnit (1 : Matrix (Fin d) (Fin d) S).det := by rw [Matrix.det_one]; exact isUnit_one
  obtain ⟨ψ, hψ0, hψΘ, hΘψ⟩ := ReciprocityTheory.ChartRestriction.G.LF.InvFun.exists_inv Θ' h0' 1 h1' hu
  have hsψ : HasSubst ψ := hasSubst_of_constantCoeff_zero hψ0
  have hsΘ : HasSubst Θ' := hasSubst_of_constantCoeff_zero h0'
  refine ⟨fun a => map S.subtype (ψ a), ?_, ?_, ?_, ?_⟩
  · intro a α
    rw [coeff_map]
    exact (coeff α (ψ a)).2
  · intro a
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hψ0 a]
    rfl
  · intro a
    have key := map_subst hsψ (h := S.subtype) (Θ' a)
    rw [hΘ', hψΘ a, map_X] at key
    exact key.symm
  · intro a
    have key := map_subst hsΘ (h := S.subtype) (ψ a)
    have e : (fun s => map S.subtype (Θ' s)) = Θ := funext hΘ'
    rw [e, hΘψ a, map_X] at key
    exact key.symm

end GlobalTheory.IntInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralChangeBaseFrameOrthonormalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_change_baseFrame_orthonormal : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsBaseFrame V β Λ N → ∃ u : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E), Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (β * intGL D.host.F D.host.E V.rank u).val * V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) * (β * intGL D.host.F D.host.E V.rank u).val = 1 := by
  first | exact @GlobalTheory.AdelicOrthFrame.exists_orthonormal_baseFrame | exact GlobalTheory.AdelicOrthFrame.exists_orthonormal_baseFrame | (intros; apply GlobalTheory.AdelicOrthFrame.exists_orthonormal_baseFrame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAmpleTensorAmplePowProjective
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem IsAmpleLB.eventually_isGenerated_tens_lbPow {X : Scheme.{0}} {A N : LB X} (hA : IsAmpleLB A)
    (hN : N.IsLB) : ∀ᶠ n : ℕ in atTop, IsGenerated (tens N (lbPow A n)) := by
  have := isFiniteQC_twist (F := GlobalTheory.structureModule X) hN
  refine (hA.eventually_isGloballyGenerated_twist (twist (GlobalTheory.structureModule X) N)).mono
    fun n hn => ?_
  have hP := isLB_lbPow hA.isLB n
  have hT := isLB_tens hN hP
  obtain ⟨e⟩ := nonempty_twist_twist_iso_of_cls_eq (GlobalTheory.structureModule X) hN hP hT
    (cls_tens hN hP hT)
  exact (isGloballyGenerated_toMod_iff hT).1 ((hn.of_epi e.hom).of_epi (unitTwistIso _).hom)

theorem IsAmpleLB.eventually_isAmpleLB_tens_lbPow_succ {X : Scheme.{0}} {A N : LB X}
    (hA : IsAmpleLB A) (hN : N.IsLB) : ∀ᶠ n : ℕ in atTop, IsAmpleLB (tens N (lbPow A (n + 1))) := by
  refine (hA.eventually_isGenerated_tens_lbPow hN).mono fun n hn => ?_
  have hP := isLB_lbPow hA.isLB n
  have hP' := isLB_lbPow hA.isLB (n + 1)
  have hT := isLB_tens hN hP'
  have hD := LB.isLB_div hT hA.isLB
  refine hA.tensor_isGenerated hn hT ((cls_eq_zero_iff (LB.isLB_div hD hn.isLB)).1 ?_)
  rw [cls_div hD hn.isLB, cls_div hT hA.isLB, cls_tens hN hP', cls_tens hN hP,
    cls_lbPow hA.isLB, cls_lbPow hA.isLB, succ_nsmul]
  abel

theorem exists_isAmpleLB_tens_lbPow : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ A N : LB X, IsAmpleLB A → N.IsLB → ∃ c : ℕ, 1 ≤ c ∧ IsAmpleLB (tens N (lbPow A c)) := by
  intro k _ _ X _ _ A N hA hN
  obtain ⟨n, hn⟩ := (hA.eventually_isAmpleLB_tens_lbPow_succ hN).exists
  exact ⟨n + 1, Nat.succ_pos n, hn⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDetRoot
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DetOnto

theorem sigR_mem_intAE (D : D7) {y : Af D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ intAE D) :
    sigR (Af D.host.F) D.sp.cm.sig y ∈ intAE D := by
  induction hy using AddSubgroup.closure_induction with
  | mem y h =>
    obtain ⟨a, ha, x, rfl⟩ := h
    exact AddSubgroup.subset_closure ⟨a, ha,
      ⟨D.sp.cm.sig x, (x.2 : IsIntegral ℤ (x : D.host.E)).map D.sp.cm.sig.toRingHom.toIntAlgHom⟩, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

theorem sigR_sigR (D : D7) (a : Af D.host.F ⊗[D.host.F] D.host.E) :
    sigR (Af D.host.F) D.sp.cm.sig (sigR (Af D.host.F) D.sp.cm.sig a) = a := by
  induction a using TensorProduct.inductionOn with
  | tmul a b => exact congrArg (fun x => a ⊗ₜ[D.host.F] x) (star_star b)
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem ext_parts (D : D7) {a b : AE D} (h1 : infPart D a = infPart D b) (h2 : finPart D a = finPart D b) :
    a = b := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  apply e.injective
  exact Prod.ext ((he a).1.trans (h1.trans (he b).1.symm)) ((he a).2.trans (h2.trans (he b).2.symm))

theorem norm_one {R : Type} [CommRing R] (σ : R →+* R) (hσ : ∀ a, σ (σ a) = a) {a b : R} (h : a * b = 1) :
    a * σ b * σ (a * σ b) = 1 := by
  have h' := congrArg σ h
  rw [map_mul, map_one] at h'
  rw [map_mul, hσ]
  linear_combination (σ a * σ b) * h + h'

theorem infPart_det {D : D7} (V : HSp D) (k : GA D V) (hk : k ∈ GfC V) : infPart D (matHom V k).1.det = 1 := by
  have h : infHom V k = 1 := hk
  have h' : (infHom V k).1.det = infPart D (matHom V k).1.det := ((infPart D).map_det _).symm
  rw [← h', h, Units.val_one, Matrix.det_one]

theorem infPart_sigR (D : D7) (x : AE D) :
    infPart D (sigR (AF D.host.F) D.sp.cm.sig x) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D x) :=
  GlobalTheory.DetRootCong.map_sigR _ _ x

end GlobalTheory.DetOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaTildeUnramified
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum

namespace GlobalTheory.WeilParts

theorem exists_isEtaTilde_unramified (D : D7) : ∃ η, IsEtaTilde D η := by
  obtain ⟨χ, h1, h2, h3, h4⟩ := GlobalTheory.Mem.EtaTilde.exists_etaTilde D
  exact ⟨χ, h1, h4, h3, h2⟩

end GlobalTheory.WeilParts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKFiniteModuleIrreducibleUnitary
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.KModExistsStep

theorem kModExists_holds : CompanionTheory.D.LK.KModExists :=
  GlobalTheory.CompanionTheory.KModExists.kModExists CompanionTheory.D.DSIC.hSmMod CompanionTheory.D.gk.admitted.kFin_mem_smoothVecs CompanionTheory.D.DSIC.hKFinStab
    CompanionTheory.D.DSIC.hStabLink CompanionTheory.D.DSIC.hHWofType CompanionTheory.D.DSIC.hTypeOfHW

end GlobalTheory.CompanionTheory.KModExistsStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPadicPowMulMemTensorUnramifiedIntegers
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKRes.Denom

variable (p : ℕ) [Fact p.Prime]

theorem exists_pow_mul_norm_le_one (y : PadicAlgCl p) : ∃ k : ℕ, ‖(p : PadicAlgCl p) ^ k * y‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.PowerScaledNormBound.exists_pow_mul_norm_le_one
  | exact _root_.GlobalTheory.PowerScaledNormBound.exists_pow_mul_norm_le_one
  | (apply _root_.GlobalTheory.PowerScaledNormBound.exists_pow_mul_norm_le_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerScaledNormBound.exists_pow_mul_norm_le_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerScaledNormBound.exists_pow_mul_norm_le_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerScaledNormBound.exists_pow_mul_norm_le_one ..)

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ)

theorem inclK_mem (a : K) (ha : ‖(a : PadicAlgCl p)‖ ≤ 1) : inclK p K r a ∈ intKQ p K r :=
  Subring.subset_closure (Or.inl ⟨⟨a, (ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff (p := p)).2 ha⟩, rfl⟩)

theorem inclQ_mem (b : Qr p r) (hb : ‖(b : PadicAlgCl p)‖ ≤ 1) : inclQ p K r b ∈ intKQ p K r :=
  Subring.subset_closure (Or.inr ⟨⟨b, (ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff (p := p)).2 hb⟩, rfl⟩)

theorem aux (x : K ⊗[ℚ_[p]] Qr p r) :
    ∃ k : ℕ, (p : K ⊗[ℚ_[p]] Qr p r) ^ k * x ∈ intKQ p K r := by
  have hp : ∀ m : ℕ, (p : K ⊗[ℚ_[p]] Qr p r) ^ m ∈ intKQ p K r := fun m => pow_mem (natCast_mem _ p) m
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [mul_zero]; exact (intKQ p K r).zero_mem⟩
  | tmul a b =>
    obtain ⟨k, hk⟩ := exists_pow_mul_norm_le_one p (a : PadicAlgCl p)
    obtain ⟨l, hl⟩ := exists_pow_mul_norm_le_one p (b : PadicAlgCl p)
    refine ⟨k + l, ?_⟩
    have e : (p : K ⊗[ℚ_[p]] Qr p r) ^ (k + l) * (a ⊗ₜ[ℚ_[p]] b) =
        ((p : K) ^ k * a) ⊗ₜ[ℚ_[p]] ((p : Qr p r) ^ l * b) := by
      calc (p : K ⊗[ℚ_[p]] Qr p r) ^ (k + l) * (a ⊗ₜ[ℚ_[p]] b)
          = (Algebra.TensorProduct.includeLeft (R := ℚ_[p]) (S := ℚ_[p]) (B := Qr p r) ((p : K) ^ k)) *
            (Algebra.TensorProduct.includeRight (R := ℚ_[p]) (A := K) ((p : Qr p r) ^ l)) * (a ⊗ₜ[ℚ_[p]] b) := by
            simp only [map_pow, map_natCast, pow_add]
        _ = _ := by
            simp only [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
              Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e]
    have hm := mul_mem (inclK_mem p K r ((p : K) ^ k * a) (by simpa using hk))
      (inclQ_mem p K r ((p : Qr p r) ^ l * b) (by simpa using hl))
    have e2 : inclK p K r ((p : K) ^ k * a) * inclQ p K r ((p : Qr p r) ^ l * b) =
        ((p : K) ^ k * a) ⊗ₜ[ℚ_[p]] ((p : Qr p r) ^ l * b) := by
      change (((p : K) ^ k * a) ⊗ₜ[ℚ_[p]] (1 : Qr p r)) * ((1 : K) ⊗ₜ[ℚ_[p]] ((p : Qr p r) ^ l * b)) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [← e2]
    exact hm
  | add x y hx hy =>
    obtain ⟨k, hk⟩ := hx
    obtain ⟨l, hl⟩ := hy
    refine ⟨k + l, ?_⟩
    have e : (p : K ⊗[ℚ_[p]] Qr p r) ^ (k + l) * (x + y) =
        (p : K ⊗[ℚ_[p]] Qr p r) ^ l * ((p : K ⊗[ℚ_[p]] Qr p r) ^ k * x) +
          (p : K ⊗[ℚ_[p]] Qr p r) ^ k * ((p : K ⊗[ℚ_[p]] Qr p r) ^ l * y) := by
      ring
    rw [e]
    exact add_mem (mul_mem (hp l) hk) (mul_mem (hp k) hl)

end GlobalTheory.LKRes.Denom

namespace GlobalTheory.LKRes

theorem exists_pow_mul_mem_intKQ : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ)
    (x : KQ p K r), ∃ k : ℕ, (p : KQ p K r) ^ k * x ∈ intKQ p K r :=
  fun p _ K r x => Denom.aux p K r x

end GlobalTheory.LKRes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeEqSpanOfCoheightLeOne
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_prime_eq_span_of_coheight_le_one (R : Type) [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (X : Scheme.{0}) (q : X ⟶ Sp R) (hq : GeneralizingMap q)
    (x : X) (hx : Order.coheight x ≤ 1) (hne : (q x).asIdeal ≠ ⊥) :
    ∃ π : R, Prime π ∧ (q x).asIdeal = Ideal.span {π} := by
  obtain ⟨π, hπP, hπ⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot (q x).isPrime hne
  refine ⟨π, hπ, ?_⟩
  by_contra hQP
  have hQle : Ideal.span {π} ≤ (q x).asIdeal := (Ideal.span_singleton_le_iff_mem _).2 hπP
  have hQprime : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).2 hπ
  let Q : PrimeSpectrum R := ⟨_, hQprime⟩
  have hQsp : Q ⤳ q x := (PrimeSpectrum.le_iff_specializes Q (q x)).1 hQle
  obtain ⟨x', hx'x, hqx'⟩ := hq hQsp
  let B : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  have hBQ : B ⤳ Q := (PrimeSpectrum.le_iff_specializes B Q).1 bot_le
  obtain ⟨x'', hx''x', hqx''⟩ := hq (hqx' ▸ hBQ)
  have h1 : x < x' := by
    refine lt_of_le_not_ge hx'x ?_
    intro h
    have h' : q x ⤳ q x' := h.map q.continuous
    rw [hqx'] at h'
    exact hQP (le_antisymm ((PrimeSpectrum.le_iff_specializes (q x) Q).2 h') hQle)
  have h2 : x' < x'' := by
    refine lt_of_le_not_ge hx''x' ?_
    intro h
    have h' : q x' ⤳ q x'' := h.map q.continuous
    rw [hqx', hqx''] at h'
    have hle : Ideal.span {π} ≤ ⊥ := (PrimeSpectrum.le_iff_specializes Q B).2 h'
    exact hπ.ne_zero (Ideal.span_singleton_eq_bot.1 (le_bot_iff.1 hle))
  have c1 := Order.coheight_add_one_le h1
  have c2 := Order.coheight_add_one_le h2
  have : (2 : ℕ∞) ≤ Order.coheight x := by
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ Order.coheight x'' + 1 + 1 := by gcongr; exact bot_le
      _ ≤ Order.coheight x' + 1 := by gcongr
      _ ≤ Order.coheight x := c1
  have := this.trans hx
  norm_num at this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitIdempotentConjugation
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CentAtP

variable {p : ℕ} [Fact p.Prime]

theorem exists_conj_ne (G : HTGroup p) : ∃ x ∈ G.Kq, IsCMField.complexConj G.F x ≠ x := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace G.F) := inferInstance
  obtain ⟨x, hx, him⟩ := G.hKq.2 v.embedding
  refine ⟨x, hx, fun h => him ?_⟩
  have h2 := IsCMField.complexEmbedding_complexConj G.F v.embedding x
  rw [h] at h2
  have := congrArg Complex.im h2
  simp only [Complex.conj_im] at this
  linarith

end GlobalTheory.CentAtP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrbitsEqFinsumConjClasses
section
open GlobalTheory.LKCount GlobalTheory.OrbitUnfold

namespace GlobalTheory.OrbitUnfold

theorem finsum_orbits_eq_finsum_conjClasses : ∀ {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ), (∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) → (∀ y : Y, (MulAction.stabilizer Γ y : Set Γ).Finite) → (∀ y : Y, (Function.support (F y)).Finite) → {o : MulAction.orbitRel.Quotient Γ Y | ∃ γ, F (Quotient.out o) γ ≠ 0}.Finite → ∑ᶠ o : MulAction.orbitRel.Quotient Γ Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o)) : ℕ) : ℂ)⁻¹ * ∑ᶠ γ : Γ, F (Quotient.out o) γ = ∑ᶠ c : ConjClasses Γ, ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {Quotient.out c}) Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Subgroup.centralizer {Quotient.out c} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) (Quotient.out c) := by
  intro Γ Y _ _ F hF hst hs ho
  rw [GlobalTheory.T.weightedOrbitSum_eq_pairOrbitSum F hF hst hs ho, GlobalTheory.T.finsum_conjClasses_centralizer_orbits_eq_pairOrbits F hF hst hs ho]

end GlobalTheory.OrbitUnfold
end

