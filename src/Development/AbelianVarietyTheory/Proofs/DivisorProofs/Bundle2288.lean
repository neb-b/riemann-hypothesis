module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2185
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0038
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2203
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousLatticeVectorsAlongArc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedChartExponentialToroidalModel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0590
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentialKernelsIsHolomorphicLatticeFamily
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0554
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0581
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0551
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0555
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0562
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2194

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenTorsionKernelLocus
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section
namespace GlobalTheory.LevCover

theorem clopenCond_comp_eq_one {Y : Scheme.{0}} (Zt B : Over Y) [GrpObj B] (hB : IsAbelianScheme B) (n : ℕ)
    (hn : IsUnit (n : Γ(Y, ⊤))) (g : Zt ⟶ B) (hg : g ^ n = 1) :
    ClopenCond Zt (fun _ z => z ≫ g = 1) := by
  obtain ⟨-, hfin, het⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion B (hG := hB) hn
  obtain ⟨u, hu, -⟩ := GlobalTheory.LatticeTorsion.existsUnique_torsion B n g hg
  obtain ⟨u', hu', -⟩ := GlobalTheory.LatticeTorsion.existsUnique_torsion B n (1 : Zt ⟶ B) (one_pow n)
  refine (clopenCond_eq u u').congr fun T z => ⟨fun h => ?_, fun h => ?_⟩
  · have hz : (z ≫ g) ^ n = 1 := by rw [← MonObj.comp_pow, hg, MonObj.comp_one]
    refine (GlobalTheory.LatticeTorsion.existsUnique_torsion B n (z ≫ g) hz).unique ?_ ?_
    · rw [Category.assoc, hu]
    · rw [Category.assoc, hu', MonObj.comp_one, h]
  · rw [← hu, ← Category.assoc, h, Category.assoc, hu', MonObj.comp_one]

theorem kerlocus_open_closed : ∀ (Y : Scheme.{0}) (A : Over Y) [GrpObj A] [IsCommMonObj A] (n : ℕ) (J : Type) [Finite J] (B : J → Over Y) [∀ i, GrpObj (B i)] (f : ∀ i, A ⟶ B i) (B' : Over Y) [GrpObj B'] (f' : A ⟶ B'), IsAbelianScheme A → (∀ i, IsAbelianScheme (B i)) → IsAbelianScheme B' → (∀ i, IsMonHom (f i)) → IsMonHom f' → IsUnit (n : Γ(Y, ⊤)) → ∃ W : Set Y, IsOpen W ∧ IsClosed W ∧ (∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y), Set.range t.base ⊆ W ↔ ∀ (T : Over Y) (σ : T.left ⟶ Tb), σ ≫ t = T.hom → ∀ a : T ⟶ A, a ^ n = 1 → (∀ i, a ≫ f i = 1) → a ≫ f' = 1) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y), Set.range x.base ⊆ W ↔ ∀ a : Over.mk x ⟶ A, a ^ n = 1 → (∀ i, a ≫ f i = 1) → a ≫ f' = 1 := by
  intro Y A _ _ n J _ B _ f B' _ f' hA hB hB' hf hf' hn
  obtain ⟨-, hfin, het⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A (hG := hA) hn
  have hι : torsion.ι A n ^ n = 1 := GlobalTheory.LatticeTorsion.torsionι_pow_eq_one A n
  have hpow : ∀ (C : Over Y) [GrpObj C] (g : A ⟶ C) [IsMonHom g], (torsion.ι A n ≫ g) ^ n = 1 := by
    intro C _ g _
    rw [← MonObj.pow_comp, hι, MonObj.one_comp]
  obtain ⟨W, hWo, hWc, H1, H2⟩ := implocus_open_closed Y (torsion A n)
    (fun _ z => ∀ i, z ≫ (torsion.ι A n ≫ f i) = 1) (fun _ z => z ≫ (torsion.ι A n ≫ f') = 1) hfin het
    (ClopenCond.forall_finite fun i =>
      clopenCond_comp_eq_one _ (B i) (hB i) n hn _ (hpow (B i) (f i)))
    (clopenCond_comp_eq_one _ B' hB' n hn _ (hpow B' f'))
  have key : ∀ T : Over Y, (∀ z : T ⟶ torsion A n, (∀ i, z ≫ (torsion.ι A n ≫ f i) = 1) →
      z ≫ (torsion.ι A n ≫ f') = 1) ↔
      ∀ a : T ⟶ A, a ^ n = 1 → (∀ i, a ≫ f i = 1) → a ≫ f' = 1 := by
    intro T
    constructor
    · intro H a ha hfa
      obtain ⟨z, hz, -⟩ := GlobalTheory.LatticeTorsion.existsUnique_torsion A n a ha
      have h := H z (fun i => by rw [← Category.assoc, hz, hfa i])
      rwa [← Category.assoc, hz] at h
    · intro H z hz
      have h := H (z ≫ torsion.ι A n) (by rw [← MonObj.comp_pow, hι, MonObj.comp_one])
        (fun i => by rw [Category.assoc]; exact hz i)
      rwa [Category.assoc] at h
  refine ⟨W, hWo, hWc, fun Tb t => (H1 Tb t).trans ?_, fun k _ _ x => (H2 k x).trans (key _)⟩
  exact forall_congr' fun T => forall_congr' fun σ => forall_congr' fun _ => key T

end GlobalTheory.LevCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionSplitTorusIntoTorusExtensionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosedImmersion_splitTorus_into_torusExtension : ∀ (Ω : Type) [Field Ω] (H : Over (Spec (CommRingCat.of Ω))) [GrpObj H], TorusExtension H → ∀ (r : ℕ) (v : splitTorus (Spec (CommRingCat.of Ω)) (Fin r → ℤ) ⟶ H), IsMonHom v → (∀ (p : ℕ), p.Prime → ∀ φ : (Fin r → ℤ) →+ ZMod p, φ ≠ 0 → GlobalTheory.SplitTorus.torusMap (Spec (CommRingCat.of Ω)) φ ≫ v ≠ 1) → IsClosedImmersion v.left := by
  first | exact @GlobalTheory.TorusFieldCrit.isClosedImmersion_of_torusExtension | exact GlobalTheory.TorusFieldCrit.isClosedImmersion_of_torusExtension | (intros; apply GlobalTheory.TorusFieldCrit.isClosedImmersion_of_torusExtension <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCobWholeOfIsCobCover
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PtExt

theorem isCob_whole_of_isCob_cover : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens), ⨆ i, W i = ⊤ → ∀ u : Fn1 X, IsCoc (whole X) u → ∀ k : Fn0 X, IsCob W u k → ∃ k' : Fn0 X, IsCob (whole X) u k' := by
  intro R _ X K W hW u hu k hk
  have ex : ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D), ∃! d : D,
      ∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E), Sm W (D := E) (spOver ψ ≫ x) →
        k E (spOver ψ ≫ x) - u D E ψ x = ψ d := by
    intro D _ _ x
    refine natFamily_existsUnique R X K W hW D x (fun E _ _ ψ ↦ k E (spOver ψ ≫ x) - u D E ψ x) ?_
    intro E _ _ E' _ _ ψ θ hψ
    have c := hu D E E' ψ θ x (sm_whole x)
    have b := hk E E' θ (spOver ψ ≫ x) hψ
    have e : spOver (θ.comp ψ) ≫ x = spOver θ ≫ spOver ψ ≫ x := by
      rw [← Category.assoc, spOver_comp]
    show k E' (spOver (θ.comp ψ) ≫ x) - u D E' (θ.comp ψ) x = θ (k E (spOver ψ ≫ x) - u D E ψ x)
    rw [e, c, b, map_sub]
    ring
  let k' : Fn0 X := fun D _ _ x ↦ (ex D x).exists.choose
  have hk' : ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D) (E : Type) [CommRing E] [Algebra R E]
      (ψ : D →ₐ[R] E), Sm W (D := E) (spOver ψ ≫ x) → k E (spOver ψ ≫ x) - u D E ψ x = ψ (k' D x) :=
    fun D _ _ x ↦ (ex D x).exists.choose_spec
  refine ⟨k', fun D _ _ D' _ _ φ x _ ↦ ?_⟩
  have huniq : k' D' (spOver φ ≫ x) = u D D' φ x + φ (k' D x) := by
    refine (ex D' (spOver φ ≫ x)).unique (hk' D' (spOver φ ≫ x)) ?_
    intro E _ _ ψ hψ
    have e : spOver (ψ.comp φ) ≫ x = spOver ψ ≫ spOver φ ≫ x := by
      rw [← Category.assoc, spOver_comp]
    have h1 := hk' D x E (ψ.comp φ) (by rw [e]; exact hψ)
    have c := hu D D' E φ ψ x (sm_whole x)
    rw [e, c, AlgHom.comp_apply] at h1
    rw [map_add (f := _), ← h1]
    ring
  rw [huniq]
  ring

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCocOfIsSecDiff
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt

theorem isCoc_of_isSecDiff : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A]
    [IsCommMonObj A] (n : ℕ), HasRoots A n → ∀ b : Fn0 A, IsTorsChar n b → ∀ S : SecFam A,
    (∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsSec n b x (S D x)) →
    ∀ u : Fn1 A, IsSecDiff n S u → IsCoc (whole A) u := by
  intro R _ A _ _ n hR b _ S _ u hu
  unfold IsCoc
  intro D _ _ D' _ _ D'' _ _ φ ψ x _
  obtain ⟨E, _, _, χ, z, hχ, hz⟩ := hR D'' (spOver ψ ≫ spOver φ ≫ x)
  apply (show Function.Injective χ from hχ.injective)
  have h1 := hu D D'' (ψ.comp φ) x E χ z (by rw [hz, ← spOver_comp, Category.assoc])
  have h2 := hu D D' φ x E (χ.comp ψ) z (by rw [hz, ← spOver_comp, Category.assoc])
  have h3 := hu D' D'' ψ (spOver φ ≫ x) E χ z hz
  rw [AlgHom.comp_apply] at h2
  rw [map_add χ, h1, h2, h3, ← spOver_comp, Category.assoc, AlgHom.comp_assoc]
  abel

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCoordEnd
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Mum.EndThick

def IsCoordEnd {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
    (a a' : D.P.A ⟶ D.P.A) (h' : D.X →+ D.X) (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A a' a) rosatiε))
    (F : thickObj R I e G ⟶ thickObj R I e G) : Prop :=
  F.left ≫ g.pG.left = g.pG.left ≫ a.left ∧
    ∀ (χ : D.X) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι),
      Good D.P.L z J →
      val (g.t χ) (r ≫ F.left) z J =
        val (g.t (h' χ)) r z J * val (LB.pullGen D.P.L _ _ u (lift (toUnit _ ≫ D.c χ) g.pG).left) r z J

end GlobalTheory.Mum.EndThick
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeformationChartPointSpecMap
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechKS

theorem valR_spMap_comp {Z : Scheme.{0}} {S S' : Type} [CommRing S] [CommRing S'] (σ : S →+* S')
    (z : Sp S ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ z ⁻¹ᵁ U) (f : Γ(Z, U)) :
    valR (spMap σ ≫ z) U f = σ (valR z U f) := by
  have h' := GlobalTheory.FlagMod.le_preimage_comp (spMap σ) h
  rw [valR_eq_ev _ _ h', valR_eq_ev _ _ h, GlobalTheory.FlagMod.ev_spMap σ z U h h']
  rfl

theorem top_le_transl {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {B : Type} [CommRing B] (φ : K →+* B)
    (x : Sp B ⟶ A.left) (hx : x ≫ A.hom = spMap φ) {v : epsR K ⟶ A} (hv : IsTangent v) {U : A.left.Opens}
    (h : ⊤ ≤ x ⁻¹ᵁ U) : ⊤ ≤ (transl φ x v) ⁻¹ᵁ U := by
  intro p _
  have hs : Function.Surjective (spMap (TrivSqZeroExt.fstHom B B B).toRingHom) := by
    intro q
    refine ⟨spMap (algebraMap B (DualNumber B)) q, ?_⟩
    refine PrimeSpectrum.ext (Ideal.ext fun c ↦ ?_)
    change algebraMap B (DualNumber B) c.fst ∈ q.asIdeal ↔ c ∈ q.asIdeal
    have hn : c - algebraMap B (DualNumber B) c.fst ∈ q.asIdeal := by
      refine q.isPrime.mem_of_pow_mem 2 ?_
      have : (c - algebraMap B (DualNumber B) c.fst) ^ 2 = 0 := by
        ext <;> simp [pow_two, TrivSqZeroExt.algebraMap_eq_inl]
      rw [this]; exact zero_mem _
    exact ⟨fun hc ↦ by simpa using add_mem hn hc, fun hc ↦ by simpa using sub_mem hc hn⟩
  obtain ⟨q, rfl⟩ := hs p
  have := h (Set.mem_univ q)
  rw [← (isTransl_transl φ x hx v).red hv] at this
  exact this

theorem transl_spMap {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {B B' : Type} [CommRing B] [CommRing B']
    (φ : K →+* B) (σ : B →+* B') (x : Sp B ⟶ A.left) (hx : x ≫ A.hom = spMap φ) (v : epsR K ⟶ A) :
    transl (σ.comp φ) (spMap σ ≫ x) v = spMap (dualMap σ) ≫ transl φ x v := by
  have hx' : (spMap σ ≫ x) ≫ A.hom = spMap (σ.comp φ) := by
    rw [Category.assoc, hx, Cris.spMap_comp]
  exact (isTransl_transl _ _ hx' v).unique ((isTransl_transl φ x hx v).map σ)

theorem baseMap_eq {K : Type} [Field K] {B B' : Type} [CommRing B] [Algebra (DualNumber K) B] [CommRing B']
    [Algebra (DualNumber K) B'] (ρ : B →ₐ[DualNumber K] B') :
    baseMap K B' = (ρ : B →+* B').comp (baseMap K B) :=
  RingHom.ext fun k ↦ by simp [baseMap]

theorem dualMap_snd {B B' : Type} [CommRing B] [CommRing B'] (σ : B →+* B') (c : DualNumber B) :
    (dualMap σ c).snd = σ c.snd := by
  simp [dualMap]

section Map

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]
  {B B' : Type} [CommRing B] [Algebra (DualNumber K) B] [CommRing B'] [Algebra (DualNumber K) B']

theorem dlogAt_spMap (ρ : B →ₐ[DualNumber K] B') {x : Sp B ⟶ A.left}
    (hx : x ≫ A.hom = spMap (baseMap K B)) {v : epsR K ⟶ A} (hv : IsTangent v) {Wo : A.left.Opens}
    (g : Γ(A.left, Wo)ˣ) (hxWo : ⊤ ≤ x ⁻¹ᵁ Wo) :
    dlogAt (baseMap K B') (spMap (ρ : B →+* B') ≫ x) v Wo g = ρ (dlogAt (baseMap K B) x v Wo g) := by
  rw [dlogAt, dlogAt, baseMap_eq ρ, transl_spMap _ _ x hx v,
    valR_spMap_comp _ _ _ (top_le_transl _ x hx hv hxWo), valR_spMap_comp _ _ _ hxWo, dualMap_snd, map_mul]
  rfl

theorem chartVal_spMap {Z : Scheme.{0}} (m : A.left ⟶ Z) (Ω : Z.Opens) (δ : Γ(Z, Ω) → Γ(Z, Ω))
    {n : ℕ} (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K) (Wo : A.left.Opens) (g : Γ(A.left, Wo)ˣ)
    (ρ : B →ₐ[DualNumber K] B') {x : Sp B ⟶ A.left}
    (hx : x ≫ A.hom = spMap (baseMap K B)) (hxΩ : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ Ω)) (hxWo : ⊤ ≤ x ⁻¹ᵁ Wo)
    (hut : ∀ a, IsTangent (u a)) (f : Γ(Z, Ω)) :
    chartVal m Ω δ u θ Wo g (spMap (ρ : B →+* B') ≫ x) f = ρ (chartVal m Ω δ u θ Wo g x f) := by
  have hxm : ⊤ ≤ (x ≫ m) ⁻¹ᵁ Ω := hxΩ
  have ht : ∀ a, ⊤ ≤ (transl (baseMap K B) x (u a) ≫ m) ⁻¹ᵁ Ω := fun a ↦
    top_le_transl _ x hx (hut a) hxΩ
  have hd : ∀ b, dlogAt (baseMap K B') (spMap (ρ : B →+* B') ≫ x) (u b) Wo g =
      ρ (dlogAt (baseMap K B) x (u b) Wo g) := fun b ↦ dlogAt_spMap ρ hx (hut b) g hxWo
  have htr : ∀ a, transl (baseMap K B') (spMap (ρ : B →+* B') ≫ x) (u a) =
      spMap (dualMap (ρ : B →+* B')) ≫ transl (baseMap K B) x (u a) := fun a ↦ by
    rw [baseMap_eq ρ]; exact transl_spMap _ _ x hx (u a)
  simp only [chartVal, hd, htr, Category.assoc]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [valR_spMap_comp _ _ _ hxm, valR_spMap_comp _ _ _ (ht _), dualMap_snd, map_add (f := _), map_mul, map_sum]
  simp only [RingHom.coe_coe, AlgHom.commutes, baseMap_eq ρ, RingHom.comp_apply]

end Map

theorem isChartPt_spMap : ∀ {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))} {Z : Scheme.{0}} {m : A.left ⟶ Z} {m' : A'.left ⟶ Z} {Ω : Z.Opens} {δ : Γ(Z, Ω) → Γ(Z, Ω)} {n : ℕ} {u : Fin n → (epsR K ⟶ A)} {θ : Matrix (Fin n) (Fin n) K} {Wo : A.left.Opens} {g : Γ(A.left, Wo)ˣ} {B : Type} [CommRing B] [Algebra (DualNumber K) B] {x : Sp B ⟶ A.left} {l : Sp B ⟶ A'.left} (hx : x ≫ A.hom = spMap (baseMap K B)) (hxΩ : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ Ω)) (hxWo : ⊤ ≤ x ⁻¹ᵁ Wo) (hut : ∀ a, IsTangent (u a)) (hl : IsChartPt A' m m' Ω δ u θ Wo g x l) (B' : Type) [CommRing B'] [Algebra (DualNumber K) B'] (ρ : B →ₐ[DualNumber K] B'), IsChartPt A' m m' Ω δ u θ Wo g (spMap (ρ : B →+* B') ≫ x) (spMap (ρ : B →+* B') ≫ l) := by
  intro K _ A _ A' Z m m' Ω δ n u θ Wo g B _ _ x l hx hxΩ hxWo hut hl B' _ _ ρ
  obtain ⟨h1, h2, h3⟩ := hl
  refine ⟨?_, ?_, fun f ↦ ?_⟩
  · rw [Category.assoc, h1, ← Cris.spMap_comp, AlgHom.comp_algebraMap]
  · rw [Category.assoc]
    exact GlobalTheory.FlagMod.le_preimage_comp _ h2
  · rw [Category.assoc, valR_spMap_comp _ _ _ h2, h3 f, chartVal_spMap m Ω δ u θ Wo g ρ hx hxΩ hxWo hut f]
    rfl

end GlobalTheory.CechKS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExponentialOfSemiAbelianFibreLinearChange
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj
open GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix

namespace GlobalTheory.ShFam.Hor.LogCh

theorem isExpAt_mulVec {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (X : Scheme.{0}) (t : SAB H X) (y : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ t.G))
    (M : Matrix (Fin g) (Fin g) ℂ) (hM : IsUnit M.det) (hhol : IsHolTo Set.univ (fun z => (e z).left))
    (he : IsExpAt t y e) : IsExpAt t y (fun w => e (M *ᵥ w)) := by
  have hchain : ∀ w v, IsDerivAt0 (fun u => (e (M *ᵥ u)).left) w v ↔
      IsDerivAt0 (fun u => (e u).left) (M *ᵥ w) v := by
    intro w v
    rw [GlobalTheory.HolHom.isDerivAt0_iff, GlobalTheory.HolHom.isDerivAt0_iff]
    exact GlobalTheory.ShFam.BdArc.LatSec.isDerivAt_comp_iff (GlobalTheory.HolHom.holAt_of_isHolTo hhol (Set.mem_univ 0))
      (Matrix.mulVecLin M).toContinuousLinearMap w v
  have hMi : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hM
  have hiM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hM
  refine ⟨fun v w => ?_, fun w => ?_, fun v hv => ?_⟩
  · simp only [Matrix.mulVec_add]
    exact he.1 _ _
  · simp_rw [hchain]
    exact he.2.1 (M *ᵥ w)
  · obtain ⟨w', hw', huniq⟩ := he.2.2 v hv
    refine ⟨M⁻¹ *ᵥ w', ?_, fun w₂ hw₂ => ?_⟩
    · show IsDerivAt0 (fun u => (e (M *ᵥ u)).left) (M⁻¹ *ᵥ w') v
      rw [hchain, Matrix.mulVec_mulVec, hMi, Matrix.one_mulVec]
      exact hw'
    · have h2 : M *ᵥ w₂ = w' := huniq _ ((hchain w₂ v).1 hw₂)
      rw [← h2, Matrix.mulVec_mulVec, hiM, Matrix.one_mulVec]

end GlobalTheory.ShFam.Hor.LogCh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteFromSpecResidueFieldCompOfIsClosedOfClos
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem isFinite_fromSpecResidueField_comp_of_isClosed_of_closedPoint : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Over (Sp R)), LocallyOfFiniteType X.hom → ∀ x : X.left, X.hom x = closedPoint R → IsClosed ({x} : Set X.left) → IsFinite (X.left.fromSpecResidueField x ≫ X.hom) := by
  intro R _ _ X hX x hx hc
  haveI := hX
  haveI := isClosed_singleton_iff_isClosedImmersion.mp hc
  have hf : LocallyOfFiniteType (X.left.fromSpecResidueField x ≫ X.hom) := inferInstance
  have hpt : ∀ p : Spec (X.left.residueField x), (X.left.fromSpecResidueField x ≫ X.hom) p = closedPoint R := by
    intro p
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply, hx]
  rw [← Spec.map_preimage (X.left.fromSpecResidueField x ≫ X.hom)] at hf hpt ⊢
  rw [IsFinite.SpecMap_iff]
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hf
  generalize Spec.preimage (X.left.fromSpecResidueField x ≫ X.hom) = φ at hf hpt ⊢
  let K := X.left.residueField x
  let p0 : PrimeSpectrum K := ⟨⊥, Ideal.isPrime_bot⟩
  have hker : RingHom.ker φ.hom = maximalIdeal R := by
    have h1 := congrArg PrimeSpectrum.asIdeal (hpt p0)
    have h2 : (Spec.map φ).base p0 = PrimeSpectrum.comap φ.hom p0 := rfl
    rw [show (Spec.map φ) p0 = (Spec.map φ).base p0 from rfl, h2] at h1
    have h3 : Ideal.comap φ.hom ⊥ = (closedPoint R).asIdeal := by simpa [p0] using h1
    exact h3
  let k := ResidueField R
  let ψ : k →+* K := Ideal.Quotient.lift (maximalIdeal R) φ.hom (fun a ha => by
    rw [← RingHom.mem_ker, hker]; exact ha)
  have hφ : φ.hom = ψ.comp (residue R) := by
    ext a; rfl
  rw [hφ] at hf ⊢
  have hψ : ψ.FiniteType := RingHom.FiniteType.of_comp_finiteType hf
  letI : Algebra k K := ψ.toAlgebra
  haveI : Algebra.FiniteType k K := hψ
  have : Module.Finite k K := finite_of_finite_type_of_isJacobsonRing k K
  have hψf : ψ.Finite := this
  exact hψf.comp (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackBaseChangeWithSquareStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGrpPullback_baseChange_with_square : ∀ {S S' T : Scheme.{0}} (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → ∀ t : T ⟶ S', IsGrpPullback ((Over.pullback t).obj G') G (t ≫ f) (pullback.fst G'.hom t ≫ φ) ∧ ∃ φ₂ : (G2 ((Over.pullback t).obj G')).left ⟶ (G2 G).left, IsSquare (pullback.fst G'.hom t ≫ φ) φ₂ := by
  first | exact @GlobalTheory.GrpPB.baseChange_square | exact GlobalTheory.GrpPB.baseChange_square | (intros; apply GlobalTheory.GrpPB.baseChange_square <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralDiscMulCoordsOfCmFieldIntegralStatement
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_disc_mul_coords_of_cmField_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (θ : E) (D : ℕ) (x : Fin 2 → FR E), 0 < D → IsIntegral ℤ θ → (θ - IsCMField.complexConj E θ) ^ 2 = -(D : E) → IsIntegral ℤ ((x 0 : E) * θ + (x 1 : E)) → ∀ j, IsIntegral ℤ ((D : FR E) * x j ^ 2) ∧ IsIntegral ℤ ((D : FR E) * x j) := by
  first | exact @GlobalTheory.HilbFam.isIntegral_coord_of_isIntegral | exact GlobalTheory.HilbFam.isIntegral_coord_of_isIntegral | (intros; apply GlobalTheory.HilbFam.isIntegral_coord_of_isIntegral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelStableIffPulledBackIdentityStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelStable_iff_pulledBack_identity : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (T Y : Scheme.{0}) (s₁ : T ⟶ Sp R) (s : Y ⟶ Sp R) (t : T ⟶ Y) (o₁ : Obj b N s₁) (o : Obj b N s) (m : ObjMap o₁ o t) (B₁ : Over T) [GrpObj B₁] [IsCommMonObj B₁] (B : Over Y) [GrpObj B] [IsCommMonObj B] (θ : B₁.left ⟶ B.left) (ψ₁ : o₁.A ⟶ B₁) (ψ : o.A ⟶ B), IsGrpPullback B₁ B t θ → m.φ ≫ ψ.left = ψ₁.left ≫ θ → (KerStableAt o ψ t ↔ KerStableAt o₁ ψ₁ (𝟙 T)) := by
  first | (exact @GlobalTheory.UPel.HT.ES.kerStableAt_iff_pull) | (exact GlobalTheory.UPel.HT.ES.kerStableAt_iff_pull) | (intros; apply GlobalTheory.UPel.HT.ES.kerStableAt_iff_pull  <;> assumption)
end

