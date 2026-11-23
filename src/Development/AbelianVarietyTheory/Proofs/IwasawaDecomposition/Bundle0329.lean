module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0294
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FbarExistsComplexAutCompEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0174
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
public import ReciprocityTheory.ResidueCardinality.ArtinOntoB
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1252
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0942
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0374
public import Formalism.LocalToGlobal.NumberFieldFamilies.HeckeStd0Of
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0322
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Formalism.LocalToGlobal.HermitianForms.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicFiniteExtContainingCoeffFieldAndNumbe
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section
namespace GlobalTheory.HeckeLocN

theorem exists_finExt_big (D : D7) (pl : PlSide D) (big : D.what₂.places.Pl → Finset ℂ) (w : D.what₂.places.Pl) :
    ∃ F0 : Loc.FinExt (D.what₂.places.resChar w), (∀ x, (plEmb pl).emb w x ∈ F0.1) ∧
      ∀ z ∈ big w, (pl.ι w).symm z ∈ F0.1 := by
  classical
  let c := (plEmb pl).emb w
  let S : Finset (Loc.Om (D.what₂.places.resChar w)) := (big w).image (fun z => (pl.ι w).symm z)
  have h1 := GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range c
  have h2 : FiniteDimensional ℚ_[D.what₂.places.resChar w]
      (IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] (S : Set (Loc.Om (D.what₂.places.resChar w)))) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine ⟨⟨IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] (Set.range c) ⊔
      IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] (S : Set (Loc.Om (D.what₂.places.resChar w))),
      IntermediateField.finiteDimensional_sup _ _⟩, fun x => ?_, fun z hz => ?_⟩
  · exact (le_sup_left (a := IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] (Set.range c)) (b := IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] (S : Set (Loc.Om (D.what₂.places.resChar w))))) (IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩)
  · exact (le_sup_right (a := IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] (Set.range c)) (b := IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] (S : Set (Loc.Om (D.what₂.places.resChar w))))) (IntermediateField.subset_adjoin _ _ (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hz)))

end GlobalTheory.HeckeLocN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPlaceIsTeichmullerLiftFbar
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting

noncomputable section
namespace GlobalTheory.TeichPlace

theorem exists_place_isTeich : ∀ (g : ℕ) [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ), (∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) → ∃ (A : ValuationSubring ℂ) (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g), IsTeich A κ t := by
  intro g _ t ht
  obtain ⟨ι⟩ := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex g
  obtain ⟨κ₀⟩ := GlobalTheory.HeightCounting.nonempty_residueField_unitBall_equiv ι
  obtain ⟨t₀, ht₀, hinj₀⟩ := _root_.GlobalTheory.TeichAt.exists_teich_reindex g (GlobalTheory.HeightCounting.unitBall ι) κ₀ t ht
  obtain ⟨σ, hσ⟩ := _root_.GlobalTheory.TeichGalois.exists_ringEquiv_comp_eq g t t₀ ht hinj₀
  let A : ValuationSubring ℂ := (GlobalTheory.HeightCounting.unitBall ι).comap (σ.symm : ℂ →+* ℂ)
  have hmem : ∀ z : ℂ, z ∈ A ↔ σ.symm z ∈ GlobalTheory.HeightCounting.unitBall ι := fun z => ValuationSubring.mem_comap
  let e : A ≃+* GlobalTheory.HeightCounting.unitBall ι :=
    { toFun := fun a => ⟨σ.symm a, (hmem a).1 a.2⟩
      invFun := fun b => ⟨σ b, (hmem _).2 (by simpa using b.2)⟩
      left_inv := fun a => Subtype.ext (by simp)
      right_inv := fun b => Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  refine ⟨A, (IsLocalRing.ResidueField.mapEquiv e).trans κ₀, fun x => ?_⟩
  have hx : σ.symm (t x) = t₀ x := by rw [← hσ x, RingEquiv.symm_apply_apply]
  obtain ⟨h₀, e₀⟩ := ht₀ x
  refine ⟨(hmem _).2 (hx ▸ h₀), ?_⟩
  refine Eq.trans ?_ e₀
  change κ₀ (IsLocalRing.ResidueField.map (e : A →+* GlobalTheory.HeightCounting.unitBall ι) (IsLocalRing.residue A _)) = _
  rw [IsLocalRing.ResidueField.map_residue]
  congr 2
  exact Subtype.ext hx

end GlobalTheory.TeichPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsResidueHomZmodAtTypePlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TypePlaceResidue

theorem residueHom_zmod : ∀ (D : D7) (kv : Σ k : Fin 2, D.nd.PlG k) (s : SplitPlace D.host.E), s.w = NX.pG D kv →
    Nonempty (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1)) := by
  intro D kv s hs
  have hp := D.host.g_prime kv.1
  haveI : Fact (D.host.g kv.1).Prime := ⟨hp⟩
  have hN := GlobalTheory.TameLabels.normV_eq_of_split hp (D.nd.g_split kv.1) (D.naut.plGw_over kv.1 kv.2)
  have hc : Nat.card (IsLocalRing.ResidueField (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E))) =
      D.host.g kv.1 := by
    rw [ReciprocityTheory.Bridge.ResidueFieldCardinality.card_residue, ← s.card_quot, hs]
    rw [← hN]
    rfl
  haveI : Finite (IsLocalRing.ResidueField (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E))) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact hp.ne_zero)
  letI := Fintype.ofFinite (IsLocalRing.ResidueField (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)))
  have hcF : Fintype.card (IsLocalRing.ResidueField (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E))) =
      D.host.g kv.1 := by rw [Fintype.card_eq_nat_card]; exact hc
  haveI := charP_of_card_eq_prime hcF
  exact ⟨(ZMod.ringEquiv _ hcF).symm.toRingHom.comp (IsLocalRing.residue _)⟩

end GlobalTheory.TypePlaceResidue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSphericalEigensystemFirstLiftBaseLevel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3.EigEx

theorem stdPsi_of_stdFrame {D : D7} {V : HSp D} {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E} {P : principalLevelFrame.RowPsi V n}
    (h : StdFrame hF P) : GlobalTheory.StdFrame.StdPsi hF P := h

theorem isSF_ssetF {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    {R : RealDat3 D A3 Ks} {F : Face3 D A3} (h : R.WeakCharacterisation F) :
    GlobalTheory.Hk3.IsSF R.toRealDat (SsetF R.toRealDat A3.A.μ0) := by
  classical
  have hQ : R.Q A3.A.μ0 = ∅ := (GlobalTheory.GoodPrimes.good_primes R.toRealDat F.lv2 h.base.lev).1
  have hS : R.Sb = R.Pg := h.allPl
  intro v
  unfold SsetF
  rw [hQ, hS, Finset.union_empty, Finset.mem_image]
  refine exists_congr fun PP => and_congr_right fun _ => ?_
  rw [HeightOneSpectrum.ext_iff]
  rfl

theorem exists_hasEig : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ π : D.what₂.FT, ∃ c, HasEig R F Y π c := by
  intro _ _ _ _ D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH _ hgen π
  have hμ : Y.tupT D.what₂.mu0 = A3.A.μ0 := by rw [← Y.tup0, Y.tupT_tup]
  unfold HasEig
  rw [hμ]
  exact _root_.GlobalTheory.RowEig.row_type_eig R.toRealDat F.lv2 hH.ok.ok2 (GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hH.aux.ex).1 hgen _
    (isSF_ssetF hP.char) Y.hF Y.PY Y.PW (stdPsi_of_stdFrame Y.stdPsi.1) (fun i => stdPsi_of_stdFrame (Y.stdPsi.2 i)) _
    (principalLevelFrame.rowRepR_occ R.θ (Y.eFT π)) ⟨0, Y.hm⟩

end GlobalTheory.Mem.R3.EigEx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitPlaceWPlGw
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FixedPlaceOverType

theorem exists_splitPlace_w_plGw : ∀ (D : D7) (k : Fin 2) (v : D.nd.PlG k), ∃ s : SplitPlace D.host.E, s.w = D.naut.plGw k v :=
  fun D k v => GlobalTheory.SplitPlaceOfFixed.exists_splitPlace_plGw D ⟨k, v⟩

end GlobalTheory.FixedPlaceOverType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FifteenNotMemAndDeltaInertiaOrderDividesFifteenP
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.Member.DeltaTame

theorem delta_tame_and_15 : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw) (P : PlE D.host), P ∈ T.pD i →
    ((15 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P → ∀ σ ∈ Ine (F := D.host.E) A,
      ∃ N : ℕ, T.delta i σ ^ (15 ^ N) = 1 := by
  intro D T i P hP
  refine ⟨?_, ?_⟩
  · intro h15
    have hmem : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := Ideal.absNorm_mem _
    have hmod := T.delta_tame i P hP
    have hdecomp : Ideal.absNorm P.asIdeal = 15 * (Ideal.absNorm P.asIdeal / 15) + 1 := by
      have := Nat.div_add_mod (Ideal.absNorm P.asIdeal) 15
      omega
    rw [hdecomp] at hmem
    push_cast at hmem h15
    have h1 : (1 : 𝓞 D.host.E) ∈ P.asIdeal := by
      have hm2 : (15 : 𝓞 D.host.E) * ((Ideal.absNorm P.asIdeal / 15 : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal :=
        P.asIdeal.mul_mem_right _ h15
      have := P.asIdeal.sub_mem hmem hm2
      simpa using this
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  · intro A hA σ hσ
    have h15 := T.delta_15 i P hP A hA
    have hfin : Finite ((Ine (F := D.host.E) A).map (T.delta i)) :=
      Nat.finite_of_card_ne_zero (by rw [h15]; norm_num)
    have hpow := pow_card_eq_one' (G := (Ine (F := D.host.E) A).map (T.delta i))
      (x := ⟨T.delta i σ, Subgroup.mem_map_of_mem _ hσ⟩)
    rw [h15] at hpow
    refine ⟨1, ?_⟩
    have := congrArg Subtype.val hpow
    simpa using this

end GlobalTheory.Member.DeltaTame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalLocalisationSpaceAll
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.FinDimVProof

theorem finDimV_all : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (B : LocBase0 H what₂), FinDimV B := by
  intro R H what₂ B j w
  classical
  have hfin : (Formalism.L2.Fam.NPC.LatticeFinitenessFree.latJ (what₂ := what₂) j w).Finite :=
    Set.Finite.subset ((what₂.MtLat (what₂.muTw w) j).gen.finite_toSet.preimage
      ((Formalism.L2.Fam.NPC.LatticeFinitenessFree.jMt_injective (what₂.muTw w) j).injOn)) fun x hx => hx
  have hs := Formalism.L2.Fam.NPC.LatticeFinitenessFree.span_iV (B := B) j w
  exact Module.finite_def.2 ⟨(hfin.image (B.iV j w)).toFinset, by simpa using hs⟩

end GlobalTheory.FinDimVProof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosets
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd

namespace GlobalTheory.SatInd.CosetFin

theorem finite_cosets {G H : Type} [Group G] [Group H] (φ : G →* H) (H' : Subgroup H) (K : Subgroup H')
    (U : Subgroup G) (p : G → Prop) (F : Set (H' ⧸ K)) (hF : F.Finite)
    (hp : ∀ x, p x → ∃ hx : φ x ∈ H', ((⟨φ x, hx⟩ : H') : H' ⧸ K) ∈ F)
    (hU : ∀ x y, p x → p y → ∀ hz : φ (x⁻¹ * y) ∈ H', (⟨φ (x⁻¹ * y), hz⟩ : H') ∈ K → x⁻¹ * y ∈ U) :
    Set.Finite {c : G ⧸ U | ∃ x : G, (x : G ⧸ U) = c ∧ p x} := by
  have hsub : {c : G ⧸ U | ∃ x : G, (x : G ⧸ U) = c ∧ p x} ⊆
      ⋃ d ∈ F, {c : G ⧸ U | ∃ x : G, (x : G ⧸ U) = c ∧ p x ∧
        ∃ hx : φ x ∈ H', ((⟨φ x, hx⟩ : H') : H' ⧸ K) = d} := by
    rintro c ⟨x, hc, hx⟩
    obtain ⟨h1, h2⟩ := hp x hx
    exact Set.mem_biUnion h2 ⟨x, hc, hx, h1, rfl⟩
  refine (hF.biUnion fun d _ => Set.Subsingleton.finite ?_).subset hsub
  rintro c ⟨x, rfl, hx, hx1, hx2⟩ c' ⟨y, rfl, hy, hy1, hy2⟩
  have hk := QuotientGroup.eq.1 (hx2.trans hy2.symm)
  have hz : φ (x⁻¹ * y) ∈ H' := by
    rw [map_mul, map_inv]; exact H'.mul_mem (H'.inv_mem hx1) hy1
  refine QuotientGroup.eq.2 (hU x y hx hy hz ?_)
  convert hk using 1
  apply Subtype.ext
  simp

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem trivOutside_mul {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {x y : GA L n}
    (hx : TrivOutside T x) (hy : TrivOutside T y) : TrivOutside T (x * y) := by
  intro w hw
  have : ((x * y).1 : Matrix (Fin n) (Fin n) (AL L)) =
      (x.1 : Matrix (Fin n) (Fin n) (AL L)) * (y.1 : Matrix (Fin n) (Fin n) (AL L)) := rfl
  rw [this, Matrix.map_mul, hx w hw, hy w hw, mul_one]

theorem trivOutside_inv {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {x : GA L n}
    (hx : TrivOutside T x) : TrivOutside T x⁻¹ := by
  intro w hw
  have h1 : (((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
    rfl
  have h2 := congrArg (fun M => M.map (compAt L w)) h1
  simp only [Matrix.map_mul, hx w hw, mul_one] at h2
  rw [h2, Matrix.map_one _ (map_zero _) (map_one _)]

variable {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}

def locHom (D : InertDatum L n v w) : GAf L n →* GL (Fin n) (w.adicCompletion L) :=
  MonoidHom.mk' D.loc fun x y => by
    simp only [InertDatum.loc, Subgroup.coe_mul, map_mul, mul_assoc, mul_inv_cancel_left]

theorem entries_int {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] {σ : K →+* K}
    {g : GU σ n} (hg : g ∈ KU σ n) (i j : Fin n) :
    ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ intL K := by
  obtain ⟨-, k, hk⟩ := hg
  have hk' : bc (n := Fin n) (intL K).subtype k = (g : GL (Fin n) K) := hk
  rw [← hk']
  exact ((k : Matrix (Fin n) (Fin n) (intL K)) i j).2

theorem finite_inert_support : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w), (∀ s : GU Dv.σw n, Set.Finite {c : GU Dv.σw n ⧸ KU Dv.σw n | ∃ a ∈ KU Dv.σw n, ((a * s : GU Dv.σw n) : GU Dv.σw n ⧸ KU Dv.σw n) = c}) → (∀ z : GAf L n, TrivOutside {v} z → (∀ i j, ((Dv.loc z : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j ∈ intL (w.adicCompletion L)) → z ∈ Umax L n) → ∀ (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ h ∈ Hecke ℂ (KU Dv.σw n), Set.Finite {c : GAf L n ⧸ U | ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x ∧ Dv.hval h (Dv.loc x) ≠ 0} := by
  intro L _ _ _ n v w Dv hfin hint U hU h hh
  obtain ⟨-, S, hS⟩ := hh
  refine finite_cosets (locHom Dv) (GU Dv.σw n) (KU Dv.σw n) U
    (fun x => TrivOutside {v} x ∧ Dv.hval h (Dv.loc x) ≠ 0) _
    (S.finite_toSet.biUnion fun s _ => hfin s) ?_ ?_
  · rintro x ⟨-, hx⟩
    have hm : Dv.loc x ∈ GU Dv.σw n := by
      by_contra hm
      exact hx (dif_neg hm)
    have hne : h ⟨Dv.loc x, hm⟩ ≠ 0 := by
      intro h0
      exact hx ((dif_pos hm).trans h0)
    obtain ⟨s, hs, a, b, e⟩ := hS _ hne
    refine ⟨hm, Set.mem_biUnion hs ⟨a, a.2, ?_⟩⟩
    have e' : (⟨locHom Dv x, hm⟩ : GU Dv.σw n) = (a : GU Dv.σw n) * s * b := e
    rw [e']
    exact (QuotientGroup.mk_mul_of_mem _ b.2).symm
  · rintro x y ⟨hx, -⟩ ⟨hy, -⟩ hz hk
    have ht : TrivOutside {v} (x⁻¹ * y) := trivOutside_mul (trivOutside_inv hx) hy
    exact (hU _ ht).2 (hint _ ht fun i j => entries_int hk i j)

end GlobalTheory.SatInd.CosetFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyIrreducible
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AutUnr

section Fixed
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem exists_fixed_of_mem_biSup (ρ : Representation ℂ (GQ L n) W) (K : Set (GAf L n))
    (t : Finset (Submodule ℂ (GAf L n → W))) :
    (∀ S ∈ t, NG.IsIrrRep ρ S) → ∀ f ∈ ⨆ S ∈ t, S, f ≠ 0 → (∀ κ ∈ K, NG.rt L n κ f = f) →
      ∃ S ∈ t, ∃ g ∈ S, g ≠ 0 ∧ ∀ κ ∈ K, NG.rt L n κ g = g := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro _ f hf hf0 _
    simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hf
    exact absurd hf hf0
  | insert S t hS ih =>
    intro ht f hf hf0 hfix
    have ht' : ∀ S' ∈ t, NG.IsIrrRep ρ S' := fun S' h => ht S' (Finset.mem_insert_of_mem h)
    have hSi := ht S (Finset.mem_insert_self _ _)
    have hNst : ∀ h, ∀ g ∈ ⨆ S' ∈ t, S', NG.rt L n h g ∈ ⨆ S' ∈ t, S' := by
      intro h
      have hle : (⨆ S' ∈ t, S') ≤ (⨆ S' ∈ t, S').comap (NG.rt L n h) := by
        refine iSup₂_le fun S' hS' g hg => ?_
        exact (le_iSup₂ (f := fun (S'' : Submodule ℂ (GAf L n → W)) (_ : S'' ∈ t) => S'') S' hS')
          ((ht' S' hS').1.stable h g hg)
      exact fun g hg => hle hg
    rw [Finset.iSup_insert] at hf
    by_cases hd : S ⊓ (⨆ S' ∈ t, S') = ⊥
    · obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hf
      have hfa : ∀ κ ∈ K, NG.rt L n κ a = a ∧ NG.rt L n κ b = b := by
        intro κ hκ
        have e := hfix κ hκ
        rw [map_add (f := _)] at e
        have h1 : NG.rt L n κ a - a = b - NG.rt L n κ b := by
          rw [sub_eq_sub_iff_add_eq_add, e, add_comm]
        have hm : NG.rt L n κ a - a ∈ S ⊓ (⨆ S' ∈ t, S') :=
          ⟨S.sub_mem (hSi.1.stable κ a ha) ha, h1 ▸ Submodule.sub_mem _ hb (hNst κ b hb)⟩
        rw [hd, Submodule.mem_bot] at hm
        refine ⟨sub_eq_zero.1 hm, ?_⟩
        rw [hm] at h1
        exact (sub_eq_zero.1 h1.symm).symm
      by_cases ha0 : a = 0
      · subst ha0
        rw [zero_add] at hf0
        obtain ⟨S', hS', g, hg, hg0, hgf⟩ := ih ht' b hb hf0 fun κ hκ => (hfa κ hκ).2
        exact ⟨S', Finset.mem_insert_of_mem hS', g, hg, hg0, hgf⟩
      · exact ⟨S, Finset.mem_insert_self _ _, a, ha, ha0, fun κ hκ => (hfa κ hκ).1⟩
    · have hsub : NG.IsSubrep ρ (S ⊓ (⨆ S' ∈ t, S')) :=
        ⟨inf_le_left.trans hSi.1.le, fun h g hg => ⟨hSi.1.stable h g hg.1, hNst h g hg.2⟩⟩
      have heq : S ⊓ (⨆ S' ∈ t, S') = S := (hSi.2.2 _ hsub inf_le_left).resolve_left hd
      have hSN : S ≤ ⨆ S' ∈ t, S' := heq ▸ inf_le_right
      have hfN : f ∈ ⨆ S' ∈ t, S' := (sup_le hSN le_rfl) hf
      obtain ⟨S', hS', g, hg, hg0, hgf⟩ := ih ht' f hfN hf0 hfix
      exact ⟨S', Finset.mem_insert_of_mem hS', g, hg, hg0, hgf⟩

theorem exists_fixed_of_isoTyp (ρ : Representation ℂ (GQ L n) W) {S : Submodule ℂ (GAf L n → W)}
    (hS : ∀ h, ∀ f ∈ S, NG.rt L n h f ∈ S) (K : Set (GAf L n)) {f : GAf L n → W} (hf : f ∈ NG.isoTyp ρ S)
    (hf0 : f ≠ 0) (hfix : ∀ κ ∈ K, NG.rt L n κ f = f) : ∃ g ∈ S, g ≠ 0 ∧ ∀ κ ∈ K, NG.rt L n κ g = g := by
  unfold NG.isoTyp at hf
  obtain ⟨s, hs, hfs⟩ := Submodule.mem_sSup_iff_exists_finset.1 hf
  obtain ⟨S', hS', g, hg, hg0, hgf⟩ :=
    exists_fixed_of_mem_biSup ρ K s (fun S' h => (hs h).1) f hfs hf0 hfix
  obtain ⟨T, hT⟩ := (hs hS').2
  refine ⟨(T.symm ⟨g, hg⟩ : S), (T.symm ⟨g, hg⟩).2, ?_, fun κ hκ => ?_⟩
  · intro h0
    apply hg0
    have h1 : T.symm ⟨g, hg⟩ = 0 := Subtype.ext h0
    have h2 := congrArg T h1
    rw [LinearEquiv.apply_symm_apply, map_zero] at h2
    exact congrArg Subtype.val h2
  · set a := T.symm ⟨g, hg⟩
    have e := hT κ a ⟨NG.rt L n κ (a : GAf L n → W), hS κ _ a.2⟩ rfl
    have hTa : ((T a : _) : GAf L n → W) = g := by simp [a]
    rw [hTa, hgf κ hκ] at e
    have e2 : T ⟨NG.rt L n κ (a : GAf L n → W), hS κ _ a.2⟩ = T a := Subtype.ext (e.trans hTa.symm)
    exact congrArg Subtype.val (T.injective e2)

end Fixed

end GlobalTheory.AutUnr

namespace GlobalTheory.AutUnr

theorem mem_placesOver_of_overPl {D : D7} {p : ℕ} {w w' : PlE D.host}
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))} (hw : NG.OverPl w v) (hw' : NG.OverPl w' v)
    (h : w' ∈ placesOver D.host.E p) : w ∈ placesOver D.host.E p := by
  have h1 : ((p : ℕ) : 𝓞 (maximalRealSubfield D.host.E)) ∈ v.asIdeal := by
    rw [← hw', Ideal.mem_comap, map_natCast]; exact h
  rw [← hw, Ideal.mem_comap, map_natCast] at h1
  exact h1

theorem exists_splitPlace_eq (D : D7) (w : PlE D.host) (hw : IsSplitPl D.host w) :
    ∃ s : SplitPlace D.host.E, s.w = w := by
  obtain ⟨s, -, h, -⟩ := GlobalTheory.SplitConjPlace.splitEx_all D w hw
  refine ⟨GlobalTheory.SplitConjPlace.conjSP s, HeightOneSpectrum.ext (Ideal.ext fun x => ?_)⟩
  rw [GlobalTheory.SplitConjPlace.mem_conj_w]
  refine (h x _ ?_).symm
  rw [IsCMField.coe_ringOfIntegersComplexConj]
  exact D.host.φ₀.injective (by
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])


end GlobalTheory.AutUnr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianColumnChoicesOfFormsLevelsClassesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianColumnChoices_of_formsLevelsClasses : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Ch : B.Word → ℕ → Type) (chOf : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch u) (chOf u)) (hf : ∀ u i, Finite (Ch u i)) (hm : ∀ u, Nonempty (Unique (Ch u B.R.m))), (∀ u, I.StdF l Z u (F u)) → ∃ lev0 lev cls vT Fv, CarH (D := (I.rec7 l Z)) { lev0 := lev0, Ch := Ch, ChFin := hf, Ch_m := hm, chOf := chOf, lev := lev, cls := cls, vT := vT, Fv := Fv } F := by
  first | exact @GlobalTheory.Mem.Col2.TC.hermColsCh_of_forms | exact GlobalTheory.Mem.Col2.TC.hermColsCh_of_forms | (intros; apply GlobalTheory.Mem.Col2.TC.hermColsCh_of_forms <;> assumption)
end

