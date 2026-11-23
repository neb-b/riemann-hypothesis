module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2128
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2833
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2814
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2798
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2829
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2812
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2816
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2637
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2815
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2823
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1622
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1636
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2788
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1597
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1655
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateRowBoundOfDictionary
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0918
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0971
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianNegTraceZeroInvHermitianUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2819
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2817
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedSpaceClosedFibreFinitelyGeneratedExt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem connectedSpace_pullback_of_finitelyGenerated_residue :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (S : Scheme.{0}) (π : S ⟶ Sp R),
      IsProper π → Surjective π → Function.Bijective π.appTop.hom →
      ∀ (K : Type) [Field K] (κ : ResidueField R →+* K) (L : Subfield K) (hL : ∀ x, κ x ∈ L) (n : ℕ) (c : Fin n → K),
        L = Subfield.closure (Set.range κ ∪ Set.range c) →
        ConnectedSpace (pullback π (spMap ((κ.codRestrict L hL).comp (residue R))) : Scheme.{0}) := by
  intro R _ _ _ S π hprop hsurj hbij K _ κ L hL n c hLc
  haveI := hprop
  haveI := hsurj
  have hc : ∀ j, c j ∈ L := fun j => hLc ▸ Subfield.subset_closure (Or.inr ⟨j, rfl⟩)
  set A := MvPolynomial (Fin n) R
  set ιC : R →+* A := MvPolynomial.C with hC
  set β : R →+* L := (κ.codRestrict L hL).comp (residue R) with hβ
  set φ : A →+* L := MvPolynomial.eval₂Hom β (fun j => ⟨c j, hc j⟩) with hφ
  have hφC : φ.comp ιC = β := by
    refine RingHom.ext fun r => ?_
    show MvPolynomial.eval₂ β (fun j => (⟨c j, hc j⟩ : L)) (MvPolynomial.C r) = β r
    exact MvPolynomial.eval₂_C _ _ _
  have hx : spMap β = spMap φ ≫ spMap ιC := by
    rw [← hφC]
    show Spec.map (CommRingCat.ofHom (φ.comp ιC)) = Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom ιC)
    rw [← Spec.map_comp]; rfl

  have hdiv : ∀ x : L, ∃ a b : A, φ b ≠ 0 ∧ φ b * x = φ a := by
    have hsub : Subring.closure (Set.range κ ∪ Set.range c) ≤ (φ.range).map L.subtype := by
      rw [Subring.closure_le]
      rintro y (⟨z, rfl⟩ | ⟨j, rfl⟩)
      · obtain ⟨r, rfl⟩ := residue_surjective z
        exact ⟨β r, ⟨MvPolynomial.C r, MvPolynomial.eval₂_C _ _ _⟩, rfl⟩
      · exact ⟨⟨c j, hc j⟩, ⟨MvPolynomial.X j, MvPolynomial.eval₂_X _ _ _⟩, rfl⟩
    intro x
    have hx' : (x : K) ∈ Subfield.closure (Set.range κ ∪ Set.range c) := hLc ▸ x.2
    obtain ⟨y, hy, z, hz, hyz⟩ := Subfield.mem_closure_iff.1 hx'
    obtain ⟨y', ⟨a, rfl⟩, rfl⟩ := hsub hy
    obtain ⟨z', ⟨b, rfl⟩, rfl⟩ := hsub hz
    by_cases hb : φ b = 0
    · refine ⟨0, 1, by simp, ?_⟩
      have : (x : K) = 0 := by rw [← hyz]; simp [hb]
      have : x = 0 := Subtype.ext this
      simp [this]
    · refine ⟨a, b, hb, ?_⟩
      apply Subtype.ext
      have hb' : ((φ b : L) : K) ≠ 0 := fun h => hb (Subtype.ext h)
      simp only [Subfield.coe_mul, L.subtype_apply] at hyz ⊢
      rw [← hyz]; field_simp
  have hstalk : φ.SurjectiveOnStalks := by
    refine RingHom.surjectiveOnStalks_of_exists_div fun x => ?_
    obtain ⟨a, b, hb, e⟩ := hdiv x
    exact ⟨a, b, (isUnit_iff_ne_zero).2 hb, e⟩
  haveI hpre : IsPreimmersion (spMap φ) := by
    rw [IsPreimmersion.SpecMap_iff]
    refine ⟨?_, hstalk⟩
    haveI : Subsingleton (PrimeSpectrum L) := inferInstance
    exact Topology.IsEmbedding.of_subsingleton _

  set π' : pullback π (spMap ιC) ⟶ Sp A := pullback.snd π (spMap ιC) with hπ'
  have hflat : Flat (spMap ιC) := by
    refine Flat.SpecMap_iff.2 ?_
    show (algebraMap R A).Flat
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  have hbij' : ∀ V : (Sp A).Opens, Function.Bijective (π'.app V).hom :=
    GlobalTheory.Mum.app_bijective_of_flat_baseChange R S (Sp A) _ π (spMap ιC) _ _ inferInstance inferInstance
      hbij hflat (IsPullback.of_hasPullback π (spMap ιC)).flip
  obtain ⟨q⟩ : Nonempty (PrimeSpectrum L) := inferInstance
  have hconn := _root_.GlobalTheory.ZConn.isPreconnected_fibre _ _ π' inferInstance inferInstance hbij' (spMap φ q)
  have hrange : Set.range (spMap φ) = {spMap φ q} := by
    ext y
    constructor
    · rintro ⟨q', rfl⟩; rw [Subsingleton.elim q' q]; rfl
    · rintro rfl; exact ⟨q, rfl⟩
  set f := pullback.fst π' (spMap φ) with hf
  have hfr : Set.range f = {s | π' s = spMap φ q} := by
    rw [hf, Scheme.Pullback.range_fst, hrange]; rfl
  have hP : PreconnectedSpace ↥(pullback π' (spMap φ)) := by
    refine ⟨?_⟩
    rw [← f.isEmbedding.isInducing.isPreconnected_image, Set.image_univ, hfr]
    exact hconn
  have e : pullback π (spMap β) ≅ pullback π' (spMap φ) :=
    pullback.congrHom rfl hx ≪≫ (pullbackLeftPullbackSndIso π (spMap ιC) (spMap φ)).symm
  obtain ⟨z, -⟩ := (pullback.snd π (spMap β)).surjective q
  haveI : ConnectedSpace ↥(pullback π' (spMap φ)) := ConnectedSpace.mk ⟨e.hom z⟩
  exact (Scheme.homeoOfIso e).symm.surjective.connectedSpace (Scheme.homeoOfIso e).symm.continuous

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousHeckeCharacterFinitePart
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeckeUChar

open IsDedekindDomain Topology

theorem toFinE_symm_mem_OhE {D : D7} (t : FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (ht : ∀ w : HeightOneSpectrum (𝓞 D.host.E), t w ∈ w.adicCompletionIntegers D.host.E) :
    (GlobalTheory.BotFormula.toFinE D).symm t ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D := by
  have hι : ∀ (x : D.host.E) (a : FiniteAdeleRing (𝓞 ℚ) ℚ), (GlobalTheory.BotFormula.toFinE D).toRingHom (x ⊗ₜ[ℚ] a) =
      algebraMap D.host.E _ x * GlobalTheory.AdeleBaseChange.adMap ℚ D.host.E a := fun x a => by
    show GlobalTheory.LFun.toFinAd ℚ D.host.E (a ⊗ₜ x) = _
    rw [GlobalTheory.LFun.toFinAd_tmul, mul_comm]
  refine GlobalTheory.AdeleBaseChange.mem_int_of_map (ι := (GlobalTheory.BotFormula.toFinE D).toRingHom) hι ?_
  change (GlobalTheory.BotFormula.toFinE D) ((GlobalTheory.BotFormula.toFinE D).symm t) ∈ _
  rw [RingEquiv.apply_symm_apply]
  exact ht

theorem continuous_finChar {D : D7} {N : ℕ} (c : HeckeU D N) : Continuous (finChar c) := by
  refine continuous_of_continuousAt_one (finChar c) ?_
  obtain ⟨m, hm, hc⟩ := c.cont
  have hcont : Continuous (finIdl D) :=
    Continuous.units_map _ (GlobalTheory.DefU.ClassFin.continuous_finAdEquiv.comp (GlobalTheory.Member.continuous_finPart D))
  set W : Set (FiniteAdeleRing (𝓞 D.host.E) D.host.E) :=
    {z | ∀ w : HeightOneSpectrum (𝓞 D.host.E), z w ∈ w.adicCompletionIntegers D.host.E} with hW
  have hWo : IsOpen W := RestrictedProduct.isOpen_forall_mem fun v => Valued.isOpen_valuationSubring _
  set k : FiniteAdeleRing (𝓞 D.host.E) D.host.E := algebraMap D.host.E _ (m : D.host.E)⁻¹ with hk
  have h1 : Continuous fun x : (AE D)ˣ => ((finIdl D x : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) :
      FiniteAdeleRing (𝓞 D.host.E) D.host.E) := Units.continuous_val.comp hcont
  have h2 : Continuous fun x : (AE D)ˣ => (((finIdl D x)⁻¹ : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) :
      FiniteAdeleRing (𝓞 D.host.E) D.host.E) := Units.continuous_coe_inv.comp hcont
  have h3 : Continuous fun x : (AE D)ˣ => (((finIdl D x : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) :
      FiniteAdeleRing (𝓞 D.host.E) D.host.E) - 1) * k := (h1.sub continuous_const).mul continuous_const
  set V : Set (AE D)ˣ := ((fun x : (AE D)ˣ => ((finIdl D x : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) :
      FiniteAdeleRing (𝓞 D.host.E) D.host.E)) ⁻¹' W ∩
      (fun x : (AE D)ˣ => (((finIdl D x)⁻¹ : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) :
      FiniteAdeleRing (𝓞 D.host.E) D.host.E)) ⁻¹' W ∩
      (fun x : (AE D)ˣ => (((finIdl D x : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) :
      FiniteAdeleRing (𝓞 D.host.E) D.host.E) - 1) * k) ⁻¹' W) with hVdef
  have hV : IsOpen V :=
    ((hWo.preimage h1).inter (hWo.preimage h2)).inter (hWo.preimage h3)
  have hzero : (0 : FiniteAdeleRing (𝓞 D.host.E) D.host.E) ∈ W := fun w => zero_mem _
  have hone : (1 : FiniteAdeleRing (𝓞 D.host.E) D.host.E) ∈ W := fun w => one_mem _
  have h1V : (1 : (AE D)ˣ) ∈ V := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show ((finIdl D 1 : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) : FiniteAdeleRing (𝓞 D.host.E) D.host.E) ∈ W
      rw [map_one, Units.val_one]; exact hone
    · show (((finIdl D 1)⁻¹ : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) : FiniteAdeleRing (𝓞 D.host.E) D.host.E) ∈ W
      rw [map_one, inv_one, Units.val_one]; exact hone
    · show (((finIdl D 1 : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) : FiniteAdeleRing (𝓞 D.host.E) D.host.E) - 1) * k ∈ W
      rw [map_one, Units.val_one, sub_self, zero_mul]; exact hzero
  have hmE : (m : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have key : ∀ x ∈ V, finChar c x = 1 := by
    rintro x ⟨⟨hx1, hx2⟩, hx3⟩
    set u := finIdl D x with hu
    have hy : Formalism.MainNotions.StandardLatticesGL3.IntU D (finY D x) := by
      refine ⟨?_, ?_⟩
      · rw [coe_finY, ← coe_finIdl]
        exact toFinE_symm_mem_OhE _ hx1
      · rw [← map_inv, coe_finY, ← coe_finIdl, map_inv]
        exact toFinE_symm_mem_OhE _ hx2
    have hs : ∃ s ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D, ((finY D x : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) : Formalism.MainNotions.StandardLatticesGL3.AE D) - 1 =
        (m : Formalism.MainNotions.StandardLatticesGL3.AE D) * s := by
      refine ⟨(GlobalTheory.BotFormula.toFinE D).symm ((((u : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) :
        FiniteAdeleRing (𝓞 D.host.E) D.host.E) - 1) * k), toFinE_symm_mem_OhE _ hx3, ?_⟩
      rw [coe_finY, ← coe_finIdl, ← hu, ← map_natCast (GlobalTheory.BotFormula.toFinE D).symm m, ← map_mul, ← map_one
        (GlobalTheory.BotFormula.toFinE D).symm, ← map_sub]
      congr 1
      have hmk : (m : FiniteAdeleRing (𝓞 D.host.E) D.host.E) * k = 1 := by
        rw [hk, ← map_natCast (algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E)) m, ← map_mul,
          mul_inv_cancel₀ hmE, map_one]
      rw [mul_comm, mul_assoc, mul_comm k, hmk, mul_one]
    have hf := hc _ hy hs
    exact Circle.ext (by rw [coe_finChar, hf, Units.val_one, Circle.coe_one])
  show Filter.Tendsto (finChar c) (𝓝 1) (𝓝 (finChar c 1))
  rw [map_one]
  exact tendsto_nhds_of_eventually_eq (Filter.eventually_of_mem (hV.mem_nhds h1V) key)

end GlobalTheory.HeckeUChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomDictionaryFramesExponentsKernel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotDict

open GlobalTheory.ChainFr

theorem gBig_three {P Q R S : GP} (hP : GBig P) (hQ : GBig Q) (hR : GBig R)
    (h : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Lc.Is μ₀ → P G μ₀ C x b → Q G μ₀ C x b → R G μ₀ C x b → S G μ₀ C x b) : GBig S := by
  obtain ⟨CF1, h1⟩ := hP
  obtain ⟨CF2, h2⟩ := hQ
  obtain ⟨CF3, h3⟩ := hR
  refine ⟨max CF1 (max CF2 CF3), fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, g1⟩ := h1 ε CF ((le_max_left _ _).trans hCF)
  obtain ⟨C2, x2, g2⟩ := h2 ε CF (((le_max_left _ _).trans (le_max_right _ _)).trans hCF)
  obtain ⟨C3, x3, g3⟩ := h3 ε CF (((le_max_right _ _).trans (le_max_right _ _)).trans hCF)
  refine ⟨max C1 (max C2 C3), max x1 (max x2 x3), fun C hC D large₂ he hx hr T Lc μ₀ hμ G => h G μ₀ _ _ _ hμ ?_ ?_ ?_⟩
  · exact g1 C ((le_max_left _ _).trans hC) D large₂ he ((le_max_left _ _).trans hx) hr T Lc μ₀ hμ G
  · exact g2 C (((le_max_left _ _).trans (le_max_right _ _)).trans hC) D large₂ he
      (((le_max_left _ _).trans (le_max_right _ _)).trans hx) hr T Lc μ₀ hμ G
  · exact g3 C (((le_max_right _ _).trans (le_max_right _ _)).trans hC) D large₂ he
      (((le_max_right _ _).trans (le_max_right _ _)).trans hx) hr T Lc μ₀ hμ G

theorem bottom_dictionary : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∃ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (a b : D.what₂.Tau → ℚ), (∀ τ, Formalism.UG.HasSignature (gramAt D A τ) A.rank 0) ∧ (∀ τ, Formalism.UG.HasSignature (gramAt D A' τ) A'.rank 0) ∧ (∀ τ, Formalism.UG.HasSignature (gramAt D WW τ) WW.rank 0) ∧ ∀ t : T, IsTriple A A' WW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) ∧ (∀ τ, HasInfExp D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) τ (a τ) ∧ HasInfExp D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) τ (b τ)) ∧ IsFinF W.ψ W.θ true FA FW (X.f t) ∧ IsFinF W.ψ W.θ false FA' FW (X.f' t) ∧ (∀ P g h, thetaKO (X.ω t) g h (fockF W.ψ W.θ true FA FW (X.f t) P) = X.ker W.ψ W.θ t P h g) ∧ ∀ P g h, thetaKO (X.ω' t) g h (fockF W.ψ W.θ false FA' FW (X.f' t) P) = X.ker' W.ψ W.θ t P h g := by
  refine gBig_three _root_.GlobalTheory.BotRankSize.bottom_ranks _root_.GlobalTheory.BotDict.bottom_infExp_gap _root_.GlobalTheory.BotRam.bottom_ram ?_
  intro D T Lc sc G μ₀ C x b _ hsz hinf hram W i j A A' WW X hX
  obtain ⟨a, b, hab⟩ := hinf W i j
  have hs := hX.std
  have hs' := hX.std'
  have hw := hX.stdW
  have hr : WW.rank = SqNum.botBig D i j + SqNum.botSmall D i j := by rw [← hX.is.rank, hX.rank, hX.rank']
  refine ⟨stdFr A hs.1, stdFr A' hs'.1, stdFr WW hw.1, a, b, hasSignature_of_gram_eq_one hs.1,
    hasSignature_of_gram_eq_one hs'.1, hasSignature_of_gram_eq_one hw.1, fun t => ⟨?_, fun τ => ⟨(hab t τ).1, (hab t τ).2.1⟩,
    _root_.GlobalTheory.BotDict.fst_isFinF X _ _ _ _ _ _ hs hw hX.is t, _root_.GlobalTheory.BotDict.isFinF_snd_std X _ _ _ _ _ _ hs' hw hX.is t, ?_, ?_⟩⟩
  · refine
      { hecA := (hX.is.weil' t).hecS
        hecB := (hX.is.weil t).hecS
        resA := (hX.is.weil' t).resS
        resB := (hX.is.weil t).resS
        rank := hX.is.rank.symm
        even := by rw [hr]; exact (hsz i j).1
        sig := ⟨0, 0, fun τ => ⟨by simpa using hasSignature_of_gram_eq_one hs.1 τ, by simpa using hasSignature_of_gram_eq_one hs'.1 τ,
          by simpa using hasSignature_of_gram_eq_one hw.1 τ⟩, by rw [hX.rank, hX.rank']; have := (hsz i j).2; omega,
          by rw [hX.rank']; have := (hsz i j).2.2; omega⟩
        gap := fun τ => ⟨a τ, b τ, (hab t τ).1, (hab t τ).2.1, by rw [hr]; exact (hab t τ).2.2⟩
        ram := hram W i j A A' WW X hX t }
  · intro P g h
    have e1 : (GlobalTheory.SquareComm.frSgn true (stdFr A hs.1)).cart = fun τ => -X.rA.s τ :=
      funext fun τ => by rw [cart_frSgn_true_stdFr, (hs.2.2 τ).1]
    have e2 : (stdFr WW hw.1).cart = X.rW.s := funext fun τ => by rw [cart_stdFr, (hw.2.2 τ).1]
    have e3 : (stdFr A hs.1).onb = X.rA.B := funext fun τ => by rw [onb_stdFr, (hs.2.2 τ).2]
    have e4 : (stdFr WW hw.1).onb = X.rW.B := funext fun τ => by rw [onb_stdFr, (hw.2.2 τ).2]
    unfold GlobalTheory.SquareComm.fockF GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.ker
    rw [e1, e2, e3, e4]
  · intro P g h
    have e1 : (GlobalTheory.SquareComm.frSgn false (stdFr A' hs'.1)).cart = X.rA'.s :=
      funext fun τ => by rw [cart_frSgn_false_stdFr, (hs'.2.2 τ).1]
    have e2 : (stdFr WW hw.1).cart = X.rW.s := funext fun τ => by rw [cart_stdFr, (hw.2.2 τ).1]
    have e3 : (stdFr A' hs'.1).onb = X.rA'.B := funext fun τ => by rw [onb_stdFr, (hs'.2.2 τ).2]
    have e4 : (stdFr WW hw.1).onb = X.rW.B := funext fun τ => by rw [onb_stdFr, (hw.2.2 τ).2]
    unfold GlobalTheory.SquareComm.fockF GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.ker'
    rw [e1, e2, e3, e4]
    rfl

end GlobalTheory.BotDict

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTripleConstantsEqOfSameLatticesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteBottomTriple_constants_eq_of_same_lattices : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y →
    X.rA = Y.rA → X.rA' = Y.rA' → X.rW = Y.rW → ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c → X.IsConst W.ψ W.θ c := by
  first | exact @GlobalTheory.BotSameRig.const_of_sameRig | exact GlobalTheory.BotSameRig.const_of_sameRig | (intros; apply GlobalTheory.BotSameRig.const_of_sameRig <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryDepthPairStandard
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean GlobalTheory.SumSize.OppConj

namespace GlobalTheory.KerConjMean

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem le_of_ext (D : D7) (δ t0 : ℂ) (σ : D.what₂.LL →+* ℂ) (hfin : (ext D δ t0 σ).Finite) (hne : (ext D δ t0 σ).Nonempty)
    (a n G a' n' G' : ℝ) (ha : a ≤ a') (hn : n ≤ n') (hG : G ≤ G') (x B : ℝ) (hB : 0 ≤ B)
    (h : ∀ ρ ∈ ext D δ t0 σ, x ≤ Real.exp (a + n * hArea D δ t0 ρ + G * hTh D δ t0 ρ) * B) :
    x ≤ Real.exp (a' + n' * avg D δ t0 σ (hArea D δ t0) + G' * avg D δ t0 σ (hTh D δ t0)) * B := by
  obtain ⟨ρ, hρ, h1⟩ := (exists_avg _ hfin hne a' n' G' (hArea D δ t0) (hTh D δ t0)).1
  have hA : 0 ≤ hArea D δ t0 ρ := by unfold hArea; exact Real.posLog_nonneg
  have hT : 0 ≤ hTh D δ t0 ρ := by unfold hTh; exact Real.posLog_nonneg
  calc x ≤ Real.exp (a + n * hArea D δ t0 ρ + G * hTh D δ t0 ρ) * B := h ρ hρ
    _ ≤ Real.exp (a' + n' * hArea D δ t0 ρ + G' * hTh D δ t0 ρ) * B :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by nlinarith)) hB
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 h1) hB

section Std

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

theorem mapVV_conj_embLL {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (x : VV D.what₂.LL lam) :
    GlobalTheory.CoefModel.mapVV (starRingEnd ℂ) lam (GlobalTheory.CoefModel.mapVV D.what₂.embLL lam x) =
      GlobalTheory.CoefModel.mapVV D.what₂.embLL lam (mapF (starRingEnd D.what₂.LL) lam x) := by
  rw [mapVV_mapF, embLL_comp_star, mapVV_mapVV]

theorem pairStdAt_of (C b C1 : ℝ)
    (hmA : Formalism.PairingDivisionLocalBalance.meanInf D.what₂.LL (fun p => avg D ch.S.Z.δ ch.S.Z.t0 p.embedding (hArea D ch.S.Z.δ ch.S.Z.t0)) ≤
      C1 * Real.log b)
    (hmT : Formalism.PairingDivisionLocalBalance.meanInf D.what₂.LL (fun p => avg D ch.S.Z.δ ch.S.Z.t0 p.embedding (hTh D ch.S.Z.δ ch.S.Z.t0)) ≤
      C1 * Real.log b)
    (hfin : ∀ σ : D.what₂.LL →+* ℂ, (ext D ch.S.Z.δ ch.S.Z.t0 σ).Finite ∧ (ext D ch.S.Z.δ ch.S.Z.t0 σ).Nonempty)
    (hRT : RatTopAt ch) (hCT : ConjTopAt ch (C / 2) b C1) (hRR : RatRowAt ch) (hCR : ConjRowAt ch (C / 2) b C1) :
    PairStdAt ch C b := by
  obtain ⟨a1, n1, G1, ha1, hn1, hG1, hs1, hb1⟩ := hCT
  obtain ⟨a2, n2, G2, ha2, hn2, hG2, hs2, hb2⟩ := hCR
  refine ⟨fun p => (a1 + a2) + (n1 + n2) * avg D ch.S.Z.δ ch.S.Z.t0 p.embedding (hArea D ch.S.Z.δ ch.S.Z.t0) +
    (G1 + G2) * avg D ch.S.Z.δ ch.S.Z.t0 p.embedding (hTh D ch.S.Z.δ ch.S.Z.t0), ?_, ?_⟩
  · have eA : aOne ch.G (C / 2) b + aOne ch.G (C / 2) b = aOne ch.G C b := by unfold aOne; ring
    refine (meanInf_affine _ (a1 + a2) (n1 + n2) (G1 + G2) _ _ (by linarith)).trans ?_
    have e1 := mul_le_mul_of_nonneg_left hmA (add_nonneg hn1 hn2)
    have e2 := mul_le_mul_of_nonneg_left hmT (add_nonneg hG1 hG2)
    nlinarith
  · intro p Φ β d hO c
    obtain ⟨hf0, hne⟩ := hfin p.embedding
    refine ⟨fun j B v hv => ?_, fun i B v hv => ?_⟩
    · obtain ⟨f, hf⟩ := hRT Φ β d hO c j
      obtain ⟨u, rfl, hu⟩ := hv
      refine ⟨f u, (hf u).symm, ?_⟩
      exact le_of_ext D _ _ p.embedding hf0 hne a1 n1 G1 _ _ _ (by linarith) (by linarith) (by linarith) _ B
        ((nrm_one_nonneg _ _).trans hu) (fun ρ hρ => hb1 Φ β d hO c j f hf p.embedding ρ hρ u B hu)
    · obtain ⟨f, hf⟩ := hRR Φ β d hO c i
      obtain ⟨w, rfl, hw⟩ := hv
      refine ⟨mapF (starRingEnd D.what₂.LL) _ (f (mapF (starRingEnd D.what₂.LL) _ w)), ?_, ?_⟩
      · rw [conjMap, mapVV_conj_embLL, hf, mapVV_conj_embLL]
      · have hu : nrm _ (fun _ => 1) (GlobalTheory.CoefModel.mapVV (p.embedding.comp (starRingEnd D.what₂.LL)) _
            (mapF (starRingEnd D.what₂.LL) _ w)) ≤ B := by
          rwa [mapVV_mapF, RingHom.comp_assoc, star_comp_star, RingHom.comp_id]
        rw [mapVV_mapF]
        exact le_of_ext D _ _ p.embedding hf0 hne a2 n2 G2 _ _ _ (by linarith) (by linarith) (by linarith) _ B
          ((nrm_one_nonneg _ _).trans hw) (fun ρ hρ => hb2 Φ β d hO c i f hf p.embedding ρ hρ _ B hu)

end Std

end GlobalTheory.KerConjMean

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicWeilRepUnitaryPairSchroedingerModel
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilSchrodinger

theorem exists_isWeil : ∀ (D : D7) (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (n d : ℕ) (X : Spc D.host.F D.host.E n) (Y : Spc D.host.F D.host.E d) (r s r' s' : ℕ),
      X.IsHerm D.sp.cm.sig B r s → Y.IsSkew D.sp.cm.sig B r' s' →
      ∀ Mo : Model D.sp.cm.sig X Y, Mo.IsGood B.ψ →
      ∀ χX χW : Chr D.host.F D.host.E, GlobalTheory.LFun.IsHecke D.host.F D.host.E χX → GlobalTheory.LFun.IsHecke D.host.F D.host.E χW →
        GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χX n →
        GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χW d →
        ∃ om, Mo.IsWeil B.ψ χX χW om := by
  intro D B hB n d X Y r s r' s' hX hY Mo hMo χX χW hcX hcW rX rW
  obtain ⟨h1, h2, h3⟩ := _root_.GlobalTheory.WeilSchrodingerHerm.main D B hB n X r s hX
  obtain ⟨hJ, L, hL, h4, h5, h6⟩ := _root_.GlobalTheory.WeilSchrodingerSkew.main D B hB d Y r' s' hY
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  let T := hspOf D X.Jᵀ h1 h2 X.L (by letI := hX.lat; infer_instance) h3 (fun _ => (r, s))
  let S := hspOf D (-D.host.xi0 • Y.J⁻¹) h4 h5 L hL h6 (fun _ => (s', r'))
  have eA : X.J = T.gramᵀ := by rw [gram_hspOf]; rfl
  have eB : (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • incM D.host.F Y.J = incM D.host.F (D.host.xi0 • S.gram⁻¹) := by
    rw [gram_hspOf]
    have e1 : (-D.host.xi0 • Y.J⁻¹)⁻¹ = (-D.host.xi0)⁻¹ • Y.J := Matrix.inv_eq_left_inv (by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hJ,
        inv_mul_cancel₀ (neg_ne_zero.2 hξ), one_smul])
    have e2 : D.host.xi0 • (-D.host.xi0)⁻¹ • Y.J = -Y.J := by
      rw [smul_smul, inv_neg, mul_neg, mul_inv_cancel₀ hξ, neg_one_smul]
    show (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • incM D.host.F Y.J = incM D.host.F (D.host.xi0 • (-D.host.xi0 • Y.J⁻¹)⁻¹)
    rw [e1, e2]
    funext i j
    simp [incM]
  exact _root_.GlobalTheory.WeilSchrodinger.exists_isUWeilPair_hsp D B.ψ (_root_.GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd D B.ψ hB.std) S T χW χX hcW hcX (_root_.GlobalTheory.ResEtaOfPow.resEta_of_resEtaPow D χW d rW) (_root_.GlobalTheory.ResEtaOfPow.resEta_of_resEtaPow D χX n rX) X.J Y.J (-1) eA eB
    (Fin n × Fin d) Mo.co hMo.rat

end GlobalTheory.WeilSchrodinger

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleDieudonneBaseByCartierDuality
section
open CategoryTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem GlobalTheory.dieuBase_isEt_of_isConn :
    ∀ (p : ℕ) [Fact p.Prime] (Bc : GlobalTheory.Dieu.Base p (fun _ _ G => G.IsConn)),
      ∃ Be : GlobalTheory.Dieu.Base p (fun _ _ G => G.IsEt), Be.EtDual Bc :=
  fun p _ Bc => GlobalTheory.Dieu.exists_etDual_of_conn p Bc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFixedPullbackHomSchemeOfSectionBasesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fixedPullbackHomScheme_of_sectionBases : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Rigidified A L → Rigidified B M → RelAmple A L → 1 ≤ k → VeryAmpleAt B M k → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow A L (k : ℤ) (overRes (T := baseOver (Sp Rg)) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) ⊤).left) (b' : Fin m → LB.Sec (LPow A L (k : ℤ) (baseAt t))), (∀ i, IsPullSec A L (k : ℤ) (homAt t ▷ A) (whiskerRight_snd (homAt t) A) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) = ⊤) → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow B M (k : ℤ) (overRes (T := baseOver (Sp Rg)) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) ⊤).left) (b' : Fin m → LB.Sec (LPow B M (k : ℤ) (baseAt t))), (∀ i, IsPullSec B M (k : ℤ) (homAt t ▷ B) (whiskerRight_snd (homAt t) B) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec B (b' i) : SecM B M (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec B (b' i) : SecM B M (k : ℤ) (baseAt t))) = ⊤) → ∃ R : HomFixRep A B L M, QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  first | (exact @GlobalTheory.HomFixGlob.exists_homFixRep_of_secBases) | (exact GlobalTheory.HomFixGlob.exists_homFixRep_of_secBases) | (intros; apply GlobalTheory.HomFixGlob.exists_homFixRep_of_secBases  <;> assumption)
end

