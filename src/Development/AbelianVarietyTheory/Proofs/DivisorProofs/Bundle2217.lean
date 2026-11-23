module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1960
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0038
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomEqOneOfNilpotent
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFgForallOverLbIso
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2060
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.PullbackSquarePartialSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2122
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1962
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2119
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanThetaTranslatesTorsionEqTop
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.TSpan

noncomputable def actL {K : Type} [Field K] (P : PolAV (Sp K)) (k : ℕ)
    (ρ : ThetaGrp P.A P.L (k : ℤ) (baseOver (Sp K)) → (SecM P.A P.L (k : ℤ) (baseOver (Sp K)) ≃ₗ[Γ((baseOver (Sp K)).left, ⊤)] SecM P.A P.L (k : ℤ) (baseOver (Sp K))))
    (θ : ThetaGrp P.A P.L (k : ℤ) (baseOver (Sp K))) : EA P (𝟙 (Sp K)) k →ₗ[K] EA P (𝟙 (Sp K)) k where
  toFun w := SecMod.mk _ (SecM.toSec P.A (ρ θ (SecM.ofSec P.A w.sec)))
  map_add' a b := by
    show SecMod.mk _ (SecM.toSec P.A (ρ θ (SecM.ofSec P.A a.sec + SecM.ofSec P.A b.sec))) = _
    rw [map_add (f := _)]; rfl
  map_smul' c w := by
    show SecMod.mk _ (SecM.toSec P.A (ρ θ ((Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv c • SecM.ofSec P.A w.sec))) = _
    rw [map_smul]; rfl

theorem span_eq_top : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : KeyIn K) (m : ℕ), Odd m → 3 ≤ m →
    ∀ (I : Type) (pt : I → (baseOver (Sp K) ⟶ x.P.A)), (∀ z : baseOver (Sp K) ⟶ x.P.A, z ^ (m ^ 2) = 1 → ∃ i, pt i = z) →
    ∀ (th : LB.Sec (LPow x.P.A x.P.L ((1 : ℕ) : ℤ) (baseOver (Sp K)))), IsPolAVSectionInverseImage x.P (baseOver (Sp K)) x.th th →
    ∀ (U : I → ThetaGrp x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)))
      (t : I → LB.Sec (LPow x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)))),
    (∀ i, SymLift x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) (pt i) (U i) ∧ Tr x.P x.rig m th (U i) (t i)) →
    Submodule.span K (Set.range fun i =>
      (SecMod.mk (fst (baseOver (Sp K)) x.P.A).left (t i) : EA x.P (𝟙 (Sp K)) (m ^ 2))) = ⊤ := by
  intro K _ _ _ x m hm hm3 I pt hpt th hth U t hUt
  haveI : IsLocallyNoetherian (Sp K) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of K)))
  haveI := x.P.isAb.comm
  have hm0 : m ≠ 0 := by omega
  have hN : ((m ^ 2 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero 2 hm0)
  have hN1 : 1 ≤ m ^ 2 := Nat.one_le_iff_ne_zero.2 (pow_ne_zero 2 hm0)
  obtain ⟨-, hirr⟩ := GlobalTheory.ThetaIrred.main GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1 (Sp K) x.P K (𝟙 _) (m ^ 2) hN
  obtain ⟨ρ, hact, -, hrat, hmul⟩ := GlobalTheory.thetaGrp_acts_linearly GlobalTheory.allSixLaws.1.globalFns (Sp K) x.P ((m ^ 2 : ℕ) : ℤ)
    (baseOver (Sp K))
  let f := actL x.P (m ^ 2) ρ
  have hf : ∀ θ (a b : LB.Sec (LPow x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)))), IsActOf x.P.A x.P.L _ θ a b →
      f θ (SecMod.mk _ a) = SecMod.mk _ b := fun θ a b h => by
    show SecMod.mk _ (SecM.toSec x.P.A (ρ θ (SecM.ofSec x.P.A a))) = _
    rw [(hact θ a b).1 h]; rfl
  have hf' : ∀ θ (a : LB.Sec (LPow x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)))),
      IsActOf x.P.A x.P.L _ θ a (f θ (SecMod.mk _ a)).sec := fun θ a => (hact θ _ _).2 rfl

  have hker : ∀ θ : ThetaGrp x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)), θ.pt ^ (m ^ 2) = 1 := fun θ =>
    (GlobalTheory.allSixLaws.1.kerPow (Sp K) x.P (m ^ 2) hN1 _ θ.pt).1 fun _ =>
      ⟨⊤, trivial, GlobalTheory.exists_isGen_pull _ θ.φ θ.isGen _⟩
  let Wsp := Submodule.span K (Set.range fun i =>
    (SecMod.mk (fst (baseOver (Sp K)) x.P.A).left (t i) : EA x.P (𝟙 (Sp K)) (m ^ 2)))
  refine (hirr Wsp fun θ hθ v v' hvv' hv => ?_).resolve_left fun h => ?_
  · have e0 : f θ v = v' := hf θ v.sec v'.sec hvv'
    rw [← e0]
    refine (Submodule.span_le.2 ?_ : Wsp ≤ Wsp.comap (f θ)) hv
    rintro _ ⟨i, rfl⟩
    obtain ⟨-, α, s₁, hα, -, htw, ha⟩ := hUt i
    obtain ⟨θ₂, hp₂, hv₂⟩ := hmul θ (U i)
    obtain ⟨k, hk⟩ := hpt (θ.pt * pt i) (by rw [mul_pow, hθ, ← (hUt i).1.pt_eq, hker, _root_.mul_one])
    obtain ⟨-, α', s₁', hα', -, htw', ha'⟩ := hUt k
    obtain ⟨c, hc⟩ := GlobalTheory.T.exists_smul_of_twistedPullbacks_sameBundle K x.P m (by omega) th α' α s₁' s₁ hα' hα htw' htw
    obtain ⟨d, hd⟩ := hrat (U k) θ₂ (by rw [hp₂, (hUt k).1.pt_eq, (hUt i).1.pt_eq, hk])
    have e : f θ (SecMod.mk _ (t i)) = f θ₂ (SecMod.mk _ s₁) := by
      rw [← hf _ _ _ ha]
      show SecMod.mk _ (SecM.toSec x.P.A (ρ θ _)) = SecMod.mk _ (SecM.toSec x.P.A (ρ θ₂ _))
      rw [hv₂]; rfl
    have e₂ : f θ₂ (SecMod.mk _ s₁) =
        ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (d : Γ((baseOver (Sp K)).left, ⊤))) • f (U k) (SecMod.mk _ s₁) := by
      show SecMod.mk _ (SecM.toSec x.P.A (ρ θ₂ _)) = _
      rw [hd]
      have e3 : (d : Γ((baseOver (Sp K)).left, ⊤)) = (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
          ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (d : Γ((baseOver (Sp K)).left, ⊤))) := by
        simp [Iso.commRingCatIsoToRingEquiv]
      conv_lhs => rw [e3]
      rfl
    show f θ (SecMod.mk _ (t i)) ∈ Wsp
    rw [e, e₂, hc, map_smul, hf _ _ _ ha']
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  · obtain ⟨i, hi⟩ := _root_.GlobalTheory.TransNZ.exists_ne K x m hm hm3 I pt hpt th hth U t hUt
    exact hi ((Submodule.eq_bot_iff _).1 h _ (Submodule.subset_span ⟨i, rfl⟩))

end GlobalTheory.TSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusHomExtOfEqModMaximalIdealPow
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)

namespace GlobalTheory


open TorusNil TorusLocal in
theorem splitTorus_hom_ext_of_forall_pow (R : Type) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (A : Type) [AddCommGroup A] (B : Over (Spec (CommRingCat.of R)))
    (hB : IsSeparated B.hom) (f g : splitTorus (Spec (CommRingCat.of R)) A ⟶ B)
    (hn : ∀ n : ℕ, (Over.pullback (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))).map f =
      (Over.pullback (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))).map g) : f = g := by
  set t := torusPt R A (AddMonoidAlgebra.of R A) with ht
  have h1 : t ≫ f = t ≫ g := by
    refine pt_ext_of_quotients (fun n : ℕ =>
      (IsLocalRing.maximalIdeal R ^ (n + 1)).map (algebraMap R (AddMonoidAlgebra R A)))
      eq_zero_of_forall_mem_map_pow fun n => ?_
    rw [← Category.assoc, ← Category.assoc _ t]
    exact comp_eq_of_pullback_map_eq (hn n) _
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _
        (algebraMap R (AddMonoidAlgebra R A ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1)).map
          (algebraMap R (AddMonoidAlgebra R A)))) (fun a ha => by
          rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.mem_map_of_mem _ ha))))
      (by rw [← Spec.map_comp]; rfl)
  have := isIso_torusPt_of R A
  apply Over.OverMorphism.ext
  rw [← cancel_epi t.left, ← Over.comp_left, h1, ← Over.comp_left]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusHomTrivialModPow
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)

namespace GlobalTheory

namespace TorusThicken

theorem pullback_map_eq_of_comp {S S' S'' : Scheme.{0}} (s : S'' ⟶ S') (p : S' ⟶ S) {V W : Over S}
    {a b : V ⟶ W} (h : (Over.pullback p).map a = (Over.pullback p).map b) :
    (Over.pullback (s ≫ p)).map a = (Over.pullback (s ≫ p)).map b := by
  have ha := (Over.pullbackComp s p).hom.naturality a
  have hb := (Over.pullbackComp s p).hom.naturality b
  simp only [Functor.comp_map] at ha hb
  rw [← cancel_mono ((Over.pullbackComp s p).hom.app W), ha, hb, h]

theorem pullback_pullback_map_eq_of_comp {S S' S'' : Scheme.{0}} (s : S'' ⟶ S') (p : S' ⟶ S)
    {V W : Over S} {a b : V ⟶ W} (h : (Over.pullback (s ≫ p)).map a = (Over.pullback (s ≫ p)).map b) :
    (Over.pullback s).map ((Over.pullback p).map a) = (Over.pullback s).map ((Over.pullback p).map b) := by
  have ha := (Over.pullbackComp s p).hom.naturality a
  have hb := (Over.pullbackComp s p).hom.naturality b
  simp only [Functor.comp_map] at ha hb
  rw [← cancel_epi ((Over.pullbackComp s p).hom.app V), ← ha, ← hb, h]

end TorusThicken


open TorusThicken in
theorem splitTorus_hom_trivial_mod_pow (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (A : Type) [AddCommGroup A] (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    (f : splitTorus (Spec (CommRingCat.of R)) A ⟶ G) (hf : IsMonHom f)
    (h : (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R (IsLocalRing.ResidueField R)).map f =
      (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R (IsLocalRing.ResidueField R)).map 1) (n : ℕ) :
    (Over.pullback (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))).map f =
      (Over.pullback (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))).map 1 := by
  set I := IsLocalRing.maximalIdeal R ^ (n + 1) with hI
  set p := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) with hp
  have hIt : I ≠ ⊤ := fun e => (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    (top_le_iff.1 (e ▸ Ideal.pow_le_self (Nat.succ_ne_zero n)))
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hIt
  have : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  set J : Ideal (R ⧸ I) := (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk I) with hJ
  have hJn : IsNilpotent J := ⟨n + 1, by
    rw [hJ, ← Ideal.map_pow, ← hI, Ideal.map_quotient_self]; rfl⟩
  set q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) with hq
  let ℓ : IsLocalRing.ResidueField R →+* (R ⧸ I) ⧸ J :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) ((Ideal.Quotient.mk J).comp (Ideal.Quotient.mk I))
      (fun a ha => by
        rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_map_of_mem _ ha)
  have hsq : q ≫ p = Spec.map (CommRingCat.ofHom ℓ) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))) := by
    rw [hq, hp, ← Spec.map_comp, ← Spec.map_comp]; rfl

  have h1 : (Over.pullback q).map ((Over.pullback p).map f) =
      (Over.pullback q).map ((Over.pullback p).map 1) := by
    apply pullback_pullback_map_eq_of_comp
    rw [hsq]
    exact pullback_map_eq_of_comp _ _ h
  obtain ⟨e, he, -⟩ := splitTorus_baseChange _ _ p A
  have hg : IsMonHom (e.hom ≫ (Over.pullback p).map f) := inferInstance
  have hp1 : (Over.pullback p).map (1 : splitTorus (Spec (CommRingCat.of R)) A ⟶ G) = 1 :=
    Functor.map_one _
  have key := splitTorus_hom_eq_one_of_nilpotent (R ⧸ I) J hJn A _ (e.hom ≫ (Over.pullback p).map f) hg
    (by rw [Functor.map_comp, h1, hp1, ← Functor.map_comp, ← Hom.one_def, MonObj.comp_one])
  rw [← cancel_epi e.hom, key, ← Hom.one_def, hp1, MonObj.comp_one]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareDecompositionExtendsFromGenericFibreSemiAb
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.GenericDec


open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison in
theorem gen_pull_div_of_gen_div {X Y : Scheme.{0}} (M N : LB X) (a : Y ⟶ X)
    (h : ∃ t : LB.Gen (LB.div (M.pull a) (N.pull a)), t.IsGen) :
    ∃ t : LB.Gen ((LB.div M N).pull a), t.IsGen := by
  refine exists_gen_transfer (L := LB.div (M.pull a) (N.pull a)) (L' := (LB.div M N).pull a)
    (fun p => ((fun _ => (p PUnit.unit).1), (fun _ => (p PUnit.unit).2))) (fun j y hy => ?_)
    (fun i j y hy => ?_) h
  · exact ⟨Set.mem_iInter.2 fun _ => (Set.mem_iInter.1 hy PUnit.unit).1,
      Set.mem_iInter.2 fun _ => (Set.mem_iInter.1 hy PUnit.unit).2⟩
  · have hM : a.base y ∈ M.U (i PUnit.unit).1 ⊓ M.U (j PUnit.unit).1 :=
      ⟨(Set.mem_iInter.1 hy.1 PUnit.unit).1, (Set.mem_iInter.1 hy.2 PUnit.unit).1⟩
    have hN : a.base y ∈ N.U (i PUnit.unit).2 ⊓ N.U (j PUnit.unit).2 :=
      ⟨(Set.mem_iInter.1 hy.1 PUnit.unit).2, (Set.mem_iInter.1 hy.2 PUnit.unit).2⟩
    refine (germ_pull (LB.div M N) a i j y hy ⟨⟨hM.1, hN.1⟩, ⟨hM.2, hN.2⟩⟩).trans ?_
    refine (gU_pullU a _ y _ _).trans ?_
    refine (congrArg _ (germ_div M N _ _ (a.base y) _)).trans ?_
    rw [map_mul, map_inv]
    refine Eq.trans ?_ (germ_div _ _ _ _ y _).symm
    exact congrArg₂ (· * ·) ((germ_pull M a (fun _ => (i PUnit.unit).1) (fun _ => (j PUnit.unit).1) y _ hM).trans (gU_pullU a _ y _ _)).symm
      (congrArg (·⁻¹) ((germ_pull N a (fun _ => (i PUnit.unit).2) (fun _ => (j PUnit.unit).2) y _ hN).trans (gU_pullU a _ y _ _)).symm)

theorem lbIso_of_generic {R' : Type} [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R']
    [IsLocalRing R'] (G : Over (Sp R')) [GrpObj G] (hG : IsSemiAbelian G) {P Q : LB G.left} (hP : P.IsLB)
    (hQ : Q.IsLB) (h : LBIso (P.pull (pullback.fst G.hom (jK R'))) (Q.pull (pullback.fst G.hom (jK R')))) :
    LBIso P Q :=
  PicGenericInj.exists_gen_of_generic R' G hG (LB.div Q P) (LB.isLB_div hQ hP)
    (gen_pull_div_of_gen_div Q P _ h)

theorem sqDec_of_generic : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R']
    [IsLocalRing R'] (G : Over (Sp R')) [GrpObj G], IsSemiAbelian G → ∀ (L M : LB G.left), L.IsLB → M.IsLB →
    SqDec ((Over.pullback (jK R')).obj G) (L.pull (pullback.fst G.hom (jK R')))
      (M.pull (pullback.fst G.hom (jK R'))) → SqDec G L M := by
  intro R' _ _ _ _ _ G _ hG L M hL hM hD
  obtain ⟨N, a₀, r, a, β, hN, ha₀, hβ, H⟩ := hD
  have ext : ∀ i, ∃ B : G ⟶ G, IsMonHom B ∧ (Over.pullback (jK R')).map B = β i := fun i =>
    (semiAbelian_hom_extend_generic R' G G hG hG (β i) (hβ i)).exists
  choose B hBm hBe using ext
  refine ⟨N, a₀, r, a, B, hN, ha₀, hBm, ?_⟩
  set f := pullback.fst G.hom (jK R') with hf
  have hc : ∀ o : Option (Fin r), (o.elim (𝟙 _) fun i => (β i).left) ≫ f =
      f ≫ (o.elim (𝟙 G.left) fun i => (B i).left) := by
    intro o
    cases o with
    | none => simp
    | some i =>
      simp only [Option.elim_some]
      rw [← hBe i]
      simp only [hf, Over.pullback_map_left, pullback.lift_fst]
  have i1 := (lbIso_lbPow_pull hL f N).symm
  have i5 := GlobalTheory.SymExtend.lbIso_linComb_pull hM f (fun o : Option (Fin r) => o.elim (𝟙 _) fun i => (β i).left)
    (fun o : Option (Fin r) => o.elim (𝟙 G.left) fun i => (B i).left) (fun o => o.elim (a₀ : ℤ) fun i => (a i : ℤ)) f hc
  have j1 := i1.trans (pull_isLB (isLB_lbPow hL N) f) (isLB_lbPow (pull_isLB hL f) N)
    (LB.isLB_linComb (pull_isLB hM f) _ _) H
  have j2 := j1.trans (pull_isLB (isLB_lbPow hL N) f) (LB.isLB_linComb (pull_isLB hM f) _ _)
    (pull_isLB (LB.isLB_linComb hM _ _) f) i5
  exact lbIso_of_generic G hG (isLB_lbPow hL N) (LB.isLB_linComb hM _ _) j2

end GlobalTheory.GenericDec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareDecompositionOfBaseChangeAlongIdentity
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SqDecIdBC

theorem sqDec_of_baseChange_id : ∀ (F : Type) [CommRing F] (A : Over (Sp F)) [GrpObj A] (L M : LB A.left), L.IsLB → M.IsLB → SqDec ((Over.pullback (spMap (RingHom.id F))).obj A) (L.pull (pullback.fst A.hom (spMap (RingHom.id F)))) (M.pull (pullback.fst A.hom (spMap (RingHom.id F)))) → SqDec A L M := by
  intro F _ A _ L M hL hM hD
  have hid : spMap (RingHom.id F) = 𝟙 (Sp F) := by
    simp [spMap]
  have hw : 𝟙 A.left ≫ A.hom = A.hom ≫ spMap (RingHom.id F) := by rw [hid]; simp
  let π' : A.left ⟶ pullback A.hom (spMap (RingHom.id F)) := pullback.lift (𝟙 _) A.hom hw
  have e₁ : π' ≫ pullback.fst A.hom (spMap (RingHom.id F)) = 𝟙 _ := pullback.lift_fst _ _ _
  have e₂ : π' ≫ ((Over.pullback (spMap (RingHom.id F))).obj A).hom = A.hom ≫ 𝟙 _ := by
    change π' ≫ pullback.snd A.hom (spMap (RingHom.id F)) = A.hom ≫ 𝟙 _
    simp [π']
  have hP : IsGrpPullback A ((Over.pullback (spMap (RingHom.id F))).obj A) (𝟙 _) π' := by
    have n : IsGrpPullback A A (𝟙 _ ≫ spMap (RingHom.id F)) (π' ≫ pullback.fst A.hom (spMap (RingHom.id F))) := by
      rw [e₁, Category.id_comp, hid]; exact GlobalTheory.SiegLower.isGrpPullback_id A
    exact IsGrpPullback.cancel (isGrpPullback_pullback A _) n e₂
  obtain ⟨N, a₀, r, e, β, hN, ha₀, hβ, hI⟩ := hD
  have hβ' : ∀ i, ∃ g : A ⟶ A, IsMonHom g ∧ g.left ≫ π' = π' ≫ (β i).left := fun i => by
    haveI := hβ i
    exact GlobalTheory.HomDescent.exists_isMonHom_pull hP hP (β i)
  choose β' hβ'm hβ'c using hβ'
  have iL : LBIso L ((L.pull (pullback.fst A.hom (spMap (RingHom.id F)))).pull π') :=
    LBIso.trans hL (LB.isLB_pull hL _) (LB.isLB_pull (LB.isLB_pull hL _) _) (GlobalTheory.SiegLower.lbIso_pull_id hL)
      (GlobalTheory.ShapePull.iso_linComb_pull (GlobalTheory.SiegLower.lbIso_pull_id hL) _ _ _ π' (fun _ => by rw [e₁]; simp))
  have iM : LBIso M ((M.pull (pullback.fst A.hom (spMap (RingHom.id F)))).pull π') :=
    LBIso.trans hM (LB.isLB_pull hM _) (LB.isLB_pull (LB.isLB_pull hM _) _) (GlobalTheory.SiegLower.lbIso_pull_id hM)
      (GlobalTheory.ShapePull.iso_linComb_pull (GlobalTheory.SiegLower.lbIso_pull_id hM) _ _ _ π' (fun _ => by rw [e₁]; simp))
  refine ⟨N, a₀, r, e, β', hN, ha₀, hβ'm, ?_⟩
  have j₁ : LBIso (lbPow L N) ((lbPow (L.pull (pullback.fst A.hom (spMap (RingHom.id F)))) N).pull π') :=
    GlobalTheory.ShapePull.iso_linComb_pull iL _ _ _ π' (fun _ => by simp)
  have j₂ := GlobalTheory.RigidBundleGlue.LBIso.pull hI π'
  have j₃ : LBIso (LB.LinComb M (K := Option (Fin r))
        (fun o => o.elim (𝟙 _) fun i => (β' i).left) fun o => o.elim (a₀ : ℤ) fun i => (e i : ℤ))
      ((LB.LinComb (M.pull (pullback.fst A.hom (spMap (RingHom.id F)))) (K := Option (Fin r))
        (fun o => o.elim (𝟙 _) fun i => (β i).left) fun o => o.elim (a₀ : ℤ) fun i => (e i : ℤ)).pull π') :=
    GlobalTheory.ShapePull.iso_linComb_pull iM _ _ _ π' (fun o => by
      cases o with
      | none => simp
      | some i => exact hβ'c i)
  exact LBIso.trans (isLB_lbPow hL N) (LB.isLB_pull (isLB_lbPow (LB.isLB_pull hL _) N) _)
    (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ hM _ _) j₁
    (LBIso.trans (LB.isLB_pull (isLB_lbPow (LB.isLB_pull hL _) N) _)
      (LB.isLB_pull (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ (LB.isLB_pull hM _) _ _) _)
      (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ hM _ _) j₂ (LBIso.symm j₃))

end GlobalTheory.SqDecIdBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTheoremPicClassOverOpen
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SquareOpen

theorem pull_mul_add_pull_mul_inv_of_opens : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (U : S.Opens) (c : Pic (A.hom ⁻¹ᵁ U).toScheme) (Y : Over S) (l : (Y ⟶ A) → (Y.left ⟶ (A.hom ⁻¹ᵁ U).toScheme)), (∀ y, Y.hom y ∈ U) → (∀ p, l p ≫ (A.hom ⁻¹ᵁ U).ι = p.left) → ∀ x a : Y ⟶ A, GlobalTheory.CechPic.pull (l (x * a)) c + GlobalTheory.CechPic.pull (l (x * a⁻¹)) c = 2 • GlobalTheory.CechPic.pull (l (x)) c + GlobalTheory.CechPic.pull (l (a)) c + GlobalTheory.CechPic.pull (l (a⁻¹)) c - 2 • GlobalTheory.CechPic.pull (l ((1 : Y ⟶ A))) c := by
  intro S _ A _ hA U c Y l hY hl x a
  let A' := (Over.pullback U.ι).obj A
  have hA' : IsAbelianScheme A' := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback U.ι A hA
  have h := isGrpPullback_pullback A U.ι
  let e := (isPullback_morphismRestrict A.hom U).flip.isoPullback
  have he : e.inv ≫ (A.hom ⁻¹ᵁ U).ι = pullback.fst A.hom U.ι := by
    rw [Iso.inv_comp_eq, IsPullback.isoPullback_hom_fst]
  have hrange : Set.range Y.hom.base ⊆ Set.range U.ι.base := by
    rintro _ ⟨y, rfl⟩
    rw [U.range_ι]
    exact hY y
  let Y' : Over U.toScheme := Over.mk (IsOpenImmersion.lift U.ι Y.hom hrange)
  have hY' : Y'.hom ≫ U.ι = Y.hom := IsOpenImmersion.lift_fac _ _ _
  let τ : Over.mk (Y'.hom ≫ U.ι) ⟶ Y := Over.homMk (𝟙 Y.left) (by erw [Category.id_comp]; exact hY'.symm)
  have lift : ∀ p : Y ⟶ A, ∃ p' : Y' ⟶ A', pushHom h Y' p' = τ ≫ p := by
    intro p
    refine ⟨Over.homMk (pullback.lift p.left Y'.hom (by rw [Over.w p, hY'])) (by
      exact pullback.lift_snd _ _ _), ?_⟩
    apply Over.OverMorphism.ext
    simp only [pushHom, pushPt, τ, MonoidHom.mk'_apply, Over.homMk_left, Over.comp_left]
    rw [pullback.lift_fst]
    exact (Category.id_comp p.left).symm
  have key : ∀ (p : Y ⟶ A) (p' : Y' ⟶ A'), pushHom h Y' p' = τ ≫ p → l p = p'.left ≫ e.inv := by
    intro p p' hp
    rw [← cancel_mono (A.hom ⁻¹ᵁ U).ι, hl, Category.assoc, he]
    have := congrArg (fun q => q.left) hp
    simp only [pushHom, pushPt, τ, MonoidHom.mk'_apply, Over.homMk_left, Over.comp_left] at this
    exact (Category.id_comp _).symm.trans this.symm
  obtain ⟨x', hx⟩ := lift x
  obtain ⟨a', ha⟩ := lift a
  have hmul : pushHom h Y' (x' * a') = τ ≫ (x * a) := by
    rw [map_mul, hx, ha, MonObj.comp_mul]
  have hainv : pushHom h Y' a'⁻¹ = τ ≫ a⁻¹ := by
    rw [map_inv, ha, GrpObj.comp_inv]
  have hinv : pushHom h Y' (x' * a'⁻¹) = τ ≫ (x * a⁻¹) := by
    rw [map_mul, hainv, hx, MonObj.comp_mul]
  have hone : pushHom h Y' 1 = τ ≫ 1 := by
    rw [map_one, MonObj.comp_one]
  rw [key _ _ hmul, key _ _ hinv, key _ _ hx, key _ _ ha, key _ _ hainv, key _ _ hone]
  simp only [pull_comp]
  exact _root_.GlobalTheory.SquareSym.pull_mul_add_pull_mul_inv U.toScheme A' hA' (pull e.inv c) Y' x' a'

end GlobalTheory.SquareOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepLatZero
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.Mean4O GlobalTheory.LieHt

namespace GlobalTheory.LieRead

variable {D : D7} (O : Setup D)

def FibTie (y : Pt O.s) {K : Type} [Field K] [NumberField K] (F : SemiFib K) (ι : K →+* Qb) : Prop :=
  ∃ (jF : O.κ.c.F →+* K) (yO : Sp (𝓞 K) ⟶ O.s.T.Z.X) (ψ : F.G.left ⟶ O.s.T.Z.t.G.left),
    ι.comp jF = y.fK ∧
    spMap (ι.comp (algebraMap (𝓞 K) K)) ≫ yO = y.y ≫ genι O.s.T.Z ∧
    IsGrpPullback F.G O.s.T.Z.t.G yO ψ ∧
    LBIso (O.s.T.Z.t.PP.L.pull (F.φ ≫ ψ)) F.P₀.L ∧
    F.P₀.g = (letters O.S.Dw).length ∧
    ∀ (k : Fin F.P₀.g) (x : Letter O.S.Dw), (letters O.S.Dw)[(k : ℕ)]? = some x →
      y.u x.1 x.2 = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR ι) ≫ (F.v k).left ≫ F.φ ≫ ψ

def stepLat {K : Type} [Field K] [NumberField K] (F : SemiFib K) (τ : D.host.E →+* ℂ) (k : ℕ) :
    Submodule (𝓞 K) (Fin F.P₀.g → K) :=
  F.lieLat ⊓ (Submodule.span K {v | ∃ (i : Fin F.P₀.g) (x : Letter O.S.Dw), x.1 = τ ∧ (x.2 : ℕ) < k ∧
    (letters O.S.Dw)[(i : ℕ)]? = some x ∧ v = Pi.single i 1}).restrictScalars (𝓞 K)

end GlobalTheory.LieRead

end
end

