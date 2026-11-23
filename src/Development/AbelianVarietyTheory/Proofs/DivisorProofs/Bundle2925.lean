module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0808
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2855
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0833
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1813
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2891
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0933
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1579
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0648
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1503
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EntriesWellDefined
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2887
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2893
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2908
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0548
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRing
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0553
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0556
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0001
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2060

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialGoodReductionOfLieMultZero
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

open scoped Matrix

namespace GlobalTheory.PotGoodLie

theorem proper_pull {K W L : Type} [Field K] [CommRing W] [Field L] [Algebra K L] [Algebra W L]
    (A : Over (Sp K)) [GrpObj A] (G : Over (Sp W)) [GrpObj G] (hM : GlobalTheory.SS.IsModel (L := L) A G)
    (hA : IsAbelianScheme A) : IsProper ((Over.pullback (spMap (algebraMap W L))).obj G).hom := by
  obtain ⟨e, -⟩ := hM
  have := hA.proper
  have h : ((Over.pullback (spMap (algebraMap W L))).obj G).hom = e.hom.left ≫ ((Over.pullback (spMap (algebraMap K L))).obj A).hom := (Over.w e.hom).symm
  rw [h]
  have : IsProper ((Over.pullback (spMap (algebraMap K L))).obj A).hom := by
    show IsProper (pullback.snd A.hom _)
    infer_instance
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  infer_instance

theorem spMap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem eq_one_of_lieMult_zero {S : Scheme.{0}} {O : Type} [CommRing O] {G : Over S} [GrpObj G] (a : OAct O G)
    {k : Type} [Field k] (t : Sp k ⟶ S) (τ : O →+* k) (h : LieMult a t τ 0) (w : epsPt t ⟶ G)
    (hw : IsLieEigen a t τ w) : w = 1 := by
  obtain ⟨v, -, H⟩ := h
  obtain ⟨c, ⟨u, -, hu⟩, -⟩ := H w hw
  simpa using hu

theorem lift_ext (V K W L Ω : Type) [CommRing V] [Field K] [CommRing W] [IsDomain W] [Field L] [Field Ω]
    [IsAlgClosed Ω] [Algebra V K] [Algebra V W] [Algebra W L] [Algebra K L] [IsFractionRing W L]
    (hc : (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K))
    (hfin : Module.Finite V W) (g : K →+* Ω) : ∃ g' : L →+* Ω, g'.comp (algebraMap K L) = g := by
  letI := g.toAlgebra
  have hint : Algebra.IsIntegral V W := Algebra.IsIntegral.of_finite V W
  have halg : ∀ w : W, IsAlgebraic K (algebraMap W L w) := by
    intro w
    obtain ⟨p, hp, hpw⟩ := hint.isIntegral w
    refine ⟨p.map (algebraMap V K), (hp.map _).ne_zero, ?_⟩
    have := congrArg (algebraMap W L) hpw
    rw [map_zero, Polynomial.hom_eval₂] at this
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← this, hc]
  haveI : Algebra.IsAlgebraic K L := by
    refine ⟨fun x => ?_⟩
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := W) x
    rw [div_eq_mul_inv]
    exact IsAlgebraic.mul (halg a) (IsAlgebraic.inv (halg b))
  exact ⟨(IsAlgClosed.lift : L →ₐ[K] Ω).toRingHom, by ext x; simp [RingHom.algebraMap_toAlgebra]⟩

theorem prod_of_add {A B J : Type} [AddCommMonoid A] [CommMonoid B] (φ : A → B) (h0 : φ 0 = 1)
    (hadd : ∀ x y, φ (x + y) = φ x * φ y) (s : Finset J) (g : J → A) : φ (∑ i ∈ s, g i) = ∏ i ∈ s, φ (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, hadd, ih]

theorem exists_ringHom {R : Type} [CommRing R] {S : Scheme.{0}} {G : Over S} [GrpObj G] {O : Type} [CommRing O]
    (a : OAct O G) {n : ℕ} (M : (G ⟶ G) → Matrix (Fin n) (Fin n) R) {k : Type} [Field k] (f : R →+* k)
    (hf : Function.Injective f) {X : Over S} (T : (Fin n → k) → (X ⟶ G)) (Tinj : Function.Injective T)
    (Tadd : ∀ c c', T (c + c') = T c * T c')
    (Tact : ∀ u : G ⟶ G, IsMonHom u → ∀ c, T c ≫ u = T (((M u).map f).mulVec c)) :
    ∃ Mr : O →+* Matrix (Fin n) (Fin n) R, ∀ x, Mr x = M (a.act x) := by
  have key : ∀ P Q : Matrix (Fin n) (Fin n) R, (∀ c, T ((P.map f) *ᵥ c) = T ((Q.map f) *ᵥ c)) → P = Q := by
    intro P Q h
    apply Matrix.map_injective hf
    apply Matrix.toLin'.injective
    exact LinearMap.ext fun c => by simpa [Matrix.toLin'_apply] using Tinj (h c)
  have T0 : T 0 = 1 := by simpa using Tadd 0 0
  have act0 : a.act 0 = 1 := by simpa using a.add 0 0
  refine ⟨{ toFun := fun x => M (a.act x), map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ },
    fun _ => rfl⟩
  · apply key; intro c
    rw [← Tact _ (a.hom 1), a.one]
    simp
  · intro x y; apply key; intro c
    rw [← Tact _ (a.hom (x * y)), mul_comm x y, a.mul, ← Category.assoc, Tact _ (a.hom y), Tact _ (a.hom x),
      Matrix.mulVec_mulVec, ← Matrix.map_mul]
  · apply key; intro c
    rw [← Tact _ (a.hom 0), act0, comp_one]
    simp [T0]
  · intro x y; apply key; intro c
    rw [← Tact _ (a.hom (x + y)), a.add, comp_mul, Tact _ (a.hom x), Tact _ (a.hom y), ← Tadd, Matrix.map_add _ (map_add f),
      Matrix.add_mulVec]

theorem finrank_zero (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (G : Over (Sp W)) [GrpObj G]
    (hG : IsSemiAbelian G) (F : Type) [Field F] [NumberField F] (a : OAct (𝓞 F) G) (Ω : Type) [Field Ω] [CharZero Ω]
    [IsAlgClosed Ω] (f : W →+* Ω) (hf : Function.Injective f) (σ : 𝓞 F →+* Ω) (h0 : LieMult a (spMap f) σ 0)
    (E : TorusExtension (GlobalTheory.SS.spFibre G)) : (letI := E.addCommGroup; Module.finrank ℤ E.X) = 0 := by
  classical
  letI := E.addCommGroup
  haveI := E.free
  haveI := E.finite
  haveI : IsCommMonObj G := hG.comm
  obtain ⟨n, M, -, hT⟩ := _root_.GlobalTheory.exists_lie_coordinates_fibres W G hG.smooth
  obtain ⟨T, Tinj, Trange, Tadd, Tsc, Tact⟩ := hT Ω f
  obtain ⟨Mr, hMr⟩ := exists_ringHom a M f hf T Tinj Tadd Tact
  have T0 : T 0 = 1 := by simpa using Tadd 0 0
  have hno : ∀ c : Fin n → Ω, (∀ x, ((Mr x).map f).mulVec c = σ x • c) → c = 0 := by
    intro c hc
    have hE : IsLieEigen a (spMap f) σ (T c) := by
      refine ⟨(Trange (T c)).2 ⟨c, rfl⟩, fun x => ?_⟩
      rw [Tact _ (a.hom x), ← hMr, hc, Tsc]
    exact Tinj ((eq_one_of_lieMult_zero a _ σ h0 _ hE).trans T0.symm)
  let b := Module.Free.chooseBasis ℤ (𝓞 F)
  obtain ⟨w, ⟨i0, hu⟩, hsum⟩ := _root_.GlobalTheory.PrimAnnih.exists_primitive_annihilator F W Ω f hf n Mr σ hno _ b
  obtain ⟨ρ, U, Uinj, Ufst, Uadd, Usc, Uact⟩ := GlobalTheory.T.toric_part_fibre_lie_algebra_characters (Sp W) G (𝓞 F) a.act a.hom a.one a.mul a.add
    (ResidueField W) (spMap (residue W)) E
  obtain ⟨T', -, T'range, T'add, T'sc, T'act⟩ := hT (ResidueField W) (residue W)
  have T'0 : T' 0 = 1 := by simpa using T'add 0 0
  have U0 : U 0 = 1 := by simpa using Uadd 0 0
  refine _root_.GlobalTheory.finrank_eq_zero_of_dual_killed F E.X ρ (ResidueField W) _ b (fun i => residue W (w i)) ?_ ?_
  · intro h
    exact (residue_ne_zero_iff_isUnit _).2 hu (congrFun h i0)
  · intro l χ
    obtain ⟨c, hc⟩ := (T'range (U l)).1 (Ufst l)
    have step : ∀ i, U ((AddMonoidHom.mulLeft (residue W (w i))).comp (l.comp (ρ (b i)).toAddMonoidHom)) =
        T' (residue W (w i) • ((Mr (b i)).map (residue W) *ᵥ c)) := by
      intro i
      have e : U (l.comp (ρ (b i)).toAddMonoidHom) = T' ((Mr (b i)).map (residue W) *ᵥ c) := by
        rw [← Uact, ← hc, T'act _ (a.hom _), hMr]
      apply Over.OverMorphism.ext
      rw [Usc, T'sc, e]
    have hv : ∑ i, residue W (w i) • ((Mr (b i)).map (residue W) *ᵥ c) = 0 := by
      have := congrArg (fun P => ((residue W).mapMatrix P) *ᵥ c) hsum
      have hsm : ∀ i, (w i • Mr (b i)).map (residue W) = residue W (w i) • (Mr (b i)).map (residue W) := by
        intro i; ext; simp
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_sum, Matrix.sum_mulVec, hsm, Matrix.smul_mulVec] using this
    have hL : (∑ i, (AddMonoidHom.mulLeft (residue W (w i))).comp (l.comp (ρ (b i)).toAddMonoidHom)) = 0 := by
      apply Uinj
      rw [prod_of_add U U0 Uadd, U0, Finset.prod_congr rfl (fun i _ => step i), ← prod_of_add T' T'0 T'add, hv, T'0]
    have := congrArg (fun m => m χ) hL
    simpa using this

theorem potGood_of_lieMult_zero : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (F : Type) [Field F] [NumberField F] (act : OAct (𝓞 F) A) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (g : K →+* Ω) (σ : 𝓞 F →+* Ω), LieMult act (spMap g) σ 0 → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsAbelianScheme G) := by
  intro V K _ _ _ _ _ _ _ _ A _ hA F _ _ act Ω _ _ g σ hL
  obtain ⟨W, L, iW, iD, iDVR, iL, iVW, iWL, iKL, iFR, hc, hfin, hloc, hcpl, G, iG, hM, hsemi, ⟨E⟩⟩ :=
    _root_.GlobalTheory.SS.potModel_semiAbelian_torusExtension V K A hA
  refine ⟨W, L, iW, iD, iDVR, iL, iVW, iWL, iKL, iFR, hc, hfin, hloc, hcpl, G, iG, hM, ?_⟩
  have hAL := isGrpPullback_pullback A (spMap (algebraMap K L))
  obtain ⟨actL, ⟨h1, h2, h3, h4⟩, hLc⟩ := _root_.GlobalTheory.ActPull.exists_act_pull _ _ (spMap (algebraMap K L)) A
    ((Over.pullback (spMap (algebraMap K L))).obj A) _ hAL (𝓞 F) act.act act.hom act.one act.mul act.add
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.isGrpPullback_of_group_scheme_model_base_change K W L A G hM _ _ hAL
  obtain ⟨actG, ⟨g1, g2, g3, g4⟩, hGc⟩ := _root_.GlobalTheory.ringAct_extends_semiAbelian_dvr W L G _ φ hsemi hφ (𝓞 F) actL h1 h2 h3 h4
  let aL : OAct (𝓞 F) ((Over.pullback (spMap (algebraMap K L))).obj A) := ⟨actL, h1, h2, h3, h4⟩
  let aG : OAct (𝓞 F) G := ⟨actG, g1, g2, g3, g4⟩
  obtain ⟨g', hg'⟩ := lift_ext V K W L Ω hc hfin g
  have e1 := GlobalTheory.LiePull.lieMult_pull (𝓞 F) _ _ A _ _ (pullback.fst _ _) act aL hAL hLc Ω (spMap g') σ 0
  have hx : spMap g' ≫ spMap (algebraMap K L) = spMap g := by rw [← hg', spMap_comp]
  have e2 := GlobalTheory.LiePull.lieMult_pull (𝓞 F) _ _ G _ _ φ aG aL hφ hGc Ω (spMap g') σ 0
  have hG0 : LieMult aG (spMap (g'.comp (algebraMap W L))) σ 0 := by
    rw [spMap_comp]
    exact e2.1 (e1.2 (hx ▸ hL))
  haveI : CharZero Ω := charZero_of_injective_ringHom g.injective
  have hinj : Function.Injective (g'.comp (algebraMap W L)) :=
    g'.injective.comp (IsFractionRing.injective W L)
  exact GlobalTheory.T.isAbelianScheme_semiAbelian_dvr_noSpecialTorus W L G hsemi (proper_pull A G hM hA) E
    (finrank_zero W G hsemi F aG Ω _ hinj σ hG0 E)

end GlobalTheory.PotGoodLie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceLeTopLevelClassSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LevTopCong

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

theorem KO_le_symPr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {G : Grid k} (hs : 1 ≤ G.s) (J : G.Level) (g : G.VertexGroup) {j : ℕ} (hj : j < G.m)
    (hJ : J (G.m, j) = KO k _)
    (hc : ∀ x : GL (Fin (topRank G j)) k, toFrame hs hj (g (G.m, j)) * embX (G.m - 1 - j) x =
      embX (G.m - 1 - j) x * toFrame hs hj (g (G.m, j))) :
    KO k (Fin (topRank G j)) ≤ symPr (conjLevel hs J g hj) := by
  intro x hx
  refine ⟨1, one_mem _, ?_⟩
  rw [one_mul, conjLevel, Subgroup.map_equiv_eq_comap_symm', Subgroup.mem_comap]
  refine ⟨(g (G.m, j))⁻¹ * (toFrame hs hj).symm (embX _ x) * g (G.m, j), ?_, ?_⟩
  · rw [hJ]
    have e : toFrame hs hj ((g (G.m, j))⁻¹ * (toFrame hs hj).symm (embX _ x) * g (G.m, j)) = embX _ x := by
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
    exact OneCosetProof.mem_KO_of_frameGL _ (by
      have := GlobalTheory.TwistVertex.embX_mem_KO (c := G.m - 1 - j) hx
      rw [← e] at this
      exact this)
  · simp [mul_assoc]

end GlobalTheory.LevTopCong

namespace GlobalTheory.LevTopCong

open GlobalTheory.SplitWeil GlobalTheory.RootEx

theorem diag_comm_embX {k : Type} [Field k] {n : ℕ} {c : ℕ} (d : Fin c → kˣ) (x : GL (Fin n) k) :
    GlobalTheory.SplitFlip.diagGL (Sum.elim (fun _ => (1 : kˣ)) d) * embX c x =
      embX c x * GlobalTheory.SplitFlip.diagGL (Sum.elim (fun _ => (1 : kˣ)) d) := by
  refine Units.ext ?_
  have e : (diagonal fun i => ((Sum.elim (fun _ => (1 : kˣ)) d i : kˣ) : k)) =
      fromBlocks (1 : Matrix (Fin n) (Fin n) k) 0 0 (diagonal fun p => (d p : k)) := by
    ext (i | i) (j | j) <;> simp [Matrix.diagonal_apply, Matrix.one_apply]
  have hx : (embX c x).val = fromBlocks x.val 0 0 1 := rfl
  rw [Units.val_mul, Units.val_mul, GlobalTheory.SplitFlip.diagGL_val, e, hx, fromBlocks_multiply, fromBlocks_multiply]
  simp

end GlobalTheory.LevTopCong

namespace GlobalTheory.LevTopCong

open GlobalTheory.SplitWeil GlobalTheory.RootEx

theorem KO_le_pr_stair {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] {G : GlobalTheory.SplitFlip.Grid k} (hs : 1 ≤ G.s) (J : G.Level)
    (hJ : ∀ j, 0 < j → j < G.m → J (G.m, j) = KO k _) (ϖ : kˣ) (e : ℕ) (β : Cosets hs J)
    (hβ : ∀ i, β i = DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) {j : ℕ} (hj0 : 0 < j) (hj : j < G.m) :
    KO k (Fin (topRank G j)) ≤ symPr (conjLevel hs J ((Reps.through hs J (stair G ϖ e)).elt β) hj) := by
  refine KO_le_symPr hs J _ hj (hJ j hj0 hj) fun x => ?_
  obtain rfl : β = fun i : Fin (G.m - 2) => DoubleCoset.mk _ _ (stair G ϖ e (i + 1)) := funext hβ
  by_cases h2 : j + 2 ≤ G.m
  · rw [through_elt _ h2, toFrame_stair]
    exact diag_comm_embX _ _
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have e1 : (Reps.through hs J (stair G ϖ e)).elt (fun i : Fin (G.m - 2) => DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) (G.m, i + 1) = 1 := by
      rw [Reps.elt, onColumn_apply]
      simp [show ¬ i < G.m - 2 by omega]
    rw [e1, map_one, one_mul, mul_one]

end GlobalTheory.LevTopCong


open GlobalTheory.SplitWeil in
theorem GlobalTheory.LevTopCong.congLev_le_levTop : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x → ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F → ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK → ∀ (Φ : ch.G.Datum), ∀ β ∈ ch.S.supp A.μ0 Φ, ∀ j : Fin D.R.m, congLev D.sp.cm (ch.G.V (.top j)).gram (ch.G.Λ (.top j)) ch.G.modul ≤ ch.S.levTop A.μ0 Φ β j j.2 := by
  obtain ⟨CF0, hB⟩ := GlobalTheory.RowVal.oneAt
  refine ⟨CF0, fun CF hCF ε => ?_⟩
  obtain ⟨x₀, hx⟩ := hB ε CF hCF
  refine ⟨x₀, fun D large₂ hε hx0 Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch hsc _ Φ β hβ j => ?_⟩
  have hone := hx D large₂ hε hx0 Γ Pl0 T A Ks R F s ch hch hsc A.μ0 Φ β hβ
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hQ : R.Q A.μ0 = ∅ := Formalism.IndefR.FWT.Q_base_empty R hL
  obtain ⟨j, hj⟩ := j
  cases j with
  | zero => exact le_rfl
  | succ j =>
    intro g hg
    have hfr := ch.S.βp_is (j + 1) hj.le
    have hSt : g ∈ St (ch.S.βp (j + 1)) :=
      (GlobalTheory.LevSplit.mem_St_iff _ _ hfr g).2 (GlobalTheory.CongMember.stab_of_mem_congLev hg)
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun w => ?_,
      Subgroup.mem_iInf.2 fun w' => Subgroup.mem_iInf.2 fun _ => LevRowSucc.KO_of_St rfl _ _ hSt⟩
    have hw0 : w.1 ∈ ch.G.pl.W0 := by
      have h2 := w.2
      simp only [locPl, Finset.mem_union] at h2
      rcases h2 with h2 | h2
      · exact h2
      · have h4 : (w : Pl D.host.E) ∈ R.Q A.μ0 := h2
        rw [hQ] at h4
        exact absurd h4 (Finset.notMem_empty _)
    refine GlobalTheory.LevTopCong.KO_le_pr_stair one_le_sLen _
      (fun i hi0 hi => GlobalTheory.RowVal.givenLevel_inner _ _ _ _ (by change 1 ≤ D.R.m; omega) hi0) _ _ (β w) (hone w hw0)
      j.succ_pos hj ?_
    exact LevRowSucc.KO_of_St _ _ _ hSt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperSemiAbelianAffineOpenBaseChangeCompactCove
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin

namespace GlobalTheory

theorem pullback_fromSpec_compact_affineCover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → ∀ (U : X.affineOpens) (J : Type) (W : J → t.G.left.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → CompactSpace ↑(pullback t.G.hom U.2.fromSpec : Scheme.{0}) ∧ (∀ I : Finset J, I.Nonempty → IsAffineOpen (⨅ i ∈ I, pullback.fst t.G.hom U.2.fromSpec ⁻¹ᵁ W i)) ∧ ⨆ i, pullback.fst t.G.hom U.2.fromSpec ⁻¹ᵁ W i = ⊤ := by
  intro E _ _ _ H X t hP U J W hW hcov
  have hsep : IsSeparated t.G.hom := t.semi.separated
  have hU : IsAffineOpen U.1 := U.2
  have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  have : IsOpenImmersion (pullback.fst t.G.hom hU.fromSpec) := inferInstance
  refine ⟨?_, ?_, ?_⟩
  · exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd t.G.hom hU.fromSpec)
  · intro I hI
    have := GlobalTheory.isAffineHom_diagonal_of_isSeparated (pullback.snd t.G.hom hU.fromSpec)
    refine GlobalTheory.isAffineOpen_finset_biInf (fun i => ?_) I hI
    have hle : W i ≤ (pullback.fst t.G.hom hU.fromSpec).opensRange := by
      intro x hx
      have hx' : x ∈ t.G.hom ⁻¹ᵁ U.1 := hcov ▸ (le_iSup W i) hx
      have hy : t.G.hom x ∈ Set.range hU.fromSpec := by
        rw [hU.range_fromSpec]; exact hx'
      obtain ⟨y, hy⟩ := hy
      obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
      exact ⟨z, hz⟩
    rw [← (pullback.fst t.G.hom hU.fromSpec).isAffineOpen_iff_of_isOpenImmersion,
      Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.2 hle]
    exact hW i
  · rw [← Scheme.Hom.preimage_iSup, hcov, ← Scheme.Hom.comp_preimage, pullback.condition,
      Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self, Scheme.Hom.preimage_top]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudExtensionInvariantFieldCoeffsUnique
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TangentOrigin

noncomputable section

namespace GlobalTheory.HxUniq

open GlobalTheory.KS (rsT_self eq_of_rsT_eq)

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem evalPt_lieExp_comb {m : ℕ} (u : Fin m → TanM (𝟙 (Sp R)) G) (dd : Fin m → Fld G.left)
    (hd : ∀ i, IsInv G (u i) (dd i)) (B : Type) [CommRing B] [Algebra R B] (e : Fin m → B)
    (he : ∀ i j, e i * e j = 0) (z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ G) (O : G.left.Opens)
    (h : ⊤ ≤ z.left ⁻¹ᵁ O) :
    ∃ h' : ⊤ ≤ (GlobalTheory.SqZero.lieExp (fun i => GlobalTheory.VertCoeffRing.tvE (u i)) e (fun i => he i i) * z).left ⁻¹ᵁ O, ∀ f,
      evalPt _ O h' f = evalPt z.left O h f + ∑ i, e i * evalPt z.left O h (dd i O f) := by
  induction m with
  | zero =>
    have : GlobalTheory.SqZero.lieExp (fun i => GlobalTheory.VertCoeffRing.tvE (u i)) e (fun i => he i i) * z = z := by
      simp [GlobalTheory.SqZero.lieExp]
    rw [this]
    exact ⟨h, fun f => by simp⟩
  | succ m ih =>
    obtain ⟨h₁, H₁⟩ := ih (fun i => u i.succ) (fun i => dd i.succ) (fun i => hd i.succ) (fun i => e i.succ)
      (fun i j => he _ _)
    obtain ⟨h₂, H₂⟩ := GlobalTheory.VertCoeffRing.evalPt_tvE_mul (hd 0) (e 0) (he 0 0) _ O h₁
    have : GlobalTheory.SqZero.lieExp (fun i => GlobalTheory.VertCoeffRing.tvE (u i)) e (fun i => he i i) * z =
        (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.epsTo R (e 0) (he 0 0)) ≫ GlobalTheory.VertCoeffRing.tvE (u 0)) *
          (GlobalTheory.SqZero.lieExp (fun i => GlobalTheory.VertCoeffRing.tvE (u i.succ)) (fun i => e i.succ)
            (fun i => he i.succ i.succ) * z) := by
      rw [GlobalTheory.SqZero.lieExp, GlobalTheory.SqZero.lieExp, Fin.prod_univ_succ, _root_.mul_assoc]
    rw [this]
    refine ⟨h₂, fun f => ?_⟩
    rw [H₂, H₁, H₁, Fin.sum_univ_succ, mul_add, Finset.mul_sum]
    simp only [← _root_.mul_assoc, he, zero_mul, Finset.sum_const_zero]
    ring

theorem coeff_eq_zero [Smooth G.hom] {n : ℕ} (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G))
    (dd : Fin n → Fld G.left) (hd : ∀ a, IsInv G (v a) (dd a)) (W : G.left.Opens) (c : Fin n → Γ(G.left, W))
    (hc : ∀ Wo : G.left.Opens, Wo ≤ W → ∀ f, ∑ a, rsT (c a) Wo * dd a Wo f = 0) (a : Fin n) : c a = 0 := by
  let J := {V : G.left.Opens // IsAffineOpen V ∧ V ≤ W}
  have hcov : W ≤ ⨆ k : J, k.1 := by
    intro x hx
    obtain ⟨V, hV, hxV, hVW⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 (G.left.isBasis_affineOpens)) hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, hV, hVW⟩, hxV⟩
  refine eq_of_rsT_eq (fun k : J => k.1) (fun k => k.2.2) hcov _ _ fun k => ?_
  rw [GlobalTheory.KS.rsT_zero]
  obtain ⟨V, hV, hVW⟩ := k
  have hu := GlobalTheory.VertCoeffRing.existsUnique_coeff_affine_ring (fun a => GlobalTheory.VertCoeffRing.tvE (v a))
    (GlobalTheory.VertCoeffRing.isLieBasis_tvE v) dd
    (fun B _ _ e he z O h => evalPt_lieExp_comb (fun a => v a) dd hd B e he z O h) V V hV hV le_rfl
    (fun _ => 0) (fun _ _ => by simp) (fun _ _ => by simp) (fun _ => rfl)
  have h1 : ∀ f, (fun _ => (0 : Γ(G.left, V))) f = ∑ a, (fun a => rsT (c a) V) a * rsT (dd a V f) V := by
    intro f
    simp only [rsT_self]
    exact (hc V hVW f).symm
  have h0 : ∀ f, (fun _ => (0 : Γ(G.left, V))) f = ∑ a, (fun _ => (0 : Γ(G.left, V))) a * rsT (dd a V f) V := by
    intro f; simp
  exact congrFun (hu.unique h1 h0) a

end GlobalTheory.HxUniq

theorem GlobalTheory.HxUniq.raynaud_coeff_eq_zero : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (W : Y.H.left.Opens) (c : Fin n → Γ(Y.H.left, W)), (∀ Wo : Y.H.left.Opens, Wo ≤ W → ∀ f, ∑ a, rsT (c a) Wo * dd a Wo f = 0) → ∀ a, c a = 0 := by
  intro R _ _ Q O _ _ _ oa Y n v dd hd W c hc a
  have : Smooth Y.H.hom := (GlobalTheory.isSemiAbelian_of_isGt _ _ _ Y.isGt).smooth
  exact GlobalTheory.HxUniq.coeff_eq_zero v dd hd W c hc a
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjointIffBiextensionPullbacksIsomorphicStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rosati_adjoint_iff_biextension_pullbacks_isomorphic : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ P : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (La : Type) [AddCommGroup La] (Q : La →+ (Fin g → ℂ)) (EF : LinearMap.BilinForm ℤ La), IsExp (𝟙 (Sp ℂ)) e → Function.Injective Q → (∀ z, e z = 1 ↔ z ∈ Q.range) → (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) → ∀ (f f' : A ⟶ A) (u u' : La →+ La), IsMonHom f → IsMonHom f' → (∀ (k : ℕ) x, 0 < k → e ((k : ℂ)⁻¹ • Q (u x)) = e ((k : ℂ)⁻¹ • Q x) ≫ f) → (∀ (k : ℕ) x, 0 < k → e ((k : ℂ)⁻¹ • Q (u' x)) = e ((k : ℂ)⁻¹ • Q x) ≫ f') → (LBIso (P.pull (lift (fst A A ≫ f) (snd A A)).left) (P.pull (lift (fst A A) (snd A A ≫ f')).left) ↔ ∀ x y, EF (u x) y = EF x (u' y)) := by
  first | (exact @GlobalTheory.RosatiFormAdj.lbIso_pull_iff_adjoint) | (exact GlobalTheory.RosatiFormAdj.lbIso_pull_iff_adjoint) | (intros; apply GlobalTheory.RosatiFormAdj.lbIso_pull_iff_adjoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDescentFromCompleteRegularCharts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem descent_semiAbelian : ∀ (X S : Scheme.{0}) [AlgebraicGeometry.IsNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (j : X ⟶ S) [IsOpenImmersion j], IsDominant j → ∀ (A : Over X) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → RelAmple A L → (∀ x : S, Nonempty (Chart j A x)) → ∃ (G : Over S) (_ : GrpObj G) (e : A.left ⟶ G.left), IsSemiAbelian G ∧ IsGrpPullback A G j e ∧ ∀ (x : S) (C : Chart j A x), ∃ π : C.G.left ⟶ G.left, IsGrpPullback C.G G C.ξ π ∧ C.α ≫ e = pullback.fst C.G.hom (jK C.R) ≫ π := by
  intro X S _ hS j _ hj A _ hA L hL hamp hC
  have hloc := _root_.GlobalTheory.Desc.exists_hasExt_near X S hS j hj A hA L hL hamp hC
  obtain ⟨G, iG, e, hsemi, hpb⟩ := _root_.GlobalTheory.ExtGlue.hasExt_of_locally X S hS j hj A hA hloc
  exact ⟨G, iG, e, hsemi, hpb, fun x C => _root_.GlobalTheory.Desc.exists_grpPullback_chart_to_ext X S j hj A G e hsemi hpb x C⟩

end GlobalTheory.Desc
end

