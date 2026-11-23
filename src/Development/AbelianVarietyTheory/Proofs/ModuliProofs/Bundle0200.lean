module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFamilyAdditionMorphismThetaLevel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0077
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0071
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLaws
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
theorem _root_.GlobalTheory.closing_of_abelianSchemeLaws : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.N1c :=
  _root_.GlobalTheory.familyUnif_of_laws _root_.GlobalTheory.abelianSchemeLaws_all.1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAdditionMorphismThetaFamilyNearGoodPrime
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild
open GlobalTheory.ZM.BuildAdd

noncomputable section
namespace GlobalTheory.ZM.NearBuild

theorem exists_add_near : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (Z : Over (Sp R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (q₀ : Ideal R), Den b Mat κ β v q₀ → Fam b Mat κ β v (n ^ 2) M th sc → Smooth Z.hom → ∃ f : R, f ∉ q₀ ∧ ∀ (R' : Type) [CommRing R'] (ρ : R →+* R'), IsUnit (ρ f) → ∀ (Z' : Over (Sp R')) (π : Z'.left ⟶ Z.left), IsPullback π Z'.hom Z.hom (spMap ρ) → ∃ mu : Z' ⊗ Z' ⟶ Z', AddOk b Mat κ β v (n ^ 2) M th sc ρ π mu := by
  intro hL hL2 g J _ Mat κ n hn hodd
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.cutBy_graph_addition hL hL2 g J Mat κ n hn hodd
  refine ⟨j₀, fun j hj o _ b R _ _ _ β v Z M th sc q₀ hDen hFam hSm => ?_⟩
  obtain ⟨Q, d, hQ⟩ := hj₀ j hj o b
  have : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)⟩
  obtain ⟨⟨I, p, hPR, hp⟩, -, hfib⟩ := hFam
  obtain ⟨I₂, M₂, th₂, hPR₂, hseg⟩ :=
    GlobalTheory.SegreCoord.exists_segre_coordinates R (Ix g ((n ^ j) ^ 2)) I Z M th hPR
  have hP1 := (GlobalTheory.ZM.projRep_projective_ample _ _ _ _ _ _ hPR).2.1
  have hP2 := (GlobalTheory.ZM.projRep_projective_ample _ _ _ _ _ _ hPR₂).2.1
  have hS2 : Smooth (Z ⊗ Z).hom := by
    have := hSm
    rw [Over.tensorObj_hom]
    infer_instance
  let G : ∀ (K : Type) [Field K] (x : R →+* K), (pullback (Z ⊗ Z).hom (spMap x) ⟶ Z.left) → Prop :=
    fun K _ x φ => ∃ (_ : IsAlgClosed K) (s : Sp K ⟶ Sp o) (t : TObj g ((n ^ j) ^ 2) J b s)
      (ψ : t.A.left ⟶ Z.left) (e : (t.A ⊗ t.A).left ⟶ pullback (Z ⊗ Z).hom (spMap x)), IsIso e ∧
      Good b Mat κ β v x t ∧ Fib (n ^ 2) M th sc x t ψ ∧ IsSquare ψ (e ≫ pullback.fst _ _) ∧
      e ≫ pullback.snd _ _ = (t.A ⊗ t.A).hom ∧ e ≫ φ = (μ[t.A]).left ≫ ψ
  have mk : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (s : Sp K ⟶ Sp o)
      (t : TObj g ((n ^ j) ^ 2) J b s) (ψ : t.A.left ⟶ Z.left), Good b Mat κ β v x t →
      Fib (n ^ 2) M th sc x t ψ → ∀ φ₂ : (t.A ⊗ t.A).left ⟶ (Z ⊗ Z).left, IsSquare ψ φ₂ → ∃ φ, G K x φ := by
    intro K _ _ x s t ψ hG hF φ₂ hsq
    have hpb := GlobalTheory.ZM.BuildAdd.isPullback_square hF.1 φ₂ hsq
    refine ⟨hpb.isoPullback.inv ≫ (μ[t.A]).left ≫ ψ, inferInstance, s, t, ψ, hpb.isoPullback.hom, inferInstance, hG, hF, ?_,
      hpb.isoPullback_hom_snd, by simp⟩
    rw [hpb.isoPullback_hom_fst]
    exact hsq
  have hGprop : ∀ (K : Type) [Field K] (x : R →+* K) (φ : pullback (Z ⊗ Z).hom (spMap x) ⟶ Z.left), G K x φ →
      φ ≫ Z.hom = pullback.snd _ _ ≫ spMap x ∧
      CutBy (graphIdeal (pullback.snd (Z ⊗ Z).hom (spMap x)) M₂ th₂ (pullback.fst _ _) M th φ) Q d
        (fun (h : Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j) ^ 2)) (i : (Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j) ^ 2)) × Ix g ((n ^ j) ^ 2)) =>
          x ((p h.1 i.1.1 * p h.2 i.1.2) * p (h.1 + h.2) i.2)) := by
    intro K _ x φ hφ
    obtain ⟨_, s, t, ψ, e, _, hG, hF, hsq, hsn, heφ⟩ := hφ
    have hw : ψ ≫ Z.hom = t.A.hom ≫ spMap x := hF.1.w
    refine ⟨?_, ?_⟩
    · rw [← cancel_epi e, reassoc_of% heφ, reassoc_of% hsn, hw, ← Category.assoc, Over.w]
    have hs : s = spMap (x.comp β) := hG.1.trans (spMap_comp x β).symm
    subst hs
    obtain ⟨-, ⟨σ, hEmb, hσ⟩, -, hlab⟩ := hF
    obtain ⟨N₂, t₂, hN₂, hseg₂, heq⟩ :=
      GlobalTheory.ZM.BuildAdd.graph_transport x Z M th M₂ th₂ hPR₂.1 hseg t.A ψ _ σ hσ e hsq hsn φ heφ
    rw [← heq]
    have hl : ∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ n ^ j)).left (fun a => x (p h a)) := by
      intro h
      rw [hσ, ← Category.assoc, ← Over.comp_left, lift_snd, hlab h]
      have hx : (sc h).left ≫ Z.hom = spMap (RingHom.id R) := by
        rw [Over.w]
        simp [Out.baseOver, spMap]
      have hu := (hPR.2.1 R (RingHom.id R) (sc h).left (p h) hx (hp h)).1
      exact GlobalTheory.SegreCoord.secCoord_of_loc (GlobalTheory.SegreCoord.unimod_map hu x)
        ((GlobalTheory.SegreCoord.loc_of_secCoord (hp h)).baseChange x)
    have := hQ K (x.comp β) t σ (fun h a => x (p h a)) N₂ t₂ hN₂ hEmb hseg₂ hl
    simp only [map_mul]
    exact this
  have hDense : DenseP {q | ∃ (K : Type) (_ : Field K) (x : R →+* K) (φ : _), RingHom.ker x = q ∧ G K x φ} := by
    intro f hf
    apply hDen.1 f
    intro q hq hqp
    obtain ⟨K, _, _, x, t, hker, hsh, hth⟩ := hq
    have hG : Good b Mat κ β v x t := ⟨rfl, hsh, hth⟩
    obtain ⟨ψ, hψ⟩ := hfib K x _ t hG
    obtain ⟨φ₂, hsq⟩ := GlobalTheory.ZM.BuildAdd.exists_isSquare hψ.1.w
    obtain ⟨φ, hφ⟩ := mk K x _ t ψ hG hψ φ₂ hsq
    exact hf q ⟨K, inferInstance, x, φ, hker, hφ⟩ hqp
  obtain ⟨K₀, _, _, x₀, t₀, hker₀, hsh₀, hth₀⟩ := hDen.2
  have hG₀ : Good b Mat κ β v x₀ t₀ := ⟨rfl, hsh₀, hth₀⟩
  obtain ⟨ψ₀, hψ₀⟩ := hfib K₀ x₀ _ t₀ hG₀
  obtain ⟨φ₂₀, hsq₀⟩ := GlobalTheory.ZM.BuildAdd.exists_isSquare hψ₀.1.w
  obtain ⟨φ₀, hφ₀⟩ := mk K₀ x₀ _ t₀ ψ₀ hG₀ hψ₀ φ₂₀ hsq₀
  obtain ⟨f, hf0, H⟩ := GlobalTheory.ZM.NearBuild.exists_hom_of_graphs_of_isUnit R
    (Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j) ^ 2)) (Ix g ((n ^ j) ^ 2)) (Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j) ^ 2))
    (Z ⊗ Z) Z I₂ I M₂ M th₂ th (fun h i => p h.1 i.1 * p h.2 i.2) (fun h c => p (h.1 + h.2) c) Q d G
    hPR₂ hPR hP2 hP1 hS2 hGprop hDense K₀ x₀ φ₀ hφ₀
  refine ⟨f, fun hf => hf0 ?_, ?_⟩
  · rw [← hker₀] at hf
    exact RingHom.mem_ker.mp hf
  intro R' _ ρ hu Z' π hπ
  obtain ⟨π₂, hsqπ⟩ := GlobalTheory.ZM.BuildAdd.exists_isSquare hπ.w
  have hpbπ := GlobalTheory.ZM.BuildAdd.isPullback_square hπ π₂ hsqπ
  obtain ⟨F, hF, hU⟩ := H R' ρ hu (Z' ⊗ Z').left π₂ (Z' ⊗ Z').hom hpbπ.w
  refine ⟨Over.homMk (hπ.lift F (Z' ⊗ Z').hom hF) (hπ.lift_snd _ _ _), ?_⟩
  intro K _ _ x s t φ hG hFib hφw φ₂ hsq
  have hpb1 : IsPullback φ t.A.hom Z'.hom (spMap x) := by
    refine IsPullback.of_right ?_ hφw hπ
    rw [← spMap_comp]
    exact hFib.1
  have hpb2 := GlobalTheory.ZM.BuildAdd.isPullback_square hpb1 φ₂ hsq
  have hsq' : IsSquare (φ ≫ π) (φ₂ ≫ π₂) := by
    constructor
    · rw [Category.assoc, hsqπ.1, reassoc_of% hsq.1]
    · rw [Category.assoc, hsqπ.2, reassoc_of% hsq.2]
  have hpb3 := GlobalTheory.ZM.BuildAdd.isPullback_square hFib.1 (φ₂ ≫ π₂) hsq'
  have hGφ : G K (x.comp ρ) (hpb3.isoPullback.inv ≫ (μ[t.A]).left ≫ φ ≫ π) :=
    ⟨inferInstance, s, t, φ ≫ π, hpb3.isoPullback.hom, inferInstance, hG, hFib,
      by rw [hpb3.isoPullback_hom_fst]; exact hsq', hpb3.isoPullback_hom_snd, by simp⟩
  have key := hU K (x.comp ρ) _ hGφ (hpb3.isoPullback.inv ≫ φ₂)
    (by rw [Category.assoc]; exact hpb3.isoPullback_inv_fst)
  rw [Category.assoc, cancel_epi] at key
  show φ₂ ≫ hπ.lift F (Z' ⊗ Z').hom hF = (μ[t.A]).left ≫ φ
  apply hπ.hom_ext
  · rw [Category.assoc, hπ.lift_fst, Category.assoc]
    exact key.symm
  · rw [Category.assoc, hπ.lift_snd, Category.assoc, hφw, ← Category.assoc, Over.w]
    exact hpb2.w

end GlobalTheory.ZM.NearBuild
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBaseChangeUniformization
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorsionFormCompare
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.TorsionFormCompare


open UnifBaseChange ExpandsLinear in
theorem exists_unif_pull_of_deg (hP : PolBaseChangeSt) (hG : GlobalFnsSt) (hS : SecBaseChangeSt)
    (hT : DVR.TwistBaseChangeStatement)
    (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R)
    (I' : Ideal R') (hR : AdmBase R I) (hR' : AdmBase R' I') (φ : R →+* R') (hI : I.map φ ≤ I')
    (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R))))
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (hsa : IsSemiAbelian G)
    (U : Unif I D A G) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (hgD : D'.toPre.P.g = D.toPre.P.g)
    (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G']
    (bc : G' ≅ (Over.pullback (specOf φ)).obj G) (hbc : IsMonHom bc.hom)
    (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (hg : A'.g = A.g)
    (eA : (Over.pullback (jK R')).obj G' ≅ A'.A) (heA : IsMonHom eA.hom)
    (hwA : ∃ wA : LB.Iso (A'.L.pull eA.hom.left)
      (U.LG.L.pull (pullback.fst G'.hom (jK R') ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ))), wA.IsGen)
    (L' : RigLB G') (wL : LB.Iso L'.L (U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (specOf φ))))
    (he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) = specOf φ ≫ eSec G)
    (hwL : wL.IsGen)
    (hrig : LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L'.rig
      (rigPullOf (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) (specOf φ) he U.LG.L U.LG.rig)) :
    ∃ U' : Unif I' D' A' G', U'.LG = L' ∧ U'.gen = eA ∧ IsPullUnif φ hD bc U U' := by
  obtain ⟨U', wL', hL, hgen, hw, hlev⟩ := exists_unifPre_pull hG R R' I I' φ D D' hD A A' G G' bc hI hbc
    U.toUnifPre eA heA hwA L' wL he hwL hrig
  subst hL
  obtain rfl := eq_of_heq hw
  haveI := hsa.geomConnected
  haveI := hsa.quasiCompact
  haveI : GeometricallyConnected G'.hom := by
    rw [← Over.w bc.hom]
    have : IsIso bc.hom.left := ((Over.forget _).mapIso bc).isIso_hom
    have : GeometricallyConnected ((Over.pullback (specOf φ)).obj G).hom :=
      inferInstanceAs (GeometricallyConnected (pullback.snd G.hom (specOf φ)))
    exact MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_horiz_isIso (fst := bc.hom.left) (f := ((Over.pullback (specOf φ)).obj G).hom) (g := 𝟙 _)
        ⟨(Category.comp_id _).symm⟩) this
  haveI := hR.1
  haveI := hR'.1
  have hexp : ∀ k : ℕ, 1 ≤ k → U'.ExpBij k := by
    intro k hk
    obtain ⟨-, hd⟩ := FamDim.finrank_fam hG hP hT R D.toPre D.tau_bimult (psiOnExists R I hR D) (FractionRing R) k hk
    obtain ⟨hfin, hd'⟩ := FamDim.finrank_fam hG hP hT R' D'.toPre D'.tau_bimult (psiOnExists R' I' hR' D')
      (FractionRing R') k hk
    have hdA := finrank_fam_of_expBij hS R I hR D A G U.toUnifPre k hk (U.expand k hk)
    have hrk : D'.toPre.rank = D.toPre.rank := hD.xe.toIntLinearEquiv.finrank_eq
    refine ExpansionCriterion.expBij_of_onto hS R' I' hR' D' A' G' U' k hk hfin (by rw [hd', hrk, hgD, ← hd, hdA, hg]) fun F₀ => ?_
    obtain ⟨n, F, f, F', f', hF, hspan⟩ := _root_.GlobalTheory.FamSpan.exists_span hP hG hT R R' I hR φ D D'.toPre hD k hk
    have hb : ∀ i, ∃ b : U'.SecK k, U'.Expands k b (F' i) := by
      intro i
      obtain ⟨σ, hσ⟩ := exists_sec_expandsAt_of_integral_family R I hR D A G U.toUnifPre k (fun F => ((U.expand k hk).2 F).exists) (F i) (f i)
        (hF i).1
      obtain ⟨σ', hσ', -⟩ := SecPull.existsUnique_secPull _ _ _ _ U.LG.L U'.LG.L _ U.LG.isLB U'.LG.isLB wL' hwL
        (Fin 1) (fun _ => 𝟙 G'.left) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))
        (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) (fun _ => by rw [Category.id_comp, Category.comp_id]) σ
      obtain ⟨b, hb⟩ := exists_secScal_one U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => (k : ℤ))
        (pullback.fst G'.hom (jK R')) (fun _ => pullback.fst G'.hom (jK R'))
        (funext fun _ => (Category.comp_id _).symm) σ'
      refine ⟨b, 1, one_ne_zero, σ', f' i, by rw [scal_one]; exact hb,
        fun α => by rw [scal_one]; exact (hF i).2.1 α, fun e => ?_⟩
      obtain ⟨h, hh⟩ := hlev e
      exact expandsAt_transport R R' I I' D D' A A' G G' U.toUnifPre U' _ hD.w hD.xe _ wL' hD.w_gen hwL
        (ExpGTrans.famφB_pull hD) e e k h ⟨hh.1, hh.2⟩ σ σ' (f i) (f' i) hσ' (hF i).2.2 (hσ e)
    choose b hb using hb
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hspan ▸ Submodule.mem_top : F₀ ∈ _)
    exact ⟨secComb (fun i => scal (pullback.snd G'.hom (jK R')) (c i)) b,
      expands_linear R' I' hR' D' A' G' U' k n b F' c _ hb fun _ => rfl⟩
  exact ⟨⟨U', hexp⟩, rfl, hgen,
    (isPullUnif_iff_stalks R R' I I' φ D D' hD A A' G G' bc U ⟨U', hexp⟩).2 ⟨wL', hwL, he, hrig, hlev⟩⟩

theorem RigAlong.read {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
    {ε : G' ⟶ G} [IsMonHom ε] {L : RigLB G} {L' : RigLB G'} {w : LB.Iso L'.L (L.L.pull ε.left)}
    (h : RigAlong ε L L' w) {F : G'.left ⟶ G.left} (hF : F = ε.left) {e : S ⟶ S} (he₀ : e = 𝟙 S) :
    ∃ (wL : LB.Iso L'.L (L.L.pull F)) (he : eSec G' ≫ F = e ≫ eSec G), wL.IsGen ∧
      LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L'.rig
        (rigPullOf F e he L.L L.rig) := by
  subst hF he₀
  have he : eSec G' ≫ ε.left = 𝟙 S ≫ eSec G := by
    refine Eq.trans ?_ (Category.id_comp _).symm
    exact congrArg (fun f => f.left) (IsMonHom.one_hom ε)
  exact ⟨w, he, h.1, (maps_iff _ _ (fun _ => eSec G) _ L'.rig L.rig (𝟙 _) _ (rigPull_le _ _ he L.L)
    (fun _ => rfl)).2 h.2⟩

theorem exists_unif_move : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G G' : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (ε : G' ≅ G), AdmBase R I → IsSemiAbelian G → IsMonHom ε.hom → ∀ (U : Unif I D A G) (L' : RigLB G') (w : LB.Iso L'.L (U.LG.L.pull ε.hom.left)), RigAlong ε.hom U.LG L' w → ∀ hD : IsPullDeg (RingHom.id R) D.toPre D.toPre, ∃ (bc : G' ≅ (Over.pullback (specOf (RingHom.id R))).obj G) (U' : Unif I D A G'), IsMonHom bc.hom ∧ bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = ε.hom.left ∧ U'.LG = L' ∧ U'.gen.hom = (Over.pullback (jK R)).map ε.hom ≫ U.gen.hom ∧ IsPullUnif (RingHom.id R) hD bc U U' := by
  intro R _ _ I D A G G' _ _ _ _ ε hR hsa hε U L' w hw hD
  have hs := specOf_id R
  have gp₁ : IsGrpPullback G' G (specOf (RingHom.id R)) ε.hom.left :=
    (isGrpPullback_of_iso ε).congr hs.symm rfl
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso gp₁ (isGrpPullback_pullback G (specOf (RingHom.id R)))
  have := U.gen_hom
  let eA : (Over.pullback (jK R)).obj G' ≅ A.A := (Over.pullback (jK R)).mapIso ε ≪≫ U.gen
  have mE : IsMonHom eA.hom := by
    show IsMonHom ((Over.pullback (jK R)).map ε.hom ≫ U.gen.hom)
    infer_instance
  have wA : LBIso (A.L.pull eA.hom.left) (U.LG.L.pull (pullback.fst G'.hom (jK R) ≫ bc.hom.left ≫
      pullback.fst G.hom (specOf (RingHom.id R)))) :=
    LBIso.chartPull (h := ((Over.pullback (jK R)).map ε.hom).left)
      (chartPullSame A.L (fun _ => eA.hom.left) (fun _ => U.gen.hom.left) _ _ fun _ => rfl)
      (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => by
        rw [hbc]; exact (pullback.lift_fst _ _ _).symm) U.ext
  obtain ⟨wL, he, gL, rL⟩ := hw.read hbc hs
  obtain ⟨U', hL, hgen, hPU⟩ := exists_unif_pull_of_deg GlobalTheory.abelianSchemeLaws_all.1.polBaseChange
    GlobalTheory.abelianSchemeLaws_all.1.globalFns GlobalTheory.abelianSchemeLaws_all.1.secBaseChange GlobalTheory.twistBaseChange
    R R I I hR hR (RingHom.id R) (by rw [Ideal.map_id]) D A G hsa U D hD rfl G' bc mbc A rfl eA mE wA L' wL he gL rL
  exact ⟨bc, U', mbc, hbc, hL, by rw [hgen]; rfl, hPU⟩

end GlobalTheory.TorsionFormCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsInversionEndomorphismsThetaLevelFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.EndBuild

theorem pow_val_natCast {A : Type} [Monoid A] {k : ℕ} (y : A) (hy : y ^ k = 1) (m : ℕ) :
    y ^ ((m : ZMod k)).val = y ^ m := by
  rw [ZMod.val_natCast, ← pow_eq_pow_mod m hy]

def labMap {g : ℕ} {J : Type} (k : ℕ) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (i : Option J) (h : Ix g k) : Ix g k :=
  i.elim (-h) (fun j i' => ((∑ c, (Mat j i' c : ZMod k).val * (h c).val : ℕ) : ZMod k))

theorem linComb_eq_prod {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] {r : ℕ}
    (y : Fin r → (T ⟶ A)) (a : Fin r → ℕ) : Out.linComb y a = ∏ i, y i ^ a i := by
  rw [Out.linComb, List.prod_ofFn]

theorem lab_comp {o : Type} [CommRing o] {S : Scheme.{0}} {g k : ℕ} [NeZero k] {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
    (t : TObj g k J b s) {Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ} {κ : ℕ} (ht : t.Shape Mat κ)
    (i : Option J) (h : Ix g k) :
    t.lab h ≫ (i.elim (𝟙 t.A)⁻¹ t.act : t.A ⟶ t.A) = t.lab (labMap k Mat i h) := by
  haveI := t.ab.comm
  cases i with
  | none =>
    simp only [Option.elim, labMap]
    rw [GrpObj.comp_inv, Category.comp_id]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [TObj.lab, TObj.lab, linComb_eq_prod, linComb_eq_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun c _ => ?_
    rw [← pow_add, ← pow_val_natCast _ (t.torsion c)]
    simp
  | some j =>
    simp only [Option.elim, labMap]
    haveI := t.hom j
    have e : t.lab h ≫ t.act j = ∏ c, (t.pt c ≫ t.act j) ^ (h c).val := by
      rw [TObj.lab, linComb_eq_prod]
      have := map_prod (IsMonHom.monoidHom (t.act j) (Out.baseOver S)) (fun c => t.pt c ^ (h c).val) Finset.univ
      simp only [map_pow] at this
      exact this
    rw [e, TObj.lab, linComb_eq_prod]
    simp only [(ht j).1, TObj.lab, linComb_eq_prod, ← Finset.prod_pow, ← pow_mul]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [pow_val_natCast _ (t.torsion c), Finset.prod_pow_eq_pow_sum]

theorem graphIdeal_le {R σ₁ σ₂ : Type} [CommRing R] {Y Y' X₁ X₂ X₁' X₂' : Scheme.{0}} (s : Y ⟶ Sp R) (s' : Y' ⟶ Sp R)
    (M₁ : LB X₁) (th₁ : σ₁ → M₁.Sec) (a₁ : Y ⟶ X₁) (M₂ : LB X₂) (th₂ : σ₂ → M₂.Sec) (a₂ : Y ⟶ X₂)
    (M₁' : LB X₁') (th₁' : σ₁ → M₁'.Sec) (a₁' : Y' ⟶ X₁') (M₂' : LB X₂') (th₂' : σ₂ → M₂'.Sec) (a₂' : Y' ⟶ X₂')
    (e : Y ⟶ Y') (he : e ≫ s' = s)
    (h₁ : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (w : σ₁ → T),
      SecCoord M₁ th₁ (y ≫ a₁) w → SecCoord M₁' th₁' (y ≫ e ≫ a₁') w)
    (h₂ : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (w : σ₂ → T),
      SecCoord M₂ th₂ (y ≫ a₂) w → SecCoord M₂' th₂' (y ≫ e ≫ a₂') w) :
    graphIdeal s' M₁' th₁' a₁' M₂' th₂' a₂' ≤ graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂ := by
  unfold graphIdeal
  refine le_iInf fun T => le_iInf fun _ => le_iInf fun β => le_iInf fun y => le_iInf fun v₁ => le_iInf fun v₂ =>
    le_iInf fun hy => ?_
  refine iInf_le_of_le T <| iInf_le_of_le inferInstance <| iInf_le_of_le β <| iInf_le_of_le (y ≫ e) <|
    iInf_le_of_le v₁ <| iInf_le_of_le v₂ <| iInf_le_of_le ⟨?_, ?_, ?_⟩ le_rfl
  · rw [Category.assoc, he, hy.1]
  · rw [Category.assoc]; exact h₁ _ _ _ hy.2.1
  · rw [Category.assoc]; exact h₂ _ _ _ hy.2.2

theorem graphIdeal_eq {R σ₁ σ₂ : Type} [CommRing R] {Y Y' X₁ X₂ X₁' X₂' : Scheme.{0}} (s : Y ⟶ Sp R) (s' : Y' ⟶ Sp R)
    (M₁ : LB X₁) (th₁ : σ₁ → M₁.Sec) (a₁ : Y ⟶ X₁) (M₂ : LB X₂) (th₂ : σ₂ → M₂.Sec) (a₂ : Y ⟶ X₂)
    (M₁' : LB X₁') (th₁' : σ₁ → M₁'.Sec) (a₁' : Y' ⟶ X₁') (M₂' : LB X₂') (th₂' : σ₂ → M₂'.Sec) (a₂' : Y' ⟶ X₂')
    (e : Y ⟶ Y') [IsIso e] (he : e ≫ s' = s)
    (h₁ : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (w : σ₁ → T),
      SecCoord M₁ th₁ (y ≫ a₁) w ↔ SecCoord M₁' th₁' (y ≫ e ≫ a₁') w)
    (h₂ : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (w : σ₂ → T),
      SecCoord M₂ th₂ (y ≫ a₂) w ↔ SecCoord M₂' th₂' (y ≫ e ≫ a₂') w) :
    graphIdeal s' M₁' th₁' a₁' M₂' th₂' a₂' = graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂ := by
  refine le_antisymm (graphIdeal_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ e he (fun T _ y w => (h₁ T y w).1)
    (fun T _ y w => (h₂ T y w).1)) (graphIdeal_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ (inv e) (by rw [← he, IsIso.inv_hom_id_assoc])
    (fun T _ y w hw => ?_) (fun T _ y w hw => ?_))
  · rw [← Category.assoc, h₁]; simpa using hw
  · rw [← Category.assoc, h₂]; simpa using hw

theorem cut_fibre {o R K : Type} [CommRing o] [CommRing R] [Field K] {g N m : ℕ} [NeZero (N ^ 2)] {J : Type}
    {b : TBase o (N ^ 2)} {Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ} {κ : ℕ} (i : Option J) (Q : Polynomial ℚ) (d : ℕ)
    {s : Sp K ⟶ Sp o} (t : TObj g (N ^ 2) J b s) (ht : t.Shape Mat κ)
    (σ : Ix g (N ^ 2) → LB.Sec (Out.LPow t.A t.L ((m : ℤ) ^ 2) (Over.mk (𝟙 _))))
    (hcut : ∀ (p q : Ix g (N ^ 2) → Ix g (N ^ 2) → K) (f : t.A ⟶ t.A), f = i.elim (𝟙 t.A)⁻¹ t.act →
      (∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ N)).left (p h) ∧
        SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) ((t.lab h ≫ f) ^ N)).left (q h)) →
      CutBy (graphIdeal (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ (𝟙 _) _ σ
        (lift (fst _ _) (snd (Over.mk (𝟙 (Sp K))) t.A ≫ f)).left) Q d (fun h i => p h i.1 * q h i.2))
    (Z : Over (Sp R)) (M : LB Z.left) (hM : M.IsLB) (th : Ix g (N ^ 2) → M.Sec)
    (sc : Ix g (N ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (p : Ix g (N ^ 2) → Ix g (N ^ 2) → R)
    (hp : ∀ h, SecCoord M th (sc h).left (p h)) (x : R →+* K) (φ : t.A.left ⟶ Z.left)
    (hφ : IsPullback φ t.A.hom Z.hom (spMap x))
    (hσ : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t.A).left) (w : Ix g (N ^ 2) → T),
      SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t.A).left ≫ φ) w)
    (hl : ∀ h, (t.lab h ^ N).left ≫ φ = spMap x ≫ (sc h).left) :
    CutBy (graphIdeal (pullback.snd Z.hom (spMap x)) M th (pullback.fst _ _) M th
      (hφ.isoPullback.inv ≫ (i.elim (𝟙 t.A)⁻¹ t.act : t.A ⟶ t.A).left ≫ φ)) Q d
      (fun h c => x (p h c.1 * p (labMap (N ^ 2) Mat i h) c.2)) := by
  have hpt : ∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ N)).left (fun a => x (p h a)) := by
    intro h
    refine (hσ K _ _).2 ?_
    have e : (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ N)).left ≫ (snd (Over.mk (𝟙 (Sp K))) t.A).left ≫ φ =
        spMap x ≫ (sc h).left := by
      rw [← hl h, ← Category.assoc, ← Over.comp_left, lift_snd]
    have := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ M _ th R (sc h).left (p h) hM (hp h)).1 K x
    exact e ▸ this
  have H := hcut (fun h a => x (p h a)) (fun h a => x (p (labMap (N ^ 2) Mat i h) a)) _ rfl
    (fun h => ⟨hpt h, by rw [lab_comp t ht]; exact hpt _⟩)
  haveI : IsIso (snd (Over.mk (𝟙 (Sp K))) t.A).left :=
    inferInstanceAs (IsIso (pullback.snd (𝟙 (Sp K)) t.A.hom))
  have hs : (snd (Over.mk (𝟙 (Sp K))) t.A).left ≫ t.A.hom = (fst (Over.mk (𝟙 (Sp K))) t.A).left :=
    (pullback.condition (f := 𝟙 (Sp K)) (g := t.A.hom)).symm.trans (Category.comp_id _)
  rw [graphIdeal_eq (fst (Over.mk (𝟙 (Sp K))) t.A).left (pullback.snd Z.hom (spMap x)) _ σ (𝟙 _) _ σ
    (lift (fst _ _) (snd (Over.mk (𝟙 (Sp K))) t.A ≫ (i.elim (𝟙 t.A)⁻¹ t.act : t.A ⟶ t.A))).left M th _ M th _
    ((snd (Over.mk (𝟙 (Sp K))) t.A).left ≫ hφ.isoPullback.hom)]
  · simpa only [map_mul] using H
  · rw [Category.assoc, IsPullback.isoPullback_hom_snd]; exact hs
  · intro T _ y w
    rw [hσ, Category.assoc, Category.assoc, IsPullback.isoPullback_hom_fst, Category.id_comp]
  · intro T _ y w
    rw [hσ, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc _ _ φ,
      ← Over.comp_left, lift_snd, Over.comp_left, Category.assoc]

theorem exists_endomorphisms : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (Z : Over (Sp R)) (I : Ideal (MvPolynomial (Ix g ((n ^ j) ^ 2)) R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → R), VeryDense (objPrimes b Mat κ β v) → (ProjRep I Z.hom M th ∧ SmoothOfRelativeDimension g Z.hom ∧ GeometricallyConnected Z.hom ∧ (∀ h, SecCoord M th (sc h).left (p h))) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x (v a)) → ∃ φ : t'.A.left ⟶ Z.left, (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left)) → ∃ F : Option J → (Z ⟶ Z), (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (φ : t'.A.left ⟶ Z.left), t'.Shape Mat κ → (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) → ∀ i : Option J, φ ≫ (F i).left = (i.elim (𝟙 t'.A)⁻¹ t'.act : t'.A ⟶ t'.A).left ≫ φ) := by
  intro hL hL2 g J _ Mat κ n hn hodd
  obtain ⟨j₀, hj₀⟩ := _root_.GlobalTheory.GraphCut.cutBy_graphIdeal hL hL2 g J Mat κ n hn hodd
  refine ⟨j₀, fun j hj o _ b R _ _ _ β v Z I M th sc p hvd hPF hfib => ?_⟩
  haveI : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)⟩
  obtain ⟨hrep, hsm, -, hp⟩ := hPF
  have hprop := (_root_.GlobalTheory.ZM.projRep_projective_ample R _ I Z M th hrep).2.1
  have hsm' : Smooth Z.hom := SmoothOfRelativeDimension.smooth g _
  have key : ∀ i : Option J, ∃ F : Z ⟶ Z, ∀ (K : Type) [Field K] (x : R →+* K) (f : pullback Z.hom (spMap x) ⟶ Z.left),
      (∃ (_ : IsAlgClosed K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (φ : t'.A.left ⟶ Z.left)
        (hφ : IsPullback φ t'.A.hom Z.hom (spMap x)), t'.Shape Mat κ ∧
        (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧
        (∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) ∧
        f = hφ.isoPullback.inv ≫ (i.elim (𝟙 t'.A)⁻¹ t'.act : t'.A ⟶ t'.A).left ≫ φ) →
      f = pullback.fst _ _ ≫ F.left := by
    intro i
    obtain ⟨Q, d, hQ⟩ := hj₀ j hj o b i
    refine _root_.GlobalTheory.ZM.GraphMor.exists_hom_of_graphs R _ _ (Ix g ((n ^ j) ^ 2)) Z Z I I M M th th p (fun h => p (labMap _ Mat i h)) Q d _
      hrep hrep hprop hprop hsm' ?_ ?_
    · rintro K _ x f ⟨_, t', φ, hφ, ht, ⟨σ, hE, hσ⟩, hl, rfl⟩
      refine ⟨?_, cut_fibre (m := n ^ 2) i Q d t' ht σ ?_ Z M hrep.1 th sc p hp x φ hφ hσ hl⟩
      · rw [Category.assoc, Category.assoc, hφ.w, ← Category.assoc (Option.elim _ _ _ : t'.A ⟶ t'.A).left, Over.w,
          ← Category.assoc, IsPullback.isoPullback_inv_snd]
      · have e : spMap x ≫ spMap β = spMap (x.comp β) := by rw [← Spec.map_comp]; rfl
        clear hσ hl hφ φ
        generalize spMap x ≫ spMap β = s at e t' ht σ hE
        subst e
        exact fun p' q' f hf h => hQ K (x.comp β) t' σ p' q' f ht hf hE h
    · intro q r hq hr
      obtain ⟨P, ⟨K, _, _, x, t', hx, ht, hth⟩, hP⟩ := hvd q r hq hr
      obtain ⟨φ, hφ, hσ, -, hl⟩ := hfib K x t' ht hth
      exact ⟨P, ⟨K, _, x, _, hx, inferInstance, t', φ, hφ, ht, hσ, hl, rfl⟩, hP⟩
  choose F hF using key
  refine ⟨F, fun K _ _ x t' φ ht hfb i => ?_⟩
  obtain ⟨hφ, hσ, -, hl⟩ := hfb
  have := hF i K x _ ⟨inferInstance, t', φ, hφ, ht, hσ, hl, rfl⟩
  rw [Iso.inv_comp_eq, IsPullback.isoPullback_hom_fst_assoc] at this
  exact this.symm

end GlobalTheory.ZM.EndBuild
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LocalModelSystemTransitionSiegelClausesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localModelSystem_transition_siegel_clauses : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ (S : System Xo) p W hp hW, N2 (S.Y p W hp hW) := by
  first | exact @GlobalTheory.Models.system_clauses | exact GlobalTheory.Models.system_clauses | (intros; apply GlobalTheory.Models.system_clauses <;> assumption)
end

