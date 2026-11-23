module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2465
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1450
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0086
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1916
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1913
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1889
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2429
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqTorusOfClassify
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2433

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamValTauAdd
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

section
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.LamRigid GlobalTheory.LamBiext

namespace GlobalTheory.MumfordE8Bimultiplicative

theorem lamVal_law₁ {S : Scheme.{0}} (B₀ B : Over S) [GrpObj B₀] [IsCommMonObj B₀] [GrpObj B] [IsCommMonObj B]
    (M₀ : RigLB B₀) (M : RigLB B) (c₀ : CubicalStr B₀ M₀) (c : CubicalStr B M) (hB₀ : IsAbelianScheme B₀)
    (a b : B₀ ⟶ B) [IsMonHom a] [IsMonHom b]
    (w : LB.Iso (abelian₂ B₀ M₀.L) ((abelian₂ B M.L).pull (lift (fst B₀ B₀ ≫ a) (snd B₀ B₀ ≫ b) : G2 B₀ ⟶ G2 B).left))
    (hw : w.IsGen)
    (hn : ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ B.left) → M.L.ι) (J' : (T.left ⟶ B₀.left) → M₀.L.ι),
      Good M.L z J → Good M₀.L z J' → GlobalTheory.PolDeg.lamVal w (lift (1 : T ⟶ B₀) (1 : T ⟶ B₀)).left z J J' = 1)
    (T : Over S) (x x' y : T ⟶ B₀) (z : T.left) (J : (T.left ⟶ B.left) → M.L.ι) (J' : (T.left ⟶ B₀.left) → M₀.L.ι)
    (hJ : Good M.L z J) (hJ' : Good M₀.L z J') :
    GlobalTheory.PolDeg.lamVal w (lift (x * x') y).left z J J' * cubV c₀ z J' x x' y =
      cubV c z J (x ≫ a) (x' ≫ a) (y ≫ b) * GlobalTheory.PolDeg.lamVal w (lift x y).left z J J' *
        GlobalTheory.PolDeg.lamVal w (lift x' y).left z J J' := by
  have hG := GlobalTheory.globalFns_holds
  have hL : (abelian₂ B M.L).IsLB := DVR.linComb_isLB _ M.isLB _ _
  have hL' : (abelian₂ B₀ M₀.L).IsLB := DVR.linComb_isLB _ M₀.isLB _ _
  let β₂ : (G2 B₀).left ⟶ (G2 B).left := (lift (fst B₀ B₀ ≫ a) (snd B₀ B₀ ≫ b) : G2 B₀ ⟶ G2 B).left
  have Hlam : ∀ {T₀ : Over S} (p q : T₀ ⟶ B₀) {U : Type} [CommGroup U] (h : (T₀.left ⟶ B.left) → U),
      ∏ i, h (((lift p q).left ≫ β₂) ≫ lamφ B i) ^ lamε i =
        h ((p ≫ a) * (q ≫ b)).left * (h (p ≫ a).left)⁻¹ * (h (q ≫ b).left)⁻¹ *
          h (1 : T₀ ⟶ B).left := fun p q U _ h => by
    rw [GlobalTheory.MumRigidZero.lift_comp_left]; exact prod_lam (p ≫ a) (q ≫ b) h
  obtain ⟨l₁, l₂, hl₁, hl₂, cl₁, cl₂, vl⟩ := exists_laws M₀ c₀
  let φ3 := law1φ B₀ (x3 B₀ 0) (x3 B₀ 1) (x3 B₀ 2)
  let β₃ : (G3 B₀).left ⟶ (G3 B).left := (lift (x3 B₀ 0 ≫ a) (lift (x3 B₀ 1 ≫ a) (x3 B₀ 2 ≫ b))).left
  have fe3 : FormEq (fun I => β₃ ≫ thφ B (x3 B) I) thε (flatφ (lamφ B) (fun k => φ3 k ≫ β₂)) (flatε lamε lawε) :=
    fun U _ h => by
      have e₁ := prod_cub (x3 B₀ 0 ≫ a) (x3 B₀ 1 ≫ a) (x3 B₀ 2 ≫ b) h
      have e₂ := prod_law₁ (x3 B₀ 0) (x3 B₀ 1) (x3 B₀ 2) (fun χ => ∏ i, h ((χ ≫ β₂) ≫ lamφ B i) ^ lamε i)
      rw [id₃] at e₂
      simp only [Over.id_left, Category.id_comp, Hlam, MonObj.mul_comp] at e₂
      rw [e₁, prod_flat, e₂]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
  obtain ⟨g₃, hg₃, hv₃⟩ := exists_gen M.isLB fe3 (LB.pullGen M.L (thφ B (x3 B)) thε c.t β₃)
    (DVR.pullGen_isGen _ _ _ _ c.isGen β₃)
  have ht₃ := nest_isGen (L := M.L) (φ := lamφ B) (δ := lamε) hg₃
  have Ft3 : ∀ {T₀ : Over S} (p p' q : T₀ ⟶ B₀) (z₀ : T₀.left) (J₀ : (T₀.left ⟶ B.left) → M.L.ι), Good M.L z₀ J₀ →
      val (L := abelian₂ B M.L) (nest M.L (lamφ B) lamε (fun k => φ3 k ≫ β₂) lawε g₃) (lift p (lift p' q)).left z₀ (ind B J₀) =
        cubV c z₀ J₀ (p ≫ a) (p' ≫ a) (q ≫ b) := by
    intro T₀ p p' q z₀ J₀ hJ₀
    show val (L := LB.LinComb M.L (lamφ B) lamε) (nest M.L (lamφ B) lamε (fun k => φ3 k ≫ β₂) lawε g₃) _ z₀ (ind B J₀) = _
    rw [val_nest hg₃ _ (good_ind hJ₀) hJ₀]
    simp only [adj_ind M.isLB hJ₀, one_zpow, Finset.prod_const_one, _root_.one_mul]
    rw [hv₃ _ _ z₀ J₀ hJ₀]
    refine (val_pull hJ₀ _ _ _).trans ?_
    refine congrArg (fun r => val (L := M.L) (φ := thφ B (x3 B)) (ε := thε) c.t r z₀ J₀) ?_
    show (lift p (lift p' q) ≫ lift (x3 B₀ 0 ≫ a) (lift (x3 B₀ 1 ≫ a) (x3 B₀ 2 ≫ b))).left =
      (lift (p ≫ a) (lift (p' ≫ a) (q ≫ b))).left
    simp only [comp_lift, ← Category.assoc, cartesian_lift_three_comp_projection]
    rfl
  have Fa3 : ∀ {T₀ : Over S} (p p' q : T₀ ⟶ B₀) (z₀ : T₀.left) (J₀' : (T₀.left ⟶ B₀.left) → M₀.L.ι),
      Good M₀.L z₀ J₀' → val (L := abelian₂ B₀ M₀.L) l₁ (lift p (lift p' q)).left z₀ (ind B₀ J₀') = cubV c₀ z₀ J₀' p p' q := by
    intro T₀ p p' q z₀ J₀' hJ₀'
    show val (L := lamLB M₀) l₁ _ z₀ (ind B₀ J₀') = _
    rw [(vl z₀ (ind B₀ J₀') (good_ind hJ₀') J₀' hJ₀').1 p p' q, adj_ind M₀.isLB hJ₀', adj_ind M₀.isLB hJ₀',
      adj_ind M₀.isLB hJ₀']
    simp
  have Fp3 : ∀ {T₀ : Over S} (p p' q : T₀ ⟶ B₀) (z₀ : T₀.left) (J₀ : (T₀.left ⟶ B.left) → M.L.ι)
      (J₀' : (T₀.left ⟶ B₀.left) → M₀.L.ι),
      pw w φ3 lawε (lift p (lift p' q)).left z₀ (fun k => ind B J₀ ((lift p (lift p' q)).left ≫ φ3 k ≫ β₂))
        (fun k => ind B₀ J₀' ((lift p (lift p' q)).left ≫ φ3 k)) =
        lamVal w (lift (p * p') q).left z₀ J₀ J₀' * (lamVal w (lift p q).left z₀ J₀ J₀')⁻¹ *
          (lamVal w (lift p' q).left z₀ J₀ J₀')⁻¹ := by
    intro T₀ p p' q z₀ J₀ J₀'
    rw [pw_eq]; exact prod_law₁ p p' q (fun χ => lamVal w χ z₀ J₀ J₀')
  have sj3 : Function.Surjective ((snd B₀ (B₀ ⊗ B₀)).left ≫ (snd B₀ B₀).left ≫ B₀.hom).appTop.hom :=
    surj_comp (surj_snd hG hB₀ _) (surj_comp (surj_snd hG hB₀ _) (hG _ _ hB₀).2)
  have he3 : (lift (1 : 𝟙_ (Over S) ⟶ B₀) (lift 1 1)).left ≫ (snd B₀ (B₀ ⊗ B₀)).left ≫ (snd B₀ B₀).left ≫ B₀.hom =
      𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w (lift (1 : 𝟙_ (Over S) ⟶ B₀) (lift 1 1))
  have R3 := rigid_pw w hw hL hL' φ3 lawε hl₁ ht₃ _ _ he3 sj3 (fun y₀ => by
    obtain ⟨J₁, hJ₁⟩ := GlobalTheory.UU.exists_good_pt M.isLB y₀
    obtain ⟨J₁', hJ₁'⟩ := GlobalTheory.UU.exists_good_pt M₀.isLB y₀
    refine ⟨ind B J₁, ind B₀ J₁', good_ind hJ₁, good_ind hJ₁', ?_⟩
    rw [Ft3 (T₀ := 𝟙_ (Over S)) 1 1 1 y₀ J₁ hJ₁, Fp3, Fa3 1 1 1 y₀ J₁' hJ₁', GlobalTheory.MumRigidZero.one_comp_hom a,
      _root_.mul_one, (isCub_cubV c hJ₁).face, (isCub_cubV c₀ hJ₁').face, hn (𝟙_ (Over S)) y₀ J₁ J₁' hJ₁ hJ₁']
    simp)
  have E3 := R3 T.left (lift x (lift x' y)).left z (ind B J) (ind B₀ J') (good_ind hJ) (good_ind hJ')
  rw [Ft3 x x' y z J hJ, Fp3, Fa3 x x' y z J' hJ'] at E3
  rw [E3]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.MumfordE8Bimultiplicative

end

open GlobalTheory.Mum

namespace GlobalTheory.MumfordE8Bimultiplicative

end GlobalTheory.MumfordE8Bimultiplicative
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatWFgPow
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.LamT (CMPt)
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovTop.ShiftFG

theorem exists_good_cmPt_frame_ne_zero {D : D7} {T : Core D} {j : ℕ} (Y : Deep T j) {e : ℕ} {o : ℝ} (hG : Y.Good e o)
    [StarRing (𝓞 D.host.E)] (hstar : ∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) (G : WTZ D.host.E)
    (F : Rul Y.d.Xo₂ Y.d.c₂) (hF : F ∈ Y.V G) (hF0 : F ≠ 0) :
    ∃ (z : CMPt Y.d.Xo₂ Y.d.c₂) (La : ℝ) (y : FrPt Y.d.Xo₂ Y.d.c₂ z.K),
      z.Good (Module.finrank ℚ D.host.E / 2) La ∧ y.x = z.x ∧ evR Y.d.Xo₂ Y.d.c₂ F y ≠ 0 := by
  classical
  have hσ : GoodEmb Y.d.c₂ Y.d.c₂.F.val.toRingHom := rfl
  have hU := hG.unf _ hσ
  have hFm := GlobalTheory.AllWt.mem_cuspW.1 hF
  obtain ⟨k, x₁, hx₁, hne₁⟩ := _root_.GlobalTheory.exists_rdU_ne_zero_of_mem_secZ _ _ _ _ _ _ _ _ _ hU _ F hFm.1 hF0
  obtain ⟨Xx, 𝔄, hX, h𝔄, hΛ⟩ := _root_.GlobalTheory.CovData.exists_dataX_good D T j Y e o hG _ hσ k
  have hbdd := (Formalism.L2.Pj.abelian₂.holSub_SS ReciprocityTheory.ChartRestriction.G.FD.siegelSpaceAlgebra_holds _ _ (hFm.2 _ hσ) k).1
  have hr : 0 < D.R.r := by
    have hn : 0 < D.R.ord := D.R.ord_pos
    have hk := D.R.f_le_k
    have ht := D.R.rank_add_five_le
    unfold Ranks.r; omega
  obtain ⟨La, x, lam, hx, hB, hne⟩ := GlobalTheory.CMDetect.exists_cm_frame Xx _ hX hr _ _ hbdd hx₁ hne₁
  obtain ⟨z, σ₁, hz, hzx⟩ := GlobalTheory.LamT.exists_good_cmPt_at_frame _ _ _ _ _ _ hstar _ _ hU hr k ⟨x, hx⟩ Xx hX 𝔄 h𝔄 hΛ
    La lam hB
  have hev : evR Y.d.Xo₂ Y.d.c₂ F ((Y.U _).un k ⟨x, hx⟩) ≠ 0 := by
    intro h0
    apply hne
    change (if h : x ∈ ((Y.U _).X k).dom then toC (evR Y.d.Xo₂ Y.d.c₂ F ((Y.U _).un k ⟨x, h⟩)) else 0) = 0
    rw [dite_eq_left hx]
    exact h0
  obtain ⟨y, hy, hyne⟩ := _root_.GlobalTheory.FrameDenseZ.exists_frame_evR_ne_zero_of_complex _ _ _ _ _ _ z.K z.y _ F hFm.1 _ σ₁ _ hzx hev
  exact ⟨z, La, y, hz, hy.trans hz.2.2.2.1, hyne⟩


end GlobalTheory.CovTop.ShiftFG

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeOfUniformisationEqModelLattice
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

namespace GlobalTheory.Poinc.FibLat.UnifLat

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem exists_tau {o B X : Type} [CommRing o] [CommRing B] [AddCommGroup X] (b : o →+* B) (ζ : oˣ) {L : ℕ}
    (hL : 0 < L) (hζ : ζ ^ L = 1) (c : X →+ ZMod L) :
    ∃ τ : Multiplicative X →* Bˣ,
      (∀ χ, τ χ = Units.map b.toMonoidHom ζ ^ (c (Multiplicative.toAdd χ)).val) ∧ τ ^ L = 1 := by
  haveI : NeZero L := ⟨hL.ne'⟩
  have hu : Units.map b.toMonoidHom ζ ^ L = 1 := by rw [← map_pow, hζ, map_one]
  refine ⟨{ toFun := fun χ => Units.map b.toMonoidHom ζ ^ (c (Multiplicative.toAdd χ)).val
            map_one' := by simp
            map_mul' := fun χ χ' => by
              simp only [toAdd_mul, map_add (f := _), ZMod.val_add]
              rw [← pow_add, ← pow_eq_pow_mod _ hu] }, fun χ => rfl, ?_⟩
  refine MonoidHom.ext fun χ => ?_
  rw [MonoidHom.pow_apply, MonoidHom.one_apply]
  show (Units.map b.toMonoidHom ζ ^ (c (Multiplicative.toAdd χ)).val) ^ L = 1
  rw [← pow_mul, mul_comm, pow_mul, hu, one_pow]

end GlobalTheory.Poinc.FibLat.UnifLat


open GlobalTheory.Poinc.FibLat.UnifLat in
theorem GlobalTheory.Poinc.FibLat.latAt_of_unif : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (G : Over M.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (I T : Type) (f : I → (G ⟶ G)) (gγ : T → (Over.mk M.pt ⟶ G)) (ζ : oˣ) (L : ℕ), 0 < L → ζ ^ L = 1 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (Gu : Over (Sp V)) [GrpObj Gu] [IsCommMonObj Gu], IsSemiAbelian Gu → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A Gu) (F : I → (Gu ⟶ Gu)) (m : I → D.toPre.X →+ D.toPre.X), (∀ e, EndChar U (F e) (m e)) → ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (fV : V →+* V'), IsLocalHom fV → ∀ (ξ : Sp V' ⟶ M.Z) (a : o →+* V'), ξ ≫ M.s = spMap a → ∀ (G' : Over (Sp V')) [GrpObj G'] (β : G'.left ⟶ Gu.left) (β' : G'.left ⟶ G.left), IsGrpPullback G' Gu (spMap fV) β → IsGrpPullback G' G ξ β' → (∀ e, ∃ F' : G' ⟶ G', F'.left ≫ β = β ≫ (F e).left ∧ F'.left ≫ β' = β' ≫ (f e).left) → ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing V) K] (iK : V' →+* K), Function.Injective iK → iK.comp fV = (algebraMap (FractionRing V) K).comp (algebraMap V (FractionRing V)) → ∀ c : T → D.toPre.X →+ ZMod L, (∀ t, ExtNear (gγ t) (ξ (closedPoint V')) ∧ ∃ (q : QkPt D.toPre K L) (τ : Multiplicative D.toPre.X →* Kˣ) (x : TFK (R := V) K ⟶ A.A) (x' : Sp K ⟶ G'.left), q.y = 0 ∧ GlobalTheory.UT.IsTor τ q.g ∧ QkToAkU U.toUnifPre K L q x ∧ (∀ χ, (τ (Multiplicative.ofAdd χ) : K) = iK (a ((ζ : o) ^ (c t χ).val))) ∧ x' ≫ G'.hom = spMap iK ∧ x' ≫ β = x.left ≫ genMap U ∧ ValAt (gγ t) (spMap iK ≫ ξ) (x' ≫ β')) → LatAt f gγ ζ L m c (ξ (closedPoint V')) := by
  intro o Ω _ _ _ M G _ _ hG I T f gγ ζ L hL hζ V _ _ _ hV Gu _ _ hGu D A U F m hF V' _ _ _ fV hfV ξ a hξ G' _ β β'
    hβ hβ' hF' K _ _ _ iK hiK hKf c hc
  haveI : IsSeparated G.hom := hG.separated
  haveI : IsSeparated Gu.hom := hGu.separated
  haveI : IsSeparated G'.hom := MorphismProperty.of_isPullback (P := @IsSeparated) hβ.1 inferInstance
  obtain ⟨r, hrl, hr⟩ : ∃ r : V' →+* ResidueField V', IsLocalHom r ∧ ∀ x, r x = 0 ↔ x ∈ maximalIdeal V' :=
    ⟨residue V', inferInstance, fun x => residue_eq_zero_iff x⟩
  have hρ : ∀ x ∈ maximalIdeal V ^ (0 + 1), (r.comp fV) x = 0 := fun x hx => by
    rw [zero_add, pow_one] at hx
    exact (hr _).2 (map_nonunit fV x hx)
  obtain ⟨G₀, _, ψ, hψ⟩ : ∃ (G₀ : Over (Sp (ResidueField V'))) (_ : GrpObj G₀) (ψ : G₀.left ⟶ G'.left),
      IsGrpPullback G₀ G' (spMap r) ψ := ⟨_, inferInstance, _, isGrpPullback_pullback G' (spMap r)⟩
  have h₀ : IsGrpPullback G₀ Gu (spMap (r.comp fV)) (ψ ≫ β) := (hψ.comp hβ).congr (spMap_comp_eq fV r).symm rfl
  have hφ : IsGrpPullback G₀ G (spMap r ≫ ξ) (ψ ≫ β') := hψ.comp hβ'
  obtain ⟨s, hs1, hs2, hs3, hs4⟩ := GlobalTheory.ToricTorsionUnif.main V hV Gu hGu D A U L hL
  refine ⟨ResidueField V', inferInstance, spMap r ≫ ξ, r.comp a, G₀, inferInstance, ψ ≫ β',
    GlobalTheory.TorusPart.gtTorus (U.gt 0) hρ h₀, ?_, ?_, hφ, isTorPart_gtTorus _ hρ h₀, ?_⟩
  · show ξ ((spMap r) (closedPoint (ResidueField V'))) = _
    rw [spMap, Spec_closedPoint]
  · rw [Category.assoc, hξ, spMap_comp_eq a r]
  refine ⟨fun e => ?_, fun t => ?_⟩
  · obtain ⟨F', hF1, hF2⟩ := hF' e
    have w : (ψ ≫ F'.left) ≫ G'.hom = G₀.hom ≫ spMap r := by
      rw [Category.assoc, Over.w F', hψ.1.w]
    obtain ⟨F₀, hF₀⟩ : ∃ F₀ : G₀ ⟶ G₀, F₀.left ≫ ψ = ψ ≫ F'.left :=
      ⟨Over.homMk (hψ.1.lift (ψ ≫ F'.left) G₀.hom w) (hψ.1.lift_snd _ _ _), hψ.1.lift_fst _ _ _⟩
    have hE := hF e (ResidueField V') (r.comp fV) hρ G₀ (ψ ≫ β) h₀ F₀
      (by rw [← Category.assoc, hF₀, Category.assoc, hF1, Category.assoc])
    have k : (GlobalTheory.TorusPart.gtTorus (U.gt 0) hρ h₀).left ≫ F₀.left =
        (GlobalTheory.SplitTorus.torusMap (Sp (ResidueField V')) (m e) ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) hρ h₀).left := by
      rw [← Over.comp_left, hE]
    calc (GlobalTheory.TorusPart.gtTorus (U.gt 0) hρ h₀).left ≫ (ψ ≫ β') ≫ (f e).left
        = (GlobalTheory.TorusPart.gtTorus (U.gt 0) hρ h₀).left ≫ ψ ≫ F'.left ≫ β' := by rw [hF2]; simp only [Category.assoc]
      _ = ((GlobalTheory.TorusPart.gtTorus (U.gt 0) hρ h₀).left ≫ F₀.left) ≫ ψ ≫ β' := by
          rw [Category.assoc, reassoc_of% hF₀]
      _ = _ := by rw [k]
  · obtain ⟨hext, q, τ, x, x', hq, hτq, hqx, hτ, hx'1, hx'2, hx'3⟩ := hc t
    obtain ⟨τV, hτVv, hτV⟩ := exists_tau a ζ hL hζ (c t)
    obtain ⟨τκ, hτκv, hτκ⟩ := exists_tau (r.comp a) ζ hL hζ (c t)
    have hchar : ∀ χ, (τ χ : K) = iK (τV χ : V') := fun χ => by
      rw [hτVv]
      refine (hτ (Multiplicative.toAdd χ)).trans ?_
      simp
    have hcharκ : ∀ χ, (τκ χ : ResidueField V') = r (τV χ : V') := fun χ => by
      rw [hτVv, hτκv]
      simp
    have hτL : τ ^ L = 1 := MonoidHom.ext fun χ => Units.ext (by
      rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, hchar, ← map_pow, ← Units.val_pow_eq_pow_val,
        ← MonoidHom.pow_apply, hτV]
      simp)
    have hσ₀ : (s V' fV τV hτV).left ≫ Gu.hom = 𝟙 (Sp V') ≫ spMap fV :=
      (Over.w (s V' fV τV hτV)).trans (Category.id_comp _).symm
    obtain ⟨σ, hσβ, hσG⟩ : ∃ σ : Sp V' ⟶ G'.left, σ ≫ β = (s V' fV τV hτV).left ∧ σ ≫ G'.hom = 𝟙 _ :=
      ⟨hβ.1.lift _ _ hσ₀, hβ.1.lift_fst _ _ _, hβ.1.lift_snd _ _ _⟩
    obtain ⟨v, hv⟩ := ExtNear.exists_valAt ξ hext
    obtain ⟨σ', hσ'β, hσ'G⟩ : ∃ σ' : Sp V' ⟶ G'.left, σ' ≫ β' = v ∧ σ' ≫ G'.hom = 𝟙 _ :=
      ⟨hβ'.1.lift v (𝟙 _) (by rw [hv.over, Category.id_comp]), hβ'.1.lift_fst _ _ _, hβ'.1.lift_snd _ _ _⟩
    have eσK : spMap iK ≫ σ = x' := hβ.1.hom_ext (by
        rw [Category.assoc, hσβ, hx'2, hs4 K (iK.comp fV) τ hτL q x hKf hq hτq hqx,
          hs2 V' K fV (iK.comp fV) iK τV hτV τ hτL rfl hchar])
      (by rw [Category.assoc, hσG, hx'1, Category.comp_id])
    have eσ'K : spMap iK ≫ σ' = x' := hβ'.1.hom_ext (by
        rw [Category.assoc, hσ'β]; exact ValAt.unique (hv.comp (spMap iK)) hx'3)
      (by rw [Category.assoc, hσ'G, hx'1, Category.comp_id])
    haveI : IsDominant (spMap iK) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical iK).2
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hiK]; exact bot_le)⟩
    have eσ : σ = σ' := ext_of_isDominant_of_isSeparated G'.hom (by rw [hσG, hσ'G]) (spMap iK)
      (eσK.trans eσ'K.symm)
    let φκ : Multiplicative D.toPre.X →* Γ((Over.mk (𝟙 (Sp (ResidueField V')))).left, ⊤)ˣ :=
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of (ResidueField V'))).inv.hom.toMonoidHom).comp τκ
    obtain ⟨z, hz⟩ : ∃ z : Over.mk (𝟙 (Sp (ResidueField V'))) ⟶ splitTorus (Sp (ResidueField V')) D.toPre.X,
        ∀ χ, GlobalTheory.UU.chV z χ = unitOn (τκ (Multiplicative.ofAdd χ)) :=
      ⟨(GlobalTheory.splitTorusPointsEquiv _ _ _).symm φκ, fun χ => by
        show GlobalTheory.splitTorusPointsEquiv _ _ _ ((GlobalTheory.splitTorusPointsEquiv _ _ _).symm φκ) _ = _
        rw [MulEquiv.apply_symm_apply]; rfl⟩
    have hz1w : z.left ≫ (splitTorus (Sp (ResidueField V')) D.toPre.X).hom =
        (Over.mk (spMap (RingHom.id (ResidueField V')))).hom := by
      rw [Over.w z]
      show 𝟙 _ = Spec.map (CommRingCat.ofHom (RingHom.id (ResidueField V')))
      rw [CommRingCat.ofHom_id, Spec.map_id]
    let z₁ : Over.mk (spMap (RingHom.id (ResidueField V'))) ⟶ splitTorus (Sp (ResidueField V')) D.toPre.X :=
      Over.homMk z.left hz1w
    have hz₁ : ∀ χ, GlobalTheory.UU.chV z₁ χ = unitOn (τκ (Multiplicative.ofAdd χ)) := fun χ =>
      (Units.ext (by rw [GlobalTheory.UU.chV_val, GlobalTheory.UU.chV_val]; rfl)).trans (hz χ)
    have e3 := hs3 (ResidueField V') (ResidueField V') (r.comp fV) hρ (r.comp fV) (RingHom.id _) G₀ (ψ ≫ β) h₀ τκ hτκ
      z₁ (RingHom.id_comp _).symm hz₁
    have e2 := hs2 V' (ResidueField V') fV (r.comp fV) r τV hτV τκ hτκ rfl hcharκ
    have ez : (z ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) hρ h₀).left ≫ ψ = spMap r ≫ σ := hβ.1.hom_ext
      (by
        rw [Category.assoc, Category.assoc, hσβ, ← e2, e3]
        rfl)
      (by
        rw [Category.assoc, Category.assoc, hσG, Category.comp_id, hψ.1.w, ← Category.assoc,
          Over.w (z ≫ _)]
        exact Category.id_comp _)
    refine ⟨z, fun χ => (hz χ).trans (by rw [hτκv]; rfl), ?_⟩
    rw [← Category.assoc, ez, eσ, Category.assoc, hσ'β]
    exact hv.comp (spMap r)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LePreimageOfIsTranslate
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory.KSRechart

theorem resG_appLE {Y Z : Scheme.{0}} (m : Z ⟶ Y) (U : Y.Opens) {V V' : Z.Opens} (h : V ≤ m ⁻¹ᵁ U) (e : V' ≤ V)
    (r : Γ(Y, U)) : resG Z e ((m.appLE U V h).hom r) = (m.appLE U V' (e.trans h)).hom r := by
  show ((m.appLE U V h) ≫ Z.presheaf.map (homOfLE e).op).hom r = _
  rw [Scheme.Hom.appLE_map]

end GlobalTheory.KSRechart

namespace GlobalTheory.KSRechart


private theorem valR_comp_eq_valR_app' {A : Type} [CommRing A] {X Z : Scheme.{0}} (x : Sp A ⟶ Z) (m : Z ⟶ X)
    (U : X.Opens) (O : Z.Opens) (h : O ≤ m ⁻¹ᵁ U) (hO : ⊤ ≤ x ⁻¹ᵁ O) (r : Γ(X, U)) :
    valR x O ((m.appLE U O h).hom r) = valR (x ≫ m) U r := by
  have hU : ⊤ ≤ (x ≫ m) ⁻¹ᵁ U := fun p hp => h (hO hp)
  unfold valR
  rw [dite_eq_left hO, dite_eq_left hU]
  congr 1
  show ((m.appLE U O h) ≫ x.appLE O ⊤ hO).hom r = _
  rw [Scheme.Hom.appLE_comp_appLE]

end GlobalTheory.KSRechart

namespace GlobalTheory.KSRechart

theorem valR_appLE {X Z : Scheme.{0}} (m : Z ⟶ X) (U : X.affineOpens) {S : Type} [CommRing S] (φ : Γ(X, U.1) →+* S)
    (g₀ : Sp S ⟶ Z) (hg : g₀ ≫ m = spMap φ ≫ chart U) {O : Z.Opens} (h : O ≤ m ⁻¹ᵁ U.1) (hO : ⊤ ≤ g₀ ⁻¹ᵁ O)
    (r : Γ(X, U.1)) : valR g₀ O ((m.appLE U.1 O h).hom r) = φ r := by
  rw [valR_comp_eq_valR_app' g₀ m U.1 O h hO r, hg]
  exact GlobalTheory.FlagEmb.QuotLine.valR_chart U.2 φ r

end GlobalTheory.KSRechart

namespace GlobalTheory.KSRechart

end GlobalTheory.KSRechart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelUnitThetaConstantNeZeroDividesAll
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.IntTerm

theorem unit_ne_zero_dvd (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z)
    (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V]
    [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V)
    (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam) :
    X₁.M.Div X₁.S.th x₀ z₁ → IsUnit ((X₁.S.r * X₁.S.N : ℕ) : V) ∧ 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ ≠ 0 ∧
      ∀ a, ∃ r : V, 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ =
        algebraMap V (FractionRing V) r * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ := by
  intro hdiv
  have sp : ∀ w, X₁.M.Z.fromSpecStalk z₁ w ⤳ z₁ := fun w => by
    have : X₁.M.Z.fromSpecStalk z₁ w ∈ Set.range (X₁.M.Z.fromSpecStalk z₁) := ⟨w, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  set y' : Sp V ⟶ X₁.M.Z := spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ with hy'
  set y : Sp (FractionRing V) ⟶ X₁.M.Z := jK V ≫ y' with hy
  have h1 : y' (closedPoint V) ⤳ z₁ := sp _
  set ξ := y (closedPoint (FractionRing V)) with hξ
  have hξz : ξ ⤳ z₁ := sp _
  have hyξ : ∀ w, y w ⤳ ξ := RatModel.specializes_of_range_eq (RatModel.range_eq_singleton y _)
  have hx₀ : X₁.S.th x₀ ∈ X₁.M.O ξ := 𝔪.reg _ (X₁.S.th_mem x₀)
  have key : ∀ a, 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ =
      algebraMap V (FractionRing V) (RatModel.valLoc y' z₁ h1 ⟨_, hdiv.2 a⟩) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ := by
    intro a
    have hq : X₁.S.th a / X₁.S.th x₀ ∈ X₁.M.O ξ := RatModel.O_le_of_specializes hξz (hdiv.2 a)
    have e : X₁.S.th a = X₁.S.th a / X₁.S.th x₀ * X₁.S.th x₀ := (div_mul_cancel₀ _ hdiv.1).symm
    rw [𝔪.yK_eq, 𝔪.yK_eq]
    change X₁.M.val y (X₁.S.th a) = _ * X₁.M.val y (X₁.S.th x₀)
    rw [show X₁.M.val y (X₁.S.th a) = X₁.M.val y (X₁.S.th a / X₁.S.th x₀ * X₁.S.th x₀) from congrArg _ e,
      RatModel.val_mul hyξ hq hx₀]
    congr 1
    exact RatModel.val_spMap_comp (algebraMap V (FractionRing V)) y' h1 ⟨_, hdiv.2 a⟩
  refine ⟨?_, ?_, fun a => ⟨_, key a⟩⟩
  · have := X₁.S.unit.map (ev.comp ((X₁.M.stalkEquiv z₁).symm.toRingHom.comp (algebraMap X₁.o₁ (X₁.M.O z₁))))
    rwa [map_natCast] at this
  · intro h0
    obtain ⟨c, -, hc⟩ := GoodOut.exists_th_notMem abelianSchemeLaws_all.1 abelianSchemeLaws_all.2 X₁.ρ
      ⟨RingHom.ker 𝔪.yK, RingHom.ker_isPrime _⟩ x₀
    exact hc (by
      change 𝔪.yK _ = 0
      rw [key, h0, mul_zero])

end GlobalTheory.Poinc.IntTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleGenericFibreExtendsOverDvr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem lb_extends_over_dvr : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (H : Over (Sp R)) [Smooth H.hom] [QuasiCompact H.hom] [IsSeparated H.hom] [GeometricallyIntegral H.hom] (L : LB ((Over.pullback (jK R)).obj H).left), L.IsLB → ∃ L' : LB H.left, L'.IsLB ∧ LBIso L (L'.pull (pullback.fst H.hom (jK R))) := by
  intro R _ _ _ H _ _ _ _ L hL
  obtain ⟨M, hM, hML⟩ := GlobalTheory.LBExtDVR.exists_lineBundle_extension_genericFibre R (FractionRing R)
    H.left ((Over.pullback (jK R)).obj H).left H.hom (pullback.snd H.hom (jK R))
    (pullback.fst H.hom (jK R)) inferInstance inferInstance (IsPullback.of_hasPullback H.hom (jK R)) L hL
  exact ⟨M, hM, LBIso.symm hML⟩

end GlobalTheory.Mum
end

