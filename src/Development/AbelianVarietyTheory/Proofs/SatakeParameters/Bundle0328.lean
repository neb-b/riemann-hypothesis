module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0247
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0013
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.SameChart
public import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
public import Formalism.LocalToGlobal.InertKernelTheory.ScalG
public import Formalism.LocalToGlobal.InertKernelTheory.DefsRepLt
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1585
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0720
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0231
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsAlgChar
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0325
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1720
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0234
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedAtValueHeckeCharCompIdeleNorm
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0288
public import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardIntegralLatticeExists
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0253
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0258
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GlobLatCompanOfLev
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0321
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IntegralGLSuccEmbeddingMemParahoricTimesPrincipa

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicPointsAgreeAwayOfLatticeTuplesAgreeAway
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc

theorem bc_reGL_comm {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {m n : ℕ} (e : Fin m ≃ Fin n) (x : GL (Fin m) A) :
    Formalism.UG.bc φ (Formalism.L2.PairingIndexBounds.F.reGL e x) = Formalism.L2.PairingIndexBounds.F.reGL e (Formalism.UG.bc φ x) := by
  apply Units.ext
  ext a b
  rfl

theorem sameOff_reGL_of {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (w : HeightOneSpectrum (𝓞 F)) {m n : ℕ} (e : Fin m ≃ Fin n) (x y : GL (Fin m) (AfE F E))
    (h : SameOff w x y) : SameOff w (Formalism.L2.PairingIndexBounds.F.reGL e x) (Formalism.L2.PairingIndexBounds.F.reGL e y) := fun w' hw => by
  rw [bc_reGL_comm, bc_reGL_comm, h w' hw]

theorem sameOff_eps_of_bases {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p}
    {σ : E →ₐ[F] E} {Jm : Matrix (Fin n) (Fin n) E} {A : LocAt F E n G} (hG : LocGood σ Jm A) (i : G.comp)
    (g g' : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (v : Fin G.P.nV) (hgg : ∀ v', v' ≠ v → g v' = g' v') :
    SameOff (A.pl v).1 (Classical.epsilon fun x => A.IsPt i g x ∧ x ∈ UPts σ Jm (FiniteAdeleRing (𝓞 F) F))
      (Classical.epsilon fun x => A.IsPt i g' x ∧ x ∈ UPts σ Jm (FiniteAdeleRing (𝓞 F) F)) := by
  have ha := Classical.epsilon_spec (p := fun x => A.IsPt i g x ∧ x ∈ UPts σ Jm (FiniteAdeleRing (𝓞 F) F))
    ⟨_, hG.isPt_sec i g, Subgroup.mul_mem _ (hG.yG_mem i) (hG.sec _).2⟩
  have hb := Classical.epsilon_spec (p := fun x => A.IsPt i g' x ∧ x ∈ UPts σ Jm (FiniteAdeleRing (𝓞 F) F))
    ⟨_, hG.isPt_sec i g', Subgroup.mul_mem _ (hG.yG_mem i) (hG.sec _).2⟩
  exact GlobalTheory.TwV.Xc.sameOff_of_isPt F E σ n p G A Jm hG i g g' ⟨_, ha.2⟩ ⟨_, hb.2⟩ ha.1 hb.1 v hgg


set_option maxHeartbeats 4000000 in
theorem sameOff_len_of_sameAway : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ v j (hj : j ≤ D.R.m) (La Lb : (sysS H X std).Lt j), SameAway (hT := hT) (H := H) (X := X) std v j La Lb → SameOff ((A0 J).pl v).1 (J.pt std j hj La).1 (J.pt std j hj Lb).1 ∧ ∀ v', v' ≠ v → len (sysS H X std) v' j La.2 = len (sysS H X std) v' j Lb.2) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS v j hj La Lb hab
  obtain ⟨hLa, hLb, h1, h2⟩ := hab
  have hent : ∀ v', v' ≠ v → La.2 ((sysS H X std).vJ j v') = Lb.2 ((sysS H X std).vJ j v') := by
    intro v' hv'
    have hne : (sysS H X std).vJ j v' ≠ (sysS H X std).vJ j v := by
      intro h
      apply hv'
      have := congrArg ((sysS H X std).vB j) h
      rwa [Formalism.L2.G.Pend.vB_vJ, Formalism.L2.G.Pend.vB_vJ] at this
    have := congrFun h2 ((sysS H X std).vJ j v')
    exact (Function.update_of_ne hne _ _).symm.trans (this.trans (Function.update_of_ne hne _ _))
  refine ⟨?_, fun v' hv' => by unfold len; rw [hent v' hv']⟩
  have hlat : ∀ v', v' ≠ v → (sysS H X std).latAt v' j La.2 = (sysS H X std).latAt v' j Lb.2 := by
    intro v' hv'
    have := hent v' hv'
    cases j <;> exact this
  obtain ⟨hr, hpa⟩ := (hD j hj La hLa).1
  obtain ⟨hr', hpb⟩ := (hD j hj Lb hLb).1
  rw [hpa, hpb]
  apply sameOff_reGL_of
  obtain ⟨c, a⟩ := La
  obtain ⟨c', b⟩ := Lb
  dsimp only at h1
  subst h1
  cases j with
  | zero =>
    simp only [Joint.cp, cpAt, chAt]
    apply sameOff_reGL_of
    apply sameOff_eps_of_bases J.one.good
    intro v' hv'
    have hl := hlat v' hv'
    dsimp only at hl
    unfold basesAt
    rw [hl]
  | succ i =>
    simp only [Joint.cp, cpAt]
    simp only [chAt, dif_pos hj]
    apply sameOff_reGL_of
    rw [show (A0 J).pl v = ((I.at' i hj).st.loc ((I.at' i hj).st.eC.symm c).1).pl v from (J.pl i hj _ v).symm]
    apply sameOff_eps_of_bases (H.core i hj _).good
    intro v' hv'
    have hl := hlat v' hv'
    dsimp only at hl
    unfold basesAt
    rw [hl]

end GlobalTheory.TwV.Xc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BijectiveOfSplit
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CharLiftStep

open Matrix

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

theorem cycAt_or_split [IsGalois K M] (hp : (Module.finrank K M).Prime) (v : HeightOneSpectrum (𝓞 K))
    (u : HeightOneSpectrum (𝓞 M)) [u.asIdeal.LiesOver v.asIdeal] :
    GlobalTheory.FunExt.CycAt v u ∨ (u.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ u.asIdeal.inertiaDeg (𝓞 K) = 1) := by
  have h2 := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn v.asIdeal (𝓞 M) Gal(M/K)
  rw [IsGalois.card_aut_eq_finrank, Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal u.asIdeal Gal(M/K),
    Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal u.asIdeal Gal(M/K)] at h2
  have hp' := hp
  rw [← h2] at hp'
  rcases Nat.prime_mul_iff.1 hp' with ⟨-, h⟩ | ⟨-, h⟩
  · exact Or.inr (mul_eq_one.1 h)
  · left
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 h
    have hu : u.under (𝓞 K) = v :=
      HeightOneSpectrum.ext (Ideal.LiesOver.over (P := u.asIdeal) (p := v.asIdeal)).symm
    refine ⟨inferInstance, hp, hu, fun u' hu' => ?_⟩
    have : u'.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hu']; rfl⟩
    have m1 : u.asIdeal ∈ v.asIdeal.primesOver (𝓞 M) := ⟨u.isPrime, inferInstance⟩
    have m2 : u'.asIdeal ∈ v.asIdeal.primesOver (𝓞 M) := ⟨u'.isPrime, inferInstance⟩
    rw [ha, Set.mem_singleton_iff] at m1 m2
    exact HeightOneSpectrum.ext (m2.trans m1.symm)

section Split

variable (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 M)) [u.asIdeal.LiesOver v.asIdeal]

theorem bijective_of_split (he : u.asIdeal.ramificationIdx (𝓞 K) = 1) (hf : u.asIdeal.inertiaDeg (𝓞 K) = 1) :
    Function.Bijective (GroundTheory.Global.adicCompletionMap v u) := by
  letI : Algebra (v.adicCompletion K) (u.adicCompletion M) := (GroundTheory.Global.adicCompletionMap v u).toAlgebra
  have : ContinuousSMul (v.adicCompletion K) (u.adicCompletion M) :=
    continuousSMul_of_algebraMap _ _ (GroundTheory.Global.continuous_adicCompletionMap v u)
  have : IsScalarTower K (v.adicCompletion K) (u.adicCompletion M) :=
    .of_algebraMap_eq fun x => by
      show _ = GroundTheory.Global.adicCompletionMap v u _
      rw [GroundTheory.Global.adicCompletionMap_algebraMap, IsScalarTower.algebraMap_apply K M (u.adicCompletion M)]
  have h1 : Module.finrank (v.adicCompletion K) (u.adicCompletion M) = 1 := by
    rw [GroundTheory.Global.finrank_adicCompletion v u, he, hf]
  refine ⟨(GroundTheory.Global.adicCompletionMap v u).injective, fun y => ?_⟩
  have hy : y ∈ (⊥ : Subalgebra (v.adicCompletion K) (u.adicCompletion M)) :=
    (Subalgebra.bot_eq_top_of_finrank_eq_one h1) ▸ Algebra.mem_top
  obtain ⟨x, hx⟩ := Algebra.mem_bot.1 hy
  exact ⟨x, hx⟩

theorem normU_of_split (he : u.asIdeal.ramificationIdx (𝓞 K) = 1) (hf : u.asIdeal.inertiaDeg (𝓞 K) = 1) :
    Continuous (RingEquiv.ofBijective _ (bijective_of_split v u he hf)).symm ∧
      ∀ y : (u.adicCompletion M)ˣ, ((GlobalTheory.BCChar.normU v u y : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
        (RingEquiv.ofBijective _ (bijective_of_split v u he hf)).symm y := by
  set i := RingEquiv.ofBijective _ (bijective_of_split v u he hf)
  letI : Algebra (v.adicCompletion K) (u.adicCompletion M) := (GroundTheory.Global.adicCompletionMap v u).toAlgebra
  have : ContinuousSMul (v.adicCompletion K) (u.adicCompletion M) :=
    continuousSMul_of_algebraMap _ _ (GroundTheory.Global.continuous_adicCompletionMap v u)
  have : IsScalarTower K (v.adicCompletion K) (u.adicCompletion M) :=
    .of_algebraMap_eq fun x => by
      show _ = GroundTheory.Global.adicCompletionMap v u _
      rw [GroundTheory.Global.adicCompletionMap_algebraMap, IsScalarTower.algebraMap_apply K M (u.adicCompletion M)]
  have h1 : Module.finrank (v.adicCompletion K) (u.adicCompletion M) = 1 := by
    rw [GroundTheory.Global.finrank_adicCompletion v u, he, hf]
  have hfd : FiniteDimensional (v.adicCompletion K) (u.adicCompletion M) := GroundTheory.Global.finite_adicCompletion v u
  have hc := (GlobalTheory.adicCompletion_trace_norm_continuous K M v u _ (GroundTheory.Global.continuous_adicCompletionMap v u) hfd).2
  have key : ∀ y : u.adicCompletion M, Algebra.norm (v.adicCompletion K) y = i.symm y := by
    intro y
    conv_lhs => rw [← i.apply_symm_apply y]
    show Algebra.norm (v.adicCompletion K) (algebraMap (v.adicCompletion K) (u.adicCompletion M) (i.symm y)) = _
    rw [Algebra.norm_algebraMap, h1, pow_one]
  refine ⟨?_, fun y => key y⟩
  have e : (i.symm : u.adicCompletion M → v.adicCompletion K) = fun y => Algebra.norm (v.adicCompletion K) y :=
    funext fun y => (key y).symm
  rw [e]
  exact hc

end Split

section Char

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem trGL_ofChar (i : k ≃+* k') (hi' : Continuous i.symm) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ)
    (χ' : k'ˣ →* ℂˣ) (hχ' : IsSmoothChar χ')
    (h : ∀ y : k'ˣ, χ' y = χ (Units.map (i.symm : k' →* k) y)) :
    GlobalTheory.SuppIne.trGL i hi' (IrrGL.ofChar χ hχ) = IrrGL.ofChar χ' hχ' := by
  refine congrArg (Sigma.mk 1) (IrrRep.cl_eq_iff.2 ?_)
  obtain ⟨φ⟩ := IrrRep.nonempty_equiv_rep (IrrRep.det (Fin 1) χ hχ)
  refine ⟨Representation.Equiv.mk φ.toLinearEquiv fun g => ?_⟩
  have H := φ.toIntertwiningMap.isIntertwining' (Matrix.GeneralLinearGroup.map (n := Fin 1) i.symm.toRingHom g)
  refine LinearMap.ext fun x => ?_
  have Hx := LinearMap.congr_fun H x
  simp only [LinearMap.coe_comp, Function.comp_apply] at Hx ⊢
  change φ.toLinearEquiv _ = _
  refine Hx.trans ?_
  erw [Function.comp_apply, LinearMap.comp_apply, SmGL.twist_apply, SmGL.twist_apply]
  have e1 : ∀ g' : GL (Fin 1) k', (detChar (Fin 1) χ') g' =
      (detChar (Fin 1) χ) (GeneralLinearGroup.map i.symm.toRingHom g') := fun g' => by
    rw [detChar_apply, detChar_apply, Matrix.GeneralLinearGroup.map_det]; exact h _
  erw [e1 g]
  rfl

end Char

end GlobalTheory.CharLiftStep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharOnNormOneIdelesMulUnramifiedClassValue
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwV.Xc.ChiHom

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Dx cX} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} {t : KerEntTied ex}

theorem chiI_det (J : Joint t H X) (y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) :
    chiI J (Matrix.GeneralLinearGroup.det y.1) = ((D.chiD (J.dtU y) : ℂˣ) : ℂ) := by
  have h : ∃ y' : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det y'.1 = Matrix.GeneralLinearGroup.det y.1 := ⟨y, rfl⟩
  unfold chiI
  rw [dite_eq_left h]
  have e : h.choose = y := Subtype.ext (GlobalTheory.TwV.MuLawPf.generalLinearGroupOne_eq_of_det_eq h.choose_spec)
  rw [e]


set_option maxHeartbeats 2000000 in
theorem carries_std_of_int (y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) (hy : Matrix.GeneralLinearGroup.det y.1 ∈ intU D.host.F D.host.E) :
    Formalism.L2.Herm.Carries y.1 (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) := by
  have hu := (Submonoid.mem_units_iff _ _).1 hy
  intro v
  show v ∈ latS (Formalism.L2.Herm.Af D.host.F) (Formalism.L2.Herm.intAf D.host.F D.host.E) (Formalism.L2.Col.stdLat D.host.E 1) ↔
    _ ∈ latS (Formalism.L2.Herm.Af D.host.F) (Formalism.L2.Herm.intAf D.host.F D.host.E) (Formalism.L2.Col.stdLat D.host.E 1)
  rw [Formalism.L2.Col.mem_latS_std, Formalism.L2.Col.mem_latS_std]
  have e1 : Units.val ((y.1)⁻¹) 0 0 = Units.val ((Matrix.GeneralLinearGroup.det y.1)⁻¹) := by
    rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one]
  have e2 : ∀ i : Fin 1, (Matrix.mulVec (Units.val ((y.1)⁻¹)) v) i = Units.val ((Matrix.GeneralLinearGroup.det y.1)⁻¹) * v 0 := by
    intro i
    fin_cases i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one]
    rw [← e1]; rfl
  simp only [e2]
  constructor
  · intro h i
    exact mul_mem hu.2 (h 0)
  · intro h i
    fin_cases i
    have := mul_mem hu.1 (h 0)
    rwa [← mul_assoc, Units.mul_inv, one_mul] at this


set_option maxHeartbeats 2000000 in
theorem dtU_mem_UO (J : Joint t H X) (y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm)
    (hy : Matrix.GeneralLinearGroup.det y.1 ∈ intU D.host.F D.host.E) : J.dtU y ∈ D.UO := by
  have h := J.rel 1 ⟨_, Formalism.MainNotions.GlobalTheoryTheory.Inhab.stdL_isSD D 1⟩ ⟨_, Formalism.MainNotions.GlobalTheoryTheory.Inhab.stdL_isSD D 1⟩ y.1 y.2
    (carries_std_of_int y hy) y rfl
  exact (QuotientGroup.eq_one_iff _).1 (h.symm.trans (D.relDet_self _ _))

end GlobalTheory.TwV.Xc.ChiHom

namespace GlobalTheory.TwV.Xc


open GlobalTheory.TwV.Xc.ChiHom in
set_option maxHeartbeats 4000000 in
theorem chiI_hom : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => (∀ x ∈ U1 (sigD D), ∀ y ∈ U1 (sigD D), chiI J (x * y) = chiI J x * chiI J y) ∧ (∀ x ∈ U1 (sigD D), x ∈ intU D.host.F D.host.E → chiI J x = 1) ∧ (∀ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, chiI J (Matrix.GeneralLinearGroup.det y.1) = ((D.chiD (J.dtU y) : ℂˣ) : ℂ)) ∧ ∀ x ∈ U1 (sigD D), ∃ 𝔞, TaylorLogMetric.N1 D 𝔞 ∧ chiI J x = t.χ 𝔞) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S _ _
  refine ⟨?_, ?_, fun y => chiI_det J y, ?_⟩
  · intro x hx y hy
    obtain ⟨x', rfl⟩ := GlobalTheory.TwV.MuLawPf.exists_unitaryOne_det_eq_normOneIdele hx
    obtain ⟨y', rfl⟩ := GlobalTheory.TwV.MuLawPf.exists_unitaryOne_det_eq_normOneIdele hy
    have e : Matrix.GeneralLinearGroup.det x'.1 * Matrix.GeneralLinearGroup.det y'.1 =
        Matrix.GeneralLinearGroup.det (x' * y').1 := by
      rw [Subgroup.coe_mul, map_mul]
    rw [e, chiI_det, chiI_det, chiI_det, map_mul, map_mul, Units.val_mul]
  · intro x hx hint
    obtain ⟨y, rfl⟩ := GlobalTheory.TwV.MuLawPf.exists_unitaryOne_det_eq_normOneIdele hx
    rw [chiI_det, D.chiD_UO _ (dtU_mem_UO J y hint), Units.val_one]
  · intro x hx
    obtain ⟨y, rfl⟩ := GlobalTheory.TwV.MuLawPf.exists_unitaryOne_det_eq_normOneIdele hx
    refine ⟨t.idl (QuotientGroup.mk (J.dtU y)), (t.idl_ok.2.1 _).2 ⟨_, rfl⟩, ?_⟩
    rw [chiI_det, t.χ_rec, TaylorLogMetric.chiRec_idl D t.idl t.idl_ok.1]
    rfl

end GlobalTheory.TwV.Xc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacterDetIdealKernelLatticeLatticeTuple
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem detId_stdL_heq (D : D7) {n n' : ℕ} (h : n = n') {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin n' → D.host.E)} (hL : HEq L L') :
    TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) L = TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n') L' := by
  subst h
  cases hL
  rfl

theorem chi_detId_kerN : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ (d : Dec J std) j (hj : j ≤ D.R.m) (La : (sysS H X std).Lt j), ((sysS H X std).Pj j).IsLatTup La.2 → t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) ((J.fd std).kerN j La)) = (∏ τ, TaylorLogMetric.embT D τ (gMat J j hj (d.gam j hj La)).det)⁻¹ * ((D.chiD ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) ∧ (∏ τ, TaylorLogMetric.embT D τ (gMat J j hj (d.gam j hj La)).det) ≠ 0) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD d j hj La hLa
  obtain ⟨⟨hr, -⟩, -, hK, -⟩ := hD j hj La hLa
  have hlat := _root_.GlobalTheory.TwV.latK_lev_rat J.A J.dtU J.a J.pins J.tie j hj (clsAt X H j La.1 La.2) (J.pt std j hj La)
    (d.gam j hj La) (d.mem j hj La) (d.kap j hj La) (d.eq j hj La hLa)
  have hU : gMat J j hj (d.gam j hj La) * star (gMat J j hj (d.gam j hj La)) = 1 :=
    _root_.GlobalTheory.TwV.ratIsometry_unitary J.A J.dtU J.a J.pins J.tie j hj (d.gam j hj La) (d.mem j hj La)
  have hcl := _root_.GlobalTheory.TwV.chi_detId_lat J.A J.dtU J.a J.pins J.tie J.rel J.base j hj (clsAt X H j La.1 La.2)
  have hmv := _root_.GlobalTheory.ChiMove.chi_detId_smulLat D t.χ t.χ_ok ((t.O u μ).lat j (clsAt X H j La.1 La.2)) (gMat J j hj (d.gam j hj La)) hU
  rw [t.O_lat] at hmv
  have h1 := detId_stdL_heq D hr hK
  refine ⟨?_, ?_⟩
  · rw [h1]
    have : latK D.sp (gramN D j hj) J.a (J.pt std j hj La).1 ((J.St j hj).K (J.chart std j hj La)).lev.Lb =
        SDLat.smulLat (gMat J j hj (d.gam j hj La)) (t.seam.lat ((t.rd u μ).N j (clsAt X H j La.1 La.2))) := hlat
    rw [this, hmv, hcl]
  · have hdet : (gMat J j hj (d.gam j hj La)).det ≠ 0 := by
      intro h0
      have := congrArg Matrix.det hU
      rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
      exact zero_ne_one this
    exact Finset.prod_ne_zero_iff.mpr fun τ _ => (map_ne_zero (TaylorLogMetric.embT D τ)).mpr hdet

end GlobalTheory.TwV.DelB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartLevelBaseFrameCongrOneAtBadPrime
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV

theorem congAt_fb_lev : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x : UA D i hi) p (κ : ((St i hi).K β).lev.U), IsPtAd A a i hi β x p → ∀ P : SB t μ, CongAt (seamP t.seam P.1) 0 ((ratA D.host.F (A.fb i hi β P))⁻¹ * κ.1 * ratA D.host.F (A.fb i hi β P)) ∧ CongAt (seamP t.seam P.1) 0 ((ratA D.host.F (A.fb i hi β P))⁻¹ * κ.1 * ratA D.host.F (A.fb i hi β P))⁻¹) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP H i hi β x p κ hp P
  exact GlobalTheory.LevStab.lev_stab_cong i hi _ a κ _ _ (GlobalTheory.T.chartBaseFrame_badPrime_eq_companion_lattice A dtU a hP H i hi β x p hp P)

end GlobalTheory.TwV

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoeffRenamedThetaClassSeries
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelB

theorem taylor_reV {D : D7} {a b N N' : ℕ} (ha : a = N) (hb : b = N') (G : TaylorLogMetric.VC D N N' → ℂ)
    (α : GL3Theta.Idx D N N' →₀ ℕ) :
    TaylorLogMetric.taylor D (reV ha hb G) (α.mapDomain fun k => (k.1, Fin.cast hb.symm k.2.1, Fin.cast ha.symm k.2.2)) =
      TaylorLogMetric.taylor D G α := by
  subst ha hb
  have h1 : reV (D := D) rfl rfl G = G := by funext z; rfl
  have h2 : (fun k : GL3Theta.Idx D a b => (k.1, Fin.cast (rfl : b = b).symm k.2.1, Fin.cast (rfl : a = a).symm k.2.2)) = id := by
    funext k; rfl
  rw [h1, h2, Finsupp.mapDomain_id]

theorem coeff_resV_thCl : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (p : ℕ) [Fact p.Prime] (X : Sys p) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j) {K : Type} [Field K] (ι : ℂ →+* K) (j : ℕ) (hN : RankTie X D j) (La : X.Lt j) (La' : X.Lt (j + 1)) (s : K) (α : GL3Theta.Idx D (D.R.N j) (D.R.N (j + 1)) →₀ ℕ), MvPowerSeries.coeff (α.mapDomain (eIdx X D pos j hN)) (resV (kapOf X pos j) (s • MvPowerSeries.map ι (tay (thCl t u μ cls j La La')))) = s * ι (TaylorLogMetric.taylor D ((t.rd u μ).Th t.seam t.amb j (cls j La.1 La.2) (cls (j + 1) La'.1 La'.2)) α) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ p _ X pos cls K _ ι j hN La La' s α
  have hr : (X.Pj j).m + 1 = D.R.N j ∧ (X.Pj (j + 1)).m + 1 = D.R.N (j + 1) :=
    ⟨(Formalism.L2.G.Pend.rank_eq X j).trans hN.1.symm, (Formalism.L2.G.Pend.rank_eq X (j + 1)).trans hN.2.symm⟩
  have hres : ∀ {ι' κ' : Type} (f : κ' → ι') (Th : MvPowerSeries ι' K) (n : κ' →₀ ℕ),
      MvPowerSeries.coeff n (resV f Th) = MvPowerSeries.coeff (n.mapDomain f) Th := fun _ _ _ => rfl
  have hcomp : (Formalism.L2.G.Pend.kapOf X pos j ∘ eIdx X D pos j hN) =
      fun k => (k.1, Fin.cast hr.2.symm k.2.1, Fin.cast hr.1.symm k.2.2) := by
    funext k
    simp only [Function.comp, Formalism.L2.G.Pend.kapOf, eIdx, Sigma.eta, Equiv.apply_symm_apply]
    ext <;> rfl
  rw [hres, ← Finsupp.mapDomain_comp, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_map, hcomp]
  congr 2
  show TaylorLogMetric.taylor D (thCl t u μ cls j La La') _ = _
  rw [thCl, dite_eq_left hr]
  exact taylor_reV hr.1 hr.2 _ α

end GlobalTheory.TwV.DelB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompanionLatticeEqPointLatticeOverCompanionStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.companion_lattice_eq_point_lattice_over_companion : ∀ (D : D7) (i : ℕ) (hi : i ≤ D.R.m) (co : GL (Fin (D.R.N i)) D.host.E), cT (sigD D : D.host.E →+* D.host.E) co.1 * co.1 = gramN D i hi → ∀ (a : 𝓞 D.host.E) (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Lb : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)), Module.Finite (𝓞 D.host.E) Lb → Submodule.span D.host.E (Lb : Set (Fin (D.R.N i) → D.host.E)) = ⊤ → latCo D.sp (gramN D i hi) co a x.1 Lb = latAd (ratA D.host.F co * x.1) (compan (sp := D.sp) (gramN D i hi) a Lb) ∧ Module.Finite (𝓞 D.host.E) (compan (sp := D.sp) (gramN D i hi) a Lb) ∧ Submodule.span D.host.E ((compan (sp := D.sp) (gramN D i hi) a Lb : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) : Set (Fin (D.R.N i) → D.host.E)) = ⊤ := by
  first | exact @GlobalTheory.LatCoCompan.latCo_eq_latAd_compan | exact GlobalTheory.LatCoCompan.latCo_eq_latAd_compan | (intros; apply GlobalTheory.LatCoCompan.latCo_eq_latAd_compan <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DecompositionUnitaryMulStarEqOne
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem Dec.eM_mul_star : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    ∀ (d : Dec J std) j La, d.eM j La * star (d.eM j La) = 1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S d j La
  unfold Dec.eM
  split_ifs with h
  · have hu := _root_.GlobalTheory.TwV.ratIsometry_unitary J.A J.dtU J.a J.pins J.tie j h.1 (d.gam j h.1 La) (d.mem j h.1 La)
    have hc : (Fin.cast h.2 : Fin (((sysS H X std).Pj j).m + 1) → Fin (D.R.N j)) = ⇑(finCongr h.2) := rfl
    rw [hc, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      ← Matrix.star_eq_conjTranspose]
    have hu' : gMat J j h.1 (d.gam j h.1 La) * star (gMat J j h.1 (d.gam j h.1 La)) = 1 := hu
    rw [hu', Matrix.submatrix_one_equiv]
  · simp

end GlobalTheory.TwV.DelB
end

