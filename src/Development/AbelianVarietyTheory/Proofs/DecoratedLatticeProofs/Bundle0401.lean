module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0051
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.HaarIdx
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0382
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValLtOfRedM
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0374
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0389
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0177
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0173
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0376
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0379
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanLevelVolumeMulRelIndex
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevVol

variable {D : D7}

theorem mul_set_eq_comap (V : HSp D) (U : Subgroup (GA D V)) (hU : U ≤ GfC V) :
    {g : GA D V | ∃ k ∈ GinfC V, ∃ κ ∈ U, g = k * κ} =
      (((U.subgroupOf (GfC V)).comap (GlobalTheory.AutMult.toFin V) : Subgroup (GA D V)) : Set (GA D V)) := by
  ext g
  simp only [Set.mem_setOf_eq, SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨k, hk, κ, hκ, rfl⟩
    have e : GlobalTheory.AutMult.toFin V (k * κ) = ⟨κ, hU hκ⟩ := by
      rw [map_mul, GlobalTheory.AutMult.toFin_coe_inf (⟨k, hk⟩ : GinfC V), one_mul]
      exact GlobalTheory.AutMult.toFin_coe (⟨κ, hU hκ⟩ : GfC V)
    rw [e]
    exact hκ
  · intro h
    exact ⟨_, (GlobalTheory.AutMult.toInf V g).2, _, h, (GlobalTheory.AutMult.toInf_mul_toFin g).symm⟩

theorem volLev_mul_relIndex : ∀ (D : D7) (V : HSp D) (v : GlobalTheory.Unf.Vol V) (U U' : Subgroup (GA D V)), U ≤ U' → U' ≤ GfC V →
    IsCompact (U' : Set (GA D V)) → IsOpen ((U.subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) →
    volLev v U * (U.relIndex U' : ℝ) = volLev v U' := by
  intro D V v U U' hle hU' _ hopn
  obtain ⟨i1, -, -, -, i5, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V
  haveI := i1
  haveI := i5
  haveI := v.haar
  have hU : U ≤ GfC V := hle.trans hU'
  set A := (U.subgroupOf (GfC V)).comap (GlobalTheory.AutMult.toFin V) with hA
  set A' := (U'.subgroupOf (GfC V)).comap (GlobalTheory.AutMult.toFin V) with hA'
  have hAA : A ≤ A' := Subgroup.comap_mono (fun x hx => Subgroup.mem_subgroupOf.2 (hle (Subgroup.mem_subgroupOf.1 hx)))
  have hAo : IsOpen (A : Set (GA D V)) := hopn.preimage (GlobalTheory.AutMult.continuous_toFin V)
  have key := MassDataLevelSSteps.toReal_eq_relIndex_mul_of_open v.μ A A' hAA hAo
  have hsurj : Function.Surjective (GlobalTheory.AutMult.toFin V) := fun y => ⟨y, GlobalTheory.AutMult.toFin_coe y⟩
  have hidx : A.relIndex A' = U.relIndex U' := by
    rw [hA, Subgroup.relIndex_comap, hA', Subgroup.map_comap_eq_self_of_surjective hsurj,
      Subgroup.relIndex_subgroupOf hU']
  unfold GlobalTheory.SeeSaw.volLev
  rw [mul_set_eq_comap V U hU, mul_set_eq_comap V U' hU', ← hA, ← hA', key, hidx, mul_comm]

end GlobalTheory.LevVol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChartDecorationLevelPrimeFunctionalEqConjMul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal

namespace GlobalTheory.PhiOneVal

theorem base_deco_fn : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : TC.Laws I) (Z : TC.Later B (TC.cols I l)) (u : B.Word) (a : I.ι)
    (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ i, i ≤ B.R.m → ∀ (β : Ch i) (P : (B.primes X).vT u)
    (x : Formalism.L2.Col.Sp B.fields.E (B.R.N i)), x ∈ Formalism.L2.Col.stdLat B.fields.E (B.R.N i) → ∀ r : Fin (B.R.N i), r.1 + 1 = B.R.N i →
    ∀ c : 𝓞 B.fields.E, algebraMap (𝓞 B.fields.E) B.fields.E c = x r →
      (A.p0 i β).1.1.deco.1.f P x = Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u) * c) := by
  intro B X I l Z u a Ch A hA i hi β P x hx r hr c hc
  choose y hy using (Formalism.L2.Col.mem_stdLat x).1 hx
  have hxy : x = fun j => (y j : B.fields.E) := funext fun j => (hy j).symm
  have hyc : y r = c := NumberField.RingOfIntegers.coe_injective ((hy r).trans hc.symm)
  rw [hxy, ← hyc]
  exact GlobalTheory.BaseFn.fn_eq (hA.base i hi β).1 (hA.base i hi β).2 P r hr _ (fun j => (hA.reads i hi).k_T β P r j hr) y

end GlobalTheory.PhiOneVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BcPrVMemLevelVLOfMoves
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FamTrace


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem prV_toEAf_eq_swap (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (a : AE D) :
    Formalism.UG.prV (E := D.host.E) v (Formalism.IndefR.Datum.toEAf D a) =
      GlobalTheory.StabConjIndex.swap v (GlobalTheory.AdelicU.compFin D.host.F D.host.E v a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x e => rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]


set_option maxHeartbeats 1000000 in
theorem bc_prV_mem_levelVL_of_moves : ∀ (D : D7) (S : HSp D) (n : ℕ) (hn : S.rank = n) (L : GlobalTheory.FinPl.Lat S)
    (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), L.FG →
    (∀ x : Fin n → D.host.E, x ∈ Λ ↔ (fun i => x (finCongr hn i)) ∈ L) →
    ∀ (κ : GA D S) (g : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
    GlobalTheory.AdForm.finM S hn κ = g.1 → ∀ v : HeightOneSpectrum (𝓞 D.host.F),
    GlobalTheory.FinPl.Moves S κ L L (· = v) →
    Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) g ∈
      Formalism.UG.levelVL (Formalism.L2.Forms.sigD D) (S.gram.reindex (finCongr hn) (finCongr hn)) v Λ := by
  intro D S n hn L Λ hL hΛ κ g hg v hm
  subst hn
  have hΛL : Λ = L := by
    ext x; rw [hΛ x]; rfl
  subst hΛL
  have h1 := (GlobalTheory.StMoves.moves_iff_stabLoc S Λ hL v κ).1 hm
  have h2 := GlobalTheory.StabConjIndex.map_stabLoc (Formalism.L2.Forms.sigD D) S.gram v Λ
  have h3 : GlobalTheory.StabConjIndex.toGL (Formalism.L2.Forms.sigD D) S.gram v (GlobalTheory.AdelicU.proj _ S.gram v κ) ∈
      Formalism.UG.levelVL (Formalism.L2.Forms.sigD D) S.gram v Λ := h2 ▸ ⟨_, h1, rfl⟩
  have hgram : (S.gram.reindex (finCongr (rfl : S.rank = S.rank)) (finCongr rfl)) = S.gram := by
    ext i j; simp
  have hp := GlobalTheory.AdelicU.matHom_proj (Formalism.L2.Forms.sigD D) S.gram v κ
  have hE : Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) g =
      GlobalTheory.StabConjIndex.toGL (Formalism.L2.Forms.sigD D) S.gram v (GlobalTheory.AdelicU.proj _ S.gram v κ) := by
    ext i j
    have hij := congrFun (congrFun hg i) j
    have e1 : (GlobalTheory.StabConjIndex.toGL (Formalism.L2.Forms.sigD D) S.gram v (GlobalTheory.AdelicU.proj _ S.gram v κ)).val i j =
        GlobalTheory.StabConjIndex.swap v ((GlobalTheory.AdelicU.matHom (Fv D.host.F v) (Formalism.L2.Forms.sigD D) S.gram
          (GlobalTheory.AdelicU.proj (Formalism.L2.Forms.sigD D) S.gram v κ)).val i j) := rfl
    rw [e1, hp]
    show Formalism.UG.prV v (g.1 i j) = GlobalTheory.StabConjIndex.swap v (GlobalTheory.AdelicU.compFin _ _ v _)
    rw [← hij]
    exact prV_toEAf_eq_swap D v _
  rw [hgram, hE]
  exact h3

theorem levelVL_eq_of_std {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {Lb Λ : Submodule (𝓞 E) (Fin n → E)} {T : ℕ}
    {v : HeightOneSpectrum (𝓞 F)} (hT : (T : 𝓞 F) ∉ v.asIdeal)
    (h1 : ∀ x ∈ Lb, ∀ j, ∃ r : 𝓞 E, x j = (r : E)) (h2 : ∀ j, (Pi.single j (T : E) : Fin n → E) ∈ Lb)
    (h1' : ∀ x ∈ Λ, ∀ j, ∃ r : 𝓞 E, x j = (r : E)) (h2' : ∀ j, (Pi.single j (T : E) : Fin n → E) ∈ Λ) :
    Formalism.UG.levelVL σ J v Lb = Formalism.UG.levelVL σ J v Λ := by
  have e1 := GlobalTheory.Mem.Col2.ChartLevel.latS_eq_std hT h1 h2
  have e2 := GlobalTheory.Mem.Col2.ChartLevel.latS_eq_std hT h1' h2'
  unfold Formalism.UG.levelVL
  exact congrArg _ (e1.trans e2.symm)

end GlobalTheory.FamTrace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLevelLineVectorPrimitiveRowLatticeNorm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch.SZ

variable {D : D7}

theorem cY_eq_repr (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (y : (VS D).V) :
    GlobalTheory.Core.SBesEx.cY X h y = (X.bas.reindex (finCongr (rank_eq X h)).symm).repr y := by
  funext k
  simp [GlobalTheory.Core.SBesEx.cY, HidaSetting.crd, crdOf, Module.Basis.repr_reindex]

theorem sum_bas_mem_iff (I : AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D) (ιE : I.E ≃+* D.host.E)
    (hId : ∀ x : I.E, HEq (ιE x) x) (hn : (D.sp.Y 0).rank = I.n) (bas : Module.Basis (Fin I.n) D.host.E (VS D).V)
    (hL : ∀ x : Fin I.n → I.E, x ∈ I.L ↔ (∑ i, ιE (x i) • bas i) ∈ (VS D).L0) (v : Fin (D.sp.Y 0).rank → D.host.E) :
    (∑ k, v k • bas (Fin.cast hn k)) ∈ (VS D).L0 ↔ (∑ k, v k • (VS D).frame k) ∈ (VS D).L0 := by
  subst hI
  have h2 : ∀ i, ιE (v i) = v i := fun i => eq_of_heq (hId _)
  rw [← Formalism.L2.SG.InstExistsPf.mem_Lv]
  refine Iff.trans ?_ (hL v).symm
  apply iff_of_eq
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h2 i]
  rfl

theorem cY_mem_latS_iff (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hId : GlobalTheory.Core.Mi.IdE X)
    (y : (VS D).V) : GlobalTheory.Core.SBesEx.cY X h y ∈ latS D ↔ y ∈ (VS D).L0 := by
  have hs := sum_bas_mem_iff X.B.I h X.ιE hId (rank_eq X h) X.bas X.L_eq (GlobalTheory.Core.SBesEx.cY X h y)
  have hy : (∑ k, GlobalTheory.Core.SBesEx.cY X h y k • X.bas (Fin.cast (rank_eq X h) k)) = y := by
    rw [cY_eq_repr]
    conv_rhs => rw [← (X.bas.reindex (finCongr (rank_eq X h)).symm).sum_repr y]
    simp
  rw [hy] at hs
  rw [hs]
  simp only [latS, Formalism.L2.Herm.crdLat, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    Formalism.L2.Herm.crd]
  constructor
  · rintro ⟨w, hw, hwe⟩
    have : w = ∑ k, GlobalTheory.Core.SBesEx.cY X h y k • (VS D).frame k := by
      rw [← hwe]; exact ((VS D).frame.sum_equivFun w).symm
    rw [← this]; exact hw
  · intro hw
    exact ⟨_, hw, by
      rw [← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]⟩

theorem cY_smul (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (c : D.host.E) (y : (VS D).V) :
    GlobalTheory.Core.SBesEx.cY X h (c • y) = c • GlobalTheory.Core.SBesEx.cY X h y := by
  rw [cY_eq_repr, cY_eq_repr, map_smul, Finsupp.coe_smul]

end GlobalTheory.Core.Mi.LatMatch.SZ

namespace GlobalTheory.Core.Mi.LatMatch.SZ

variable {D : D7}

theorem smul_zu_mem_iff (X : HidaSetting D) (u : D.what₂.Word) (c : D.host.E) :
    c • X.zu u ∈ (VS D).L0 ↔ ∃ o : 𝓞 D.host.E, (o : D.host.E) = c := by
  constructor
  · intro hc
    have hfix := (X.Fu_fixed u).2.2.2.2
    apply hfix c
    have hz : (X.Fu u).z = X.zu u := X.flagZVector u
    show c • (X.Fu u).z ∈ _
    rw [hz]
    have horth : c • X.zu u ∈ Formalism.MainNotions.S.Lat.orth (VS D) (X.Fu u).X := by
      simp only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker]
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨a, rfl⟩ := hy
        rw [map_smulₛₗ, ← hz, (X.Fu u).z_orth a, smul_zero]
      | zero => simp
      | add x y _ _ hx hy => rw [map_add (f := _), LinearMap.add_apply, hx, hy, add_zero]
      | smul a x _ hx => rw [LinearMap.map_smulₛₗ₂, hx, smul_zero]
    exact Submodule.mem_inf.2 ⟨Submodule.mem_sup_left (Submodule.mem_inf.2 ⟨hc, horth⟩), horth⟩
  · rintro ⟨o, rfl⟩
    have hz : X.zu u ∈ (VS D).L0 := by
      rw [X.Lam_split]
      exact Submodule.mem_sup_left (Submodule.mem_sup_right (X.zu_Lb u))
    have := (VS D).L0.smul_mem o hz
    simpa [algebraMap_smul] using this

theorem quad {m n : Type} [Fintype m] [Fintype n] (M : Matrix m n D.host.E) (G : Matrix m m D.host.E) (x : n → D.host.E) :
    star x ⬝ᵥ (Mᴴ * G * M) *ᵥ x = star (M *ᵥ x) ⬝ᵥ G *ᵥ (M *ᵥ x) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

end GlobalTheory.Core.Mi.LatMatch.SZ


open GlobalTheory.Core.Mi.LatMatch.SZ in
theorem GlobalTheory.Core.Mi.LatMatch.sz_tied : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (μ lam : D.host.E), GlobalTheory.Core.Mi.IdE X → B.FrameAt μ lam → (∀ t : D.host.E, t • vecB B.o B.ζ ∈ coreLat B.d (latS D) ↔ μ * t ∈ (1 : FI D)) ∧ star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ = -(μ * star μ * (((D.mem u).A.T : ℕ) : D.host.E)) ∧ vecB B.o B.ζ ≠ 0 := by
  intro D X h u ψ A B μ lam hId hF
  have hz : B.d.i₀ *ᵥ vecB B.o B.ζ = μ • GlobalTheory.Core.SBesEx.cY X h (X.zu u) := hF.z
  refine ⟨fun t => ?_, ?_, ?_⟩
  · rw [mem_coreLat, Matrix.mulVec_smul, hz, smul_smul, ← cY_smul, cY_mem_latS_iff X h hId, smul_zu_mem_iff,
      FractionalIdeal.mem_one_iff, mul_comm]
  · rw [← B.o.isoB, quad, ← B.d.iso, quad]
    change star (B.d.i₀ *ᵥ vecB B.o B.ζ) ⬝ᵥ _ *ᵥ (B.d.i₀ *ᵥ vecB B.o B.ζ) = _
    rw [hz, Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct,
      GlobalTheory.Core.SBesEx.cY_isom D X h hId, X.zu_norm]
    simp only [smul_eq_mul]
    ring
  · intro h0
    apply B.line.2
    rw [← B.o.isoB, quad]
    change star (vecB B.o B.ζ) ⬝ᵥ _ *ᵥ (vecB B.o B.ζ) = 0
    rw [h0]
    simp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatWeilRepresentationCoresStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselToJacobiFlat_weilRepresentation_cores : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ → ∀ h₀, ∀ n ∈ radX J.d, ∀ h', flatBF s (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) = s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ n h' (flatBF s Ψ)) := by
  first | exact @GlobalTheory.Unf.FlatCommBF.flatBF_om | exact GlobalTheory.Unf.FlatCommBF.flatBF_om | (intros; apply GlobalTheory.Unf.FlatCommBF.flatBF_om <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselUnfoldingOrbitMemParabolicMulStabiliser
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

noncomputable section

set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.FinPl.OrbitCoset

variable {D : D7}

theorem mem_congGrp_iff' (V : HSp D) (I : Ideal (AE D)) (g : GA D V) :
    g ∈ congGrp V I ↔ (mt V g).map (Ideal.Quotient.mk I) = 1 := by
  unfold congGrp
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Units.ext_iff]
  rfl

theorem matrixTransform_wittCoreEmbedding {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (h : GA D S₀) :
    mt S (d.emb0 h) = d.jX ⬝ d.pX + d.j0 ⬝ mt S₀ h ⬝ d.p0 + d.jY ⬝ d.pY := by
  conv_lhs => rw [← Matrix.mul_one (mt S (d.emb0 h)), ← d.sum_eq_one]
  simp only [Matrix.mul_add, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, d.wittDecomp_anisotropicEmbedding_inclY]

theorem wittCoreEmbedding_mem_supportedSubgroup {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (P : Pl D → Prop) {h : GA D S₀}
    (hh : h ∈ grpAt S₀ P) : d.emb0 h ∈ grpAt S P := by
  rw [grpAt, mem_congGrp_iff'] at hh ⊢
  have hadd : ∀ A B : Matrix (Fin S.rank) (Fin S.rank) (AE D), (A + B).map (Ideal.Quotient.mk (idAt D P)) =
      A.map (Ideal.Quotient.mk (idAt D P)) + B.map (Ideal.Quotient.mk (idAt D P)) :=
    fun A B => Matrix.map_add _ (Ideal.Quotient.mk (idAt D P)).map_add A B
  have key : (mt S (d.emb0 h)).map (Ideal.Quotient.mk (idAt D P)) =
      (d.jX ⬝ d.pX + d.j0 ⬝ d.p0 + d.jY ⬝ d.pY).map (Ideal.Quotient.mk (idAt D P)) := by
    rw [matrixTransform_wittCoreEmbedding]; simp only [hadd, Matrix.map_mul, hh, Matrix.mul_one]
  rw [key, d.sum_eq_one]
  exact Matrix.map_one _ (Ideal.Quotient.mk (idAt D P)).map_zero (Ideal.Quotient.mk (idAt D P)).map_one

theorem emb_mem_grpAt' {S A B : HSp D} (o : OrthDec S A B) {P : Pl D → Prop} {a : GA D A} (ha : a ∈ grpAt A P) :
    o.emb (a, 1) ∈ grpAt S P := by
  rw [grpAt, mem_congGrp_iff'] at ha ⊢
  have hadd : ∀ M N : Matrix (Fin S.rank) (Fin S.rank) (AE D), (M + N).map (Ideal.Quotient.mk (idAt D P)) =
      M.map (Ideal.Quotient.mk (idAt D P)) + N.map (Ideal.Quotient.mk (idAt D P)) :=
    fun M N => Matrix.map_add _ (Ideal.Quotient.mk (idAt D P)).map_add M N
  have key : (mt S (o.emb (a, 1))).map (Ideal.Quotient.mk (idAt D P)) =
      (o.jA ⬝ o.pA + o.jB ⬝ o.pB).map (Ideal.Quotient.mk (idAt D P)) := by
    rw [o.mt_emb, mt_one]; simp only [hadd, Matrix.map_mul, ha, Matrix.mul_one]
  rw [key, o.sum_eq_one]
  exact Matrix.map_one _ (Ideal.Quotient.mk (idAt D P)).map_zero (Ideal.Quotient.mk (idAt D P)).map_one

theorem inK_mul' {S : HSp D} {L : Lat S} {P : Pl D → Prop} {a b : GA D S} (ha : InK S L P a) (hb : InK S L P b) :
    InK S L P (a * b) := by
  refine ⟨mul_mem ha.1 hb.1, fun y hy => ?_⟩
  have hy' : ∀ i, (mt S b *ᵥ y) i ∈ idAt D P := fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)
  rw [mt_mul, ← Matrix.mulVec_mulVec, ← ha.2 _ hy', hb.2 y hy]

end GlobalTheory.FinPl.OrbitCoset

namespace GlobalTheory.FinPl.OrbitCoset

theorem orbit_coset : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ) (L : Lat B.V) (L₀ : Lat B.V₀) (v : Pl D), MonoAt B.d L L₀ v →
    ∀ n ∈ flagN B.d, n ∈ grpAt B.V (· = v) → ∀ a ∈ grpAt B.A (· = v), ∀ κ₀, InK B.V₀ L₀ (· = v) κ₀ → ∀ κ,
    InK B.V L (· = v) κ → ∃ r ∈ besGrp B.d B.o, r ∈ grpAt B.V (· = v) ∧ ∃ κ', InK B.V L (· = v) κ' ∧
      n * B.d.emb0 (B.o.emb (a, 1) * κ₀) * κ = r * κ' := by
  intro D σ B L L₀ v hM n hn hnv a ha κ₀ hκ₀ κ hκ
  refine ⟨n * embA B.d B.o a, mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨a, rfl⟩),
    mul_mem hnv (wittCoreEmbedding_mem_supportedSubgroup B.d _ (emb_mem_grpAt' B.o ha)), B.d.emb0 κ₀ * κ,
    inK_mul' ⟨wittCoreEmbedding_mem_supportedSubgroup B.d _ hκ₀.1, (carriesLattice_wittEmbedding_iff_core D B.V B.V₀ σ B.d L L₀ v κ₀ hM).2 hκ₀.2⟩ hκ, ?_⟩
  rw [map_mul, embA_apply]
  group

end GlobalTheory.FinPl.OrbitCoset

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainEachStepSplitPlaceWithoutExcludedParams
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainNS
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainNS

theorem chainNS_holds : ∀ D : D7, ChainNS D := by
  intro D c hc S' hS' B hB hBi k hk
  obtain ⟨p, hp, -, hpS, v, hv⟩ :=
    GlobalTheory.SplitChoice.exists_split_prime D (S' : Set (HeightOneSpectrum (𝓞 D.host.F))) 1 (Finset.finite_toSet _) one_ne_zero
  have hvS : v ∉ S' := fun h => hpS v (Finset.mem_coe.2 h) hv
  refine ⟨v, hvS, GlobalTheory.SplitPlace.isSplit_of_splitsCompletely D p hp v hv, ?_⟩
  intro w hw β hβ k' hk'
  have hrt5 : D.R.r + 5 ≤ D.R.t := D.R.rank_add_five_le
  have hrt : D.R.r + 2 ≤ D.R.t := by omega
  have hwS : w ∉ GlobalTheory.LFun.above D.host.E (S' : Set (HeightOneSpectrum (𝓞 D.host.F))) := by
    simp [GlobalTheory.LFun.above, hw, hvS]
  have hpw : ((p : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
    have h := hv
    rw [← hw, HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at h
    exact h
  have hwc : w.under (𝓞 D.host.F) ∉ c.S := fun h => hvS (hw ▸ hS' h)
  set x := GlobalTheory.LFun.val (F := D.host.F) (c.chT (k + 1)) w with hx
  have hmem : x⁻¹ * β ∈ GlobalTheory.LFun.twist (chainPar c B k) (GlobalTheory.LFun.val (F := D.host.F) (c.chT (k + 1)))⁻¹ w := by
    simp only [GlobalTheory.LFun.twist, Pi.inv_apply]
    exact Multiset.mem_map_of_mem _ hβ
  rw [chainPar_twist_chT] at hmem
  have key : ((x⁻¹ * β : ℂˣ) : ℂ) ≠ GlobalTheory.LFun.npow w ((k' : ℂ) / 2) := by
    have hN := _root_.GlobalTheory.RkNs.small_entries_and_strings_avoid_excluded D.host.E w D.R.r D.R.t hrt k' hk'
    simp only [Pi.add_apply, Finset.sum_apply, Multiset.mem_add, Multiset.mem_sum] at hmem
    rcases hmem with h | ⟨i, hi, h⟩
    · simp only [GlobalTheory.LFun.twist, Pi.inv_apply] at h
      obtain ⟨b, hb, hb'⟩ := Multiset.mem_map.1 h
      rw [← hb']
      have hb1 := (hB w hwS).2 b hb
      have hb2 := (hBi w hwS).2 b⁻¹ (Multiset.mem_map_of_mem _ hb)
      have hu : ‖((GlobalTheory.LFun.val (F := D.host.F) (c.μ (k + 1)) w : ℂˣ) : ℂ)‖ = 1 := GlobalTheory.LFun.norm_val _ _
      refine hN.1 _ (Units.ne_zero _) ?_ ?_
      · rw [Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv, hu, inv_one, one_mul]
        exact hb1
      · rw [Units.val_mul, mul_inv, norm_mul, Units.val_inv_eq_inv_val, inv_inv, hu, one_mul]
        rw [Units.val_inv_eq_inv_val] at hb2
        exact hb2
    · have hi' := Finset.mem_Icc.1 hi
      exact hN.2 _ (GlobalTheory.LFun.norm_val _ _)
        (GlobalTheory.T.heckeCharQuotient_ne_one_completelySplitPrime D c hc i (k + 1) hi'.1 (by omega) (by omega) p hp w hpw hwc) _ h
  intro he
  apply key
  rw [Units.val_mul, Units.val_inv_eq_inv_val, mul_comm]
  exact he

end GlobalTheory.ChainNS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHermitianLineVectorPrescribedNormStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hermitianLine_vector_prescribed_norm : ∀ (D : D7) (c : D.host.E) (ε : ℤˣ), c ≠ 0 → ∃ (L : HSp D) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ ∧ L.SigOK ∧ star ζ ⬝ᵥ L.gram *ᵥ ζ = ((ε : ℤ) : D.host.E) * (c * star c) ∧ ∀ τ, L.sig τ = if ε = 1 then (1, 0) else (0, 1) := by
  first | exact @GlobalTheory.HermLine.exists_line_vec | exact GlobalTheory.HermLine.exists_line_vec | (intros; apply GlobalTheory.HermLine.exists_line_vec <;> assumption)
end

