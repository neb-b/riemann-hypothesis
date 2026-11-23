module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1688
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0866
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0015
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle0012
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle0014
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle0013
public import Development.AutomorphicArithmetic.DivisorFrames.ExistsUnitaryAutomorphicFormOfWeightVectorValued
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1793
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1697
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1698
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1188
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRingKrullDimQuotientMvPolynomialEqNat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
public import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1766
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLiftIsLiftPrincipalLevelDatumRealisation
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplePoleAlong
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LogCanonicalReflexive

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k}

def SimplePoleAlong (O : Y.Opens) {P B N : LB Y} (C : ProdChart P B N) (ω : H0 p P O) : Prop :=
  ∀ y, y ∉ O → ∃ (V : Y.Opens) (_ : y ∈ V) (τ : C.τ) (ha : V ≤ P.U (C.a τ)) (_ : V ≤ B.U (C.b τ))
    (_ : V ≤ N.U (C.c τ)) (t u : Γ(Y, V)),
    (∀ z (hz : z ∈ V), IsUnit (ger z hz t) ↔ z ∈ O) ∧ (∀ z (hz : z ∈ V), IsUnit (ger z hz u)) ∧
    (∀ (W : Y.Opens) (hW : W ≤ V) (f : Γ(Y, W)),
      (∀ z (hz : z ∈ W), z ∉ O → ger z hz f ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk z)) →
        ∀ z (hz : z ∈ W), ger z (hW hz) t ∣ ger z hz f) ∧
    ∀ z (hz : z ∈ V) (ho : z ∈ O), ger z hz t * H0.germ (C.a τ) z ho (ha hz) ω = ger z hz u

end GlobalTheory.LogCanonicalReflexive
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallPlacePrimeLocal
section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem emb_cj {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime] (io : PadicAlgCl l ≃+* ℂ)
    (τ : E →+* PadicAlgCl l) :
    io.toRingHom.comp (GlobalTheory.ExpFrame.cj τ) = ComplexEmbedding.conjugate (io.toRingHom.comp τ) := by
  ext x
  exact IsCMField.complexEmbedding_complexConj E (io.toRingHom.comp τ) x

private theorem places_inj {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime] (io : PadicAlgCl l ≃+* ℂ)
    {ι : Type} {inc : ι → (E →+* PadicAlgCl l)} (h : IsHalf inc) :
    Function.Injective fun τ => InfinitePlace.mk (io.toRingHom.comp (inc τ)) := by
  intro τ τ' e
  have hi : ∀ a b : E →+* PadicAlgCl l, io.toRingHom.comp a = io.toRingHom.comp b → a = b := fun a b hab =>
    RingHom.ext fun x => io.injective (RingHom.congr_fun hab x)
  rcases InfinitePlace.mk_eq_iff.1 e with e | e
  · exact h.1 (hi _ _ e)
  · exact absurd (hi _ _ ((emb_cj io _).trans e)) (h.2.1 τ τ')

set_option maxHeartbeats 1600000 in
private theorem finiteRing_sq_sub_mul_sq_eq_of_card {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
    (j : Fin D.R.m) (t : p.P.T) {l : ℕ} [Fact l.Prime] {N : ℕ} (hN : N = (Vc D j).rank)
    (F : Frame l D.what₂.Tau N) (e0 : D.what₂.LL →+* PadicAlgCl l) (ix : F.I → (blk p j t).Pl × ℕ)
    (inc : D.what₂.Tau → (D.host.E →+* PadicAlgCl l)) (T : Tied p j t F e0 ix inc)
    (mu : D.what₂.Tau → ℕ → ℕ) (θ : F.I → PadicAlgCl l) (hmu : ∀ τ, Antitone (Formalism.CohomologicalDescent.LD.res N (mu τ))) (hθ : F.IsEig mu θ) :
    ∃ π : Submodule ℂ (UA D.host.E N → ℂ), IsAutRepU π ∧
      (∀ τ, ∃ lam : DomWeight N, (∀ a, lam.w a = (mu τ a : ℤ) + T.sh τ) ∧ HasWeightAt π (T.io.toRingHom.comp (inc τ)) lam ∧
        HasWeightAt π (T.io.toRingHom.comp (GlobalTheory.ExpFrame.cj (inc τ))) lam.dual) ∧
      ∃ φ ∈ π, φ ≠ 0 ∧
        (∀ v, GlobalTheory.Hk3.Good p.R.toRealDat t v → ∀ x ∈ locU N v, cLoc v x ∈ GlobalTheory.LFun.KGL v (n := N) → RU D.host.E N x φ = φ) ∧
        ∀ Q : (blk p j t).Pl, (∀ x ∈ locU N (labOf p j t Q), cLoc (labOf p j t Q) x ∈ GlobalTheory.LFun.KGL (labOf p j t Q) (n := N) →
          RU D.host.E N x φ = φ) ∧
        ∀ i, (ix i).1 = Q →
          GlobalTheory.LFun.heckeVec ((RU D.host.E N).comp (locU N (labOf p j t Q)).subtype)
            ((GlobalTheory.LFun.KGL (labOf p j t Q) (n := N)).comap ((cLoc (labOf p j t Q)).comp (locU N (labOf p j t Q)).subtype))
            (fun x => GlobalTheory.SphPar.divInd (Formalism.UG.Ov D.host.E (labOf p j t Q))
              (Formalism.IndefR.Mult.dualLab (Formalism.IndefR.Mult.splitLab N (ix i).2))
              ((cLoc (labOf p j t Q)).comp (locU N (labOf p j t Q)).subtype x)) φ = T.io (θ i) • φ := by
  subst hN
  classical
  have hs : (Vc D j).SigOK := D.sp.V_sig _
  have hp : (Vc D j).IsPosDef := p.vpos j
  have hinf : Formalism.L2.Theta.IsInfFam p.R.θ := p.charW.base.models.inf
  obtain ⟨jj, h₀, hTr⟩ := GlobalTheory.DefTransfer.exists_isTransfer D (Vc D j) p.R.θ hinf hs hp
  obtain ⟨B, hB1, hB2⟩ := UpperTheory.exists_invariant_posDef_hermitian_form_autForm_unitary D (Vc D j) hs hp jj hTr.2.1
  obtain ⟨Fm, hF0, hFl, hFr, hFh⟩ := UpperTheory.exists_nonzero_vectorValued_eigenform_unitary p j t F e0 ix inc T mu θ hθ
  have hb : ∀ τ, T.io.toRingHom.comp (e0.comp (Links.labLL D τ)) = Formalism.BasicNotions.TH.tauE D τ := fun τ => by
    rw [← Formalism.IndefR.Conj.labE_base τ]
    exact RingHom.ext fun x => T.liftFrame_embedding_base _
  have hemb : ∀ τ, T.io.toRingHom.comp (inc τ) = Formalism.BasicNotions.TH.tauE D τ ∨
      T.io.toRingHom.comp (inc τ) = ComplexEmbedding.conjugate (Formalism.BasicNotions.TH.tauE D τ) := fun τ => by
    rcases T.lab τ with h | h
    · exact Or.inl (by rw [h, hb])
    · exact Or.inr (by rw [h, emb_cj, hb])
  have hfix : ∀ (k : Formalism.L2.Theta.GA D (Vc D j)), (∃ h : (Formalism.L2.Theta.finHom (Vc D j)).rangeRestrict k ∈ levJ p j t,
      levChi p j t ⟨_, h⟩ = 1) → ∀ g, Fm (g * (Formalism.L2.Theta.finHom (Vc D j)).rangeRestrict k) = Fm g := by
    rintro k ⟨h, h1⟩ g
    have := hFr ⟨_, h⟩ g
    rw [h1, Units.val_one, one_smul] at this
    exact this
  have hev : ∀ᶠ κ in nhds (1 : Formalism.L2.Theta.GA D (Vc D j)), ∀ g,
      Fm (g * (Formalism.L2.Theta.finHom (Vc D j)).rangeRestrict κ) = Fm g :=
    (GlobalTheory.ThetaIntegrand.eventually_level (Vc D j) (p.R.βV j) (p.R.datVt j t)).mono fun κ h => hfix κ h
  obtain ⟨F1, h10, h1l, h1i, h1e, A, hA⟩ := UpperTheory.vectorValued_autForm_equivariant_infinite_component D (Vc D j) p.R.θ jj h₀ hinf hTr
    (fun τ => T.io.toRingHom.comp (inc τ)) hemb mu T.sh Fm hF0 hFl hev
  let lam : D.what₂.Tau → DomWeight (Vc D j).rank := fun τ =>
    ⟨fun a => (mu τ a : ℤ) + T.sh τ, fun a b hab => add_le_add_left (Int.ofNat_le.2 (hmu τ hab)) _⟩
  obtain ⟨π, hπ, hw, φ, hφ, hφ0, hsum⟩ := UpperTheory.exists_unitaryAutomorphicForm_of_weightVectorValued D.host.E (Vc D j).rank D.what₂.Tau (fun τ => T.io.toRingHom.comp (inc τ))
    (places_inj T.io T.half) mu T.sh lam (fun _ _ => rfl) B hB1 hB2 F1 h10 h1l h1i h1e
  have htr : ∀ g y, F1 (g * y) = A (Fm ((Formalism.L2.Theta.finHom (Vc D j)).rangeRestrict (jj g * h₀) *
      (Formalism.L2.Theta.finHom (Vc D j)).rangeRestrict (GlobalTheory.DefTransfer.cj jj h₀ y))) := fun g y => by
    rw [hA, ← map_mul, GlobalTheory.DefTransfer.cj_apply, map_mul jj]
    congr 3
    group
  have hK : ∀ v v', GlobalTheory.Hk3.Good p.R.toRealDat t v' → GlobalTheory.Hk3.hyp (Vc D j) v = GlobalTheory.Hk3.hyp (Vc D j) v' →
      ∀ x ∈ GlobalTheory.DefTransfer.KP (Vc D j).rank v, RU D.host.E (Vc D j).rank x φ = φ := by
    intro v v' hg he x hx
    have h1 := (hTr.2.2.2.2.2.2.1 v x).2 hx
    rw [he] at h1
    have h2 := hfix _ (UpperTheory.levChi_eq_one_of_good_place p j t v' hg _ h1)
    have := hsum Unit Finset.univ (fun _ => x) 1 (fun _ _ => hx.1.1) fun g => by
      rw [Finset.univ_unique, Finset.sum_singleton, one_smul, htr, h2, hA]
    simpa using this
  refine ⟨π, hπ, fun τ => ⟨lam τ, fun _ => rfl, hw τ, ?_⟩, φ, hφ, hφ0, fun v hv x h1 h2 => hK v v hv rfl x ⟨h1, h2⟩, fun Q => ?_⟩
  · rw [emb_cj]
    exact GlobalTheory.DefU.AU.HasWt.conjugate (π := GlobalTheory.DefU.AU.mk ⟨π, hπ⟩) (hw τ)
  have hg : GlobalTheory.Hk3.Good p.R.toRealDat t (plOf p j t Q) :=
    ((GlobalTheory.GoodPrimes.good_primes p.R.toRealDat (p.P.face p.Dcf p.Spf p.Del p.h0 Csz).lv2
      p.charW.base.lev).2.2.2 p.charW.base.fam t Q.1 Q.2).1
  have hKQ := hK (labOf p j t Q) _ hg (GlobalTheory.SphConj.hyp_conj _ _)
  refine ⟨fun x h1 h2 => hKQ x ⟨h1, h2⟩, fun i hi => ?_⟩
  subst hi
  obtain ⟨r1, r2, -⟩ := (T.ix_range (ix i)).1 ⟨i, rfl⟩
  obtain ⟨hloc, R, hR, hRs⟩ := UpperTheory.exists_sphericalHeckeRep_splitLabel_of_offLevelPlace p j t (ix i).1 (ix i).2 r1 r2
  rw [GlobalTheory.SplitTransfer.heckeVec_divInd hTr hKQ hR]
  refine hsum _ R (fun γ => (GlobalTheory.DefTransfer.cj jj h₀).symm γ) _ (fun γ hγ => ((hTr.2.2.2.2.2.2.2 _ _ R hR).1 γ hγ).1.1) fun g => ?_
  simp only [htr, MulEquiv.apply_symm_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, hRs _ Fm hFr, hA, ← map_smul]
  exact congrArg A (hFh i hloc _)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTrivialAtInfinitySet
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section
open Matrix
namespace GlobalTheory.VacScalar

theorem hTens_eq_trace {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    hTens c JA JB x y = Matrix.trace (xᵀ * JA * y.map c * JBᵀ) := by
  simp only [hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem hTens_act {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (JA : Matrix α α E) (JB : Matrix β β E) (A : Matrix α α E)
    (Bm : Matrix β β E) (hA : Aᵀ * JA * A.map c = JA) (hB : Bmᵀ * JB * Bm.map c = JB) (x y : Matrix α β E) :
    hTens c JA JB (A * x * Bmᵀ) (A * y * Bmᵀ) = hTens c JA JB x y := by
  rw [hTens_eq_trace, hTens_eq_trace]
  have e1 : (A * y * Bmᵀ).map c = A.map c * y.map c * (Bm.map c)ᵀ := by
    rw [show (A * y * Bmᵀ).map c = (A * y).map c * (Bmᵀ).map c from Matrix.map_mul (f := c.toRingHom),
      show (A * y).map c = A.map c * y.map c from Matrix.map_mul (f := c.toRingHom), Matrix.transpose_map]
  have e2 : (Bm.map c)ᵀ * JBᵀ * Bm = JBᵀ := by
    conv_rhs => rw [← hB]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [e1, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  calc _ = Matrix.trace (Bm * (xᵀ * (Aᵀ * JA * A.map c) * y.map c * ((Bm.map c)ᵀ * JBᵀ))) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.trace (xᵀ * JA * y.map c * ((Bm.map c)ᵀ * JBᵀ) * Bm) := by rw [hA, Matrix.trace_mul_comm]
    _ = Matrix.trace (xᵀ * JA * y.map c * JBᵀ) := by rw [Matrix.mul_assoc _ _ Bm, e2]

theorem symp_act {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E)
    (k : UG c JA × UG c JB) (x : Matrix α β E) :
    symp c ξ JA JB (actAB c k x) (actAB c k x) = symp c ξ JA JB x x := by
  simp only [symp, actAB]
  rw [hTens_act c JA JB _ _ k.1.2 k.2.2]


open Classical in
theorem pure_update_smul {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : SInf F κ)
    (φ : ∀ w : Pl (F := F), (κ → Fv F w) → ℂ)
    (hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) (w : Pl (F := F))
    (c : ℂ) : pure f (Function.update φ w (c • φ w)) = c • pure f φ := by
  funext x
  have h1 := GlobalTheory.PureFactor.finprod_update φ w (c • φ w) hstd x
  have h2 := GlobalTheory.PureFactor.finprod_update φ w (φ w) hstd x
  rw [Function.update_eq_self] at h2
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.smul_apply, smul_eq_mul]
  rw [h1, h2]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem std_of_vac {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} (hG : G.IsGood B) (S : Finset (Pl (F := F)))
    (φ : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ) (hvac : ∀ w, w ∉ S → φ w = G.M'.vac w) :
    ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
  filter_upwards [hG.hM'.std, S.finite_toSet.compl_mem_cofinite] with v hv hvS
  rw [hvac v hvS, hv]

theorem pure_eigen {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (hT : IsTriple B G X om om') (S : Finset (Pl (F := F))) (f : SInf F (Fin a' × Fin (a + a')))
    (φ : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ) (hSB : ∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w))
    (hvac : ∀ w, w ∉ S → φ w = G.M'.vac w) (w : Pl (F := F)) (hw : w ∉ S) :
    ∃ θ : 𝓞 E, ∀ γ ∈ latAtV G.V' G.W w, G.M'.co.rho B.ψ γ (pure f φ) =
      B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) •
        pure f φ := by
  obtain ⟨-, -, θ, -, hθ⟩ := hT.geo.hM'.vac w
  refine ⟨θ, fun γ hγ => ?_⟩
  have hstd := std_of_vac hT.geo S φ hvac
  have hΦ := GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd
  have e := GlobalTheory.ThK.LocalOps.acts_pure w (G.M'.co.rho B.ψ γ) f φ _ hΦ
    (fun x => GlobalTheory.PureFactor.mulSupport_finite φ hstd x) (by rw [hvac w hw]; exact hθ γ hγ)
  rw [e, ← hvac w hw, pure_update_smul f φ hstd]
  rfl

theorem scalar_of_trivial : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (S : Finset (Pl (F := F))) (g : UA σ G.V'.J) (h : UA σ G.W.J),
    (∀ u : AF F, At (evI F) u → u • (mat g - 1) = 0) → (∀ u : AF F, At (evI F) u → u • (mat h - 1) = 0) →
    (∀ w ∈ S, ∀ u : AF F, At (evFin F w) u → u • (mat g - 1) = 0) →
    (∀ w ∈ S, ∀ u : AF F, At (evFin F w) u → u • (mat h - 1) = 0) →
    (∀ w, w ∉ S → ∀ γ, (mat g * γ * Matrix.transpose (mat h) ∈ latAtV G.V' G.W w ↔ γ ∈ latAtV G.V' G.W w)) →
    ∀ (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ w, w ∉ S → φ w = G.M'.vac w) →
    ∃ c : ℂ, om' (g, h) (pure f φ) = c • pure f φ := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT S g h hgI hhI hgS hhS hlat f φ hSB hvac
  have hstd := std_of_vac hT.geo S φ hvac
  have hΦ : pure f φ ∈ schA F (Fin a' × Fin (a + a')) := GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd
  have hW := IsUWeilPair.isUSplitting hT.weil'
  have hi : ∀ w, w ∉ S → ∀ γ ∈ latAtV G.V' G.W w, ∀ c : ℂ, G.M'.co.rho B.ψ γ (pure f φ) = c • pure f φ →
      G.M'.co.rho B.ψ γ (om' (g, h) (pure f φ)) = c • om' (g, h) (pure f φ) := by
    intro w hw γ hγ c hc
    obtain ⟨θ, hθ⟩ := pure_eigen hT S f φ hSB hvac w hw
    set γ' := actAB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((g, h)⁻¹) γ with hγ'def
    have e1 : mat g * mat g⁻¹ = 1 := by
      show (g * g⁻¹).1.1 = 1
      rw [mul_inv_cancel]; rfl
    have e2 : mat h * mat h⁻¹ = 1 := by
      show (h * h⁻¹).1.1 = 1
      rw [mul_inv_cancel]; rfl
    have hact : actAB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (g, h) γ' = γ := by
      change mat g * (mat g⁻¹ * γ * (mat h⁻¹)ᵀ) * (mat h)ᵀ = γ
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, e2,
        Matrix.transpose_one, Matrix.mul_one]
    have hγ' : γ' ∈ latAtV G.V' G.W w := (hlat w hw γ').1 (by change actAB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (g, h) γ' ∈ _; rw [hact]; exact hγ)
    have e3 := hW.impl (g, h) γ' (pure f φ) hΦ
    erw [hact] at e3
    have hsym : symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ' γ' =
        symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ := by
      erw [← symp_act (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) _ _ _ (g, h) γ', hact]
      rfl
    erw [← e3, hθ γ' hγ', map_smul, hsym]
    by_cases hΦ0 : pure f φ = 0
    · rw [hΦ0, map_zero, smul_zero, smul_zero]
    · rw [hθ γ hγ] at hc
      rw [smul_left_injective ℂ hΦ0 hc]
  have hTΦ : om' (g, h) (pure f φ) ∈ schA F (Fin a' × Fin (a + a')) := hW.pres (g, h) _ hΦ
  obtain ⟨m, f', φ', hSB', hvac', heq⟩ := GlobalTheory.T.theta_series_factorizable_restriction hP F E σ B a a' G X om om' hT S f φ hSB hvac _ hTΦ hi
  have hco := GlobalTheory.T.theta_kernel_archimedean_unipotent_support F E σ B a a' G X om om' hT S g h hgI hhI hgS hhS (pure f φ) hΦ
  obtain ⟨c, hc⟩ := GlobalTheory.T.theta_series_factorizable_restriction_finite hP F E σ B a a' G X om om' hT S f φ hSB hvac m f' φ' hSB' hvac'
    (fun u hu μ hμ => by rw [← heq]; exact hco u hu μ hμ)
  exact ⟨c, heq.trans hc⟩

end GlobalTheory.VacScalar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionVanishes
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Discrepancy GlobalTheory.Cartier GlobalTheory.QCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ZeroDimSystem

def comb {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] {M : LB X} {m : ℕ}
    (t : Fin m → M.Sec) : (Fin m → k) →ₛₗ[algebraMap k Γ(X, ⊤)] M.Sec :=
  ⟨⟨fun c => ∑ i, algebraMap k Γ(X, ⊤) (c i) • t i, fun a b => by
      simp [add_smul, Finset.sum_add_distrib]⟩, fun c a => by
      simp [mul_smul, Finset.smul_sum]⟩

theorem comb_apply {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] {M : LB X} {m : ℕ}
    (t : Fin m → M.Sec) (c : Fin m → k) :
    comb t c = ∑ i, algebraMap k Γ(X, ⊤) (c i) • t i := rfl

def vanishAt {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] {M : LB X} {m : ℕ}
    (t : Fin m → M.Sec) (x : X) : Submodule k (Fin m → k) where
  carrier := {c | x ∉ nonzeroLocus (comb t c)}
  add_mem' := fun {a b} ha hb hx => by
    rw [map_add (f := _)] at hx
    exact (nonzeroLocus_add_le _ _ hx).elim ha hb
  zero_mem' := fun hx => by
    rw [map_zero] at hx
    exact nonzeroLocus_secZero.le hx
  smul_mem' := fun c a ha hx => by
    rw [(comb t).map_smulₛₗ] at hx
    exact ha ((nonzeroLocus_secScale _ _).le hx).2

theorem mem_vanishAt {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] {M : LB X}
    {m : ℕ} (t : Fin m → M.Sec) (x : X) (c : Fin m → k) :
    c ∈ vanishAt t x ↔ x ∉ nonzeroLocus (comb t c) := Iff.rfl

theorem single_notMem_vanishAt {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]
    {M : LB X} {m : ℕ} (t : Fin m → M.Sec) {x : X} {i : Fin m} (hx : x ∈ nonzeroLocus (t i)) :
    (Pi.single i 1 : Fin m → k) ∉ vanishAt t x := by
  classical
  rw [mem_vanishAt, not_not, comb_apply,
    Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp), Pi.single_eq_same, map_one,
    one_smul]
  exact hx

section Main

variable {k : Type} [Field k] [Infinite k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]
  [AlgebraicGeometry.IsNoetherian X] {M : LB X} (hM : M.IsLB) {m : ℕ} (t : Fin m → M.Sec)
  (ht : ⨆ i, nonzeroLocus (t i) = ⊤)
  (hf : ∀ r, algebraMap k Γ(X, ⊤) r = (strHom k X).appTop ((Scheme.ΓSpecIso (.of k)).inv r))
  (hp : IsProjOver (strHom k (X := X)))
include hM ht hf hp

end Main

end GlobalTheory.ZeroDimSystem

namespace GlobalTheory

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOfAt
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.SerBase

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (w : D.what₂.places.Pl) (j : Fin D.R.m)

abbrev delW : Formalism.L2.Host.HChar D.host.E := (R2 p).C.delAt (Formalism.EigenvalueLevelCeiling.plc (D.plEq w))

abbrev plW : Finset (Pl D.host.E) := GlobalTheory.OnTies.placesOver (R2 p) ((R2 p).mu (D.plEq w)) (ownAt D (D.plEq w))

abbrev IsEv (u : ∀ τ, lowT ((R2 p).MW j (sg0 D p.P.A3.A)) τ) : Prop :=
  ∀ τ, (u τ : ((R2 p).MW j (sg0 D p.P.A3.A)).sm τ) = p.v₀ j (sg0 D p.P.A3.A) τ

def KerOf : Prop := ∀ ρ : Setup D.ntw, ρ.Good → RealPin p.R p.cG ρ →
  BaseOf (R2 p) j (ρ.B (ex.nch.twI w) j (ex.nch.sd w)) ∧ (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).de.Q = plW p w ∧
    ∃ ξR φ, KerDat (R2 p) j (delW p w) (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).de.chi ξR (plW p w)
      (ρ.om (ex.nch.twI w) j (ex.nch.sd w) 1) φ

def TraceOf : Prop := ∀ ρ : Setup D.ntw, ρ.Good → RealPin p.R p.cG ρ → ρ.LevelOf D.nexp → ∀ h P,
  ρ.theta (ex.nch.twI w) j (ex.nch.sd w) h P = levelTrace (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹
    (series (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).F (ρ.om (ex.nch.twI w) j (ex.nch.sd w) 1)
      (princ (ρ.B (ex.nch.twI w) j (ex.nch.sd w))).vecBase h P)

def KerRat : Prop := ∀ χ ξR ω φ, KerDat (R2 p) j (delW p w) χ ξR (plW p w) ω φ → ∀ h ∈ GfC (Vc D j), ∀ y, InCoefLat (R2 p) j h y →
  ∀ u, IsEv p j u → ∃ x, adForm (R2 p) j x (fun τ => u τ) = singleSeries (R2 p) j ω φ h y u

def LatIo : Prop := ∀ ρ : Setup D.ntw, ρ.Good → RealPin p.R p.cG ρ → ∀ c : ℂ, c ≠ 0 →
  IsScale p.R p.v₀ (ρ.B (ex.nch.twI w) j (ex.nch.sd w)) c → ∃ u, IsEv p j u ∧ ∀ h ∈ GfC (Vc D j),
    ∀ P ∈ ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (smallInt D) h,
      ∃ y, InCoefLat (R2 p) j h y ∧ (R2 p).ioP j (PiTensorProduct.tprod ℂ u) y = c • P

def ReadCmp : Prop := ∀ (ρ : Setup D.ntw) (hρ : ρ.Good) (e : FractionRing (ex.nch.Oe w) →+* ℂ),
  (∀ x, e (ex.nch.embW w x) = D.what₂.embLL x) →
  (∀ a : D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w),
    e (algebraMap (ex.nch.Oe w) _ (algebraMap _ (ex.nch.Oe w) a)) = ρ.eOk (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) a) →
  ∀ ν : ℂ, ν ≠ 0 → ∀ rd : Can p w j, IsCan p rd → ∀ u, IsEv p j u → ∀ f x (a : ℂ),
    rdAt p w j hρ ν f = a • ν⁻¹ • adForm (R2 p) j x (fun τ => u τ) →
      f = 0 ∨ ∃ b, e b = a ∧ ((1 : FractionRing (ex.nch.Oe w)) ⊗ₜ[D.ntw.O (ex.nch.twI w)] f : Tgt ex w j) = b • rd x

end Point

def FlatKer : Prop := ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
  (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R →
  ∀ i : Fin D.R.m, VStd D i → ∀ B : Base (Vc D i) (Wc D i), B.Good → BaseOf R i B →
  ∀ ξ ξR ω φ, KerDat R i ξ B.de.chi ξR B.de.Q ω φ → (∃ t, B.de.Q ⊆ R.Q t) → ∀ N : ℕ, N ≠ 0 →
    (∀ PP ∈ B.de.Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) →
    ∃ (z : GA D (Vc D i)) (c : ℂ), IsCentAt i B.de.Q z ∧ UnitOff N c ∧
      ∀ h P, series B.F ω (princ B).vecBase h P = c • series B.F ω φ (h * z) P

def CentLat : Prop := ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
  (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (Q : Finset (Pl D.host.E))
  (z : GA D (Vc D i)), IsCentAt i Q z → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) →
    ∃ m : ℕ, ∀ h ∈ GfC (Vc D i), ∀ y, (InCoefLat R i h y → InCoefLat R i (h * z) ((N : ℂ) ^ m • y)) ∧
      (InCoefLat R i (h * z) y → InCoefLat R i h ((N : ℂ) ^ m • y))

def TraceRat : Prop := ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
  (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → R.LUnif →
  ∀ (i : Fin D.R.m) (v₀ : (R.MW i (sg0 D A)).Vec), IsExtVec (R.MW i (sg0 D A)) v₀ →
  ∀ ξ χ ξR Q ω φ, KerDat R i ξ χ ξR Q ω φ → ∀ (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) h y
    (u : ∀ τ, lowT (R.MW i (sg0 D A)) τ), (∀ τ, (u τ : (R.MW i (sg0 D A)).sm τ) = v₀ τ) →
    ∀ x, adForm R i x (fun τ => u τ) = singleSeries R i ω φ h y u →
      ∃ x', ∀ v : ∀ τ, lowT (R.MW i (sg0 D A)) τ, adForm R i x' (fun τ => v τ) = levelTrace R i U ψ (singleSeries R i ω φ h y v)

def OwnUnit : Prop := ∀ (D : D7) (c : NChoice D) (w : D.what₂.places.Pl), IsUnit ((ownAt D (D.plEq w) : ℕ) : c.Oe w)

end GlobalTheory.BigOn.Exp.SerBase
end
end

