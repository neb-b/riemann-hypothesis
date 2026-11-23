module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0474
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0435
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0457
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetExpansionExpDepth
public import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinprodLocalDifferentIdealNormEqDiscr
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ProductLocalDensitiesAdeleCharacter
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1335
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0404
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0387
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtThetaSumHeisenbergLine
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactPairRealAverageFockEqJetOperator
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0236
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsRealFnNeZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PosDefOfNode
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries

open scoped ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefConv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G)

def IsInvCont (X : Node) (F : Fn G X) : Prop := Continuous F ∧ ∀ γ ∈ GQ (G.V X), ∀ g, F (γ * g) = F g

def Good (a : Arrow T) (f : Sch G a) : Prop :=
  (Continuous fun p : GA D (G.V a.src) × GA D (G.V a.tgt) => W.kerA a f p.1 p.2) ∧
  (∀ γ ∈ GQ (G.V a.src), ∀ γ' ∈ GQ (G.V a.tgt), ∀ g h, W.kerA a f (γ * g) (γ' * h) = W.kerA a f g h) ∧
  (∀ τ, (gramAt D (G.V a.src) τ).PosDef) ∧ (M.ν a.src).IsHaarMeasure ∧
  IsFundamentalDomain (GQ (G.V a.src)) (M.fd a.src) (M.ν a.src)

theorem step {a : Arrow T} {f : Sch G a} (hg : Good W M a f) {F : Fn G a.src} (hF : IsInvCont a.src F) :
    LiftConv W M a f F ∧ IsInvCont a.tgt (liftA W M a f F) := by
  obtain ⟨hK, hinv, hpos, hH, hfd⟩ := hg
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact _ hpos
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V a.src)
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V a.tgt)
  have hl : ∀ γ ∈ GQ (G.V a.src), ∀ g h, W.kerA a f (γ * g) h = W.kerA a f g h := fun γ hγ g h => by
    simpa using hinv γ hγ 1 (one_mem _) g h
  have hr : ∀ γ ∈ GQ (G.V a.tgt), ∀ g h, W.kerA a f g (γ * h) = W.kerA a f g h := fun γ hγ g h => by
    simpa using hinv 1 (one_mem _) γ hγ g h
  refine ⟨fun h => ?_, ?_, fun γ hγ h => ?_⟩
  · exact GlobalTheory.CocompactIntegrable.integrableOn_of_cocompact _ _ _ C hfd hC hcov _
      ((hK.comp (Continuous.prodMk_left h)).mul hF.1) (fun γ hγ g => by simp only [hl γ hγ, hF.2 γ hγ])
  · exact GlobalTheory.DefLiftCont.continuous_integral_of_cocompact (G := GA D (G.V a.tgt)) (GQ (G.V a.src)) (M.ν a.src)
      (M.fd a.src) C hfd hC hcov (fun h g => W.kerA a f g h * F g)
      ((hK.comp continuous_swap).mul (hF.1.comp continuous_snd)) (fun γ hγ h g => by simp only [hl γ hγ, hF.2 γ hγ])
  · simp only [liftA_apply, hr γ hγ]

theorem path {X : Node} {F : Fn G X} (hF : IsInvCont X F) : ∀ {Y : Node} (p : Path T X Y) (d : PureT G p),
    Path.Fam.All (fun a f => Good W M a f) d → PathConv W M p d F ∧ IsInvCont Y (liftP W M p d F) := by
  intro Y p
  induction p with
  | nil =>
    intro d h
    exact ⟨trivial, hF⟩
  | snoc a p ih =>
    intro d h
    obtain ⟨h1, h2⟩ := ih d.1 h.1
    obtain ⟨h3, h4⟩ := step W M h.2 h2
    exact ⟨⟨h1, h3⟩, h4⟩

theorem all_colFam {S : Arrow T → Type} {P : ∀ a, S a → Prop} (t : T) :
    ∀ n (f : ∀ j : Fin n, S (.col t j)), (∀ j, P _ (f j)) → Path.Fam.All P (colFam t n f)
  | 0, _, _ => trivial
  | n + 1, f, h => ⟨all_colFam t n _ fun j => h j.castSucc, h (Fin.last n)⟩

theorem all_rowFam {S : Arrow T → Type} {P : ∀ a, S a → Prop} (j : ℕ) :
    ∀ n (f : ∀ i : Fin n, S (.right i j)), (∀ i, P _ (f i)) → Path.Fam.All P (rowFam j n f)
  | 0, _, _ => trivial
  | n + 1, f, h => ⟨all_rowFam j n _ fun i => h i.castSucc, h (Fin.last n)⟩

end GlobalTheory.DefConv

namespace GlobalTheory.DefConv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem posDef_of_node (G : GridData L sc) {μ0 : T} (hL : L.Is μ0) {X : Node} (h : X.InRange D.R.m)
    (h0 : X.neg D.R.m = 0) (τ : D.what₂.Tau) : (gramAt D (G.V X) τ).PosDef := by
  have hV := node_isV G hL h
  rw [h0] at hV
  refine GlobalTheory.RepsObj.gramAt_posDef (fun σ => ?_) hV.sigOK τ
  rw [hV.sig σ, hV.rank, Nat.sub_zero]

variable (W : G.Weil) {U : Set T} (S : GridChoice W U)

theorem theta_fock {t : T} {p : Pair T} (hp : DefPair D.R.m p) (hr : p.InRange D.R.m) (d : FinDatum G t p)
    (hv : S.Z.HasVec d) (Q : PolF D (G.pT p).rank (G.pS p).rank) :
    IsThetaFunO W.ψ (G.pS p) (G.pT p) (W.fock p (movedVec t S d) Q) := by
  have h1 := (GlobalTheory.FockRealVec.vec_theta_fock W S.Z hp d hv).1
  have h2 : IsThetaFunO W.ψ _ _ (movedVec t S d) := (W.om_is p hr).om_pres _ _ h1
  exact GlobalTheory.FockTheta.ptStable D W.ψ W.θ W.ψ_std W.θ_is _ _ _ _ _ _ _ Q h2

end GlobalTheory.DefConv

namespace GlobalTheory.DefConv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G)

theorem good_col {t : T} {j : ℕ} (hj : j < D.R.m) (f : Sch G (.col t j))
    (hf : IsThetaFunO W.ψ (G.pS (.top t j)) (G.pT (.top t j)) f) (hpos : ∀ τ, (gramAt D (G.V (.top j)) τ).PosDef)
    {K : Subgroup (GL (Fin (G.V (.top j)).rank) (Lev.EAf D))} (hM : M.IsAt (.top j) K) : Good W M (.col t j) f := by
  have hr : (Pair.top t j : Pair T).InRange D.R.m := by show j + 1 ≤ D.R.m; omega
  obtain ⟨hc, -⟩ := GlobalTheory.thetaKO_continuous_and_rat_invariant W.ψ _ _ _ _ _ (W.om_is _ hr) f hf
  exact ⟨hc, fun γ hγ γ' hγ' g h => _root_.GlobalTheory.RowReal.ker_rat_left W _ hr f hf γ hγ γ' hγ' g h, hpos, hM.haar_fund.1, hM.haar_fund.2⟩

theorem good_row {i : ℕ} (hi : i < D.R.m) (f : Sch G (.right i D.R.m))
    (hf : IsThetaFunO W.ψ (G.pS (.chi i D.R.m)) (G.pT (.chi i D.R.m)) f)
    (hpos : ∀ τ, (gramAt D (G.V (.grid i D.R.m)) τ).PosDef)
    {K : Subgroup (GL (Fin (G.V (.grid i D.R.m)).rank) (Lev.EAf D))} (hM : M.IsAt (.grid i D.R.m) K) :
    Good W M (.right i D.R.m) f := by
  have hr : (Pair.chi i D.R.m : Pair T).InRange D.R.m := by show i + 1 ≤ D.R.m ∧ D.R.m ≤ D.R.m; omega
  obtain ⟨hc, -⟩ := GlobalTheory.thetaKO_continuous_and_rat_invariant W.ψ _ _ _ _ _ (W.om_is _ hr) f hf
  refine ⟨?_, fun γ hγ γ' hγ' g h => _root_.GlobalTheory.RowReal.ker_rat_left W _ hr f hf γ hγ γ' hγ' g h, hpos, hM.haar_fund.1, hM.haar_fund.2⟩
  exact hc.comp (((continuous_negGA _).comp continuous_snd).prodMk continuous_fst)

end GlobalTheory.DefConv

namespace GlobalTheory.DefConv

end GlobalTheory.DefConv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdCardAdicCompletionIntegersQuotDvdPowFinrank
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory

theorem prod_card_quot_natCast_dvd_pow_finrank : ∀ (F : Type) [Field F] [NumberField F] (s : Finset (HeightOneSpectrum (𝓞 F))) (k : ℕ), 0 < k → ∏ v ∈ s, Nat.card (v.adicCompletionIntegers F ⧸ Ideal.span {(k : v.adicCompletionIntegers F)}) ∣ k ^ Module.finrank ℚ F := by
  intro F _ _ s k hk
  classical
  set I : Ideal (𝓞 F) := Ideal.span {(k : 𝓞 F)} with hIdef
  have hI : I ≠ 0 := by
    rw [hIdef, Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hk.ne'
  have hmap : ∀ v : HeightOneSpectrum (𝓞 F),
      I.map (algebraMap (𝓞 F) (v.adicCompletionIntegers F)) =
        Ideal.span {(k : v.adicCompletionIntegers F)} := by
    intro v
    rw [hIdef, Ideal.map_span, Set.image_singleton, map_natCast]
  obtain ⟨hfin, hprod⟩ := GlobalTheory.LocalDifferentProduct.finprod_card_quot_map hI
  simp only [hmap] at hfin hprod
  have hnorm : Ideal.absNorm I = k ^ Module.finrank ℚ F := by
    rw [hIdef, Ideal.absNorm_span_singleton]
    have e : (k : 𝓞 F) = algebraMap ℤ (𝓞 F) (k : ℤ) := by simp
    rw [e, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Int.natAbs_pow]
    simp
  rw [← hnorm, ← hprod, finprod_eq_prod_of_mulSupport_subset (s := s ∪ hfin.toFinset) _
    (by intro x hx; simp [hx])]
  exact Finset.prod_dvd_prod_of_subset _ _ _ Finset.subset_union_left

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealMetaplecticFamilyDerivativeQuadratic
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical Matrix

namespace GlobalTheory.QuadFam

open GlobalTheory.RealWeil

theorem coordAll (hP : GlobalTheory.Published.RealMetaplecticRepresentation) (l : Type) [Fintype l] [DecidableEq l]
    (A : ℝ → (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ)) (T : ℝ → Sch l →ₗ[ℂ] Sch l)
    (hA : ∀ w, Continuous fun t => A t w) (hT : ∀ s t f, T (s + t) f = T s (T t f)) (hT0 : ∀ f, T 0 f = f)
    (hI : ∀ t w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(T t f₁) = rhoFun (A t w) ⇑(T t f))
    (hiso : ∀ t f, ∫ x, ‖T t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) (hpt : ∀ f y, Continuous fun t => T t f y) :
    ∃ (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (c : ℂ), ∀ f y, HasDerivAt (fun t => T t f y) (quad X f y + c * f y) 0 := by
  obtain ⟨hs, hgrp, h0⟩ := _root_.GlobalTheory.RealWeil.intertwining_symplectic_and_group_law l A T hT hT0 hI hiso
  cases isEmpty_or_nonempty l with
  | inl hl =>
    have hq : ∀ f y, quad (0 : Matrix (l ⊕ l) (l ⊕ l) ℝ) f y = 0 := fun f y => by simp [quad]
    obtain ⟨c, hc⟩ := _root_.GlobalTheory.famChar_hasDerivAt l (fun t w => A t w) T (fun _ => LinearMap.id) (fun f y => quad 0 f y) hT hT0
      (fun _ _ _ => rfl) (fun _ => rfl) hgrp h0 hI
      (fun t w f f₁ h => by
        rw [LinearMap.id_apply, LinearMap.id_apply, h, Subsingleton.elim (A t w) w]) hiso
      (fun _ _ => rfl) hpt (fun f y => by rw [hq]; exact hasDerivAt_const _ _)
    exact ⟨0, c, hc⟩
  | inr hl =>
    let M : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ := fun t => LinearMap.toMatrix' (A t)
    have hM : ∀ t w, M t *ᵥ w = A t w := fun t w => LinearMap.toMatrix'_mulVec (A t) w
    have hMc : Continuous M := by
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [M, LinearMap.toMatrix'_apply]
      exact (continuous_apply i).comp (hA _)
    have hM0 : M 0 = 1 := by
      have : A 0 = LinearMap.id := LinearMap.ext h0
      simp only [M, this, LinearMap.toMatrix'_id]
    have hMm : ∀ s t, M (s + t) = M s * M t := by
      intro s t
      have : A (s + t) = (A s).comp (A t) := LinearMap.ext (hgrp s t)
      simp only [M, this, LinearMap.toMatrix'_comp]
    obtain ⟨X, hX⟩ := _root_.GlobalTheory.matrix_oneParamGroup_eq_exp _ M hMc hM0 hMm
    have hsp : X ∈ LieAlgebra.Symplectic.sp l ℝ := by
      refine GlobalTheory.T.mem_symplecticLieAlgebra_of_exp_smul_mem_symplecticGroup l X fun t => ?_
      obtain ⟨N, hN⟩ := GlobalTheory.exists_symplecticGroup_of_sympl l (A t) (hs t)
      have e : Matrix.toLin' (N : Matrix (l ⊕ l) (l ⊕ l) ℝ) = A t := LinearMap.ext fun w => by
        rw [Matrix.toLin'_apply, hN]
      have e2 : (N : Matrix (l ⊕ l) (l ⊕ l) ℝ) = M t := by
        simp only [M, ← e, LinearMap.toMatrix'_toLin']
      rw [← hX t, ← e2]
      exact N.2
    obtain ⟨U, hU, hU0, hUI, hUiso, hUd⟩ := _root_.GlobalTheory.RealWeil.metaplectic_oneParam_schwartz hP l X hsp
    have hB : ∀ t w, NormedSpace.exp (t • X) *ᵥ w = A t w := fun t w => by rw [← hX, hM]
    obtain ⟨c, hc⟩ := _root_.GlobalTheory.famChar_hasDerivAt l (fun t w => A t w) T U (fun f y => quad X f y) hT hT0 hU hU0 hgrp h0 hI
      (fun t w f f₁ h => by rw [hUI t w f f₁ h, hB]) hiso hUiso hpt hUd
    exact ⟨X, c, hc⟩

theorem deriv_quad : GlobalTheory.Published.RealMetaplecticRepresentation → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V), μ.IsAddHaarMeasure → ∀ (P : V → V → ℝ), IsPairing P →
    ∀ (A : ℝ → (V × V) →ₗ[ℝ] (V × V)) (T : ℝ → 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ)),
    (∀ v, Continuous fun t => A t v) →
    (∀ s t f, T (s + t) f = T s (T t f)) → (∀ f, T 0 f = f) →
    (∀ t v (f f₁ : 𝓢(V, ℂ)), ⇑f₁ = schrF P v ⇑f → ⇑(T t f₁) = schrF P (A t v) ⇑(T t f)) →
    (∀ t f, ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    (∀ f y, Continuous fun t => T t f y) →
    (∀ f φ : 𝓢(V, ℂ), Continuous fun t => ∫ x, T t f x * starRingEnd ℂ (φ x) ∂μ) →
    ∃ (m : ℕ) (a b : Fin m → V × V) (c : Fin m → ℂ) (c₀ : ℂ), ∀ (f : 𝓢(V, ℂ)) (g₁ g₂ : Fin m → 𝓢(V, ℂ)),
      (∀ i y, g₁ i y = fderiv ℝ (⇑f) y (b i).1 - 2 * Real.pi * Complex.I * (P y (b i).2 : ℂ) * f y) →
      (∀ i y, g₂ i y = fderiv ℝ (⇑(g₁ i)) y (a i).1 - 2 * Real.pi * Complex.I * (P y (a i).2 : ℂ) * g₁ i y) →
      ∀ y, HasDerivAt (fun t => T t f y) (∑ i, c i * g₂ i y + c₀ * f y) 0 := by
  intro hP V _ _ _ _ _ μ hμ P hp A T hA hT hT0 hI hiso hpt _
  exact _root_.GlobalTheory.ArchUniq.SchrTransport.transport V μ hμ P hp _ rfl (fun A' T' => coordAll hP (Fin _) A' T') A T hA hT hT0 hI hiso hpt

end GlobalTheory.QuadFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceHeisenbergDerivThetaTransformAlgebraicD
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree.HeisDeriv

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM

section Gen

variable {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F}
  {κ : Type} [Fintype κ]

theorem rho_rho (d : Darboux B κ) (ψ : AddChar (AF F) ℂ) (w v : W) (Φ : (κ → AF F) → ℂ) :
    d.rho ψ w (d.rho ψ v Φ) = ψ (⅟(2 : AF F) * B w v) • d.rho ψ (w + v) Φ := by
  funext x
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul, map_add (f := _), Prod.fst_add, Prod.snd_add, ← mul_assoc,
    ← AddChar.map_add_eq_mul, add_assoc]
  congr 2
  rw [d.form]
  simp only [add_dotProduct, dotProduct_add]
  have h2 : ⅟(2 : AF F) + ⅟(2 : AF F) = 1 := invOf_two_add_invOf_two
  linear_combination (-((d.e w).1 ⬝ᵥ (d.e v).2)) * h2

theorem thetaSum_smul (c : ℂ) (Φ : (κ → AF F) → ℂ) : thetaSum F (c • Φ) = c * thetaSum F Φ := by
  simp only [thetaSum, Pi.smul_apply, smul_eq_mul]
  exact tsum_mul_left

end Gen

section Model

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : Spc F E n} {Wd : Spc F E d}

theorem algD_le_schA (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w)
    (hM : M.IsGood ψ) : algD M ψ emb ≤ schA F (Fin n × Fin d) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, φ, -, hSB, hev, rfl⟩
  exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hev.and hM.std).mono fun v hv => hv.1.trans hv.2)

theorem exists_actsD_mem_Pol (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w)
    (hψ : IsStd ψ) (u : Matrix (Fin n) (Fin d) (AE F E)) (hu : At (evI F) u) (g : SInf F (Fin n × Fin d))
    (hg : g ∈ M.Pol ψ emb) : ∃ g₁ ∈ M.Pol ψ emb, ActsD (evI F) (M.heisLine ψ u) g g₁ := by
  obtain ⟨Dr, hDr⟩ := _root_.GlobalTheory.HeisDer.derEx F E σ (Fin n) (Fin d) (Fin n × Fin d) ψ (incM F Y.J) (incM F Wd.J) M.co hψ
  have hSD := (hDr u hu g).1
  have hA : ActsD (evI F) (M.heisLine ψ u) g (Dr u g) :=
    (GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) g (Dr u g) (Dr u g)).1 (M.heisLine ψ u)
      (fun t => by funext x; simp [Model.heisLine, Darboux.rho, schr]) hSD
  refine ⟨Dr u g, Submodule.mem_sInf.2 fun N hN => hN.2 u hu g (Submodule.mem_sInf.1 hg N hN) _ hA, hA⟩

theorem exists_deriv_algD (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w)
    (hψ : IsStd ψ) (hM : M.IsGood ψ) (u : Matrix (Fin n) (Fin d) (AE F E)) (hu : At (evI F) u) :
    ∀ Φ ∈ algD M ψ emb, ∃ Φ' ∈ algD M ψ emb,
      ∀ x, HasDerivAt (fun t : ℝ => M.co.rho ψ (realAd F t • u) Φ x) (Φ' x) 0 := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | zero =>
    refine ⟨0, zero_mem _, fun x => ?_⟩
    simpa [Darboux.rho, schr] using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add a b _ _ ha hb =>
    obtain ⟨a', ha', hda⟩ := ha
    obtain ⟨b', hb', hdb⟩ := hb
    refine ⟨a' + b', add_mem ha' hb', fun x => ?_⟩
    have e : (fun t : ℝ => M.co.rho ψ (realAd F t • u) (a + b) x) =
        fun t => M.co.rho ψ (realAd F t • u) a x + M.co.rho ψ (realAd F t • u) b x := by
      funext t; simp [Darboux.rho, schr, mul_add]
    rw [e]
    exact (hda x).add (hdb x)
  | smul c a _ ha =>
    obtain ⟨a', ha', hda⟩ := ha
    refine ⟨c • a', Submodule.smul_mem _ c ha', fun x => ?_⟩
    have e : (fun t : ℝ => M.co.rho ψ (realAd F t • u) (c • a) x) =
        fun t => c * M.co.rho ψ (realAd F t • u) a x := by
      funext t; simp [Darboux.rho, schr]; ring
    rw [e]
    simpa using (hda x).const_mul c
  | mem Φ hΦ =>
    obtain ⟨g, φ, hg, hSB, hev, rfl⟩ := hΦ
    obtain ⟨g₁, hg₁, hA⟩ := exists_actsD_mem_Pol M ψ emb hψ u hu g hg
    have hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
      (hev.and hM.std).mono fun v hv => hv.1.trans hv.2
    refine ⟨pure g₁ φ, Submodule.subset_span ⟨g₁, φ, hg₁, hSB, hev, rfl⟩, fun x => ?_⟩
    exact hA _ (GlobalTheory.ThK.EvUniqInf.rest_pure g φ hSB hstd) x

end Model

end GlobalTheory.SquareAgree.HeisDeriv

namespace GlobalTheory.SquareAgree.HeisDeriv

theorem heisDeriv_algD : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ ΦD ∈ algD M Bs.ψ Bs.emb, ∀ f : WO S X → ℂ, IsDatum M ψ cS ΦD f → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin X.rank) (Fin S.rank) ℂ),
        ∃ ΦD' ∈ algD M Bs.ψ Bs.emb, IsDatum M ψ cS ΦD' (dRho (heisO ψ (sgn ε S) X) θ τ z f) := by
  intro D ψ θ hθ ε S X A B d e Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW hemb M hM cS hcS ΦD hΦD f hf τ z
  subst hψ
  obtain ⟨hline, hAt⟩ := _root_.GlobalTheory.LineRealAd.lineAt_realAd_smul D θ hθ τ z
  have hsm : ∀ (a : AF D.host.F) (u : Matrix (Fin S.rank) (Fin d) (AE D)), cS (a • u) = a • cS u := by
    intro a u
    rw [hcS, hcS]
    ext i j
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.smul_apply, Finset.smul_sum,
      smul_mul_assoc, id]
  set w₀ := lineAt θ τ z 1 with hw₀
  set u := cS.symm w₀ with hu_def
  have hcu : cS u = w₀ := cS.apply_symm_apply w₀
  have hu : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u := by
    intro a ha
    apply cS.injective
    rw [hsm, hcu, map_zero]
    exact hAt a ha
  have hLt : ∀ t : ℝ, cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u) = lineAt θ τ z t := by
    intro t
    rw [hsm, hcu, hline t]
  have hstd := hBs.std
  obtain ⟨Φ', hΦ', hder⟩ := exists_deriv_algD M Bs.ψ Bs.emb hstd hM u hu ΦD hΦD
  refine ⟨Φ', hΦ', algD_le_schA M Bs.ψ Bs.emb hM hΦ', fun u' => ?_⟩
  have h2 : ⅟(2 : AF D.host.F) = algebraMap D.host.F (AF D.host.F) (1 / 2) := by
    refine invOf_eq_right_inv ?_
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
    simp
  have key : ∀ t : ℝ, GlobalTheory.WeilM.thetaSum D.host.F (M.co.rho Bs.ψ u' (M.co.rho Bs.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u) ΦD)) =
      heisO Bs.ψ (sgn ε S) X (lineAt θ τ z t) f (cS u') := by
    intro t
    rw [rho_rho, thetaSum_smul, hf.2, map_add (f := _), ← hLt t, heisO, symplOH, ← _root_.GlobalTheory.SquareAgree.SympForm.symp_model_eq_symplO D ε S X e Vs Ws hJ hJW cS hcS, h2]
  have hd := _root_.GlobalTheory.HeisLineTheta.hasDerivAt_thetaSum_line M.co Bs.ψ hstd u hu ΦD (algD_le_schA M Bs.ψ Bs.emb hM hΦD) Φ' (algD_le_schA M Bs.ψ Bs.emb hM hΦ')
    hder u'
  simp only [key] at hd
  exact hd.deriv.symm

end GlobalTheory.SquareAgree.HeisDeriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPointsTopNodeOntoUnitaryHaarUnique
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowTest

theorem realPts_ontoUni_haar_unique : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {μ0 : T}, L.Is μ0 → ∀ (j : ℕ), j ≤ D.R.m →
    GlobalTheory.KJInf.OntoUni (fun (k : GinfC (G.V (.top j))) τ =>
      ((realIn W.θ S.N.fr (.top j) (k : GA D (G.V (.top j))) τ : GL (Fin (G.V (.top j)).rank) ℂ) :
        Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ)) ∧
    ∀ κ κ' : Measure (GinfC (G.V (.top j))), κ.IsHaarMeasure → IsProbabilityMeasure κ → κ'.IsHaarMeasure →
      IsProbabilityMeasure κ' → κ = κ' := by
  intro D T L sc G W U S μ0 _ j hj
  have hX : DefNode D.R.m (Node.top j) := hj
  have hO := GlobalTheory.SeeSaw.ontoUni_inB D W.θ (G.V (.top j)) (S.N.frC _) W.θ_is (GlobalTheory.RealType.frC_on S.N hX)
  refine ⟨?_, ?_⟩
  · have e : (fun (k : GinfC (G.V (.top j))) τ =>
        ((realIn W.θ S.N.fr (.top j) (k : GA D (G.V (.top j))) τ : GL (Fin (G.V (.top j)).rank) ℂ) :
          Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ)) =
        fun k : GinfC (G.V (.top j)) => GlobalTheory.SeeSaw.inB W.θ (G.V (.top j)) (S.N.frC (.top j)) k.1 :=
      funext fun k => funext fun τ => GlobalTheory.RowHoweAvg.realIn_coe W.θ S.N _ _ τ
    rw [e]
    exact hO
  · intro κ κ' h1 h2 h3 h4
    haveI : LocallyCompactSpace (GinfC (G.V (.top j))) :=
      (GlobalTheory.AdelicSplit.isClosed_GinfC' _).locallyCompactSpace
    exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure κ κ'

end GlobalTheory.RowTest
end

