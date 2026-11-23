module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0641
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0639
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0522
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1769
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedFiniteMapsRestriction
public import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.HoweDualityUnramifiedAllPlaces
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0013

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomClassSumIntegralNeg
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
open scoped ComplexOrder
open GlobalTheory.ClassRegroup GlobalTheory.DefiniteClassAvg GlobalTheory.DefiniteClassReal
open GlobalTheory.Grid (neg sgn ofSgn)
namespace GlobalTheory.RowTest.BottomClassSumNeg
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}
end GlobalTheory.RowTest.BottomClassSumNeg
namespace GlobalTheory.RowTest.BottomClassSumNeg
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}
theorem integral_eq_bottom_classSum : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ (v : ℝ) (N : ℕ) (z : Fin N → GA D A) (w : Fin N → ℕ) (κ : Measure (GinfC A)), 0 < v ∧ (∀ l, z l ∈ GfC A) ∧
      (∀ l, 0 < w l) ∧ κ.IsMulLeftInvariant ∧ IsProbabilityMeasure κ ∧
      ∀ (t : T) (P : PolF D WW.rank A.rank), ∀ h ∈ GfC WW,
        X.I W.ψ W.θ t P h = (v : ℂ) * ∑ l, ((w l : ℂ))⁻¹ * ∫ g, X.ker W.ψ W.θ t P h (z l * (g : GA D A)) ∂κ := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ hL hX
  have hV : ∀ φ : D.host.E →+* ℂ, (A.gram.map φ).PosDef := fun φ => by
    rw [hX.std.1, Matrix.map_one φ (map_zero φ) (map_one φ)]
    exact Matrix.PosDef.one
  let V' : HSp D := { A with sig := fun _ => (A.rank, 0) }
  have hS' : V'.SigOK := fun τ => GlobalTheory.Proof.GenusMassSignature.hasSignature_of_posDef (hV τ)
  have hD' : V'.IsDefinite := fun τ => Or.inl rfl
  have hGc : IsCompact (GinfC A : Set (GA D A)) := Formalism.IndefR.Eqv.isCompact_GinfC (V := V') hS' hD'
  haveI : CompactSpace (GinfC A) := isCompact_iff_compactSpace.1 hGc
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  have hLC := hT.1
  have hSC := hT.2.1
  have hB := hT.2.2.2.1
  have hG := hT.2.2.2.2.1
  have hC := hT.2.2.2.2.2.2
  obtain ⟨K'', hK'', hr⟩ := level_all μ₀ hX
  have hfin0 : Finite (FinCl A K'') := (finite_finCl_and_gamOrd A K'' hV hK'').1
  let μ := X.m
  haveI : μ.IsHaarMeasure := hX.is.meas.1
  have hfd : IsFundamentalDomain (GQ A) X.fd μ := hX.is.meas.2
  let J : Subgroup (GA D A) := K''.comap (Lev.finE A)
  have hJo : IsOpen (J : Set (GA D A)) := hK''.1
  have hJc : IsCompact (J : Set (GA D A)) := by
    refine (hK''.2.mul hGc).of_isClosed_subset (Subgroup.isClosed_of_isOpen J hK''.1) ?_
    intro k hk
    exact ⟨finPart A k, finPart_mem_levA A hk, realPart A k, realPart_mem A k, finPart_mul_realPart A k⟩
  have hJtop : μ J ≠ ⊤ := hJc.measure_lt_top.ne
  have hJ0 : μ J ≠ 0 := (hJo.measure_pos μ ⟨1, J.one_mem⟩).ne'
  have hinfJ : GinfC A ≤ J := by
    show GinfC A ≤ K''.comap (Lev.finE A)
    rw [GlobalTheory.Mass.Levels.comap_finE]
    exact le_sup_right
  let κ : Measure (GinfC A) := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (GinfC A))
  haveI hκH : κ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  have hκ1 : κ Set.univ = 1 := by
    have := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (GinfC A)))
    simpa using this
  haveI : IsProbabilityMeasure κ := ⟨hκ1⟩
  let e := finEquiv A
  have he : ∀ γ, e (((finPt A).comp (GQ A).subtype) γ) = Bridge.ratF A γ := fun γ => e.apply_symm_apply _
  have hJe : ∀ a, e a ∈ GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin A K'' ↔ a ∈ K''.comap (finG A) := fun a => Iff.rfl
  have hy := isReps_transfer _ _ e he _ _ hJe _ (isReps_out A K'')
  let N := Nat.card (FinCl A K'')
  let eq : FinCl A K'' ≃ Fin N := Finite.equivFin _
  let y : FinCl A K'' → Bridge.Gf A := fun c => e (Quotient.out c)
  let zc : FinCl A K'' → GA D A := fun c => ((Quotient.out c : GfC A) : GA D A)
  have hz : ∀ c, (finHom A).rangeRestrict (zc c) = y c := fun c => rfl
  have hu0 : ∀ x : GA D A, ∃! c, ∃ γ ∈ GQ A, ∃ k ∈ J, x = γ * zc c * k :=
    existsUnique_doubleCoset (finHom A).rangeRestrict (GQ A) (GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin A K'') y hy zc hz
  let z : Fin N → GA D A := fun l => zc (eq.symm l)
  have hu : ∀ x : GA D A, ∃! l, ∃ γ ∈ GQ A, ∃ k ∈ J, x = γ * z l * k := fun x =>
    (eq.existsUnique_congr_left (p := fun c => ∃ γ ∈ GQ A, ∃ k ∈ J, x = γ * zc c * k)).1 (hu0 x)
  have hfinΓ : ∀ l, {γ : GQ A | (z l)⁻¹ * (γ : GA D A) * z l ∈ J}.Finite := fun l =>
    GlobalTheory.InnerClassSum.finite_stab_of_measure μ (GQ A) J hfd hJ0 hJtop (z l)
  have him : ∀ l, {γ : GA D A | γ ∈ GQ A ∧ (z l)⁻¹ * γ * z l ∈ J} =
      Subtype.val '' {γ : GQ A | (z l)⁻¹ * (γ : GA D A) * z l ∈ J} := by
    intro l
    ext γ
    simp only [Set.mem_setOf_eq, Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
    exact ⟨fun h => ⟨h.1, h.2⟩, fun ⟨h, h'⟩ => ⟨h, h'⟩⟩
  have hfin : ∀ l, {γ : GA D A | γ ∈ GQ A ∧ (z l)⁻¹ * γ * z l ∈ J}.Finite := fun l =>
    him l ▸ (hfinΓ l).image _
  have hdec : ∀ k ∈ J, ∃ k' ∈ Lev.levA A K'', ∃ w : GinfC A, k = k' * (GinfC A).subtype w := fun k hk =>
    ⟨finPart A k, finPart_mem_levA A hk, ⟨realPart A k, realPart_mem A k⟩, (finPart_mul_realPart A k).symm⟩
  have hcomm : ∀ k ∈ Lev.levA A K'', ∀ w : GinfC A, k * (GinfC A).subtype w = (GinfC A).subtype w * k :=
    fun k hk w => (Formalism.IndefR.Eqv.Act.comm_inf_fin w.2 (Subgroup.mem_inf.1 hk).1).symm
  have hrt : ∀ w : GinfC A, MeasurePreserving (· * (GinfC A).subtype w) μ μ := fun w =>
    measurePreserving_mul_right_of_mem μ J hJo hJ0 hJtop (hinfJ w.2)
  refine ⟨(μ J).toReal, N, z, fun l => {γ : GA D A | γ ∈ GQ A ∧ (z l)⁻¹ * γ * z l ∈ J}.ncard, κ,
    ENNReal.toReal_pos hJ0 hJtop, fun l => (Quotient.out (eq.symm l)).2, fun l => ?_, inferInstance, inferInstance,
    fun t P h _ => ?_⟩
  · exact (Set.ncard_pos (hfin l)).2 ⟨1, (GQ A).one_mem, by simp [J.one_mem]⟩
  · have hcont : Continuous (X.ker W.ψ W.θ t P h) :=
      continuous_of_level A K'' hK''.1 _ (fun k hk g => hr t P h k hk g) (ker_cont hX t P h)
    obtain ⟨-, heq⟩ := integral_eq_sum_avg (GA D A) μ (GQ A) J (Lev.levA A K'') X.fd hfd hJo hJtop (GinfC A) κ
      (GinfC A).subtype continuous_subtype_val hrt hdec hcomm (Fin N) z hu hfin (X.ker W.ψ W.θ t P h) hcont
      (ker_left hX t P h) (fun k hk g => hr t P h k hk g)
    exact heq
end GlobalTheory.RowTest.BottomClassSumNeg
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_class_sum_integral_neg : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ (v : ℝ) (N : ℕ) (z : Fin N → GA D A) (w : Fin N → ℕ) (κ : Measure (GinfC A)), 0 < v ∧ (∀ l, z l ∈ GfC A) ∧
      (∀ l, 0 < w l) ∧ κ.IsMulLeftInvariant ∧ IsProbabilityMeasure κ ∧
      ∀ (t : T) (P : PolF D WW.rank A.rank), ∀ h ∈ GfC WW,
        X.I W.ψ W.θ t P h = (v : ℂ) * ∑ l, ((w l : ℂ))⁻¹ * ∫ g, X.ker W.ψ W.θ t P h (z l * (g : GA D A)) ∂κ := by
  first | exact @_root_.GlobalTheory.RowTest.BottomClassSumNeg.integral_eq_bottom_classSum | exact _root_.GlobalTheory.RowTest.BottomClassSumNeg.integral_eq_bottom_classSum | (intros; apply _root_.GlobalTheory.RowTest.BottomClassSumNeg.integral_eq_bottom_classSum <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BoundaryRealGroupAction
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
open scoped Matrix
namespace GlobalTheory.BottomRealAct
theorem boundary_real_group_action : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ (m : D.what₂.Tau → ℤ) (ρ : GinfC A' →* (D.what₂.Tau → Matrix.unitaryGroup (Fin A'.rank) ℂ)),
      (∀ τ a b, Measurable fun g => (ρ g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ) a b) ∧ Function.Surjective ρ ∧
      ∀ (t : T), ∀ x ∈ GfC A', ∀ h ∈ GfC WW, ∀ (g : GinfC A') (P : MvPolynomial (FVar D WW.rank A'.rank) ℂ),
        X.ker' W.ψ W.θ t P h (x * (g : GA D A')) =
          (∏ τ, (ρ g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ).det ^ (m τ)) *
            X.ker' W.ψ W.θ t (GlobalTheory.MinorFrame.colSub (fun τ => (ρ g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)) P) h x := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX
  have hθ : IsInfFam W.θ := hX.is.isVac.2.inf
  have hV : HSpace.gram A' = 1 := hX.std'.1
  have hVW : HSpace.gram WW = 1 := hX.stdW.1
  have hW := fun t => GlobalTheory.RowTest.BottomClassSum.weil' hX t
  have hxi : ∀ t τ, HasInfExp D (L.xi t) τ 0 := fun t τ => by
    obtain ⟨n, hn, ho⟩ := hL.xi_fin t
    exact GlobalTheory.Chain.StepVac.hasInfExp_of_order hθ (hL.xi t) hn ho τ
  choose b hb using fun τ => GlobalTheory.SplitCharExp.exists_hasInfExp D W.θ _ WW.rank τ hθ (hW μ₀).hecT (hW μ₀).resT
  have hrel : ∀ t, (L.mu t (↑j + 1) * L.eta ^ (rankV D ↑i ↑j % 2)) /
      (G.ch.chi (D.R.m - ↑i) * L.eta ^ (rankV D ↑i ↑j % 2)) =
      (L.mu μ₀ (↑j + 1) * L.eta ^ (rankV D ↑i ↑j % 2)) / (G.ch.chi (D.R.m - ↑i) * L.eta ^ (rankV D ↑i ↑j % 2)) *
        (L.xi t * (L.xi μ₀)⁻¹) := by
    intro t
    simp only [LevCh.mu, Lift.tup]
    exact rightRegularAction_list_dLR_eq_append _ _ _ _ _
  have hbt : ∀ t τ, HasInfExp D ((L.mu t (↑j + 1) * L.eta ^ (rankV D ↑i ↑j % 2)) /
      (G.ch.chi (D.R.m - ↑i) * L.eta ^ (rankV D ↑i ↑j % 2))) τ (b τ) := by
    intro t τ
    rw [hrel t]
    have := GlobalTheory.Mem.HeckeExp.hasInfExp_mul (hb τ)
      (GlobalTheory.Mem.HeckeExp.hasInfExp_mul (hxi t τ) (GlobalTheory.Mem.HeckeExp.hasInfExp_inv (hxi μ₀ τ)))
    simpa using this
  choose k hk using fun τ => _root_.GlobalTheory.SplitParity.exists_int_add_half D _ WW.rank τ (b τ) (hW μ₀).hecT (hW μ₀).resT (hb τ)
  refine ⟨k, GlobalTheory.RealColAct.realCol W.θ hθ A' hV, ?_, _root_.GlobalTheory.RealColAct.realCol_surjective hθ A' hV, ?_⟩
  · intro τ a c
    simp only [GlobalTheory.RealColAct.realCol_apply, Matrix.transpose_apply]
    exact (((continuous_apply a).comp ((continuous_apply c).comp ((GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp
      ((GlobalTheory.RealWeil.continuous_mt A').2.comp continuous_subtype_val))))).measurable
  · intro t x _ h _ g P
    choose a ha using fun τ => GlobalTheory.SplitCharExp.exists_hasInfExp D W.θ _ A'.rank τ hθ (hW t).hecS (hW t).resS
    choose e₁ he₁ using fun τ => _root_.GlobalTheory.SplitParity.exists_int_add_half D _ A'.rank τ (a τ) (hW t).hecS (hW t).resS (ha τ)
    have hψ : Continuous W.ψ := hX.is.isVac.1.1.1
    have es : X.rA'.s = fun _ => 1 := funext fun τ => (hX.std'.2.2 τ).1
    have eB : X.rA'.B = fun _ => 1 := funext fun τ => (hX.std'.2.2 τ).2
    have esW : X.rW.s = fun _ => 1 := funext fun τ => (hX.stdW.2.2 τ).1
    have eBW : X.rW.B = fun _ => 1 := funext fun τ => (hX.stdW.2.2 τ).2
    have hf : IsThetaFunO W.ψ A' WW (X.f' t) := (GlobalTheory.ConstRatio.theta_f hX.is t).2
    have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hX.is.idem t)
    have hv : ∀ τ, IsFockVacAt (heisO W.ψ A' WW) W.θ τ (cplxO 1 1) (X.f' t) := fun τ => by
      have h0 := hX.is.isVac'.2.fock τ
      rw [es, esW] at h0
      exact GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ hθ ho.conj.infPart_eq ho.conj.conj.infPart_eq (hX.is.snd t)
        hX.is.isVac'.2.theta hf h0
    have hBS : ∀ τ, ((fun _ => (1 : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)) τ)ᴴ * gramAt D A' τ * 1 = 1 := fun τ => by
      rw [GlobalTheory.RealColAct.gramAt_of_gram_one hV]; simp
    have hBT : ∀ τ, ((fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) τ)ᴴ * gramAt D WW τ * 1 = 1 := fun τ => by
      rw [GlobalTheory.RealColAct.gramAt_of_gram_one hVW]; simp
    have key0 := GlobalTheory.RealFockPos.om_pureTensorO_pos D W.ψ W.θ A' WW _ _ (X.ω' t) (hW t) hθ (fun _ => 1) (fun _ => 1) hBS hBT
      a b ha (hbt t) e₁ (fun τ => -k τ) he₁ (fun τ => by push_cast; rw [hk τ]) (X.f' t) hf hv (g : GA D A') g.2 1 (one_mem _) P
    simp only [inv_one, Matrix.one_mul, Matrix.mul_one, GlobalTheory.StdUnn.CartanMove.compAt_mt_one, Matrix.det_one, one_zpow, mul_one]
      at key0
    have hinv : ∀ τ, (compAt W.θ τ (Formalism.L2.Theta.mt A' (g : GA D A')))⁻¹ =
        compAt W.θ τ (Formalism.L2.Theta.mt A' (g : GA D A')⁻¹) := fun τ =>
      Matrix.inv_eq_right_inv (GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := W.θ) τ (g : GA D A'))
    have hsc : ∀ τ, (compAt W.θ τ (Formalism.L2.Theta.mt A' (g : GA D A'))).det ^ (-k τ) =
        ((GlobalTheory.RealColAct.realCol W.θ hθ A' hV g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)).det ^ (k τ) := fun τ => by
      rw [GlobalTheory.RealColAct.realCol_apply, Matrix.det_transpose, ← hinv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv',
        inv_zpow', zpow_neg]
    have hsub : GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ))
        (fun τ => ((compAt W.θ τ (Formalism.L2.Theta.mt A' (g : GA D A')))⁻¹)ᵀ) =
        GlobalTheory.MinorFrame.colSub (fun τ => (GlobalTheory.RealColAct.realCol W.θ hθ A' hV g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)) := by
      rw [substF_one_eq_colSub]
      congr 1
      funext τ
      rw [GlobalTheory.RealColAct.realCol_apply, hinv]
    have key : (X.ω' t) ((g : GA D A'), 1) ((pureTensorO W.ψ W.θ A' WW (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) (X.f' t)) P) =
        (∏ τ, ((GlobalTheory.RealColAct.realCol W.θ hθ A' hV g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)).det ^ (k τ)) •
          (pureTensorO W.ψ W.θ A' WW (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) (X.f' t))
            (GlobalTheory.MinorFrame.colSub (fun τ => (GlobalTheory.RealColAct.realCol W.θ hθ A' hV g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)) P) := by
      rw [key0, ← hsub]
      congr 1
      exact Finset.prod_congr rfl fun τ _ => hsc τ
    unfold Tri.ker' thetaKO
    rw [es, eB, esW, eBW]
    have e : ((x * (g : GA D A'), h) : GA D A' × GA D WW) = (x, h) * ((g : GA D A'), 1) := by simp
    rw [e, map_mul, Module.End.mul_apply, key, map_smul, Pi.smul_apply, smul_eq_mul]
end GlobalTheory.BottomRealAct
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_boundary_real_action : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ (m : D.what₂.Tau → ℤ) (ρ : GinfC A' →* (D.what₂.Tau → Matrix.unitaryGroup (Fin A'.rank) ℂ)),
      (∀ τ a b, Measurable fun g => (ρ g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ) a b) ∧ Function.Surjective ρ ∧
      ∀ (t : T), ∀ x ∈ GfC A', ∀ h ∈ GfC WW, ∀ (g : GinfC A') (P : MvPolynomial (FVar D WW.rank A'.rank) ℂ),
        X.ker' W.ψ W.θ t P h (x * (g : GA D A')) =
          (∏ τ, (ρ g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ).det ^ (m τ)) *
            X.ker' W.ψ W.θ t (GlobalTheory.MinorFrame.colSub (fun τ => (ρ g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)) P) h x := by
  first | exact @_root_.GlobalTheory.BottomRealAct.boundary_real_group_action | exact _root_.GlobalTheory.BottomRealAct.boundary_real_group_action | (intros; apply _root_.GlobalTheory.BottomRealAct.boundary_real_group_action <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HoweReBase
section
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
noncomputable section
namespace UpperTheory.Lit.HoweDuality
open GlobalTheory GlobalTheory.FinUniq
theorem exists_local_iso_scalar_of_reG : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
    ∀ (V : Spc F E a) (V' : Spc F E a') (W : Spc F E (a + a')) (Rf₃ : FinMaps F a a'), IsFinMaps B (reG G V V' W) X om om' Rf₃ →
    ∀ v : Pl F, ∃ (ψ : Rf.Pi v ≃ₗ[ℂ] Rf₃.Pi v) (l : ℂ), l ≠ 0 ∧ (∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), Rf₃.p v φ = ψ (Rf.p v φ)) ∧
      (∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Rf₃.p' v φ = l • ψ (Rf.p' v φ)) ∧ (v ∉ X.T → l = 1) := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM V V' W Rf₃ h₃ v
  have hT := hM.triple
  have hf := hM.fin
  have hP := GlobalTheory.ThK.Inhab.pairV hT
  have hP' := GlobalTheory.ThK.Inhab.pairV' hT
  have hAE := _root_.GlobalTheory.ThK.LocalOps.theta_kernel_local_operators_act hK
  have h1V : (1 : UA σ G.V.J) ∈ UAt σ G.V (evFin F v) := fun u _ => by
    show u • ((1 : UA σ G.V.J).1.1 - 1) = 0
    rw [show (1 : UA σ G.V.J).1.1 = 1 from rfl, sub_self, smul_zero]
  have h1V' : (1 : UA σ G.V'.J) ∈ UAt σ G.V' (evFin F v) := fun u _ => by
    show u • ((1 : UA σ G.V'.J).1.1 - 1) = 0
    rw [show (1 : UA σ G.V'.J).1.1 = 1 from rfl, sub_self, smul_zero]
  have exV : ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ := fun h hh φ hφ => by
    obtain ⟨φ₁, ⟨h1, h2⟩, -⟩ := (hAE F E σ B _ _ _ _ _ _ _ om _ _ _ _ hP v).1 1 h1V h hh φ hφ
    exact ⟨φ₁, h1, h2⟩
  have exV' : ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, h)) φ φ₁ := fun h hh φ hφ => by
    obtain ⟨φ₁, ⟨h1, h2⟩, -⟩ := (hAE F E σ B _ _ _ _ _ _ _ om' _ _ _ _ hP' v).1 1 h1V' h hh φ hφ
    exact ⟨φ₁, h1, h2⟩
  have props : ∀ Q : FinMaps F a a',
      (SB (Fin a' × Fin (a + a') → Fv F v)).map (Q.p' v) = ⊤ →
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁' ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om (1, h)) φ φ₁ → Acts (evFin F v) (om' (1, h)) φ' φ₁' → Q.p v φ = Q.p' v φ' →
          Q.p v φ₁ = Q.p' v φ₁') →
      (∀ N : Submodule ℂ (Q.Pi v), (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om (1, h)) φ φ₁ → Q.p v φ ∈ N → Q.p v φ₁ ∈ N) → N = ⊥ ∨ N = ⊤) →
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om (1, h)) φ φ₁ → Q.p v φ = 0 → Q.p v φ₁ = 0) ∧
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om' (1, h)) φ φ₁ → Q.p' v φ = 0 → Q.p' v φ₁ = 0) ∧
      (∀ N : Submodule ℂ (Q.Pi v), (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om' (1, h)) φ φ₁ → Q.p' v φ ∈ N → Q.p' v φ₁ ∈ N) → N = ⊥ ∨ N = ⊤) := by
    intro Q onto' eqv irr
    refine ⟨fun h hh φ hφ φ₁ hφ₁ hact e => ?_, fun h hh φ hφ φ₁ hφ₁ hact e => ?_, fun N hN => irr N ?_⟩
    · rw [eqv h hh φ hφ 0 (zero_mem _) φ₁ hφ₁ 0 (zero_mem _) hact (acts_zero_zero v _) (by rw [e, map_zero]), map_zero]
    · rw [← eqv h hh 0 (zero_mem _) φ hφ 0 (zero_mem _) φ₁ hφ₁ (acts_zero_zero v _) hact (by rw [e, map_zero]), map_zero]
    · intro h hh φ hφ φ₁ hφ₁ hact hmem
      obtain ⟨φ', hφ', e⟩ : ∃ φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v), Q.p' v φ' = Q.p v φ := by
        have : Q.p v φ ∈ (SB (Fin a' × Fin (a + a') → Fv F v)).map (Q.p' v) := by rw [onto']; trivial
        exact this
      obtain ⟨φ₁', hφ₁', hact'⟩ := exV' h hh φ' hφ'
      rw [eqv h hh φ hφ φ' hφ' φ₁ hφ₁ φ₁' hφ₁' hact hact' e.symm]
      exact hN h hh φ' hφ' φ₁' hφ₁' hact' (e ▸ hmem)
  obtain ⟨sV, sV', iV'⟩ := props Rf (hf.onto' v) (hf.equiv v) (hf.irred v)
  obtain ⟨tV, tV', jV'⟩ := props Rf₃ (h₃.onto' v) (h₃.equiv v) (h₃.irred v)
  haveI := hf.nontriv v
  haveI := h₃.nontriv v
  have mV := ker_maximal om v (Rf.p v) (hf.onto v) (hf.inv v) sV (hf.irred v)
  have mV₃ := ker_maximal (Y := G.V) (Z := G.W) om v (Rf₃.p v) (h₃.onto v) (h₃.inv v) tV (h₃.irred v)
  have mV' := ker_maximal om' v (Rf.p' v) (hf.onto' v) (hf.inv' v) sV' iV'
  have mV₃' := ker_maximal (Y := G.V') (Z := G.W) om' v (Rf₃.p' v) (h₃.onto' v) (h₃.inv' v) tV' jV'
  have howe := PositivityTheory.Sph.maxFinT_of sphTri F E σ B a a' G X om om' hT v trivial
  have eV := howe.1 _ _ mV mV₃
  have eV' := howe.2 _ _ mV' mV₃'
  obtain ⟨ψ, hψ⟩ := equiv_of_ker_eq' (Rf.p v) (Rf₃.p v) (hf.onto v) (h₃.onto v) eV
  obtain ⟨ψ', hψ'⟩ := equiv_of_ker_eq' (Rf.p' v) (Rf₃.p' v) (hf.onto' v) (h₃.onto' v) eV'
  set T : Module.End ℂ (Rf.Pi v) := ψ.symm.toLinearMap ∘ₗ ψ'.toLinearMap with hTdef
  have hTapp : ∀ x, T x = ψ.symm (ψ' x) := fun x => rfl
  have comm : ∀ h ∈ UAt σ G.W (evFin F v), ∀ χ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ χ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) χ χ₁ → ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → Rf.p v φ = T (Rf.p v χ) → Rf.p v φ₁ = T (Rf.p v χ₁) := by
    intro h hh χ hχ χ₁ hχ₁ hc φ hφ φ₁ hφ₁ ha e
    obtain ⟨χ', hχ', e1⟩ : ∃ χ' ∈ SB (Fin a' × Fin (a + a') → Fv F v), Rf.p' v χ' = Rf.p v χ := by
      have : Rf.p v χ ∈ (SB (Fin a' × Fin (a + a') → Fv F v)).map (Rf.p' v) := by rw [hf.onto' v]; trivial
      exact this
    obtain ⟨χ₁', hχ₁', hc'⟩ := exV' h hh χ' hχ'
    have e2 : Rf.p v χ₁ = Rf.p' v χ₁' := hf.equiv v h hh χ hχ χ' hχ' χ₁ hχ₁ χ₁' hχ₁' hc hc' e1.symm
    have e3 : Rf₃.p v φ = Rf₃.p' v χ' := by
      rw [hψ φ hφ, e, hTapp, ← e1, LinearEquiv.apply_symm_apply, ← hψ' χ' hχ']
    have e4 : Rf₃.p v φ₁ = Rf₃.p' v χ₁' := h₃.equiv v h hh φ hφ χ' hχ' φ₁ hφ₁ χ₁' hχ₁' ha hc' e3
    rw [hTapp, e2, ← hψ' χ₁' hχ₁', ← e4, hψ φ₁ hφ₁, LinearEquiv.symm_apply_apply]
  have hrank : Module.rank ℂ (Rf.Pi v) ≤ Cardinal.aleph0 := by
    haveI := sc_Fv v
    have sp : Function.Surjective ((Rf.p v).comp (SB (Fin a × Fin (a + a') → Fv F v)).subtype) := fun y => by
      have : y ∈ (SB (Fin a × Fin (a + a') → Fv F v)).map (Rf.p v) := by rw [hf.onto v]; trivial
      obtain ⟨x, hx, rfl⟩ := this
      exact ⟨⟨x, hx⟩, rfl⟩
    exact (LinearMap.rank_le_of_surjective _ sp).trans (rank_SB_le _)
  have hker : ∀ c : ℂ, ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → Rf.p v φ ∈ LinearMap.ker (T - c • 1) →
        Rf.p v φ₁ ∈ LinearMap.ker (T - c • 1) := by
    intro c h hh φ hφ φ₁ hφ₁ hact hmem
    rw [LinearMap.mem_ker] at hmem ⊢
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at hmem ⊢
    have hsc := GlobalTheory.ThK.LocalOps.acts_lin v (om (1, h)) (exV h hh) hφ hφ hact hact c 0
    rw [zero_smul, zero_smul, add_zero, add_zero] at hsc
    have e : Rf.p v (c • φ) = T (Rf.p v φ) := by rw [map_smul, hmem]
    have := comm h hh φ hφ φ₁ hφ₁ hact (c • φ) ((SB (Fin a × Fin (a + a') → Fv F v)).smul_mem c hφ) (c • φ₁)
      ((SB (Fin a × Fin (a + a') → Fv F v)).smul_mem c hφ₁) hsc e
    rw [← this, map_smul]
  have hran : ∀ c : ℂ, ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → Rf.p v φ ∈ LinearMap.range (T - c • 1) →
        Rf.p v φ₁ ∈ LinearMap.range (T - c • 1) := by
    intro c h hh φ hφ φ₁ hφ₁ hact hmem
    obtain ⟨y, hy⟩ := hmem
    obtain ⟨χ, hχ, rfl⟩ : ∃ χ ∈ SB (Fin a × Fin (a + a') → Fv F v), Rf.p v χ = y := by
      have : y ∈ (SB (Fin a × Fin (a + a') → Fv F v)).map (Rf.p v) := by rw [hf.onto v]; trivial
      exact this
    obtain ⟨χ₁, hχ₁, hc⟩ := exV h hh χ hχ
    have hsum := GlobalTheory.ThK.LocalOps.acts_lin v (om (1, h)) (exV h hh) hφ hχ hact hc 1 c
    rw [one_smul, one_smul] at hsum
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hy
    have e : Rf.p v (φ + c • χ) = T (Rf.p v χ) := by
      rw [map_add (f := _), map_smul, ← hy]; abel
    have := comm h hh χ hχ χ₁ hχ₁ hc (φ + c • χ) (add_mem hφ ((SB (Fin a × Fin (a + a') → Fv F v)).smul_mem c hχ)) (φ₁ + c • χ₁)
      (add_mem hφ₁ ((SB (Fin a × Fin (a + a') → Fv F v)).smul_mem c hχ₁)) hsum e
    refine ⟨Rf.p v χ₁, ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [← this, map_add (f := _), map_smul]; abel
  obtain ⟨l, hl⟩ := scalar_of_irred (fun N => ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ → Rf.p v φ ∈ N → Rf.p v φ₁ ∈ N)
    hrank (hf.irred v) T hker hran
  have hTl : ∀ x, ψ' x = l • ψ x := fun x => by
    have := congrArg (fun f : Module.End ℂ (Rf.Pi v) => f x) hl
    simp only [hTapp, LinearMap.smul_apply, Module.End.one_apply] at this
    rw [← map_smul, ← this, LinearEquiv.apply_symm_apply]
  have hl0 : l ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := exists_ne (0 : Rf.Pi v)
    have := hTl x
    rw [zero_smul, LinearEquiv.map_eq_zero_iff] at this
    exact hx this
  refine ⟨ψ, l, hl0, hψ, fun φ hφ => by rw [hψ' φ hφ, hTl], fun hv => ?_⟩
  obtain ⟨s1, s2⟩ := hf.sph v hv
  obtain ⟨s3, -⟩ := h₃.sph v hv
  have hvac := (hT.geo.hM.vac v).1
  have hvac' := (hT.geo.hM'.vac v).1
  change Rf₃.p v (G.M.vac v) = Rf₃.p' v (G.M'.vac v) at s3
  have e1 : Rf₃.p' v (G.M'.vac v) = l • Rf₃.p v (G.M.vac v) := by
    rw [hψ' _ hvac', hTl, ← s1, ← hψ _ hvac]
  have hne : Rf₃.p v (G.M.vac v) ≠ 0 := by
    rw [hψ _ hvac]; exact (LinearEquiv.map_ne_zero_iff ψ).2 s2
  rw [← s3] at e1
  have : (l - 1) • Rf₃.p v (G.M.vac v) = 0 := by rw [sub_smul, one_smul, ← e1, sub_self]
  rcases smul_eq_zero.1 this with h | h
  · exact sub_eq_zero.1 h
  · exact absurd h hne
end UpperTheory.Lit.HoweDuality
end
end
end

