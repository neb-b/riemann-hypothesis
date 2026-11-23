module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.DegenerationDataAtModelPointOfUniformisation
public import Formalism.LocalToGlobal.ProjectiveLattices.LocFld
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0017
public import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAlgebraMapEqOfValVLeOne
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstTwoPointsPowerSeriesZeroOfVanishFirstAxis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffDpolyNEqDerivAt0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralUnitMatrixGauge
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0113
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthNonnegIntegralOperatorIntegralVectors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0890
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1050
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0889
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0870
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0916
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0896
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0893
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0886
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0923
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0871
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1849
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AutomorphicArithmetic.CMTraceForms.Places

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralFramedPointCompletionIndexOne
section
open AlgebraicGeometry CategoryTheory
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.CompletionPoint

theorem exists_intFr_index_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → ∀ (Z : Comp Xo c) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K), LiesOn Z y → ∀ (w : HeightOneSpectrum (𝓞 c.F)) (𝔭 : HeightOneSpectrum (𝓞 K)), (∀ a : c.F, vLa 𝔭 (algebraMap c.F K a) = vLa w a) → ∃ (T : CDVR) (ι : c.F →+* T.Fr) (y' : IntFr Xo c T ι), OverLa w T.V ι 1 ∧ algOn Z T ι y' := by
  intro E _ _ _ H Dw l Xo c hpq hg Z K _ _ _ y hy w 𝔭 hv
  classical
  obtain ⟨hP, hN⟩ := GlobalTheory.Moduli.jointExistence_and_moduliScheme
  obtain ⟨O, _, β, Y, -, hPI, hbase⟩ := GlobalTheory.Frames.modelAtSt_of_good hP hN E H Dw l Xo c hpq hg w
  obtain ⟨T, k, hk, hfin, -⟩ := GlobalTheory.PlaceCompletion.exists_initial_completion K 𝔭
  have ho : OverLa w T.V (k.comp (algebraMap c.F K)) 1 :=
    ⟨Nat.one_pos, fun a => by rw [← hv a]; exact hk.2 _⟩
  obtain ⟨b, hb⟩ := hbase T _ 1 ho
  have hT := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  have hIF : IntFramesSt Xo c := GlobalTheory.intFrames_of_laws GlobalTheory.abelianSchemeLaws_all.1.secBaseChange hT E H Dw l Xo c
  let _ := (k.comp (algebraMap c.F K)).toAlgebra
  have hz : ptF y ≫ Limits.pullback.snd _ _ = spMap (algebraMap c.F K) := Limits.pullback.lift_snd _ _ _
  have hs : (spMap k ≫ ptF y) ≫ Limits.pullback.snd _ _ = spMap (k.comp (algebraMap c.F K)) := by
    rw [Category.assoc, ← GlobalTheory.EtaVal.spMap_comp_spMap]
    exact congrArg _ hz
  have hx : ((spMap k ≫ ptF y) ≫ Limits.pullback.fst _ _) ≫ Xo.s = sOf c T.Fr := by
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hs, GlobalTheory.EtaVal.spMap_comp_spMap]
    rfl
  obtain ⟨y₀, -, h0, -, -⟩ := gfp_frPt_gen (Xo := Xo) (c := c) (L := T.Fr) (L' := T.Fr) hT (fun _ => rfl) _ hx
    (fun _ i j => if i = j then 1 else 0) (fun _ _ => if_pos rfl) (fun _ _ _ h => if_neg h.ne')
  obtain ⟨y', t, hbor⟩ := intFr_of_model hIF T (k.comp (algebraMap c.F K)) Y hPI b hb y₀
  refine ⟨T, k.comp (algebraMap c.F K), y', ho, hfin, fun q => ?_⟩
  have h1 : y'.1.x = y₀.x := hbor.1
  have h2 : ptF y'.1 = spMap k ≫ ptF y := by
    apply Limits.pullback.hom_ext
    · exact (Limits.pullback.lift_fst _ _ _).trans (h1.trans h0)
    · exact (Limits.pullback.lift_snd _ _ _).trans hs.symm
  rw [h2]
  exact hy (spMap k q)

end GlobalTheory.CompletionPoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGermOnColumnsSameValue
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns GlobalTheory.LawLog ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.ColApprox

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}

theorem map_polyT {T : CDVR} {C : Type} [Field C] (φ : T.Fr →+* C) (cx : Lt1 Dw → ℕ) {n : ℕ}
    (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V) :
    MvPolynomial.map φ (polyT B cx) = MvPolynomial.aeval (fun ℓ : Let cx => ∑ j,
      MvPolynomial.C (φ (algebraMap T.V T.Fr (B ℓ.1.1.1 ℓ.1.2 j))) *
        (MvPolynomial.X ⟨ℓ.1.1.1.1, Fin.castLE (rk_le _) ℓ.2, j⟩ : MvPolynomial (LtN Dw n) C)) (polyH C cx) := by
  classical
  unfold polyT polyP polyH
  rw [map_prod, map_prod, ← Finset.prod_filter_of_ne (p := fun f => cx f ≠ 0)
    (fun f _ hf h0 => hf (by rw [h0, pow_zero, map_one])),
    Finset.prod_subtype (p := fun f => cx f ≠ 0) _ (fun f => by simp)]
  refine Finset.prod_congr rfl fun f _ => ?_
  rw [MvPolynomial.aeval_rename, GlobalTheory.FGDepth.detPow, map_pow, map_pow, RingHom.map_det, AlgHom.map_det, ← Matrix.det_transpose]
  congr 2
  ext a b : 2
  simp [GlobalTheory.CombMinor.cMat]

theorem exists_cols {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {p : ℕ} {cx : Lt1 Dw → ℕ} {n : ℕ}
    {B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V} (hB : IsCols c T io p cx B) (N : ℕ) :
    ∃ x : Col cx → Fin n → 𝓞 E,
      (∀ b j, ∃ z : T.V, io (embK c b.1.1.1 (x b j)) = algebraMap T.V T.Fr (B b.1.1 b.2 j + (p : T.V) ^ N * z)) ∧
      ∀ b b', ∑ j, H.bar (x b j) * x b' j ∈ Ideal.span {(p : 𝓞 E) ^ N} := by
  obtain ⟨blk, hb⟩ := hB
  choose x h0 h1 h2 using fun f => (hb f).2.2 N
  refine ⟨fun b => x b.1 b.2, fun b j => h1 b.1 b.2 j, ?_⟩
  rintro ⟨f, b⟩ ⟨f', b'⟩
  by_cases hf : f = f'
  · subst hf
    simpa only [mul_comm] using h2 f b' b
  · rw [Finset.sum_eq_zero]
    · exact Ideal.zero_mem _
    intro j _
    dsimp only
    by_cases hj : j ∈ Set.range fun j => blk ⟨f, j⟩
    · rw [h0 f' b' j, mul_zero]
      rintro ⟨j2, e2⟩
      obtain ⟨j1, e1⟩ := hj
      exact hf (congrArg Sigma.fst (blk.injective (e1.trans e2.symm)))
    · rw [h0 f b j hj, map_zero, zero_mul]

theorem isIntV_ringHom {T : CDVR} {p : ℕ} [Fact p.Prime] (X : ValExt T p) (φ : 𝓞 E →+* X.C) (a : 𝓞 E) :
    IsIntV (vX_vp X) (φ a) := by
  rw [isIntV_iff, ← X.ints.isIntegral_iff_v_le_one]
  exact (map_isIntegral_int φ (Algebra.IsIntegral.isIntegral a)).tower_top

theorem le_v_pow_mul {T : CDVR} {p : ℕ} [Fact p.Prime] (X : ValExt T p) (N : ℕ) {z : X.C}
    (hz : IsIntV (vX_vp X) z) : (((N : ℝ) : ℝ) : WithTop ℝ) ≤ vX_vp X ((p : X.C) ^ N * z) := by
  rw [AddValuation.map_mul, AddValuation.map_pow, vX_vp_p]
  refine le_add_of_le_of_nonneg (le_of_eq ?_) hz
  simp

theorem lin_col {C : Type} [Field C] {d m : ℕ} {κ : Type} [Fintype κ] {ι : κ → Type} [∀ b, Fintype (ι b)]
    (e : κ ≃ Fin m) (u : ∀ b, ι b → Fin d → C) (q : Fin m) :
    lin (fun ℓ : Σ b, ι b => u ℓ.1 ℓ.2) (fun ℓ => if e ℓ.1 = q then 1 else 0) =
      fun i => ∑ a, u (e.symm q) a i • (MvPowerSeries.X ⟨e.symm q, a⟩ : MvPowerSeries (Σ b, ι b) C) := by
  funext i
  unfold lin
  rw [Fintype.sum_sigma, Finset.sum_eq_single (e.symm q)]
  · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun a _ => ?_
    have hq : e b ≠ q := fun h => hb (by rw [← h]; simp)
    simp [hq]
  · simp

theorem exists_germ_cols : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (cx : Lt1 Dw → ℕ) (n : ℕ) (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V), IsCols c T io p cx B → ∀ (N k : ℕ) (g : PS X.C n (chD Ch.ch)), MvIsInt (vX_vp X) g → ∃ f : MvPowerSeries (Σ _ : GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.Col cx, Fin (chD Ch.ch)) X.C, MvIsInt (vX_vp X) f ∧ (((N : ℝ) : ℝ) : WithTop ℝ) ≤ vX_vp X (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nabX Ch X cx B k g - derivAt0 (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.polyH X.C cx) (MvPowerSeries.subst (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.expH Ch X cx) f)) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p _ la T io e _ y Ch X cx n B hB N k g hg
  classical
  letI := io.toAlgebra
  obtain ⟨BT, -, -, -, -, -, -, e7⟩ := GlobalTheory.integralChart_formalBiext E H Dw l Xo c T io y Ch
  letI : Algebra T.Fr X.C := X.ιF.toAlgebra
  letI : Algebra T.V X.C := (X.ιF.comp (algebraMap T.V T.Fr)).toAlgebra
  haveI : IsScalarTower T.V T.Fr X.C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨h1, h2, h3, h4⟩ := e7 X.C
  have hc := (h3 _).2 h4
  let eC := Fintype.equivFin (Col cx)
  let σ : Col cx → 𝓞 E →+* X.C := fun b => X.ιF.comp (io.comp (embK c b.1.1.1))
  have heig : ∀ (a : 𝓞 E) (ℓ : Lt1 Dw), (dAct X.C BT a).mulVec (lieVec Ch X ℓ) =
      X.ιF (io (embK c ℓ.1 a)) • lieVec Ch X ℓ := by
    intro a ℓ
    funext i
    have h := congrArg X.ιF (congrFun (GlobalTheory.PowGerm.eigDirSt E H Dw l Xo c T io y Ch a ℓ) i)
    have hu : ∀ i, lieVec Ch X ℓ i = X.ιF (Ch.ch.uvec ℓ i) := fun i =>
      congrArg X.ιF (Ch.gen.1.2.2.2.2.2.2 ℓ i).symm
    simp only [Matrix.mulVec, dotProduct, dAct, h2, hu, Pi.smul_apply, smul_eq_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, dAct, FB.actK, MvPowerSeries.coeff_map, map_sum, map_mul, Pi.smul_apply,
      smul_eq_mul] at h ⊢
    exact h
  obtain ⟨K, hK⟩ := exists_germ_close (v := vX_vp X) BT (G := lawX Ch X) h1.symm (fgl Ch X).F_int
    (fun ℓ : Let cx => eC ℓ.1) (fun ℓ => frame Ch X ℓ.1.1.1 ℓ.2) (fun b a => σ (eC.symm b) a)
    (fun a ℓ => by rw [eC.symm_apply_apply]; exact heig a _) (isIntV_jX X) hc H.w0
    (fun ℓ i => isIntV_jX X _) (fun b a => isIntV_ringHom X _ a)
    (fun x => (GlobalTheory.exists_integral_unit_matrix_gauge _ _ _ _ BT _ hc H.w0 _ n x).imp fun _ h => h.2)
    (polyH X.C cx) k g hg
  obtain ⟨N', hN'⟩ := exists_nat_ge ((N : ℝ) + K)
  obtain ⟨x, hx1, hx2⟩ := exists_cols hB N'
  let β : Col cx → Fin n → X.C := fun b j => jX X (B b.1.1 b.2 j)
  obtain ⟨f, hf, hv⟩ := hK N' (fun b => x (eC.symm b)) (fun b => β (eC.symm b)) (fun b j => isIntV_jX X _)
    (fun b j => by
      obtain ⟨z, hz⟩ := hx1 (eC.symm b) j
      have : β (eC.symm b) j - σ (eC.symm b) (x (eC.symm b) j) = (p : X.C) ^ N' * jX X (-z) := by
        show _ - X.ιF (io (embK c _ _)) = _
        rw [hz]
        show jX X _ - jX X _ = _
        simp
      rw [this]
      exact le_v_pow_mul X N' (isIntV_jX X _))
    (fun b b' => by
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.1 (hx2 (eC.symm b) (eC.symm b'))
      have : σ (eC.symm b') (H.w0 * ∑ j, star (x (eC.symm b) j) * x (eC.symm b') j) =
          (p : X.C) ^ N' * σ (eC.symm b') (H.w0 * r) := by
        rw [show ∑ j, star (x (eC.symm b) j) * x (eC.symm b') j = _ from hr, mul_left_comm, map_mul, map_pow,
          map_natCast]
      rw [this]
      exact le_v_pow_mul X N' (isIntV_ringHom X _ _))
  have cX : ∀ q : Fin (Fintype.card (Col cx)) × Fin (chD Ch.ch), MvPowerSeries.constantCoeff
      (MvPowerSeries.X ⟨eC.symm q.1, q.2⟩ : MvPowerSeries (Σ _ : Col cx, Fin (chD Ch.ch)) X.C) = 0 := fun q => by simp
  have hE : MvPowerSeries.HasSubst (expH Ch X cx) := MvPowerSeries.hasSubst_of_constantCoeff_zero fun q =>
    nc_exPt (fgl Ch X) (fun i => by simp) q.2
  refine ⟨MvPowerSeries.subst (fun q : Fin (Fintype.card (Col cx)) × Fin (chD Ch.ch) =>
    (MvPowerSeries.X ⟨eC.symm q.1, q.2⟩ : MvPowerSeries (Σ _ : Col cx, Fin (chD Ch.ch)) X.C)) f,
    ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst _ hf
      (fun q α => by rw [MvPowerSeries.coeff_X]; split_ifs <;> simp [IsIntV]) cX, ?_⟩
  refine le_trans (WithTop.coe_le_coe.2 (by linarith)) (hv.trans (le_of_eq ?_))
  congr 2
  · have hA := GlobalTheory.ExpCoord.constantCoeff_dpolyN_eq_derivAt0 X.C (vX_vp X) _ (lawX Ch X) (fgl Ch X) (fun _ => rfl) n (LtN Dw n) (Let cx)
      (fun ℓ => ℓ.2.2) (fun ℓ => lieVec Ch X ⟨ℓ.1, ℓ.2.1⟩) (fun ℓ => β ℓ.1)
      (fun ℓ j => ⟨ℓ.1.1.1.1, Fin.castLE (rk_le _) ℓ.2, j⟩) (fun ℓ => frame Ch X ℓ.1.1.1 ℓ.2) (fun _ _ => rfl)
      (fun _ _ => rfl) (polyH X.C cx)
    unfold nabX nabValN
    rw [map_polyT]
    simp only [eC.symm_apply_apply, FB.hL, h2]
    exact (hA _).symm
  · rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero cX) hE]
    congr 2
    funext q
    rw [MvPowerSeries.subst_X hE]
    unfold colExp
    rw [lin_col eC (fun b : Col cx => frame Ch X b.1.1)]
    rfl

end GlobalTheory.ColApprox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGermOnCopiesSameValue
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ColumnGerm

open NumberField MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns GlobalTheory.IsoTriv

theorem mvIsInt_pow {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {σ : Type} {g : MvPowerSeries σ C}
    (hg : MvIsInt v g) (k : ℕ) : MvIsInt v (g ^ k) := by
  classical
  induction k with
  | zero =>
    intro α
    unfold IsIntV
    rw [pow_zero, coeff_one]
    split_ifs <;> simp
  | succ k ih => rw [pow_succ]; exact GlobalTheory.DepthNonneg.mvIsInt_mul ih hg

theorem exists_nabX_eq (hN : NabSt) (hI : InclSt) (hR : RetrSt) (hU : UnitSt) (hF : FrameSt)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    {c : Coeff l} [StarRing (𝓞 E)] (hs : ∀ a : 𝓞 E, star a = H.bar a)
    {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} (Ch : IntegralChartA3 Xo c T io y)
    {p : ℕ} [Fact p.Prime] (X : ValExt T p) (cx : Lt1 Dw → ℕ) {n : ℕ} (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V)
    (hB : IsCols c T io p cx B) (k : ℕ) (f : MvPowerSeries (Σ _ : Col cx, Fin (chD Ch.ch)) X.C)
    (hf : MvIsInt (vX_vp X) f) :
    ∃ g : PS X.C n (chD Ch.ch), MvIsInt (vX_vp X) g ∧
      nabX Ch X cx B k g = derivAt0 (polyH X.C cx) (subst (expH Ch X cx) f) := by
  obtain ⟨ψ, ψ0, -, ψe, ψU⟩ := hI E H Dw l Xo c hs T io y Ch p X cx n B hB
  obtain ⟨ρ, ρ0, ρi, ρe⟩ := hR E H Dw l Xo c hs T io y Ch p X cx n B hB
  have hψ : HasSubst ψ := hasSubst_of_constantCoeff_zero ψ0
  have hρ : HasSubst ρ := hasSubst_of_constantCoeff_zero ρ0
  have e0 : ∀ q, constantCoeff (expH Ch X cx q) = 0 := fun q =>
    cc_expPt (fgl Ch X) (fun e => by simp) q.2
  have c0 : ∀ q, constantCoeff (colPt Ch X cx B q) = 0 := fun q =>
    cc_expPt (fgl Ch X) (fun e => by simp) q.2
  have he : HasSubst (expH Ch X cx) := hasSubst_of_constantCoeff_zero e0
  have hc : HasSubst (colPt Ch X cx B) := hasSubst_of_constantCoeff_zero c0
  have fr1 : constantCoeff (frameX Ch X n) = 1 := by
    letI := io.toAlgebra
    letI : Algebra T.Fr X.C := X.ιF.toAlgebra
    exact (hF X.C (vX_vp X) _ T.Fr (𝓞 E) Ch.ch.B (isIntFB_chart Ch X) _ (gauge_chart Ch X) H.w0 n).1
  have U1 : constantCoeff (subst ψ (frameX Ch X n) : MvPowerSeries (Σ _ : Col cx, Fin (chD Ch.ch)) X.C) = 1 := by
    have h := constantCoeff_subst_eq_zero hψ ψ0 (f := frameX Ch X n - 1) (by rw [map_sub, fr1, map_one, sub_self])
    rw [← coe_substAlgHom hψ, map_sub, map_one, map_sub, map_one, sub_eq_zero, coe_substAlgHom] at h
    exact h
  obtain ⟨U', U'i, hU'⟩ := (hU X.C (vX_vp X) _).2.2.2.2.2 _ ψU U1
  refine ⟨subst ρ (f * U' ^ k), ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst _
    (GlobalTheory.DepthNonneg.mvIsInt_mul hf (mvIsInt_pow U'i k)) ρi ρ0, ?_⟩
  rw [hN E H Dw l Xo c T io y Ch p X cx n B k]
  congr 1
  have h1 : subst (colPt Ch X cx B) (subst ρ (f * U' ^ k) : PS X.C n (chD Ch.ch)) =
      subst (expH Ch X cx) (f * U' ^ k) := by
    rw [subst_comp_subst_apply hρ hc, funext ρe]
  have h2 : subst (colPt Ch X cx B) (frameX Ch X n) = subst (expH Ch X cx)
      (subst ψ (frameX Ch X n) : MvPowerSeries (Σ _ : Col cx, Fin (chD Ch.ch)) X.C) := by
    rw [subst_comp_subst_apply hψ he, funext ψe]
  rw [subst_mul hc, subst_pow hc, h1, h2, ← subst_pow he, ← subst_mul he, mul_assoc, ← mul_pow, mul_comm U', hU',
    one_pow, mul_one]

end GlobalTheory.ColumnGerm

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ColumnGerm

theorem exists_germ_on_copies : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (cx : Lt1 Dw → ℕ) (n : ℕ) (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V), IsCols c T io p cx B → ∀ (N k : ℕ) (f : MvPowerSeries (Σ _ : GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.Col cx, Fin (chD Ch.ch)) X.C), MvIsInt (vX_vp X) f → ∃ g : PS X.C n (chD Ch.ch), MvIsInt (vX_vp X) g ∧ (((N : ℝ) : ℝ) : WithTop ℝ) ≤ vX_vp X (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nabX Ch X cx B k g - derivAt0 (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.polyH X.C cx) (MvPowerSeries.subst (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.expH Ch X cx) f)) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p _ la T io e _ y Ch X cx n B hB N k f hf
  have hadd := _root_.GlobalTheory.IsoTriv.log_sum_additive_preserves_integrality
  have hact := _root_.GlobalTheory.IsoTriv.actSt
  have hunit := _root_.GlobalTheory.IsoTriv.unitSt
  have hcont := _root_.GlobalTheory.IsoTriv.contSt_holds
  have hbi := _root_.GlobalTheory.IsoTriv.GaugeBiadd.biadd_of_add_of_act hadd hact
  have hfr := GlobalTheory.T.frameSeriesExpSum_of_actionLinear_logUnit hact hunit
  have hfin := GlobalTheory.T.gaugeHermitianCombination_of_steps hadd hact hunit hbi
  have hla := GlobalTheory.T.limitActionLieAlgebra_of_primeIdempotentApprox _root_.GlobalTheory.IsoTriv.PrimeIdempotent.epsSt
  have hlp := _root_.GlobalTheory.IsoTriv.limPt_of_steps hadd hact hcont
  have hlf := _root_.GlobalTheory.IsoTriv.limFrame hadd hact hunit hbi hfr hfin hcont
  obtain ⟨g, hg, h⟩ := exists_nabX_eq (_root_.GlobalTheory.IsoTriv.nabSt_of _root_.GlobalTheory.InvDer.invDer _root_.GlobalTheory.IsoTriv.linSt_holds hfr) (GlobalTheory.T.columnInclusionIntegral_of_limitSteps hla hlp hlf)
    (_root_.GlobalTheory.IsoTriv.retrSt_of hla hlp GlobalTheory.IsoTriv.limitEntriesMatrixInverseClosed_proof) hunit hfr (fun _ => rfl) Ch X cx B hB k f hf
  refine ⟨g, hg, ?_⟩
  rw [h, sub_self, AddValuation.map_zero]
  exact le_top

end GlobalTheory.ColumnGerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulInvPow
section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.CombTw

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

theorem wt_diff_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) (u : GlobalTheory.AllWt.Weight Dw) (w₀ : Psi H → ℤ) (m : ℕ) :
    wtOf Dw u 0 - wtOf Dw (u + parWt Dw w₀) m = wtOf Dw (parWt Dw (-w₀)) 0 + m • (-wtOf Dw 0 1) := by
  ext x
  · simp only [Prod.fst_sub, Prod.fst_add, Prod.smul_fst, Prod.fst_neg, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      Pi.neg_apply]
    simp only [wtOf, parWt, Pi.zero_apply, Pi.neg_apply, Pi.add_apply, nsmul_eq_mul]
    split_ifs <;> ring
  · simp only [Prod.snd_sub, Prod.snd_add, Prod.smul_snd, Prod.snd_neg]
    simp only [wtOf, nsmul_eq_mul]
    ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}

theorem exists_mul_inv_pow {Z : Comp Xo c} {G₀ G₁ : WTZ E} (s : TwSec U x Z G₀) (t : TwSec U x Z G₁) (m : ℕ) :
    ∃ z : TwSec U x Z (G₀ + m • (-G₁)), z.lo = s.lo - (m : ℝ) • t.hi ∧ z.hi = s.hi - (m : ℝ) • t.lo := by
  induction m with
  | zero => exact ⟨s.copy (by simp), by simp [TwSec.copy], by simp [TwSec.copy]⟩
  | succ n ih =>
    obtain ⟨z, hlo, hhi⟩ := ih
    refine ⟨(z.mul t.symm).copy (by rw [succ_nsmul, add_assoc]), ?_, ?_⟩
    · show z.lo + -t.hi = _
      rw [hlo]; push_cast; rw [add_smul, one_smul]; abel
    · show z.hi + -t.lo = _
      rw [hhi]; push_cast; rw [add_smul, one_smul]; abel

theorem exists_twSec_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (x : ℝ) (B : Finset ℕ) (Z : Comp Xo c) (u : GlobalTheory.AllWt.Weight Dw) (w₀ : Psi H → ℤ) (m : ℕ) (k : HeightOneSpectrum (𝓞 c.F) → ℝ) (s : TwSec U x Z (wtOf Dw (parWt Dw (-w₀)) 0)) (t : TwSec U x Z (wtOf Dw 0 1)), s.hi = s.lo → IntOff B s.lo → IntOff B t.hi → (∀ w, t.hi w - t.lo w ≤ k w) → ∃ z : TwSec U x Z (wtOf Dw u 0 - wtOf Dw (u + parWt Dw w₀) m), IntOff B z.lo ∧ ∀ w, z.hi w - z.lo w ≤ m * k w := by
  intro E _ _ _ H Dw l Xo c r U _ x B Z u w₀ m k s t hs hslo hthi hk
  obtain ⟨z, hlo, hhi⟩ := exists_mul_inv_pow s t m
  refine ⟨z.copy (wt_diff_eq Dw u w₀ m).symm, ?_, ?_⟩
  · show IntOff B z.lo
    rw [hlo]
    intro w hw
    obtain ⟨a, ha⟩ := hslo w hw
    obtain ⟨b, hb⟩ := hthi w hw
    exact ⟨a - m * b, by simp [ha, hb]⟩
  · intro w
    show z.hi w - z.lo w ≤ _
    rw [hhi, hlo]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hs]
    have := hk w
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith

end GlobalTheory.CombTw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOverLaUnder
section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.PlaceBelow

theorem exists_overLa_under : ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (i : K →+* K') (q : ℕ) (la' : HeightOneSpectrum (𝓞 K')), q.Prime → ((q : ℕ) : 𝓞 K') ∈ la'.asIdeal → ∀ (T : CDVR) (io' : K' →+* T.Fr) (e' : ℕ), OverLa la' T.V io' e' → ∃ (la : HeightOneSpectrum (𝓞 K)) (e : ℕ), ((q : ℕ) : 𝓞 K) ∈ la.asIdeal ∧ OverLa la T.V (io'.comp i) e := by
  intro K K' _ _ _ _ i q la' hq hmem T io' e' h
  letI : Algebra K K' := i.toAlgebra

  set la : HeightOneSpectrum (𝓞 K) := la'.under (𝓞 K) with hla
  set r : ℕ := la.asIdeal.ramificationIdx' la'.asIdeal with hr
  have hr0 : r ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver la'.asIdeal la.ne_bot
  refine ⟨la, e' * r, ?_, ?_⟩
  ·
    show ((q : ℕ) : 𝓞 K) ∈ la'.asIdeal.under (𝓞 K)
    rw [Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hmem
  · unfold OverLa vLa at h ⊢
    obtain ⟨he', hv⟩ := h
    refine ⟨Nat.mul_pos he' (Nat.pos_of_ne_zero hr0), fun a => ?_⟩

    have key : la.valuation K a ^ r = la'.valuation K' (algebraMap K K' a) :=
      by
        rw [hr, Ideal.ramificationIdx'_eq_ramificationIdx _ _ la.ne_bot]
        exact HeightOneSpectrum.valuation_liesOver K' la la' a
    rw [RingHom.comp_apply, hv, show i a = algebraMap K K' a from rfl, ← key, WithZero.log_pow]
    push_cast
    ring

end GlobalTheory.PlaceBelow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorDepthUpperBoundOddUnramifiedPrimeStatement
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factorDepth_upperBound_oddUnramifiedPrime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), ¬ IsUnit (p : T.V) → y.IsAlg → p ≠ 2 → ¬ (p : ℤ) ∣ discr E → ∀ (f : Lt1 Dw) (k : ℕ), InPsi H f.1 → (SplitInK H p → nuFac p y f k ≤ ((k * (Dw.q / ((p : ℝ) - 1)) : ℝ) : EReal)) ∧ (InertInK H p → nuFac p y f k ≤ ((k * (Dw.q / ((p : ℝ) - 1) + ((Dw.p : ℝ) - Dw.q) * p / ((p : ℝ) ^ 2 - 1)) : ℝ) : EReal)) := by
  first | exact @GlobalTheory.FacUpOdd.nuFac_le_odd_unram | exact GlobalTheory.FacUpOdd.nuFac_le_odd_unram | (intros; apply GlobalTheory.FacUpOdd.nuFac_le_odd_unram <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanUpperBoundBigFactorsPlaceAboveTwoStatement
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.meanUpperBound_bigFactors_placeAboveTwo : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (F : ℕ) (vd : ℝ), UpperTheory.Depth.SplitPlaces p H F vd → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), ¬ IsUnit ((p : ℕ) : T.V) → y.IsAlg → ∃ len : (E →+* ℂ) → ℝ, (∀ τ, 0 ≤ len τ) ∧ (∀ τ, ¬ InPsi H τ → len τ = 0) ∧ ∑ τ, len τ ≤ F * Dw.q * (1 + vd / 2) ∧ ∀ (f : Lt1 Dw) (k : ℕ), InPsi H f.1 → nuFac p y f k ≤ ((k * len f.1 : ℝ) : EReal) := by
  first | exact @GlobalTheory.RefSum.mean_bound_big_factors_at_two | exact GlobalTheory.RefSum.mean_bound_big_factors_at_two | (intros; apply GlobalTheory.RefSum.mean_bound_big_factors_at_two <;> assumption)
end

