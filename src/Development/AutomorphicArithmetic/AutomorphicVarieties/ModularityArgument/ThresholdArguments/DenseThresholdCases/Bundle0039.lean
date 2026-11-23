module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.WeightInfinitesimalCharacters.PtHypU
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.RigEnd3
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphyUnramifiedCoefficients
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypeIIOfBlochKatoLocalPoint
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.UnramifiedTwists.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0042
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0036
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0038
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.ExistsRec

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.FPtHypU
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3
theorem UpperTheory.V.Z.J.ptHyp_of_autB_of_lemW_of_isBase :
    U3.CohInp → _root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.KatoTwoW → _root_.UpperTheory.V.Th.RigidityFirstCase → _root_.UpperTheory.V.Th.RigiditySecondCase → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : (_root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition _ (D.η.comp D.ι) (D.Ψ.comp D.ι)))} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ (S : D.Ring U g₁), ∀ [IsCMField K] (ι : Qbar l ≃+* ℂ), _root_.UpperTheory.V.Aut.AutBAlt D ι g₁ → _root_.UpperTheory.V.Aut.LemWAlt D ι g₁ →
      ∀ x₀ : S.R →ₐ[c.O] c.O, IsBase D.η D.Ψ S.r.hom x₀ → PtHyp D.η S.r.hom x₀ := by
  intro hC hK hRI hRII Ω _ _ _ K _ _ _ l _ c N _ e ψ D U g₁ hM S _ ι hB hW x₀ hx
  have h0 : push (toBar x₀) S.r.hom = r0 D.η D.ΨQ := by
    have e1 : push (toBar x₀) S.r.hom =
        (GG.map (algebraMap c.O (PadicAlgCl l))).comp (push x₀ S.r.hom) := rfl
    rw [e1, show push x₀ S.r.hom = r0 D.η D.Ψ from hx]
    refine MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ?_) rfl
    let φ := algebraMap c.O (PadicAlgCl l)
    show (tor c.O (D.Ψ g) : Matrix (Fin 3) (Fin 3) c.O).map φ =
      tor (PadicAlgCl l) (Units.map φ.toMonoidHom (D.Ψ g))
    rw [tor_val, tor_val, Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    exact congrArg Units.val (map_zpow (Units.map φ.toMonoidHom) (D.Ψ g) (wt1 i))
  have hCob {Γ κ : Type} [Group Γ] [CommRing κ] (r : Γ →* GG (m := 3) (R := κ))
      (γ : Γ → Matrix (Fin 3) (Fin 3) κ) (h : γ ∈ ReciprocityTheory.Gal.B1 (adRep r)) :
      ∃ X, γ = cob r X := by
    obtain ⟨X, rfl⟩ := LinearMap.mem_range.mp h
    refine ⟨-X, funext fun g => ?_⟩
    show adRep r g X - X = -X - adRep r g (-X)
    rw [map_neg]
    abel
  refine ⟨fun f hf hU hL => ?_, fun j hj F hF hw => ?_, fun f hf F hF => ?_⟩
  · rw [h0]
    exact pt_fixed hC D hM (isPt_push D hM S f hf) hU hL
  · have hLoc : IsLocPt (toBar x₀) := by
      intro y hy
      have hsurj : Function.Surjective x₀ := fun a => ⟨algebraMap c.O S.R a, x₀.commutes a⟩
      have hmax : (Ideal.comap (x₀ : S.R →+* c.O) (IsLocalRing.maximalIdeal c.O)).IsMaximal :=
        Ideal.comap_isMaximal_of_surjective _ hsurj
      have hxy : x₀ y ∈ IsLocalRing.maximalIdeal c.O := by
        change y ∈ Ideal.comap (x₀ : S.R →+* c.O) (IsLocalRing.maximalIdeal c.O)
        rwa [IsLocalRing.eq_maximalIdeal hmax]
      have hnonunit := (IsLocalRing.mem_maximalIdeal _).mp hxy
      change ‖(x₀ y : PadicAlgCl l)‖ < 1
      by_cases hzero : x₀ y = 0
      · simp [hzero]
      have hval : (IsDiscreteValuationRing.addVal c.O (x₀ y)).toNat ≠ 0 := by
        rw [Ne, ENat.toNat_eq_zero, IsDiscreteValuationRing.addVal_eq_zero_iff,
          IsDiscreteValuationRing.addVal_eq_top_iff]
        exact fun h => h.elim hnonunit hzero
      have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
      have hpow := pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hl) hval
      rw [← normO l c.O (x₀ y) hzero] at hpow
      exact lt_of_not_ge fun h => (not_lt_of_ge (one_le_pow₀ h)) hpow
    have h1 := tanCoc_isBK hC D hM S F (hF ▸ hLoc)
    rw [hF, h0] at h1
    rw [h0]
    exact hCob _ _ (bloch_kato_nonpositive_weight hC D j hj _ h1.1 hw h1.2)
  · have h1 := tanCoc_isBK hC D hM S F (hF ▸ hf.1)
    rw [hF] at h1
    have hp := isPt_push D hM S f hf.1
    have hPush : IsPush (f.comp (entAlg c.O S.r.hom).val) S.r.hom (push f S.r.hom) := by
      intro g
      refine ⟨rfl, fun a b => ⟨?_, rfl⟩⟩
      unfold entAlg
      exact Algebra.subset_adjoin ⟨g, a, b, rfl⟩
    have hz : Af.BlochKatoSelmerVanishes l (adRep (push f S.r.hom)) := by
      rcases (twoPt_shape S D.gd.l_odd hM f hf).1 with h | h
      · exact hRI D hM S f hf.1 hp.mult ι h (hB U S _ _ hp.mult hPush h)
      · exact _root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.bloch_kato_selmer_vanishes_of_type_ii_modular_ext hC hK hRII D hM S f hf.1 ι h
          (hW U S _ _ hPush h (typeII_facts hC D hM hp h).1)
    exact hCob _ _ (hz _ h1.1 h1.2)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuFrobTotT
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.PRep GlobalTheory.SmGL
open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Win.Gu
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
private theorem unr_lpSum {x y : WD h} (hx : x.unr) (hy : y.unr) : (x.lpSum y).unr := by
  induction x using Quotient.inductionOn with | h a => ?_
  induction y using Quotient.inductionOn with | h b => ?_
  have ha : a.2.Unr := hx
  have hb : b.2.Unr := hy
  show (WD.mk (a.2.sum b.2)).unr
  rw [WD.unr_mk]
  refine ⟨?_, fun σ => ?_⟩
  · rw [WDRep.sum_N, ha.1, hb.1, LinearMap.prodMap_zero]
  · rw [WDRep.sum_ρ, ha.2, hb.2]; exact LinearMap.prodMap_one
private theorem sumList_spec (g : Weil h) : ∀ (c : ℕ) (f : Fin c → WD h) (M : Fin c → Multiset ℂ),
    (∀ i, (f i).unr ∧ (f i).charPol g = ((M i).map fun b => X - C b).prod) →
    (sumList (List.ofFn f)).unr ∧ (sumList (List.ofFn f)).charPol g = ((∑ i, M i).map fun b => X - C b).prod := by
  intro c
  induction c with
  | zero =>
    intro f M _
    have e : sumList (List.ofFn f) = WD.lpZero (h := h) := by simp [sumList]
    rw [e, WD.lpZero, WD.unr_mk, WD.charPol_mk, WDRep.diag_ρ, charpoly_diagEnd]
    exact ⟨WDRep.unr_diag _, by simp⟩
  | succ c ih =>
    intro f M H
    obtain ⟨h1, h2⟩ := ih (fun i => f i.succ) (fun i => M i.succ) fun i => H i.succ
    have e : sumList (List.ofFn f) = (f 0).lpSum (sumList (List.ofFn fun i => f (Fin.succ i))) := by
      rw [List.ofFn_succ]; rfl
    rw [e, WD.charPol_lpSum, h2, (H 0).2, Fin.sum_univ_succ, Multiset.map_add (f := _), Multiset.prod_add]
    exact ⟨unr_lpSum (H 0).1 h1, rfl⟩
private theorem rec_eq_diagV {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : IsRecV h rc) {a : ℕ}
    {σ : IrrRep (GL (Fin a) (w.adicCompletion E))} {α : Fin a → ℂˣ} (hα : HasSatake σ.ρ α) :
    rc (cls σ) = WD.mk (WDRep.diag h fun i => (α i)⁻¹) := by
  obtain ⟨_, _, _, L⟩ := H
  have φ := equivRep σ
  exact L.sat (cls σ) α ⟨IrrRep.irr _, fixed_ne_bot_of_equiv φ hα.2.1,
    (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans hα.2.2⟩
private theorem rec_tw_diag {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : IsRecV h rc) {n : ℕ}
    (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ) (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B) (s : ℝ) :
    ∃ α : Fin n → ℂˣ, B = Finset.univ.val.map α ∧
      (rc (cl σ)).lpTw s = WD.mk (WDRep.diag h fun i => (α i)⁻¹ * qPow w s) := by
  have hsph : IsSpherical (ParLaws.toRep σ).ρ := by
    have := hB.1
    unfold IsSpherical IsSphericalFor
    rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n]
    exact this
  obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.main UpperTheory.Zero.LLC.Pr.bz (w.adicCompletion E) n
    ⟨_, σ.ρ, σ.smooth, σ.irred⟩ hsph
  refine ⟨α, hB.unique (GlobalTheory.T.hasSatakeGL_of_hasSatakeParameters_principalSeries E w n _ σ.ρ α hα), ?_⟩
  have e : rc (IrrGL.of σ.ρ σ.smooth σ.irred) = WD.mk (WDRep.diag h fun i => (α i)⁻¹) :=
    rec_eq_diagV H (σ := ParLaws.toRep σ) hα
  rw [e, WD.lpTw_mk]
  refine WD.sound ⟨.refl _ _, fun g v => funext fun i => ?_, fun v => rfl⟩
  simp [mul_zpow, mul_comm, mul_left_comm, mul_assoc]
private theorem val_inv_eq (n d k : ℕ) (a : ℂˣ) :
    (((a⁻¹ * qPow w ((ex n d k : ℝ) / 2) : ℂˣ) : ℂ)) ^ (-1 : ℤ) =
      ((((normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) *
        ((a * qPow w ((k : ℝ) - ((d : ℝ) - 1) / 2) : ℂˣ) : ℂ) := by
  have hq : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (zero_lt_one.trans (one_lt_normV w)).ne'
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), zpow_neg_one, Units.val_mul, mul_inv, Units.val_inv_eq_inv_val, inv_inv,
    coe_qPow, ← Complex.cpow_neg, Units.val_mul, coe_qPow, mul_left_comm, Complex.ofReal_natCast, ← Complex.cpow_add _ _ hq]
  congr 2
  simp only [ex]
  push_cast
  ring
private theorem totPar_spec {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : IsRecV h rc) (n c : ℕ) (a d : Fin c → ℕ)
    (ρ : ∀ i, SmIrr (GL (Fin (a i)) (w.adicCompletion E))) (S : Fin c → Multiset ℂˣ)
    (hS : ∀ i, GlobalTheory.LFun.HasSatGL w (ρ i).ρ (S i)) (g : Weil h) (hg : deg g = -1) :
    (totPar n d ρ A h rc).unr ∧
      (totPar n d ρ A h rc).charPol g = ((algSat n (normV w) (satTot w d S)).map fun b => X - C b).prod := by
  have e : algSat n (normV w) (satTot w d S) = ∑ i, ∑ k : Fin (d i),
      algSat n (normV w) ((S i).map (· * qPow w (((k : ℕ) : ℝ) - ((d i : ℝ) - 1) / 2))) := by
    have hm : ∀ {α β ι : Type} (f : α → β) (s : Finset ι) (M : ι → Multiset α),
        (∑ i ∈ s, M i).map f = ∑ i ∈ s, (M i).map f := fun f s M => map_sum (Multiset.mapAddMonoidHom f) M s
    simp only [algSat, satTot, Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton, hm]
  rw [e]
  refine sumList_spec g c _ _ fun i => sumList_spec g (d i) _ _ fun k => ?_
  obtain ⟨α, hα, e⟩ := rec_tw_diag H (ρ i) (S i) (hS i) ((ex n (d i) k : ℝ) / 2)
  rw [e, hα, WD.unr_mk, WD.charPol_mk, WDRep.diag_ρ, charpoly_diagEnd, hg]
  refine ⟨WDRep.unr_diag _, ?_⟩
  simp only [val_inv_eq, algSat, Multiset.map_map, Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton]
  rfl
end UpperTheory.V.Z.Win.Gu
theorem UpperTheory.V.Z.Win.Gu.frobTotT_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → ExtraV → GdLaws → FrobTotT := by
  intro _ hX hG F Ω _ _ _ _ _ l _ ι n c a d r _ w hl ρ S hS H A h
  obtain ⟨rc, hrc⟩ := UpperTheory.Zero.LLC.recTExists F Ω A w h
  have hsp := totPar_spec (hX F Ω A w h rc hrc) n c a d ρ S hS
  have hu := (hsp (frob h)⁻¹ (by rw [deg_inv, deg_frob])).1
  have hx := ((H A h rc hrc).1 hl).isWDOf ((hG F Ω A w h).2.2.2 _ hu)
  have hw := hx.wdOf_eq hl
  obtain ⟨t, ht, φ, hφ, N, b, hN, -⟩ := hx
  refine ⟨(hN.unr_wdOf_iff hl ht ι).1 (by rw [hw]; exact hu), fun s hs => ?_⟩
  have hd : deg (⟨s, mem_Weil_of_isFrob h hs⟩ : Weil h) = 1 := deg_eq_one_iff.2 hs
  have := hN.charPol_wdOf hl ht ι (⟨s, mem_Weil_of_isFrob h hs⟩ : Weil h)⁻¹
  rw [hw, (hsp _ (by rw [deg_inv, hd])).2] at this
  exact this.symm
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TGalAEOf
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
open scoped commutatorElement
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Desc.W.GaloisCompatibilityAlmostEverywhere
section Loc
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
private theorem rc_chars (hE : GlobalTheory.Published.LanglandsExhaustionGL) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing)
    {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {rc : IrrGL (k := w.adicCompletion E) → WD h}
    (H : UpperTheory.Zero.LLC.LawsT a ha rc) (x : IrrGL (k := w.adicCompletion E)) (n : ℕ)
    (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)) (hs : HasSupport x.rep (chars ξ hξ))
    (hu : Unlinked (chars ξ hξ)) :
    (rc x).mono0 ∧ ∀ g : Weil h, (rc x).charPol g = ∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ)) := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨𝔪, hm⟩ := hE (w.adicCompletion E) x
  have hs' : HasSupport x.rep (msupp 𝔪) := GlobalTheory.LocGL.hasSupport_msupp_of_isL hZ _ 𝔪 x hm
  have he : chars ξ hξ = msupp 𝔪 :=
    GlobalTheory.LocGL.SupportUnique.hasSupport_unique GlobalTheory.RecT.geometricLemma_holds GlobalTheory.bernsteinZelevinskyFiniteness_holds
      hZ _ x _ _ hs hs'
  have hL := H.langlands 𝔪.toList x (by rw [Multiset.coe_toList]; exact hm)
  have hmem : ∀ Δ ∈ 𝔪, ∀ i : Fin Δ.len, Δ.term i ∈ chars ξ hξ := fun Δ hΔ i => by
    rw [he, msupp]
    exact Multiset.mem_bind.2 ⟨Δ, hΔ, Multiset.mem_map.2 ⟨i, Finset.mem_univ_val _, rfl⟩⟩
  have hlen : ∀ Δ ∈ 𝔪, Δ.len = 1 := by
    intro Δ hΔ
    by_contra hne
    have h2 : 1 < Δ.len := lt_of_le_of_ne Δ.len_pos (Ne.symm hne)
    refine hu _ (hmem Δ hΔ ⟨1, h2⟩) _ (hmem Δ hΔ ⟨0, Δ.len_pos⟩) ?_
    simp only [Segment.term, IrrGL.nu_nu]
    norm_num
  have hms : ∀ Δ ∈ 𝔪, Δ.ms = {Δ.first} := by
    intro Δ hΔ
    have e : Δ = Segment.single Δ.first Δ.isCusp_first := Segment.ext_first rfl (by rw [hlen Δ hΔ]; rfl)
    rw [e, Segment.ms_single]
    rfl
  have hsupp : msupp 𝔪 = 𝔪.map Segment.first := by
    rw [msupp, ← Multiset.bind_singleton]
    exact Multiset.bind_congr hms
  have hchar : ∀ y ∈ chars ξ hξ, ∃ j, y = IrrGL.ofChar (ξ j) (hξ j) := fun y hy => by
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hy
    exact ⟨j, rfl⟩
  have hfirst : ∀ Δ ∈ 𝔪, ∃ j, Δ.first = IrrGL.ofChar (ξ j) (hξ j) := fun Δ hΔ =>
    hchar _ (by rw [he, hsupp]; exact Multiset.mem_map_of_mem _ hΔ)
  have hsum : rc x = sumList (𝔪.toList.map fun Δ => rc Δ.first) := by
    rw [hL, segSum]
    congr 1
    apply List.map_congr_left
    intro Δ hΔ
    rw [hlen Δ (Multiset.mem_toList.1 hΔ)]
    simp only [Nat.cast_one, sub_self, zero_div]
    exact (GlobalTheory.WeilDeligne.charPol_lpTw_lpChar_lpSp E Ω A w h _).1
  have hpol1 : ∀ j (g : Weil h), (rc (IrrGL.ofChar (ξ j) (hξ j))).charPol g = X - C ((ξ j (a g) : ℂˣ) : ℂ) := by
    intro j g
    rw [H.one, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
    simp
  refine ⟨?_, fun g => ?_⟩
  · rw [hsum]
    have key : ∀ L : List (Segment (w.adicCompletion E)), (∀ Δ ∈ L, Δ ∈ 𝔪) →
        (sumList (L.map fun Δ => rc Δ.first)).mono0 := by
      intro L
      induction L with
      | nil =>
        intro _
        show (WD.lpZero (h := h)).mono0
        exact (WD.monodromyZero_ofWeilDeligneRepClass_iff _).2 rfl
      | cons Δ L ih =>
        intro hL'
        obtain ⟨j, hj⟩ := hfirst Δ (hL' Δ List.mem_cons_self)
        show (WD.lpSum _ _).mono0
        refine (WD.monomial_sum_iff _ _).2 ⟨?_, ih fun Δ' h' => hL' Δ' (List.mem_cons_of_mem _ h')⟩
        change (rc Δ.first).mono0
        rw [hj]
        exact WD.mono0_of_lpDim_eq_one (by rw [H.dim]; rfl)
    exact key _ fun Δ hΔ => Multiset.mem_toList.1 hΔ
  · rw [hsum, GlobalTheory.LocLanglands.CuspExt.charPol_sumList, List.map_map]
    have r1 : (∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ))) = ((chars ξ hξ).map fun y => (rc y).charPol g).prod := by
      rw [chars, Multiset.map_map, Finset.prod_eq_multiset_prod]
      exact congrArg Multiset.prod (Multiset.map_congr rfl fun j _ => (hpol1 j g).symm)
    rw [r1, he, hsupp, Multiset.map_map, ← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList]
    rfl
end Loc
private theorem norm_absPow_unif (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : Valued.v (ϖ : w.adicCompletion E) = WithZero.exp (-1 : ℤ)) :
    ‖((GlobalTheory.SmGL.absPow (w.adicCompletion E) (1 : ℂ) ϖ : ℂˣ) : ℂ)‖ = (Ideal.absNorm w.asIdeal : ℝ)⁻¹ := by
  have h1 : ord (w.adicCompletion E) ϖ = 1 := by
    rw [SphCompletion.ord_completion, hϖ, WithZero.log_exp]; simp
  rw [GlobalTheory.SmGL.val_absPow, Complex.cpow_one, GlobalTheory.LGrp.nabs_eq_zpow, h1, GlobalTheory.LFun.SatBoundGL.resCard_completion w]
  simp
private theorem unlinked_of_sat (hJ : GlobalTheory.Published.JacquetShalikaBound) (E : Type) [Field E] [NumberField E] [IsCMField E]
    (n : ℕ) (hn : 1 ≤ n) (π : CuspSub E n) (w : HeightOneSpectrum (𝓞 E)) (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ))
    (hξ : ∀ j, IsSmoothChar (ξ j)) (ϖ : (w.adicCompletion E)ˣ)
    (hϖ : Valued.v (ϖ : w.adicCompletion E) = WithZero.exp (-1 : ℤ))
    (hB : (CG.mk π).HasSat w (Finset.univ.val.map fun j => ξ j ϖ)) : Unlinked (chars ξ hξ) := by
  intro y hy z hz e
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
  obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hz
  simp only [IrrGL.nu, IrrGL.tw_ofChar] at e
  have e' := IrrGL.ofChar_inj.1 e
  have hval : ((ξ i ϖ : ℂˣ) : ℂ) = ((ξ j ϖ : ℂˣ) : ℂ) * ((GlobalTheory.SmGL.absPow (w.adicCompletion E) (1 : ℂ) ϖ : ℂˣ) : ℂ) := by
    rw [e']; rfl
  have hnorm : ‖((ξ i ϖ : ℂˣ) : ℂ)‖ = ‖((ξ j ϖ : ℂˣ) : ℂ)‖ * (Ideal.absNorm w.asIdeal : ℝ)⁻¹ := by
    rw [hval, norm_mul, norm_absPow_unif E w ϖ hϖ]
  obtain ⟨π₀, t, hu, he⟩ := CG.exists_isUnitary_twist_absPow (CG.mk π) hn
  have hT := (hB.twist_absPow (-t)).1
  have e0 : (CG.mk π).twist (GlobalTheory.HeckeGal.Model.absPow E (-t)) = π₀ := by
    rw [he, ← CG.twist_mul, mul_comm, CG.absPow_neg_mul, CG.twist_one]
  rw [e0] at hT
  set c := (GlobalTheory.HeckeGal.Model.absPow E (-t)).val w
  have hmem : ∀ m, ξ m ϖ * c ∈ (Finset.univ.val.map fun j => ξ j ϖ).map (· * c) := fun m =>
    Multiset.mem_map.2 ⟨ξ m ϖ, Multiset.mem_map.2 ⟨m, Finset.mem_univ_val _, rfl⟩, rfl⟩
  have hi := hJ E n π₀ hu w _ hT _ (hmem i)
  have hj := hJ E n π₀ hu w _ hT _ (hmem j)
  simp only [Units.val_mul, norm_mul] at hi hj
  have hq : (1 : ℝ) < (Ideal.absNorm w.asIdeal : ℝ) := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w
  set q : ℝ := (Ideal.absNorm w.asIdeal : ℝ)
  have hq0 : 0 < q := zero_lt_one.trans hq
  set s : ℝ := q ^ (1 / 2 : ℝ)
  have hs0 : 0 < s := Real.rpow_pos_of_pos hq0 _
  have hss : s * s = q := by
    rw [← Real.rpow_add hq0]; norm_num
  have hsn : q ^ (-(1 / 2) : ℝ) = s⁻¹ := Real.rpow_neg hq0.le _
  rw [hsn] at hi
  rw [hnorm] at hi
  set b := ‖((ξ j ϖ : ℂˣ) : ℂ)‖
  set C := ‖((c : ℂˣ) : ℂ)‖
  have key : b * C = q * (b * q⁻¹ * C) := by field_simp
  have h1 : s * (s⁻¹) < s * (b * q⁻¹ * C) := mul_lt_mul_of_pos_left hi.1 hs0
  rw [mul_inv_cancel₀ hs0.ne'] at h1
  have h2 : s * 1 < s * (s * (b * q⁻¹ * C)) := mul_lt_mul_of_pos_left h1 hs0
  rw [mul_one, ← mul_assoc, hss, ← key] at h2
  exact absurd hj.2 (not_lt.2 h2.le)
private theorem comm_one {G : Type} [Group G] {H : Type} [CommGroup H] (f : G →* H) (s t : G) : f ⁅s, t⁆ = 1 := by
  rw [map_commutatorElement]
  exact (Commute.all _ _).commutator_eq
private theorem rec_sat (hE : GlobalTheory.Published.LanglandsExhaustionGL) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing)
    (hJ : GlobalTheory.Published.JacquetShalikaBound) {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (n : ℕ) (hn : 1 ≤ n) (π : CuspSub E n) (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω)
    (h : IsPlaceOver A w) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ) (hB : (CG.mk π).HasSat w B)
    (hBσ : GlobalTheory.LFun.HasSatGL w σ.ρ B) (rc : IrrGL (k := w.adicCompletion E) → WD h) (hrc : UpperTheory.Zero.LLC.IsRecT h rc) :
    rc (algNorm σ) = satWD h n B ∧ UpperTheory.GalStar.Tor (rc (algNorm σ)) ∧ (rc (algNorm σ)).mono0 := by
  obtain ⟨a, ha, hL⟩ := hrc
  obtain ⟨ξ, hξ, ϖ, hsup, hunr, hϖ, rfl⟩ := GlobalTheory.T.supercuspidal_support_characters E n hn w σ B hBσ
  have hun : Unlinked (chars ξ hξ) := unlinked_of_sat hJ E n hn π w ξ hξ ϖ hϖ hB
  set s : ℂ := (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) with hs
  let ξ' : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ) := fun j => ξ j * GlobalTheory.SmGL.absPow _ s
  have hξ' : ∀ j, IsSmoothChar (ξ' j) := fun j => (hξ j).mul (GlobalTheory.LocGL.isSmoothChar_absPow _)
  have hnu := GlobalTheory.RoadU.TwistSupp.supp_nu_chars (w.adicCompletion E) (IrrGL.of σ.ρ σ.smooth σ.irred) n ξ ξ' hξ hξ' s
    (fun _ => rfl)
  have hsup' : HasSupport (algNorm σ).rep (chars ξ' hξ') := hnu.1.1 hsup
  have hun' : Unlinked (chars ξ' hξ') := hnu.2.1 hun
  have h2 := rc_chars hE hZ hL (algNorm σ) n ξ' hξ' hsup' hun'
  have h3 := GlobalTheory.SatChar.satWD_charPol_chars Ω E w A h n ξ ξ' (fun _ => rfl) hunr ϖ hϖ a ha
  have hm : (satWD h n (Finset.univ.val.map fun j => ξ j ϖ)).mono0 := by
    unfold satWD
    rw [WD.monomial_twist_iff]
    exact WD.unr_mono0 _ ((WD.unr_mk _).2 (WDRep.unr_diag _))
  refine ⟨GlobalTheory.WeakTheRep.eq_of_mono0_charPol _ _ h2.1 hm fun g => (h2.2 g).trans (h3 g).symm, fun u v => ?_, h2.1⟩
  show WD.charPol _ _ = _
  rw [h2.2, hL.dim]
  have h1 : ∀ j, ξ' j (a ⁅u, v⁆) = 1 := fun j => by
    rw [map_commutatorElement]
    exact comm_one (ξ' j) (a u) (a v)
  simp only [h1]
  simp
  rfl
private theorem val_frob (q a : ℕ) (b : ℂˣ) :
    ((q : ℂ) ^ ((((1 : ℝ) - a) / 2 : ℝ) : ℂ)) ^ (-1 : ℤ) * ((b : ℂ)⁻¹) ^ (-1 : ℤ) =
      (((q : ℝ) ^ (((a : ℝ) - 1) / 2) : ℝ) : ℂ) * (b : ℂ) := by
  have h1 : (((q : ℝ) ^ (((a : ℝ) - 1) / 2) : ℝ) : ℂ) = ((q : ℂ) ^ ((((1 : ℝ) - a) / 2 : ℝ) : ℂ))⁻¹ := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg _), ← Complex.cpow_neg]
    congr 1
    push_cast
    ring
  rw [h1, zpow_neg_one, zpow_neg_one, inv_inv]
end UpperTheory.V.Z.Desc.W.GaloisCompatibilityAlmostEverywhere
open UpperTheory.V.Z.Desc.W.GaloisCompatibilityAlmostEverywhere in
theorem UpperTheory.V.Z.Desc.W.galAEOf_alt  :
    _root_.UpperTheory.V.Z.Desc.W.GalAEOfAlt := by
  intro P hRow E Ω _ _ _ _ _ _ l _ ι a ha π hc s hreg
  have hp := GlobalTheory.HeightCounting.Blocks.isPolarized_twist_absPow hc s
  have hpp : GlobalTheory.ContraPair.PolarizedPair (π.twist (GlobalTheory.HeckeGal.Model.absPow E s)) _ :=
    ⟨hp.sign, GlobalTheory.T.cuspContragredientIsCMConjTwist_of_paired_invTranspose E a _ (GlobalTheory.GalOfCusp.compNorm E _) (P.litN.aut.gk E a _) hp.dual⟩
  obtain ⟨r, wt, HT, H⟩ := hRow E Ω l ι a ha _ _ hreg hpp
  refine ⟨r, H.cont, fun w hl B hB A hA g hg => ?_⟩
  obtain ⟨rc, hrc⟩ := UpperTheory.Zero.LLC.recTExists E Ω A w hA
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := _root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P E a (π.twist (GlobalTheory.HeckeGal.Model.absPow E s)) w
  have hBσ : GlobalTheory.LFun.HasSatGL w σ.ρ B := ((_root_.UpperTheory.V.Af.satake_local_of_printed_results P E a w σ).2 _ _ (hiso σ hσ) B).1 hB
  obtain ⟨e1, hT, hM⟩ := rec_sat P.litN.loc.exh P.litN.loc.zel P.litN.aut.js.2 a ha _ w A hA σ B hB hBσ rc hrc
  have e : wdOf hA hl ι r = satWD hA a B := ((H.away w hl A hA rc hrc σ hσ).tor hT hM).trans e1
  let φ : Weil hA := ⟨g, mem_Weil_of_isFrob hA hg⟩
  have hφ : deg φ = 1 := deg_eq_one_iff.2 hg
  have c := charPol_wdOf (h := hA) hl ι (Units.continuous_val.comp H.cont) φ⁻¹
  rw [e, GlobalTheory.SatChar.charPol_satWD, deg_inv, hφ] at c
  refine (show _ = _ from c.symm).trans ?_
  simp only [UpperTheory.V.Af.algSat, Multiset.map_map, Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton]
  refine congrArg _ (Multiset.map_congr rfl fun b _ => ?_)
  simp only [Function.comp_apply]
  rw [val_frob]
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypePSTAltAlt
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.V.Z.J.D
theorem typePST'_alt : _root_.UpperTheory.V.Z.J.D.PotentiallySemistableType := _root_.UpperTheory.V.Z.J.D.type_pst_of_type_v _root_.UpperTheory.V.Z.J.D.type_v_statement
end UpperTheory.V.Z.J.D
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WinConv
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Win
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
theorem exRec'_alt (_N : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (h : IsPlaceOver A w) : ∃ rc, IsRecT h rc := recTExists E Ω A w h
theorem exists_rec_alt_alt_alt : _root_.UpperTheory.V.Af.Hypotheses'.exists_rec_ty := by
  unfold _root_.UpperTheory.V.Af.Hypotheses'.exists_rec_ty
  intros
  exact _root_.UpperTheory.V.Z.Win.exRec'_alt (by assumption : _root_.UpperTheory.V.Af.Hypotheses').litN _
end UpperTheory.V.Z.Win
end
end
end

