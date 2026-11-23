module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1790
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarModelLocalTriple
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1784
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0395
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1521
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviCentreFlowConjScalesHaarIsotropicUnipotent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1736
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1556
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1786
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1763
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1792
public import Formalism.PieriBlockIdeals.PieriColumnMinors.LargeParameterEstimates

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightRhoThickPlaceCentreWindow
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ExpTie.Lift

variable {D : D7}

theorem thick_of_mem (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau) (hv : ValsAt L j τ)
    (hτ : τ ∈ (wts L j).T2) :
    (parOf L j).Thick ((wts L j).e τ) ∧ ((wts L j).xp τ : ℝ) ≤ (parOf L j).h := by
  have hmem : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces := by
    simpa [wts] using hτ
  have hm2 := D.R.two_le_m
  have hj := j.2
  have h1 := L.win_thick ((j : ℕ) + 1) (by omega) (by omega) τ hmem
  have h2 := L.win_thick D.R.m (by omega) le_rfl τ hmem
  have hc := c_le L j τ hv
  have hb : (parOf L j).b = L.sc.b := rfl
  refine ⟨?_, ?_⟩
  · show (parOf L j).b ≤ wj D ((j : ℕ) + 1) τ ∧ wj D ((j : ℕ) + 1) τ ≤ (parOf L j).b + L.etaSz + 1
    rw [hb]; exact h1
  · have hfl : ((wts L j).xp τ : ℝ) ≤ cT j τ + L.Sc := by
      show ((⌊cT j τ + L.Sc⌋ : ℤ) : ℝ) ≤ cT j τ + L.Sc
      exact Int.floor_le _
    have hc' : cT j τ ≤ wj D D.R.m τ + ((D.R.t : ℝ) - 1) / 2 := hc
    have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
    show ((wts L j).xp τ : ℝ) ≤ (parOf L j).b + L.Sc + L.etaSz + (D.R.t : ℝ) + 1
    rw [hb]
    linarith [h2.2]

end GlobalTheory.ExpTie.Lift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarModelLocalTripleStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_bar_model_local_triple : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v)
    (ι : (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι →
    ∀ (d' : Darboux (symp (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J)) (Fin a' × Fin (a + a'))),
    (∀ x : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.W.J) (dbl (incM F G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')))),
    IsDblCoord (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J) d' dd →
    ∀ (f : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f → f * f = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) →
    f * cA σ f = -algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) → piW t f = 1 → piW (t.comp σ) f = -1 →
    ∀ w : UG (cA σ) (dbl (incM F G.V'.J)),
      ((w : GL (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
        Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin a') (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) (f • 1) (f • 1)
          ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) →
    ∀ S : (((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v) → ℂ) →
        ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v) → ℂ,
    (∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      S Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v)) →
    (∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      ∀ Φ' ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v), ∀ c : ℂ, S (c • Φ + Φ') = c • S Φ + S Φ') →
    (∀ u, At (evFin F v) u → ∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      S (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v u) Φ) =
        schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (actB (cA σ) w u)) (S Φ)) →
    ∃ c : ℂ, ∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      GlobalTheory.SwapSlice.sliceT ι (S Φ) = c • (GlobalTheory.SwapSlice.sliceT ι Φ ∘ GlobalTheory.SwapSlice.swapNeg) := by
  first | exact @GlobalTheory.SwapSchur.sliceT_swap_eq_smul | exact GlobalTheory.SwapSchur.sliceT_swap_eq_smul | (intros; apply GlobalTheory.SwapSchur.sliceT_swap_eq_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalElementsCommuteDistinctFinitePlaces
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocComm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem ext_cmp {z₁ z₂ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E}
    (h : ∀ w, GlobalTheory.HeckeRowsCompare.cmp D w z₁ = GlobalTheory.HeckeRowsCompare.cmp D w z₂) : z₁ = z₂ := by
  refine (Algebra.TensorProduct.basis (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (Module.finBasis D.host.F D.host.E)).ext_elem fun i => ?_
  refine FiniteAdeleRing.ext _ fun w => ?_
  have e := congrArg (fun z => (Algebra.TensorProduct.basis (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F w)
    (Module.finBasis D.host.F D.host.E)).repr z i) (h w)
  simp only [GlobalTheory.HeckeRowsCompare.cmp, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at e
  rw [GlobalTheory.HeckeRowsCompare.repr_map, GlobalTheory.HeckeRowsCompare.repr_map] at e
  exact e

theorem mul_comm_of_locAt (V : Formalism.BasicNotions.TH.HSp D) {v v' : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ≠ v') {x y : Bridge.Gf V}
    (hx : GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt V v x) (hy : GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt V v' y) : x * y = y * x := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  apply ext_cmp
  intro w
  have hm : ∀ a b : Bridge.Gf V,
      GlobalTheory.HeckeRowsCompare.cmp D w ((a * b : Bridge.Gf V).1.1 i j) =
        ((a.1.1.map (GlobalTheory.HeckeRowsCompare.cmp D w)) * (b.1.1.map (GlobalTheory.HeckeRowsCompare.cmp D w))) i j := by
    intro a b
    rw [← Matrix.map_mul]
    rfl
  show GlobalTheory.HeckeRowsCompare.cmp D w ((x * y : Bridge.Gf V).1.1 i j) = GlobalTheory.HeckeRowsCompare.cmp D w ((y * x : Bridge.Gf V).1.1 i j)
  rw [hm, hm]
  by_cases hw : w = v
  · subst hw
    have h1 : y.1.1.map (GlobalTheory.HeckeRowsCompare.cmp D w) = 1 := hy w hv
    rw [h1, mul_one, one_mul]
  · have h1 : x.1.1.map (GlobalTheory.HeckeRowsCompare.cmp D w) = 1 := hx w hw
    rw [h1, mul_one, one_mul]

theorem mul_comm_of_isLocEnv : ∀ {D : D7} (V : Formalism.BasicNotions.TH.HSp D) {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (i i' : ok × ℕ)
    (x y : Bridge.Gf V), (pl i.1).under (𝓞 D.host.F) ≠ (pl i'.1).under (𝓞 D.host.F) → isLocEnv V pl ok i x →
      isLocEnv V pl ok i' y → x * y = y * x := by
  intro D V Pl0 pl ok i i' x y hv hx hy
  exact mul_comm_of_locAt V hv
    (GlobalTheory.Mem.R3.LiftInertChi.locAt_of_isLocElt V _ x ((GlobalTheory.Hk3Split.isLabElt_of_isTEnv V pl ok i x).2.1 hx))
    (GlobalTheory.Mem.R3.LiftInertChi.locAt_of_isLocElt V _ y ((GlobalTheory.Hk3Split.isLabElt_of_isTEnv V pl ok i' y).2.1 hy))

end GlobalTheory.LocComm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapEqOneOfIsLocEnv
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EvLocal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem map_eq_zero_of_repr {F A E R ι : Type} [Field F] [CommRing A] [CommRing E] [Algebra F A] [Algebra F E] [CommRing R]
    [Fintype ι] (b : Module.Basis ι F E) (φ : A ⊗[F] E →+* R) (z : A ⊗[F] E)
    (hc : ∀ i, φ (((Algebra.TensorProduct.basis A b).repr z i) ⊗ₜ[F] 1) = 0) : φ z = 0 := by
  have hs : z = ∑ i, ((Algebra.TensorProduct.basis A b).repr z i ⊗ₜ[F] (1 : E)) * ((1 : A) ⊗ₜ[F] b i) := by
    conv_lhs => rw [← (Algebra.TensorProduct.basis A b).sum_repr z]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul', smul_eq_mul,
      one_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hs, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_mul, hc i, zero_mul]

theorem ev_eq_zero {D : D7} {l : ℕ} [Fact l.Prime] {inc : D.host.E →+* PadicAlgCl l}
    {ev : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E →+* PadicAlgCl l} (hev : EvOk inc ev)
    (z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)
    (hz : ∀ w : HeightOneSpectrum (𝓞 D.host.F), ((l : ℕ) : 𝓞 D.host.F) ∈ w.asIdeal → GlobalTheory.HeckeRowsCompare.cmp D w z = 0) :
    ev z = 0 := by
  refine map_eq_zero_of_repr (A := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (Module.finBasis D.host.F D.host.E) ev z fun i => ?_
  refine hev.2.2.1 _ fun w hw => ?_
  have e := congrArg (fun z => (Algebra.TensorProduct.basis (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F w)
    (Module.finBasis D.host.F D.host.E)).repr z i) (hz w hw)
  simp only [GlobalTheory.HeckeRowsCompare.cmp, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at e
  rw [GlobalTheory.HeckeRowsCompare.repr_map, map_zero] at e
  exact e

theorem map_eq_one_of_isLocEnv : ∀ {D : D7} (V : Formalism.BasicNotions.TH.HSp D) {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (i : ok × ℕ) (x : Bridge.Gf V) {l : ℕ} [Fact l.Prime] (inc : D.host.E →+* PadicAlgCl l) (ev : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E →+* PadicAlgCl l), EvOk inc ev → ((l : ℕ) : 𝓞 D.host.E) ∉ (pl i.1.1).asIdeal → isLocEnv V pl ok i x → ((x : GL (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map ev = 1 := by
  intro D V Pl0 pl ok i x l _ inc ev hev hl hx
  have hloc : GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt V ((pl i.1).under (𝓞 D.host.F)) x :=
    GlobalTheory.Mem.R3.LiftInertChi.locAt_of_isLocElt V _ x ((GlobalTheory.Hk3Split.isLabElt_of_isTEnv V pl ok i x).2.1 hx)
  ext a b
  have h0 : ev (x.1.1 a b - (1 : Matrix (Fin V.rank) (Fin V.rank) _) a b) = 0 := by
    refine ev_eq_zero hev _ fun w hw => ?_
    have hne : w ≠ (pl i.1).under (𝓞 D.host.F) := by
      rintro rfl
      apply hl
      have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (l : 𝓞 D.host.F) ∈ (pl i.1.1).asIdeal := hw
      rwa [map_natCast] at h2
    have h1 : x.1.1.map (GlobalTheory.HeckeRowsCompare.cmp D w) = 1 := hloc w hne
    have h3 := congrFun (congrFun h1 a) b
    rw [Matrix.map_apply] at h3
    rw [map_sub, h3, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [map_sub, sub_eq_zero] at h0
  rw [Matrix.map_apply]
  refine h0.trans ?_
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end GlobalTheory.EvLocal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureHeightShellLeIsotropicFrameQuotient
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ResidueEisenstein

theorem measure_shell_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), DataJ σ J X Y L a h → ∀ (μ : Measure (GAd σ J)) (D : Set (GAd σ J)), μ.IsHaarMeasure → IsFundamentalDomain ((ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤) : Subgroup (GAd σ J)) D μ → ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ j : ℕ, μ.restrict D {x | Real.exp (-(j + 1 : ℝ)) < h x ∧ h x ≤ Real.exp (-(j : ℝ))} ≤ B * ENNReal.ofReal (Real.exp (((n : ℝ) - (r + 1)) * j)) := by
  intro F E _ _ _ _ _ σ n J r X Y L a h hD μ D hμ hFD
  obtain ⟨b, hb⟩ := _root_.GlobalTheory.ResidueEisenstein.exists_isFlowJ F E σ n J r X Y hD.cm hD.herm hD.witt
  obtain ⟨-, hHt, hlaw⟩ := _root_.GlobalTheory.ResidueEisenstein.HtCont.isCompact_isHt_scales F E σ n J r X Y L a h hD
  obtain ⟨-, ν, DN, hν, hDN, hone⟩ := unipRad_frame_closed_mass_one F E σ n J r X Y hD.cm hD.herm hD.witt
  have hmod := _root_.GlobalTheory.ResidueEisenstein.ModConj.modulus_conj_flow F E σ n J r X Y hD.cm hD.herm hD.witt b hb ν hν
  obtain ⟨π, DM, hSL⟩ := _root_.GlobalTheory.ResidueEisenstein.semiLat_frameGrp F E σ n J r X Y hD.cm hD.herm hD.witt ν DN hν hDN hone
  obtain ⟨C, hC, hslab⟩ := _root_.GlobalTheory.ResidueEisenstein.slab_subset F E σ n J r X Y L a h hD b hb
  haveI : Countable (ratPts σ J) := inferInstance
  haveI : Countable ((ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤) : Subgroup (GAd σ J)) :=
    Function.Injective.countable (Subgroup.inclusion_injective
      (inf_le_left : ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤ ≤ ratPts σ J))
  obtain ⟨B, hB, hsh⟩ := GlobalTheory.ResLine.modulus_mul_measure_shell_le (GAd σ J) _ _ _ ν π DN DM hSL μ D hμ hFD C hC
  refine ⟨B, hB, fun j => ?_⟩
  have hS : MeasurableSet {x | Real.exp (-(j + 1 : ℝ)) < h x ∧ h x ≤ Real.exp (-(j : ℝ))} :=
    (measurableSet_Ioc (a := Real.exp (-(j + 1 : ℝ))) (b := Real.exp (-(j : ℝ)))).preimage hHt.cont.measurable
  have key := hsh (b j) _ (fun m hm => hb.comm j m (Subgroup.mem_inf.mp hm).1) (hmod j) _ hS (fun x hx => by
    obtain ⟨β, hβ, e⟩ := hb.onX j
    have e2 : h (b j * x) = Real.exp j * h x := by rw [hlaw _ β hβ, e]
    have hp : 0 < Real.exp (j : ℝ) := Real.exp_pos _
    refine hslab _ ?_ ?_
    · rw [e2]
      have : Real.exp (-1) = Real.exp j * Real.exp (-(j + 1 : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hx.1.le hp.le
    · rw [e2]
      have : (1 : ℝ) = Real.exp j * Real.exp (-(j : ℝ)) := by rw [← Real.exp_add]; simp
      rw [this]
      exact mul_le_mul_of_nonneg_left hx.2 hp.le)
  rw [Measure.restrict_apply hS]
  have e1 : ENNReal.ofReal (Real.exp (((n : ℝ) - (r + 1)) * j)) * ENNReal.ofReal (Real.exp (-(((n : ℝ) - (r + 1)) * j))) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; simp
  calc _ = ENNReal.ofReal (Real.exp (((n : ℝ) - (r + 1)) * j)) * (ENNReal.ofReal (Real.exp (-(((n : ℝ) - (r + 1)) * j))) * _) := by
        rw [← mul_assoc, e1, one_mul]
    _ ≤ ENNReal.ofReal (Real.exp (((n : ℝ) - (r + 1)) * j)) * B := by gcongr
    _ = _ := mul_comm _ _

end GlobalTheory.ResidueEisenstein
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelCuspFormsSpan
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn GlobalTheory.ShareOn.Reading

set_option autoImplicit false

namespace GlobalTheory.ShareOn.Reading

section Onto
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ss_transport {X X' : Data E r} (hX : X = X') {Ψ : Finset (E →+* ℂ)} (h1 : X.Ψ = Ψ) (h2 : X'.Ψ = Ψ)
    (g : Frame Ψ r → ℂ) (la : Wt Ψ r) (la' : Wt X'.Ψ r)
    (hla : ∀ τ (t1 : τ ∈ Ψ) (t2 : τ ∈ X'.Ψ) a, la ⟨τ, t1⟩ a = la' ⟨τ, t2⟩ a)
    (hg : (fun x => g (castFrame h1 x)) ∈ X.SS (castWt h1 la)) :
    (fun y => g (castFrame h2 y)) ∈ X'.SS la' := by
  subst hX
  have hw : castWt h1 la = la' := by
    funext τ a
    exact hla τ.1 _ τ.2 a
  rw [← hw]
  exact hg

end Onto

theorem rdFun_onto {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz}
    {r : TwoRuns p.T p.P.Gp} (h : RunsOk (fw2 p) r) {i : Fin D.R.m} {C : Type} [MulAction p.P.Gp C]
    {M : TwoLevels D.host.E D.R.r p.P.Gp C} {ka : Wt M.Ψ D.R.r} {v : HeightOneSpectrum (𝓞 D.what₂.LL)}
    {e : C ≃ ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp}
    (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c))
    (hb : ∀ c τ (h1 : τ ∈ M.Ψ) (h2 : τ ∈ (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).Ψ) a,
      ka ⟨τ, h1⟩ a = laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) (e c) ⟨τ, h2⟩ a) :
    0 < badN D → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → ∀ (G : C → Frame M.Ψ D.R.r → ℂ), G ∈ M.SS ka →
      ∃ (m : ℕ) (α : Fin m → ℂ) (Fs : Fin m → (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)),
        ∀ c, ∀ x ∈ M.dom, G c x = ∑ k, α k * rdFun h ha (Fs k) c x := by
  intro hN hnV G hG
  classical
  have ha' : ∀ k, (M.comp (e.symm k)).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X k := fun k => by
    rw [ha (e.symm k), e.apply_symm_apply]
  have hΨk : ∀ k, M.Ψ = (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X k).Ψ := fun k => by
    rw [← ha' k]; exact (M.comp_Ψ _).symm
  have hb' : ∀ k τ (h1 : τ ∈ M.Ψ) (h2 : τ ∈ (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X k).Ψ) a,
      ka ⟨τ, h1⟩ a = laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) k ⟨τ, h2⟩ a := by
    intro k
    obtain ⟨c, rfl⟩ := e.surjective k
    exact hb c

  have hf : 0 < D.R.f := lt_of_lt_of_le (lt_of_le_of_lt (Nat.zero_le _) i.2) D.R.m_le_f
  have hTau : Nonempty D.what₂.Tau := by
    rw [← Fintype.card_pos_iff, D.what₂.card_Tau]; exact hf
  obtain ⟨τ0⟩ := hTau
  have hn : 8 * D.R.f * D.R.r + 4 ≤ (p.κ i).n := by
    rw [(p.fw.kap i τ0).2.2]; exact hnV
  have hOnto : RdOnto (h.laws v).p ((i : ℕ) + 1) (p.κ i) :=
    GlobalTheory.Shares.rdOnto_rec GlobalTheory.chartIndependence_unconditional D (r.used v).full.toTop (h.laws v).p ((i : ℕ) + 1)
      (GlobalTheory.OnTies.inR_succ i) (h.laws v).sh
      (GlobalTheory.RunIn.gamAt_of_lawsCore D _ (h.laws v).p.toLawsCore) hN
      (GlobalTheory.Dict.gram_xi_eq_of_lawsFull (h.laws v)) (p.κ i) hn
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA (h.laws v).p (GlobalTheory.OnTies.inR_succ i) _ (lastPos_kappa p i))
  let f : ∀ k : ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp, Frame (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X k).Ψ D.R.r → ℂ := fun k y => G (e.symm k) (castFrame (hΨk k).symm y)
  have hfm : ∀ k, f k ∈ (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X k).SS (laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) k) := fun k =>
    ss_transport (ha' k) (M.comp_Ψ (e.symm k)) (hΨk k).symm (G (e.symm k)) ka _ (hb' k) (hG (e.symm k))
  obtain ⟨m, α, Fs, -, hsum⟩ := hOnto f hfm
  refine ⟨m, α, Fs, fun c x hx => ?_⟩
  have hy := (mem_dom_iff ha c x).2 hx
  have key := hsum (e c) _ hy
  have hl : f (e c) (castFrame (psi_eq ha c) x) = G c x := by
    show G (e.symm (e c)) (castFrame (hΨk (e c)).symm (castFrame (psi_eq ha c) x)) = G c x
    have hc : e.symm (e c) = c := e.symm_apply_apply c
    have hx' : castFrame (hΨk (e c)).symm (castFrame (psi_eq ha c) x) = x := rfl
    rw [hx', hc]
  rw [← hl, key]
  rfl

end GlobalTheory.ShareOn.Reading
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterLargeAllPointsBound
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie

namespace GlobalTheory.ExpTie

open Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.LargeParameterEstimates

theorem large_of_rows_pow {P : Par} {X' A : ℝ} (hH : P.Hyp) (hR : Rows P X' A) (hB : Big P.L P.x X' A)
    (h45 : P.b ^ ((4 : ℝ) / 5) ≤ P.w'' / P.S)
    (hpow : 4 * P.x ^ 2 * P.L ^ 2 * P.b ^ ((4 : ℝ) / 7) < P.b ^ ((4 : ℝ) / 5)) : P.Large := by
  have ht4 : (4 : ℝ) ≤ P.t := by
    have := hH.t_ge; have : 4 ≤ P.t := by omega
    exact_mod_cast this
  have hA1 : 1 ≤ A := by linarith [hR.t_le]
  have hx := hB.x_ge
  have hL := hB.L_ge
  have hA7 : A ^ 7 ≤ P.b := by
    have h3 := hB.b3
    have hx2 : (1 : ℝ) ≤ P.x ^ 2 := one_le_pow₀ (by linarith)
    have hL3 : (1 : ℝ) ≤ P.L ^ 3 := one_le_pow₀ (by linarith)
    have hA70 : 0 ≤ A ^ 7 := by positivity
    have : A ^ 7 ≤ 40 * A ^ 7 * P.x ^ 2 * P.L ^ 3 := by
      have h1 : (1 : ℝ) ≤ 40 * P.x ^ 2 * P.L ^ 3 := by nlinarith
      nlinarith
    exact this.trans h3
  have hA4 : A ^ 4 ≤ P.b ^ ((4 : ℝ) / 7) := by
    have e : (A ^ 7) ^ ((4 : ℝ) / 7) = A ^ 4 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      norm_num
    rw [← e]
    exact Real.rpow_le_rpow (by positivity) hA7 (by norm_num)
  refine Formalism.CohomologicalDescent.LargeParameterEstimates.large_bound_of_constraints P X' A hH hR hB h45 ?_
  have hc : 0 ≤ 4 * P.x ^ 2 * P.L ^ 2 := by positivity
  calc 4 * A ^ 4 * P.x ^ 2 * P.L ^ 2 = (4 * P.x ^ 2 * P.L ^ 2) * A ^ 4 := by ring
    _ ≤ (4 * P.x ^ 2 * P.L ^ 2) * P.b ^ ((4 : ℝ) / 7) := mul_le_mul_of_nonneg_left hA4 hc
    _ = 4 * P.x ^ 2 * P.L ^ 2 * P.b ^ ((4 : ℝ) / 7) := by ring
    _ < P.b ^ ((4 : ℝ) / 5) := hpow

theorem w_over_S_real {x e k n Δ a1 a2 : ℝ} (hx : 0 < x) (hk : 0 ≤ k) (hn : 0 < n) (hS : 0 < k * (4 * Δ))
    (hkx : k ≤ x ^ a1) (hnx : n ≤ x ^ a2) (hΔ : Δ ≤ Real.exp (x ^ (e / 4) / 2))
    (E1 : 4 * x ^ (a1 + a2) ≤ Real.exp (1 / 10 * x ^ e)) (E2 : 20 * x ^ (e / 3) ≤ x ^ e)
    (E3 : 10 * x ^ (e / 4) ≤ x ^ e) :
    Real.exp (x ^ e) ^ ((4 : ℝ) / 5) ≤ x * Real.exp (x ^ e) / Real.exp (x ^ (e / 3)) / (x * n) / (k * (4 * Δ)) := by
  have hΔ0 : 0 ≤ Δ := by
    by_contra h; push_neg at h; nlinarith
  have hrhs : x * Real.exp (x ^ e) / Real.exp (x ^ (e / 3)) / (x * n) = Real.exp (x ^ e - x ^ (e / 3)) / n := by
    rw [Real.exp_sub]; field_simp
  rw [hrhs, le_div_iff₀ hS, ← Real.exp_mul, le_div_iff₀ hn]
  have hkn : k * n ≤ x ^ (a1 + a2) := by
    rw [Real.rpow_add hx]; exact mul_le_mul hkx hnx hn.le (by positivity)
  have h1 : k * (4 * Δ) * n ≤ Real.exp (1 / 10 * x ^ e) * Real.exp (x ^ (e / 4) / 2) := by
    calc k * (4 * Δ) * n = (4 * (k * n)) * Δ := by ring
      _ ≤ (4 * x ^ (a1 + a2)) * Real.exp (x ^ (e / 4) / 2) := by
          apply mul_le_mul (by linarith) hΔ hΔ0 (by positivity)
      _ ≤ Real.exp (1 / 10 * x ^ e) * Real.exp (x ^ (e / 4) / 2) :=
          mul_le_mul_of_nonneg_right E1 (by positivity)
  rw [← Real.exp_add] at h1
  have h2 : Real.exp (1 / 10 * x ^ e + x ^ (e / 4) / 2) ≤ Real.exp (x ^ e * (1 / 5) - x ^ (e / 3)) :=
    Real.exp_le_exp.2 (by linarith)
  have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) (Real.exp_pos (x ^ e * ((4 : ℝ) / 5))).le
  rw [← Real.exp_add] at h3
  have e4 : x ^ e * ((4 : ℝ) / 5) + (x ^ e * (1 / 5) - x ^ (e / 3)) = x ^ e - x ^ (e / 3) := by ring
  rw [e4] at h3
  calc Real.exp (x ^ e * ((4 : ℝ) / 5)) * (k * (4 * Δ)) * n
      = Real.exp (x ^ e * ((4 : ℝ) / 5)) * (k * (4 * Δ) * n) := by ring
    _ ≤ _ := h3

theorem pow_real {x e : ℝ} (hx : 0 < x) (E : 5 * x ^ (2 + 2 * e) ≤ Real.exp (8 / 35 * x ^ e)) :
    4 * x ^ 2 * (x ^ e) ^ 2 * Real.exp (x ^ e) ^ ((4 : ℝ) / 7) < Real.exp (x ^ e) ^ ((4 : ℝ) / 5) := by
  rw [← Real.exp_mul, ← Real.exp_mul]
  have e1 : x ^ (2 + 2 * e) = x ^ 2 * (x ^ e) ^ 2 := by
    rw [Real.rpow_add hx, Real.rpow_two, mul_comm 2 e, Real.rpow_mul hx.le, Real.rpow_two]
  rw [e1] at E
  have hp : 0 < x ^ 2 * (x ^ e) ^ 2 := by have := Real.rpow_pos_of_pos hx e; positivity
  have h1 : 4 * x ^ 2 * (x ^ e) ^ 2 < Real.exp (8 / 35 * x ^ e) := by linarith
  have h2 := mul_lt_mul_of_pos_right h1 (Real.exp_pos (x ^ e * ((4 : ℝ) / 7)))
  rw [← Real.exp_add] at h2
  have e2 : 8 / 35 * x ^ e + x ^ e * ((4 : ℝ) / 7) = x ^ e * ((4 : ℝ) / 5) := by ring
  rwa [e2] at h2

end GlobalTheory.ExpTie

namespace GlobalTheory.ExpTie

open Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.LargeParameterEstimates

theorem ev_large (eps : ℝ) (he : 0 < eps) : ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x →
    0 < x ∧
    4 * x ^ ((9 / 2 + 10 * eps + eps / 100) + (2 + 8 * eps + eps / 100)) ≤ Real.exp (1 / 10 * x ^ eps) ∧
    20 * x ^ (eps / 3) ≤ x ^ eps ∧ 10 * x ^ (eps / 4) ≤ x ^ eps ∧
    5 * x ^ (2 + 2 * eps) ≤ Real.exp (8 / 35 * x ^ eps) := by
  have E1 := Formalism.CohomologicalDescent.LargeParameterEstimates.eventually_power_le_exp_mul_power 4 ((9 / 2 + 10 * eps + eps / 100) + (2 + 8 * eps + eps / 100)) (1 / 10) eps
    (by norm_num) he
  have E4 := Formalism.CohomologicalDescent.LargeParameterEstimates.eventually_power_le_exp_mul_power 5 (2 + 2 * eps) (8 / 35) eps (by norm_num) he
  have E2 : ∀ᶠ x : ℝ in Filter.atTop, 20 ≤ x ^ (2 * eps / 3) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _
  have E3 : ∀ᶠ x : ℝ in Filter.atTop, 10 ≤ x ^ (3 * eps / 4) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _
  have E : ∀ᶠ x : ℝ in Filter.atTop, 0 < x ∧
      4 * x ^ ((9 / 2 + 10 * eps + eps / 100) + (2 + 8 * eps + eps / 100)) ≤ Real.exp (1 / 10 * x ^ eps) ∧
      20 * x ^ (eps / 3) ≤ x ^ eps ∧ 10 * x ^ (eps / 4) ≤ x ^ eps ∧
      5 * x ^ (2 + 2 * eps) ≤ Real.exp (8 / 35 * x ^ eps) := by
    filter_upwards [E1, E2, E3, E4, Filter.eventually_gt_atTop 0] with x e1 e2 e3 e4 hx
    refine ⟨hx, e1, ?_, ?_, e4⟩
    · have s : x ^ eps = x ^ (eps / 3) * x ^ (2 * eps / 3) := by
        rw [← Real.rpow_add hx]; congr 1; ring
      have := Real.rpow_pos_of_pos hx (eps / 3)
      rw [s]; nlinarith
    · have s : x ^ eps = x ^ (eps / 4) * x ^ (3 * eps / 4) := by
        rw [← Real.rpow_add hx]; congr 1; ring
      have := Real.rpow_pos_of_pos hx (eps / 4)
      rw [s]; nlinarith
  exact Filter.eventually_atTop.1 E

end GlobalTheory.ExpTie
end

