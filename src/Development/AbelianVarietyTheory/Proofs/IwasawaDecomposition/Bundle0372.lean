module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Formalism.LocalToGlobal.Columns.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0207
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0346
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0095
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeUOperatorRationalInvertibleRamifiedForms
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Formalism.LocalToGlobal.HermitianColumns.Bundle0004
public import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0356
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0357

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCompletedSelfDualLatticeIffIntegralStdFrame
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

namespace GlobalTheory.Mem.SDFrameStd

theorem lamHat_iff_int : ∀ {D : D7} (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V 1 Λ 1 → ∀ y : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E, y ∈ Formalism.L2.NTheta.LamHat V ↔ ∀ j, swapAE D (y j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D V Λ hβ y
  obtain ⟨c, hf, -, -, h1, h2⟩ := hβ
  have hset : (Λ : Set (Fin V.rank → D.host.E)) = L0c D V := by
    ext x
    constructor
    · intro hx
      have := h2 x hx
      simpa using this
    · intro hx
      have := h1 x hx
      simpa using this
  have e1 : y ∈ Formalism.L2.NTheta.LamHat V ↔ (fun i => GlobalTheory.LevSplit.swp D.host.F D.host.E (y i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
    rw [← GlobalTheory.LevSplit.latHat_iff Λ y, hset]
  rw [e1, hf]
  simp only [inv_one, Units.val_one, one_mulVec]
  rfl

end GlobalTheory.Mem.SDFrameStd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemHeightOneSpectrumIffAdditiveValuationPos
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3


open Classical in
noncomputable def pickIxTw {B : Base} {px : PreX B.toPre} (I : Col2.ColIn B px) (χ : Formalism.L2.Host.HChar B.host.E) : I.ι :=
  if h : ∃ a, I.xi a = χ then h.choose else I.mu0

theorem xi_pickIxTw {B : Base} {px : PreX B.toPre} (I : Col2.ColIn B px) {χ : Formalism.L2.Host.HChar B.host.E}
    (h : χ ∈ Set.range I.xi) : I.xi (pickIxTw I χ) = χ := by
  have h' : ∃ a, I.xi a = χ := h
  unfold pickIxTw
  rw [dif_pos h']
  exact h'.choose_spec

theorem plc_eq_of_natCast_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {p : ℕ} (hp : p.Prime)
    (h : (p : 𝓞 F) ∈ v.asIdeal) : Formalism.EigenvalueLevelCeiling.plc v = p := by
  have hd : Formalism.EigenvalueLevelCeiling.plc v ∣ p := by
    unfold Formalism.EigenvalueLevelCeiling.plc
    rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact h
  haveI : Nontrivial (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr v.isPrime.ne_top
  rcases (Nat.dvd_prime hp).1 hd with h1 | h1
  · exact absurd h1 (CharP.ringChar_ne_one)
  · exact h1

section UnitConjugation
open Formalism.BasicNotions.DV

theorem additiveValuation_conjugatePlace_eq_star (D : D7) (w : D.what₂.places.Pl) (x : D.what₂.LL) :
    vAdd (D.plEq (D.what₂.places.conj w)) x = vAdd (D.plEq w) (star x) := by
  by_cases hx : x = 0
  · subst hx; simp [vAdd]
  · have h1 := D.conj_val w x
    rw [D.val_eq _ x hx, D.val_eq _ (star x) (star_ne_zero.2 hx)] at h1
    exact_mod_cast h1

theorem mem_heightOneSpectrum_iff_additiveValuation_pos {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K)
    (hx : x ≠ 0) : x ∈ w.asIdeal ↔ 0 < vAdd w (x : K) := by
  have hx' : w.valuation K (x : K) ≠ 0 := (map_ne_zero _).2 (by exact_mod_cast hx)
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K)]
  unfold vAdd
  rw [neg_pos, ← WithZero.log_one, WithZero.log_lt_log hx' one_ne_zero]

theorem plEq_conjPl (D : D7) (w : D.what₂.places.Pl) :
    D.plEq (D.what₂.places.conj w) = Formalism.DivisionValues.conjPl (D.plEq w) := by
  apply HeightOneSpectrum.ext
  ext x
  have key : ∀ y : 𝓞 D.what₂.LL, y ∈ (D.plEq (D.what₂.places.conj w)).asIdeal ↔
      Formalism.DivisionValues.cO D.what₂.LL y ∈ (D.plEq w).asIdeal := by
    intro y
    by_cases hy : y = 0
    · subst hy; simp
    · rw [mem_heightOneSpectrum_iff_additiveValuation_pos _ y hy, mem_heightOneSpectrum_iff_additiveValuation_pos _ _ ((map_ne_zero_iff _ (Formalism.DivisionValues.cO D.what₂.LL).injective).2 hy),
        additiveValuation_conjugatePlace_eq_star, Formalism.DivisionValues.ValuationRepresentative.cO_apply]
  rw [key]
  change _ ↔ x ∈ (D.plEq w).asIdeal.map (Formalism.DivisionValues.cO D.what₂.LL)
  rw [Ideal.mem_map_of_equiv]
  constructor
  · intro h
    exact ⟨_, h, Formalism.DivisionValues.ValuationRepresentative.cO_cO x⟩
  · rintro ⟨y, hy, rfl⟩
    rwa [Formalism.DivisionValues.ValuationRepresentative.cO_cO]

end UnitConjugation

end GlobalTheory.Mem.R3


open GlobalTheory.Mem.R3 in
theorem GlobalTheory.Mem.R3.tupL_of_twisted : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (T : Top.TwDat X.B) (Wt : Set X.B.places.Pl) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I (usedOf I T Wt))), Wt.Finite → (∀ w ∈ Wt, X.B.places.conj w ∈ Wt) → I.Ok → Set.range I.xi = T.set I.C → L.C = Top.Fr.at X I.C → (∀ t, L.xiH t = I.xi (ixOf I (usedOf I T Wt) t)) → ∃ (mu : HeightOneSpectrum (𝓞 X.toD7.what₂.LL) → TupU I (usedOf I T Wt)) (twPl : Finset (HeightOneSpectrum (𝓞 X.toD7.what₂.LL))), MuOf X I T Wt mu twPl ∧ ∀ Xg tr, Seed.TupL (famR X I hX (usedOf I T Wt) Xg tr) L mu twPl := by
  classical
  intro X px I hX T Wt L hWf hWc hI hrng hC hxi

  have hmemR : ∀ w ∈ Wt, T.xiTw I.C w ∈ Set.range I.xi := fun w _ => by
    rw [hrng]; exact Or.inr ⟨w, rfl⟩
  have hpickU : ∀ w ∈ Wt, pickIxTw I (T.xiTw I.C w) ∈ (usedOf I T Wt) := fun w hw => ⟨w, hw, xi_pickIxTw I (hmemR w hw)⟩

  let muP : X.B.places.Pl → TupU I (usedOf I T Wt) := fun w =>
    if h : w ∈ Wt then ⟨I.tup (pickIxTw I (T.xiTw I.C w)), Or.inr ((tup_mem_tuOf I).2 (hpickU w h))⟩
    else mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt))
  have muP_in : ∀ w (h : w ∈ Wt), muP w = ⟨I.tup (pickIxTw I (T.xiTw I.C w)), Or.inr ((tup_mem_tuOf I).2 (hpickU w h))⟩ :=
    fun w h => dif_pos h
  have muP_of_notMem : ∀ w, w ∉ Wt → muP w = mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt)) := fun w h => dif_neg h
  have ix_in : ∀ w ∈ Wt, ixOf I (usedOf I T Wt) (muP w) = pickIxTw I (T.xiTw I.C w) := fun w h => by
    rw [muP_in w h]; exact ixOf_eq I rfl
  have hcc : ∀ w, X.B.places.conj (X.B.places.conj w) = w := fun w => by
    apply X.toD7.plEq.injective
    have e1 := plEq_conjPl X.toD7 (X.toD7.what₂.places.conj w)
    have e2 := plEq_conjPl X.toD7 w
    change X.toD7.plEq (X.toD7.what₂.places.conj (X.toD7.what₂.places.conj w)) = X.toD7.plEq w
    rw [e1, e2, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]
  have hconjIff : ∀ w, X.B.places.conj w ∈ Wt ↔ w ∈ Wt := fun w =>
    ⟨fun h => hcc w ▸ hWc _ h, hWc w⟩
  have muP_conj : ∀ w, muP (X.B.places.conj w) = muP w := fun w => by
    by_cases h : w ∈ Wt
    · rw [muP_in w h, muP_in _ ((hconjIff w).2 h)]
      congr 2
      rw [(GlobalTheory.Mem.Top.TwFin.tw_fin X.B I.C T).2.2.1 w]
    · rw [muP_of_notMem w h, muP_of_notMem _ (fun h' => h ((hconjIff w).1 h'))]
  have hss : ∀ w : X.B.places.Pl, muP (X.toD7.plEq.symm (X.toD7.plEq w)) = muP w :=
    fun w => congrArg muP (X.toD7.plEq.symm_apply_apply w)
  refine ⟨fun v => muP (X.toD7.plEq.symm v), hWf.toFinset.image X.toD7.plEq, ?_, ?_⟩
  · intro w
    refine ⟨?_, ?_⟩
    · erw [Finset.mem_image]
      constructor
      · rintro ⟨w', hw', e⟩
        rw [X.toD7.plEq.injective e] at hw'
        exact (Set.Finite.mem_toFinset hWf).1 hw'
      · intro h
        exact ⟨w, (Set.Finite.mem_toFinset hWf).2 h, rfl⟩
    · show I.xi (ixOf I (usedOf I T Wt) (muP (X.toD7.plEq.symm (X.toD7.plEq w)))) = _
      rw [hss]
      by_cases h : w ∈ Wt
      · rw [if_pos h, ix_in w h, xi_pickIxTw I (hmemR w h)]
      · rw [if_neg h, muP_of_notMem w h, ixOf_mu0F]
        exact hI.trueColumnChoices_heckeChar_reference_eq_one
  · intro Xg tr
    have hμ0 : (famR X I hX (usedOf I T Wt) Xg tr).A.μ0 = mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt)) := rfl
    have memTw : ∀ v, v ∈ hWf.toFinset.image X.toD7.plEq ↔ X.toD7.plEq.symm v ∈ Wt := fun v => by
      erw [Finset.mem_image]
      constructor
      · rintro ⟨w', hw', rfl⟩
        rw [Equiv.symm_apply_apply]
        exact (Set.Finite.mem_toFinset hWf).1 hw'
      · intro h
        exact ⟨_, (Set.Finite.mem_toFinset hWf).2 h, Equiv.apply_symm_apply _ _⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro v hv
      rw [hμ0]
      exact muP_of_notMem _ (fun h => hv ((memTw v).2 h))
    · intro t
      rw [hμ0]
      rcases t.2 with h | h
      · exact Or.inl (Subtype.ext h)
      · right
        obtain ⟨b, hb, e⟩ := (mem_tuOf I).1 h
        obtain ⟨w, hw, hbw⟩ := hb
        refine ⟨X.toD7.plEq w, ?_⟩
        show muP (X.toD7.plEq.symm (X.toD7.plEq w)) = t
        rw [hss, muP_in w hw]
        apply Subtype.ext
        show I.tup (pickIxTw I (T.xiTw I.C w)) = t.1
        rw [← e]
        congr 1
        apply hI.xi_inj
        rw [xi_pickIxTw I (hmemR w hw), hbw]
    · intro v hv e
      rw [hμ0] at e
      have hw := (memTw v).1 hv
      have h1 := congrArg (ixOf I (usedOf I T Wt)) e
      rw [ix_in _ hw, ixOf_mu0F] at h1
      have h2 := congrArg I.xi h1
      rw [xi_pickIxTw I (hmemR _ hw), hI.trueColumnChoices_heckeChar_reference_eq_one] at h2
      exact (GlobalTheory.Mem.Top.TwFin.tw_fin X.B I.C T).2.1 _ h2
    · intro v
      have e : Formalism.DivisionValues.conjPl v = X.toD7.plEq (X.B.places.conj (X.toD7.plEq.symm v)) := by
        have := plEq_conjPl X.toD7 (X.toD7.plEq.symm v)
        rw [Equiv.apply_symm_apply] at this
        exact this.symm
      show muP (X.toD7.plEq.symm (Formalism.DivisionValues.conjPl v)) = muP (X.toD7.plEq.symm v)
      rw [e, hss]
      exact muP_conj _
    · intro v hv
      have hw := (memTw v).1 hv
      set w := X.toD7.plEq.symm v with hwdef
      have hv' : v = X.toD7.plEq w := by rw [hwdef, Equiv.apply_symm_apply]
      have hpl : Formalism.EigenvalueLevelCeiling.plc v = X.B.places.resChar w := by
        rw [hv']
        exact plc_eq_of_natCast_mem _ (X.B.places.resChar_prime w) (GlobalTheory.LvT.Inh.resChar_mem_plEq X.toD7 w)
      refine ⟨T.psi w, T.Q w, ?_, ?_⟩
      · rw [hpl]; exact T.psi_is w
      · rw [hxi, hpl, hC]
        show I.xi (ixOf I (usedOf I T Wt) (muP w)) = _
        rw [ix_in w hw, xi_pickIxTw I (hmemR w hw)]
        rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemParLevOfQ
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg.ActQ

variable (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (U : Set I.ι)
  (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U))

theorem mem_parLev_of_Q (i : Fin X.toD7.R.m) (t : TupU I U) (q : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q) :
    Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _) ∈
      Formalism.L2.DIV.parLev X.toD7.sp.cm (Vc X.toD7 i).gram (L.βV i) (L.datVt i t) := q.2.1

def rV (i : Fin X.toD7.R.m) (t : TupU I U) (x : GL (Fin (Vc X.toD7 i).rank) (Formalism.IndefR.Lev.EAf X.toD7)) : G0 L.Pg X.toD7.R.r :=
  rTup (L.βV i) (L.datVt i t) x

theorem rV_one (i : Fin X.toD7.R.m) (t : TupU I U) : rV X I U L i t 1 = 1 := rTup_one

theorem rV_mul (i : Fin X.toD7.R.m) (t : TupU I U) {x y : GL (Fin (Vc X.toD7 i).rank) (Formalism.IndefR.Lev.EAf X.toD7)}
    (hx : x ∈ Formalism.L2.DIV.parLev X.toD7.sp.cm (Vc X.toD7 i).gram (L.βV i) (L.datVt i t))
    (hy : y ∈ Formalism.L2.DIV.parLev X.toD7.sp.cm (Vc X.toD7 i).gram (L.βV i) (L.datVt i t)) :
    rV X I U L i t (x * y) = rV X I U L i t x * rV X I U L i t y := rTup_mul hx hy

def redQ (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (i : Fin X.toD7.R.m) (t : TupU I U) :
    (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q →* Gc X.B px where
  toFun q := eG.symm (rV X I U L i t
    (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)))
  map_one' := by
    simp only [OneMemClass.coe_one, map_one]
    rw [rV_one, map_one]
  map_mul' a b := by
    simp only [Subgroup.coe_mul, map_mul]
    rw [rV_mul X I U L i t (mem_parLev_of_Q X I U L i t a) (mem_parLev_of_Q X I U L i t b), map_mul]

theorem redQ_apply (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (i : Fin X.toD7.R.m) (t : TupU I U)
    (q : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q) :
    redQ X I U L eG i t q = eG.symm (rV X I U L i t
      (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _))) := rfl

theorem eG_redQ (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (i : Fin X.toD7.R.m) (t : TupU I U)
    (q : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q) :
    eG (redQ X I U L eG i t q) = rV X I U L i t
      (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) := by
  rw [redQ_apply]
  exact eG.apply_symm_apply _

theorem redQ_eq_one_iff (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (i : Fin X.toD7.R.m) (t : TupU I U)
    (q : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q) :
    redQ X I U L eG i t q = 1 ↔ (q : Bridge.Gf (Vc X.toD7 i)) ∈ (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).J := by
  rw [redQ_apply, MulEquiv.map_eq_one_iff]
  constructor
  · intro h
    exact ⟨mem_parLev_of_Q X I U L i t q, Subgroup.mem_bot.2 h⟩
  · intro h
    exact Subgroup.mem_bot.1 h.2

def ptS (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (EA X)) (g : Bridge.Gf (Vc X.toD7 i)) :
    Formalism.L2.Col.DecoSet (E := X.B.fields.E) (n := X.B.R.nV) (ST := ∅) (SG := Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) :=
  ptL X I U i t A k g

def redZ (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (EA X))
    (κ : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q) :
    Formalism.L2.Col.GLG (E := X.B.fields.E) (n := X.B.R.nV) (SG := Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) :=
  fun w => Formalism.L2.DIV.redFn (1 : GL (Fin X.B.R.nV) (EA X)) w.1
    ((A * k)⁻¹ * castGL (rkEq X i).symm
      (Formalism.UG.bc (swapAE X.toD7) ((κ : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) * (A * k))

end GlobalTheory.Mem.R3.LiftBrg.ActQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemRangeOfPowG
section
noncomputable section

namespace GlobalTheory.Mem.Top.ColOwe

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem natCast_kv_eq_zero (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) (h : (p : 𝓞 F) ∈ v.asIdeal) : (p : kv F v) = 0 := by

  have hval : Valued.v ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) (p : 𝓞 F) :
      v.adicCompletion F)) < 1 := by
    rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (v.valuation_lt_one_iff_mem (K := F) _).2 h
  have hmax : algebraMap (𝓞 F) (v.adicCompletionIntegers F) (p : 𝓞 F) ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) :=
    (Valuation.mem_maximalIdeal_iff _ Valued.v).2 hval
  have hres := (IsLocalRing.residue_eq_zero_iff _).2 hmax
  simpa using hres

theorem mem_range_of_pow_g (B : Base) (i : Fin 2) (z : ℂ) (hz : z ^ B.host.g i = 1) : ∃ r : B.LL, B.embLL r = z := by
  have hp : (B.host.g i).Prime := B.host.g_prime i

  have hmem : B.host.g i * (B.host.g i - 1) ∈ [B.toPre.restRowsFiniteGroupCard, B.host.g 0 * (B.host.g 0 - 1),
      B.host.g 1 * (B.host.g 1 - 1), 3 ^ 4, 5 ^ 4] := by
    fin_cases i <;> simp
  obtain ⟨z0, -, hz0⟩ := B.roots_Ks _ hmem
  have hN : B.host.g i * (B.host.g i - 1) ≠ 0 :=
    Nat.mul_ne_zero hp.ne_zero (by have := hp.two_le; omega)
  have hprim : IsPrimitiveRoot (B.embLL z0) (B.host.g i * (B.host.g i - 1)) := by
    rw [hz0]; exact Complex.isPrimitiveRoot_exp _ hN

  have hprim' : IsPrimitiveRoot (B.embLL z0 ^ (B.host.g i - 1)) (B.host.g i) :=
    hprim.pow (Nat.pos_of_ne_zero hN) (mul_comm _ _)
  have : NeZero (B.host.g i) := ⟨hp.ne_zero⟩
  obtain ⟨k, -, hk⟩ := hprim'.eq_pow_of_pow_eq_one hz
  exact ⟨(z0 ^ (B.host.g i - 1)) ^ k, by rw [map_pow, map_pow, hk]⟩

theorem psi0Rat (X : Stages) (T : ∀ u, Forms0 X.toD7 u) (u : X.toD7.what₂.Word) : Formalism.L2.G.LevelZeroCharacterRational T u := by
  intro i v h x

  have hx : ((T u).gl.psi0 i v h x) ^ X.toD7.host.g i = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, natCast_kv_eq_zero _ v _ h, zero_mul,
      AddChar.map_zero_eq_one]
  exact mem_range_of_pow_g X.B i _ hx

variable {D : D7}

def levOf (C : ColsTiedSym D) : LevelData D := C.herm.base.lev0

def formsOf (C : ColsTiedSym D) (u : D.what₂.Word) : Forms0 D u := (C.forms u).to0

def errOf (H : Formalism.L2.Herm.ColsHermS D) : ErrX D := (GlobalTheory.Mem.ErrTies.exists_errX D H).choose

theorem errOf_piG (H : Formalism.L2.Herm.ColsHermS D) : (errOf H).piG = (H.levelZeroCompatibility D.u₀).piG :=
  (GlobalTheory.Mem.ErrTies.exists_errX D H).choose_spec.1

theorem errOf_piT (H : Formalism.L2.Herm.ColsHermS D) (u : D.what₂.Word) : (errOf H).piT u = (H.atT u).piU :=
  (GlobalTheory.Mem.ErrTies.exists_errX D H).choose_spec.2.1 u

theorem errOf_vPl (H : Formalism.L2.Herm.ColsHermS D) (u : D.what₂.Word) (v : (D.mem u).A.vT) :
    (errOf H).vPl u v = (H.base.vT u v).1 :=
  (GlobalTheory.Mem.ErrTies.exists_errX D H).choose_spec.2.2.1 u v

theorem joint0 (C : ColsTiedSym D) (u : D.what₂.Word) : Joint0 (levOf C) u (formsOf C u) := by
  unfold levOf formsOf
  exact C.joint0 u

theorem dGamChoice_of_lcm (X : Stages) (hDG : ∀ u μ, (X.C.chTw u μ).DGam = GlobalTheory.Mem.Col2.DGam X.B.fields.E X.B.R) :
    DGamChoice_at X.toD7 := by
  intro M hM u

  have hc : (X.toD7.mem u).C = X.C.chTw u X.C.mu0 := (X.C.memberColumns_twistedChain_base u).symm
  rw [hc, hDG u X.C.mu0]
  have hf : X.B.fields.f = X.B.R.f := (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws X.B).2
  refine GlobalTheory.Mem.Col2.DGam_dvd_of_minkMult X.B.R (GlobalTheory.Mem.FieldsLaws.fields_ok (B := X.B)) M ?_
  rw [hf]
  exact hM

theorem colLay_of_herm (X : Stages) (hX : Nonempty (PreX X.B.toPre))
    (hDG : ∀ u μ, (X.C.chTw u μ).DGam = GlobalTheory.Mem.Col2.DGam X.B.fields.E X.B.R)
    (H : Formalism.L2.Herm.ColsHermS X.toD7) (T : ∀ u, Forms0 X.toD7 u) (hJ : ∀ u, Joint0 H.base.lev0 u (T u)) :
    ColLay X.toD7 H.base.lev0 (errOf H) := by
  have hErr := (GlobalTheory.Mem.ErrTies.exists_errX X.toD7 H).choose_spec
  refine
    { piG_lev := hErr.2.2.2.1
      piT_lev := hErr.2.2.2.2.1
      seen := hErr.2.2.2.2.2.1
      tauOf := hErr.2.2.2.2.2.2
      one := ?_
      mink := dGamChoice_of_lcm X hDG
      atT := _root_.GlobalTheory.LevelHecke.commensurable_at_level X hX H T hJ (psi0Rat X T) }
  intro u μ
  have h0 : (X.C.chTw X.B.u₀ X.C.mu0).DGam = (X.C.mem X.B.u₀).C.DGam :=
    congrArg (fun c => c.DGam) (X.C.memberColumns_twistedChain_base X.B.u₀)
  exact (hDG u μ).trans ((hDG X.B.u₀ X.C.mu0).symm.trans h0)

theorem colLay_of_tied (X : Stages) (hX : Nonempty (PreX X.B.toPre))
    (hDG : ∀ u μ, (X.C.chTw u μ).DGam = GlobalTheory.Mem.Col2.DGam X.B.fields.E X.B.R) (C : ColsTiedSym X.toD7) :
    ColLay X.toD7 (levOf C) (errOf C.herm) :=
  colLay_of_herm X hX hDG C.herm (formsOf C) (joint0 C)

end GlobalTheory.Mem.Top.ColOwe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlacesUnder
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MtIn.Under

theorem not_both {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : q ≠ p) (h1 : (p : 𝓞 E) ∈ P.asIdeal) (h2 : (q : 𝓞 E) ∈ P.asIdeal) : False := by
  have hc : IsCoprime (q : 𝓞 E) (p : 𝓞 E) := Nat.Coprime.cast ((Nat.coprime_primes hq hp).2 hne)
  obtain ⟨x, y, hxy⟩ := hc
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hxy ▸ P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ h2) (P.asIdeal.mul_mem_left _ h1)))

theorem q_mem {D : D7} {P : Pl D.host.E} {q : ℕ} (h : Nat.card (kP P) = q) : (q : 𝓞 D.host.E) ∈ P.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← h]
  have := card_nsmul_eq_zero' (G := kP P) (x := 1)
  rwa [nsmul_one] at this

theorem places_under : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → (∀ PP, PP ∈ L.Pg ↔ ∃ k v, PP = D.naut.plGw k v) → ∀ (i : Fin D.R.m) (t : T) (PP : Pl D.host.E), PP ∈ L.Pg ∨ PP ∈ L.Q t → ∀ v, NG.OverPl PP v → v ∈ gPl D ∪ qPl D (L.C.mu0 i * L.xiH t) := by
  intro D T L μ0 hL hPg i t PP hPP v hv
  by_cases hg : v ∈ gPl D
  · exact Or.inl hg
  rcases hPP with hP | hQ
  · obtain ⟨k, w, rfl⟩ := (hPg _).1 hP
    exact absurd ⟨_, hv, k, D.naut.plGw_over k w⟩ hg
  · refine Or.inr ⟨hg, PP, hv, fun hu => ?_⟩
    obtain ⟨⟨q, hq1, hq2, -, hq4⟩, -⟩ := hL.Q_pl t PP hQ
    have hm : (L.C.mu0 i).UnrAt PP := (L.C.isMu0 i).unr PP fun l hl =>
      not_both (D.host.g_prime l) hq1 (hq4 l) hl (q_mem hq2)
    have hx : (L.xiH t).UnrAt PP := by
      intro x hx
      have h1 : (L.C.mu0 i).loc PP x * (L.xiH t).loc PP x = 1 := hu x hx
      rwa [hm x hx, one_mul] at h1
    exact (hL.Q_ram t PP).2 (Or.inl hQ) hx

end GlobalTheory.MtIn.Under

end
end

