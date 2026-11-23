module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.LocalRingCardinality.Bundle0003
public import Formalism.LocalRingCardinality.SpanPowerMembership.RankRecordRowDimensionZero
public import Formalism.LocalRingCardinality.SpanPowerMembership.SignSplitEquivInl
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameHeckeCharLocalEqInvTypeCharacter
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdAbsNormDivsDvd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0057

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChiDValuesAndCcTop
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Df NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.ChiDVal

open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

section Gen

variable {L : Type} [Field L] [NumberField L]

theorem ideles_snd_mul (a b : Ideles L) (v : HeightOneSpectrum (𝓞 L)) :
    ((a * b : Ideles L) : AdeleRing (𝓞 L) L).2 v = (a : AdeleRing (𝓞 L) L).2 v * (b : AdeleRing (𝓞 L) L).2 v := rfl

theorem ideles_snd_inv_mul (a : Ideles L) (v : HeightOneSpectrum (𝓞 L)) :
    ((a⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v * (a : AdeleRing (𝓞 L) L).2 v = 1 := by
  rw [← ideles_snd_mul, inv_mul_cancel]
  rfl

theorem ideles_finite (a : Ideles L) : {v : HeightOneSpectrum (𝓞 L) | ¬ Valued.v ((a : AdeleRing (𝓞 L) L).2 v) = 1}.Finite := by
  have h1 := (a : AdeleRing (𝓞 L) L).2.2
  have h2 := ((a⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2.2
  refine Filter.eventually_cofinite.1 ((h1.and h2).mono fun v hv => ?_)
  have e1 : Valued.v ((a : AdeleRing (𝓞 L) L).2 v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hv.1
  have e2 : Valued.v (((a⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hv.2
  have e3 := congrArg Valued.v (ideles_snd_inv_mul a v)
  rw [map_mul, map_one] at e3
  refine le_antisymm e1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (((a⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v) * Valued.v ((a : AdeleRing (𝓞 L) L).2 v) := e3.symm
    _ ≤ 1 * Valued.v ((a : AdeleRing (𝓞 L) L).2 v) := mul_le_mul_left e2 _
    _ = _ := one_mul _

theorem exists_unif_zpow (v : HeightOneSpectrum (𝓞 L)) (y : v.adicCompletion L) (hy : y ≠ 0) :
    ∃ n : ℤ, Valued.v (((atFin v (unif v)) ^ n : (v.adicCompletion L)ˣ) : v.adicCompletion L) = Valued.v y := by
  have h0 : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  refine ⟨-WithZero.log (Valued.v y), ?_⟩
  have hu : Valued.v ((atFin v (unif v) : (v.adicCompletion L)ˣ) : v.adicCompletion L) = WithZero.exp (-1 : ℤ) := unif_spec v
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hu, ← WithZero.exp_zsmul]
  simp [WithZero.exp_log h0]

theorem ideles_values {Gp : Type} [CommGroup Gp] (f : Ideles L →* Gp)
    (hU : ∀ a : Ideles L, (∀ v, Valued.v ((a : AdeleRing (𝓞 L) L).2 v) = 1) → f a = 1) (S : Subgroup Gp)
    (hS : ∀ v, f (localIdele L v (atFin v (unif v))) ∈ S) (a : Ideles L) : f a ∈ S := by
  classical
  have key : ∀ (T : Finset (HeightOneSpectrum (𝓞 L))) (a : Ideles L),
      (∀ v, v ∉ T → Valued.v ((a : AdeleRing (𝓞 L) L).2 v) = 1) → f a ∈ S := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro a ha
      rw [hU a fun v => ha v (Finset.notMem_empty v)]
      exact S.one_mem
    | insert v0 T _ ih =>
      intro a ha
      have hy : (a : AdeleRing (𝓞 L) L).2 v0 ≠ 0 := by
        intro h0
        have := ideles_snd_inv_mul a v0
        rw [h0, mul_zero] at this
        exact zero_ne_one this
      obtain ⟨n, hn⟩ := exists_unif_zpow v0 _ hy
      have h1 : f (a * (localIdele L v0 ((atFin v0 (unif v0)) ^ n))⁻¹) ∈ S := by
        refine ih _ fun v hv => ?_
        rw [← map_inv, ideles_snd_mul]
        by_cases hvv : v = v0
        · subst hvv
          rw [localIdele_snd_self, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hn]
          exact mul_inv_cancel₀ ((Valuation.ne_zero_iff _).2 hy)
        · rw [(localIdele_isSupportedAt L v0 _).2 v hvv, mul_one]
          exact ha v fun h => (Finset.mem_insert.1 h).elim hvv hv
      have h2 : f a = f (a * (localIdele L v0 ((atFin v0 (unif v0)) ^ n))⁻¹) * f (localIdele L v0 (atFin v0 (unif v0))) ^ n := by
        rw [map_mul, map_inv, map_zpow (localIdele L v0), map_zpow f, inv_mul_cancel_right]
      rw [h2]
      exact S.mul_mem h1 (S.zpow_mem (hS v0) n)
  exact key (ideles_finite a).toFinset a fun v hv => by
    by_contra h
    exact hv ((ideles_finite a).mem_toFinset.2 h)

end Gen

def coeffUnits (D : D7) : Subgroup ℂˣ where
  carrier := {z | ∃ r : D.what₂.LL, D.what₂.embLL r = (z : ℂ)}
  one_mem' := ⟨1, map_one _⟩
  mul_mem' := by
    rintro a b ⟨r, hr⟩ ⟨s, hs⟩
    exact ⟨r * s, by rw [map_mul, hr, hs, Units.val_mul]⟩
  inv_mem' := by
    rintro a ⟨r, hr⟩
    exact ⟨r⁻¹, by rw [map_inv₀, hr, Units.val_inv_eq_inv_val]⟩

theorem chiD_mem_of {D : D7} {C : Formalism.L2.Host.CharFrame D} (T : Formalism.L2.Host.DtTied D C) (hV : C.chiPsi.ValuesIn 0 D.what₂.embLL) :
    ∀ z : D.Dt, ∃ r : D.what₂.LL, D.what₂.embLL r = ((D.chiD z : ℂˣ) : ℂ) := by
  intro z
  obtain ⟨a, rfl⟩ := T.surj z
  refine ideles_values (D.chiD.comp T.eDt) (fun a ha => D.chiD_UO _ ((T.UO_eq _).2 ⟨a, ha, rfl⟩)) (coeffUnits D) (fun v => ?_) a
  obtain ⟨y, hy⟩ := hV v (C.isChi.unr v)
  refine ⟨y, ?_⟩
  rw [hy]
  show _ = ((D.chiD (T.eDt (localIdele D.host.E v (atFin v (unif v)))) : ℂˣ) : ℂ)
  rw [T.chiD_eq _ (fun w => (localIdele_isSupportedAt D.host.E v _).1 w)]
  unfold HChar.valTw
  rw [Complex.ofReal_zero, neg_zero, Complex.cpow_zero, mul_one]
  rfl

theorem chiD_values_and_cc_top : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt), (∀ z : (w.D Z).Dt, ∃ r : (w.D Z).what₂.LL, (w.D Z).what₂.embLL r = (((w.D Z).chiD z : ℂˣ) : ℂ)) ∧ ∀ (L : SizeData₂ (w.D Z)) (hT : GatTies (w.D Z)) (Gi : G.Inst (w.D Z) L) (Gl : G.LatInst (w.D Z)) (K : G.Consts) (Y : DivX (w.D Z)) (cX : ExtraC) (ex : Extra (w.D Z) L hT Gi Gl K Y cX) (t : Formalism.L2.Ker.KerEntTied ex), t.cc = ⊤ := by
  intro B f T w Z
  refine ⟨?_, fun L hT Gi Gl K Y cX ex t => t.cc_rec.trans B.toPre.ccK_top⟩
  obtain ⟨dt, -⟩ := TC.dtTied_true w.I w.ok w.pins w.l Z
  have hv : Formalism.L2.Host.ValLL0 (w.D Z) (TC.cf w.I w.l Z) := by
    rcases w with ⟨px, I, ok, C_eq, S_eq, xi_range, pins, l, l0, δ, exact, fld, val⟩
    subst C_eq
    exact val _ _ _ _ _ _
  exact chiD_mem_of dt hv.toLL.chiPsi

end GlobalTheory.Mem.ChiDVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetInFramesPreimageUnderLift
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT


open Classical GlobalTheory.TopStep in
theorem sub_mem_stdAt_of_redV {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E))
    (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (m : GLint E n P) (x : Sp E n)
    (hx : (qOf P : E) • x ∈ stdAt E n P) (hred : ∀ v ∈ stdAt E n P, redV P (m.1 v) = redV P v) :
    m.1 x - x ∈ stdAt E n P := by
  have hq0 : (qOf P : E) ≠ 0 := qOf_ne_zero
  have hk0 := glint_mem m hx
  refine mem_stdAt.2 fun j => ?_
  have hi1 := mem_stdAt.1 hk0 j
  have hi2 := mem_stdAt.1 hx j
  have hr : redP P ((m.1 ((qOf P : E) • x) - (qOf P : E) • x) j) = 0 := by
    rw [Pi.sub_apply, reduction_sub hi1 hi2, sub_eq_zero]
    exact congrFun (hred _ hx) j
  have := intAt_div_of_redP hq (intAt_sub hi1 hi2) hr
  convert this using 1
  rw [LinearEquiv.map_smul]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp


set_option maxHeartbeats 1600000 in
open Classical GlobalTheory.TopStep in
theorem cosetIn_act_of_liftsInv : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (b : (I.stp u a i).β) (κ : (I.stp u a i).G b) (p : (I.stp u a i).D b) (P : SBof I a) (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), (I.stp u a i).gam b κ = 1 → LiftsInv I κ P g → ∀ z, z ∈ cosetIn ((I.stp u a i).act b κ p) P ↔ g z ∈ cosetIn p P := by
  intro B X I _ u a i b κ p P g hgam hL z
  have hX : B.fields.Ok := GlobalTheory.Mem.FieldsLaws.fields_ok B
  have hPr : (B.primes X).Ok := (GlobalTheory.BasePrimes.primes_ok B X).1
  obtain ⟨γ, h, c⟩ := κ
  have hγ : γ = 1 := by
    have e : ufGL B.fields.E (B.R.N i) γ = 1 := hgam
    have e2 : (toGLm B.fields.E (B.R.N i)) γ.1 = (toGLm B.fields.E (B.R.N i)) 1 := by
      rw [map_one]; exact e
    exact Subtype.ext ((toGLm B.fields.E (B.R.N i)).injective e2)
  subst hγ
  set p' := (I.stp u a i).act b ((1 : UF B.fields.E (B.R.N i)), h, c) p with hp'
  have hys : p'.1.2 = p.1.2 := by
    show (fun v => ((1 : UF B.fields.E (B.R.N i)) : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) v) '' p.1.2 = p.1.2
    simp
  have hg : ∀ x, g x ∈ stdAt B.fields.E (B.R.N i) P.1 ↔ x ∈ stdAt B.fields.E (B.R.N i) P.1 := hL.1
  have key : ∀ y ∈ p.1.2, ((qOf P.1 : B.fields.E) ^ (if P.1 ∈ (B.primes X).vGs then 0 else (I.cst a).M))⁻¹ •
      (g ((frsF I.sel (I.tup a) p'.1.1 P).symm y) - (frsF I.sel (I.tup a) p.1.1 P).symm y) ∈ stdAt B.fields.E (B.R.N i) P.1 := by
    intro y hy
    by_cases hP : P.1 ∈ (B.primes X).vGs
    · rw [if_pos hP, pow_zero, inv_one, one_smul]
      by_cases hj : i + 1 = B.R.m
      swap
      · have h0 : p.1.2 = ∅ := by
          have := p.2
          rw [ysAt_ys_of_ne I.sel (I.tup a) (I.cst a) hj] at this
          exact this
        rw [h0] at hy
        exact absurd hy (Set.notMem_empty y)
      obtain ⟨y0, hy0, hY⟩ := PtAt.mem_ybSet p hj
      have hy' : y - y0 ∈ locLat (rowSG (B.primes X) I.sel (I.tup a)) p.1.1.deco.1.N
          (fun P => if P.1 ∈ (B.primes X).vGs then 0 else ((I.cst a).M : ℤ)) := by
        rw [hY] at hy
        exact hy
      have hA : (qOf P.1 : B.fields.E) • y0 ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N := by
        have := Submodule.mem_iInf _ |>.1 hy0 P
        rw [Submodule.mem_comap] at this
        simpa [hP] using this
      have hB : y - y0 ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N := by
        have := Submodule.mem_iInf _ |>.1 hy' P
        rw [Submodule.mem_comap] at this
        simpa [hP] using this
      have hx : (qOf P.1 : B.fields.E) • y ∈ p.1.1.deco.1.at P.1 := by
        have e : (qOf P.1 : B.fields.E) • y = (qOf P.1 : B.fields.E) • y0 + (qOf P.1 : B.fields.E) • (y - y0) := by
          rw [← smul_add, add_sub_cancel]
        rw [e]
        exact add_mem hA (smul_mem_locP (intAt_nat _) hB)
      let w : (B.primes X).vGs := ⟨P.1, hP⟩
      have hd : p'.1.1.deco.1 = p.1.1.deco.1.act ((1 : UF B.fields.E (B.R.N i)) : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) h.1 := rfl
      have hf : IsLiftFr p.1.1.deco.1 w (p.1.1.deco.1.liftFr w) := liftFr_spec p.1.1.deco.2 w
      have hf' : IsLiftFr (p.1.1.deco.1.act ((1 : UF B.fields.E (B.R.N i)) : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) h.1) w (p'.1.1.deco.1.liftFr w) := by
        rw [← hd]
        exact liftFr_spec p'.1.1.deco.2 w
      have e1 : frsF I.sel (I.tup a) p.1.1 P = p.1.1.deco.1.liftFr w := by
        unfold frsF
        rw [dite_eq_left hP]
      have e2 : frsF I.sel (I.tup a) p'.1.1 P = p'.1.1.deco.1.liftFr w := by
        unfold frsF
        rw [dite_eq_left hP]
      rw [e1, e2]
      have e3 : (p'.1.1.deco.1.liftFr w).symm y = (passFr (w := w) _ h.1 hf hf').1 ((p.1.1.deco.1.liftFr w).symm y) := by
        show _ = (p'.1.1.deco.1.liftFr w).symm (((1 : UF B.fields.E (B.R.N i)) : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) ((p.1.1.deco.1.liftFr w) ((p.1.1.deco.1.liftFr w).symm y)))
        rw [LinearEquiv.apply_symm_apply]
        rfl
      rw [e3]
      have hv0 : (qOf P.1 : B.fields.E) • (p.1.1.deco.1.liftFr w).symm y ∈ stdAt B.fields.E (B.R.N i) P.1 := by
        rw [← LinearEquiv.map_smul, ← hf.1, LinearEquiv.apply_symm_apply]
        exact hx
      have hκ : GlobalTheory.TopStep.redGL (B.R.N i) P.1 (passFr (w := w) _ h.1 hf hf') = h.1 w := redGL_passFr (w := w) _ h.1 hf hf'
      have hq := (degOneUnram_of_mem_vGs hX hPr hP).2
      have hred : ∀ v ∈ stdAt B.fields.E (B.R.N i) P.1, redV P.1 (g ((passFr (w := w) _ h.1 hf hf').1 v)) = redV P.1 v := by
        intro v hv
        rw [hL.2.1 hP _ (glint_mem _ hv), redV_redGL _ hv, hκ, Matrix.mulVec_mulVec]
        show ((h.1 w)⁻¹.1 * (h.1 w).1).mulVec _ = _
        rw [Units.inv_mul, Matrix.one_mulVec]
      have hm := sub_mem_stdAt_of_redV P.1 hq (⟨g, hL.1⟩ * passFr (w := w) _ h.1 hf hf') _ hv0 hred
      exact hm
    · rw [if_neg hP]
      have hQ : P.1 ∈ I.Q a := (Finset.mem_union.mp P.2).resolve_left hP
      have hF' : frsF I.sel (I.tup a) p'.1.1 P = frsF I.sel (I.tup a) p.1.1 P * g := by
        unfold frsF
        rw [dite_eq_right hP, dite_eq_right hP, hL.2.2 hQ]
        exact LinearEquiv.ext fun x => rfl
      have e : g ((frsF I.sel (I.tup a) p'.1.1 P).symm y) = (frsF I.sel (I.tup a) p.1.1 P).symm y := by
        rw [eq_comm, LinearEquiv.symm_apply_eq]
        rw [hF']
        exact ((frsF I.sel (I.tup a) p.1.1 P * g).apply_symm_apply y).symm
      rw [e, sub_self, smul_zero]
      exact zero_mem _
  simp only [cosetIn, Set.mem_ofPred_eq]
  rw [hys]
  constructor
  · rintro ⟨y, hy, hz⟩
    refine ⟨y, hy, ?_⟩
    have := add_mem ((hg _).2 hz) (key y hy)
    rwa [map_smul, map_sub, ← smul_add, sub_add_sub_cancel] at this
  · rintro ⟨y, hy, hz⟩
    refine ⟨y, hy, ?_⟩
    have := sub_mem hz (key y hy)
    rw [← smul_sub, sub_sub_sub_cancel_right, ← map_sub, ← map_smul] at this
    exact (hg _).1 this

end GlobalTheory.Mem.Col2.AdT

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetInFramesShapeAtBadPrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.AdT.CosShape

section Gen

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem pow_smul_mem (S : Submodule (𝓞 E) (Sp E n)) (r : 𝓞 E) (k : ℕ) {x : Sp E n} (hx : x ∈ S) :
    ((r : E) ^ k) • x ∈ S := by

  have h : ((r : E) ^ k) • x = (r ^ k) • x := by
    rw [← algebraMap_smul E (r ^ k) x]
    simp
  rw [h]
  exact S.smul_mem _ hx

theorem core (S₀ L : Submodule (𝓞 E) (Sp E n)) (F : Sp E n ≃ₗ[E] Sp E n) (hF : ∀ w ∈ L, F.symm w ∈ S₀)
    (c : E) (hc : c ≠ 0) (hpow : ∀ (S : Submodule (𝓞 E) (Sp E n)) (k : ℕ) (x : Sp E n), x ∈ S → c ^ k • x ∈ S)
    (Y : Set (Sp E n)) (y₀ : Sp E n) (e e' : ℕ) (hY0 : y₀ ∈ Y) (hY : ∀ y ∈ Y, (c ^ e)⁻¹ • (y - y₀) ∈ L)
    (hy₀ : c ^ e' • y₀ ∈ L) (C : Set (Sp E n)) (hC : ∀ z, z ∈ C ↔ ∃ y ∈ Y, (c ^ e)⁻¹ • (z - F.symm y) ∈ S₀) :
    C.Nonempty ∧ (∀ y ∈ Y, F.symm y ∈ C) ∧ ∀ z ∈ C, (∀ z', z' ∈ C ↔ (c ^ e)⁻¹ • (z' - z) ∈ S₀) ∧
      ∀ (g g' : Sp E n ≃ₗ[E] Sp E n) (D : ℕ), (∀ x, g' x ∈ S₀ ↔ x ∈ S₀) →
        (∀ x ∈ S₀, (c ^ D)⁻¹ • (g x - g' x) ∈ S₀) → e + e' ≤ D →
        (c ^ e)⁻¹ • (g z - z) ∈ S₀ → ∀ z', g' z' ∈ C ↔ z' ∈ C := by

  have hYY : ∀ y ∈ Y, ∀ y' ∈ Y, (c ^ e)⁻¹ • (F.symm y - F.symm y') ∈ S₀ := by
    intro y hy y' hy'
    have h1 := hF _ (hY y hy)
    have h2 := hF _ (hY y' hy')
    have h3 : (c ^ e)⁻¹ • (F.symm y - F.symm y') =
        F.symm ((c ^ e)⁻¹ • (y - y₀)) - F.symm ((c ^ e)⁻¹ • (y' - y₀)) := by
      simp only [LinearEquiv.map_smul, map_sub]
      rw [← smul_sub]
      congr 1
      abel
    rw [h3]
    exact S₀.sub_mem h1 h2
  have hself : ∀ y ∈ Y, F.symm y ∈ C := by
    intro y hy
    exact (hC _).2 ⟨y, hy, by simp⟩

  have hmem : ∀ z ∈ C, ∀ z', z' ∈ C ↔ (c ^ e)⁻¹ • (z' - z) ∈ S₀ := by
    intro z hz z'
    obtain ⟨y₁, hy₁, hz1⟩ := (hC z).1 hz
    constructor
    · intro hz'
      obtain ⟨y₂, hy₂, hz2⟩ := (hC z').1 hz'
      have key := S₀.add_mem (S₀.sub_mem hz2 hz1) (hYY y₂ hy₂ y₁ hy₁)
      convert key using 1
      rw [← smul_sub, ← smul_add]
      congr 1
      abel
    · intro h
      refine (hC z').2 ⟨y₁, hy₁, ?_⟩
      have key := S₀.add_mem h hz1
      convert key using 1
      rw [← smul_add]
      congr 1
      abel
  refine ⟨⟨F.symm y₀, hself y₀ hY0⟩, hself, fun z hz => ⟨hmem z hz, ?_⟩⟩
  intro g g' D hg' hD hle hgz z'
  obtain ⟨y₁, hy₁, hz1⟩ := (hC z).1 hz
  have hce : c ^ e ≠ 0 := pow_ne_zero _ hc

  have hx₀ : c ^ e' • z ∈ S₀ := by
    have a1 : c ^ e' • (c ^ e • ((c ^ e)⁻¹ • (z - F.symm y₁))) ∈ S₀ := hpow _ _ _ (hpow _ _ _ hz1)
    have a2 : c ^ e' • (c ^ e • ((c ^ e)⁻¹ • (F.symm y₁ - F.symm y₀))) ∈ S₀ :=
      hpow _ _ _ (hpow _ _ _ (hYY y₁ hy₁ y₀ hY0))
    have a3 : F.symm (c ^ e' • y₀) ∈ S₀ := hF _ hy₀
    rw [smul_inv_smul₀ hce] at a1 a2
    rw [LinearEquiv.map_smul] at a3
    have a4 := S₀.add_mem (S₀.add_mem a1 a2) a3
    convert a4 using 1
    rw [← smul_add, ← smul_add]
    congr 1
    abel

  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  have hdiff : (c ^ e)⁻¹ • (g z - g' z) ∈ S₀ := by
    have b1 := hpow S₀ k _ (hD _ hx₀)
    convert b1 using 1
    rw [LinearEquiv.map_smul, LinearEquiv.map_smul, ← smul_sub, smul_smul, smul_smul]
    congr 1
    rw [pow_add, pow_add]
    field_simp
  have ht : (c ^ e)⁻¹ • (g' z - z) ∈ S₀ := by
    have b2 := S₀.sub_mem hgz hdiff
    convert b2 using 1
    rw [← smul_sub]
    congr 1
    abel
  rw [hmem z hz (g' z'), hmem z hz z']
  have hsplit : (c ^ e)⁻¹ • (g' z' - z) = g' ((c ^ e)⁻¹ • (z' - z)) + (c ^ e)⁻¹ • (g' z - z) := by
    rw [LinearEquiv.map_smul, ← smul_add, map_sub]
    congr 1
    abel
  rw [hsplit, add_mem_cancel_right ht]
  exact hg' _

end Gen

end GlobalTheory.Mem.Col2.AdT.CosShape

namespace GlobalTheory.Mem.Col2.AdT.CosShape


set_option maxHeartbeats 1600000 in
open Classical in
theorem cosShape : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (p : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (P : SBof I a), (i + 1 ≠ B.R.m → cosetIn p P = ∅) ∧ (i + 1 = B.R.m → (cosetIn p P).Nonempty ∧ (∀ y ∈ p.1.2, (frsF I.sel (I.tup a) p.1.1 P).symm y ∈ cosetIn p P) ∧ ∀ z ∈ cosetIn p P, (∀ z', z' ∈ cosetIn p P ↔ GlobalTheory.TwU.SameCoset I.sel (I.tup a) (I.cst a) P z' z) ∧ ∀ g g' : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i), g' ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 → CongE P.1 ((I.cst a).D P) g g' → GlobalTheory.TwU.SameCoset I.sel (I.tup a) (I.cst a) P (g z) z → ∀ z', g' z' ∈ cosetIn p P ↔ z' ∈ cosetIn p P) := by
  intro B X I hI u a i p P
  refine ⟨fun hi => ?_, fun hi => ?_⟩
  ·
    have h0 : p.1.2 = ∅ := by
      have h := p.2
      rw [ysAt_ys_of_ne (h := hi)] at h
      exact Set.mem_singleton_iff.mp h
    ext z
    simp [cosetIn, h0]
  · have hY := PtAt.mem_ybSet p hi
    unfold ybSet at hY
    obtain ⟨y₀, hy₀, hYeq⟩ := hY

    have hfr : ∀ x, (frsF I.sel (I.tup a) p.1.1 P) x ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N ↔
        x ∈ stdAt B.fields.E (B.R.N i) P.1 := by
      intro x
      simp only [frsF]
      split_ifs with h
      · exact (GlobalTheory.TopStep.liftFr_spec p.1.1.deco.2 ⟨P.1, h⟩).1 x
      · exact p.1.1.2 ⟨P.1, (Finset.mem_union.mp P.2).resolve_left h⟩ x
    have hF : ∀ w ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N,
        (frsF I.sel (I.tup a) p.1.1 P).symm w ∈ stdAt B.fields.E (B.R.N i) P.1 := by
      intro w hw
      rw [← hfr, LinearEquiv.apply_symm_apply]
      exact hw
    have hc : ((qOf P.1 : ℕ) : B.fields.E) ≠ 0 := by
      exact_mod_cast (GlobalTheory.GO.ChRoot.qOf_pos P.1).ne'
    have hpow : ∀ (S : Submodule (𝓞 B.fields.E) (Sp B.fields.E (B.R.N i))) (k : ℕ) (x : Sp B.fields.E (B.R.N i)),
        x ∈ S → ((qOf P.1 : ℕ) : B.fields.E) ^ k • x ∈ S := by
      intro S k x hx
      have h := pow_smul_mem S ((qOf P.1 : ℕ) : 𝓞 B.fields.E) k hx
      simpa using h
    have hY0 : y₀ ∈ p.1.2 := by
      rw [hYeq, Set.mem_setOf_eq, sub_self]
      exact zero_mem _
    have hY1 := (mem_locLat _ _ _ _).1 hy₀ P
    have hGL : ∀ g' : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i),
        g' ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 →
          ∀ x, g' x ∈ stdAt B.fields.E (B.R.N i) P.1 ↔ x ∈ stdAt B.fields.E (B.R.N i) P.1 := by
      intro g' hg'
      exact hg'
    by_cases hP : P.1 ∈ (B.primes X).vGs
    ·
      have hYl : ∀ y ∈ p.1.2, (((qOf P.1 : ℕ) : B.fields.E) ^ 0)⁻¹ • (y - y₀) ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N := by
        intro y hy
        rw [hYeq, Set.mem_setOf_eq] at hy
        have h := (mem_locLat _ _ _ _).1 hy P
        simpa [hP] using h
      have hy₀' : ((qOf P.1 : ℕ) : B.fields.E) ^ 1 • y₀ ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N := by
        simpa [hP] using hY1
      have hC : ∀ z, z ∈ cosetIn p P ↔ ∃ y ∈ p.1.2,
          (((qOf P.1 : ℕ) : B.fields.E) ^ 0)⁻¹ • (z - (frsF I.sel (I.tup a) p.1.1 P).symm y) ∈
            stdAt B.fields.E (B.R.N i) P.1 := by
        intro z
        simp only [cosetIn, Set.mem_setOf_eq, if_pos hP]
      have hSC : ∀ x y : Sp B.fields.E (B.R.N i), GlobalTheory.TwU.SameCoset I.sel (I.tup a) (I.cst a) P x y ↔
          (((qOf P.1 : ℕ) : B.fields.E) ^ 0)⁻¹ • (x - y) ∈ stdAt B.fields.E (B.R.N i) P.1 := by
        intro x y
        rw [GlobalTheory.GO.ChRoot.mem_stdAt']
        simp only [GlobalTheory.TwU.SameCoset, if_pos hP, Pi.smul_apply, smul_eq_mul]
      obtain ⟨k1, k2, k3⟩ := core (stdAt B.fields.E (B.R.N i) P.1) (Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N)
        (frsF I.sel (I.tup a) p.1.1 P) hF _ hc hpow p.1.2 y₀ 0 1 hY0 hYl hy₀' (cosetIn p P) hC
      refine ⟨k1, k2, fun z hz => ⟨fun z' => ((k3 z hz).1 z').trans (hSC z' z).symm, ?_⟩⟩
      intro g g' hg' hcong hgz z'
      have hD1 := (hI.idx_ok a).depthG P hP
      exact (k3 z hz).2 g g' _ (hGL g' hg') hcong (by omega) ((hSC _ _).1 hgz) z'
    ·
      have hYl : ∀ y ∈ p.1.2, (((qOf P.1 : ℕ) : B.fields.E) ^ (I.cst a).M)⁻¹ • (y - y₀) ∈
          Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N := by
        intro y hy
        rw [hYeq, Set.mem_setOf_eq] at hy
        have h := (mem_locLat _ _ _ _).1 hy P
        simpa [hP] using h
      have hy₀' : ((qOf P.1 : ℕ) : B.fields.E) ^ (I.cst a).M • y₀ ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N := by
        simpa [hP] using hY1
      have hC : ∀ z, z ∈ cosetIn p P ↔ ∃ y ∈ p.1.2,
          (((qOf P.1 : ℕ) : B.fields.E) ^ (I.cst a).M)⁻¹ • (z - (frsF I.sel (I.tup a) p.1.1 P).symm y) ∈
            stdAt B.fields.E (B.R.N i) P.1 := by
        intro z
        simp only [cosetIn, Set.mem_setOf_eq, if_neg hP]
      have hSC : ∀ x y : Sp B.fields.E (B.R.N i), GlobalTheory.TwU.SameCoset I.sel (I.tup a) (I.cst a) P x y ↔
          (((qOf P.1 : ℕ) : B.fields.E) ^ (I.cst a).M)⁻¹ • (x - y) ∈ stdAt B.fields.E (B.R.N i) P.1 := by
        intro x y
        rw [GlobalTheory.GO.ChRoot.mem_stdAt']
        simp only [GlobalTheory.TwU.SameCoset, if_neg hP, Pi.smul_apply, smul_eq_mul]
      obtain ⟨k1, k2, k3⟩ := core (stdAt B.fields.E (B.R.N i) P.1) (Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N)
        (frsF I.sel (I.tup a) p.1.1 P) hF _ hc hpow p.1.2 y₀ (I.cst a).M (I.cst a).M hY0 hYl hy₀' (cosetIn p P) hC
      refine ⟨k1, k2, fun z hz => ⟨fun z' => ((k3 z hz).1 z').trans (hSC z' z).symm, ?_⟩⟩
      intro g g' hg' hcong hgz z'
      have hD2 := (hI.idx_ok a).depthQ P hP
      exact (k3 z hz).2 g g' _ (hGL g' hg') hcong (by omega) ((hSC _ _).1 hgz) z'

end GlobalTheory.Mem.Col2.AdT.CosShape
end

