module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicConjugateCharacterStandardForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TupOfOneMemLabT
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.LocalToGlobal.NumberFieldFamilies.JMtInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianUpMoveAtLevelPrimePlace
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.HAt.UpMove

section G

variable {D : D7} {u : D.what₂.Word}


set_option maxHeartbeats 4000000 in
theorem upCl_of_crd (A : AtTTied u) (P : ∀ i hi, LvTied u A i hi) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT)
    (c : (D.mem u).C.cls i) (y : Formalism.L2.Herm.Ld D u i c)
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
    (hoff : ∀ q : HeightOneSpectrum (𝓞 D.host.E), q.asIdeal ≠ A.Pv v → q.asIdeal ≠ Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) (A.Pv v) →
      Formalism.HermitianLatticesTheory.localization₂ q.asIdeal (mulLat γ.1.1 (clsCrd D u i hi ((D.fm u).up i v c (prH A P i v c y)))) =
        Formalism.HermitianLatticesTheory.localization₂ q.asIdeal (clsCrd D u i hi c))
    (h3 : Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (mulLat γ.1.1 (clsCrd D u i hi ((D.fm u).up i v c (prH A P i v c y)))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.L2.Forms.Ld D u i hi c))
    (h4 : Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (mulLat γ.1.1 (Formalism.L2.Forms.Ld D u i hi ((D.fm u).up i v c (prH A P i v c y)))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.L2.Forms.Ld D u i hi c ⊔
          Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • (toLd i hi c y).1}))
    (h5 : ∀ (x : ↥(Formalism.L2.Forms.Ld D u i hi ((D.fm u).up i v c (prH A P i v c y))))
        (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ x.1) ∈ Formalism.L2.Forms.Ld D u i hi c),
        (D.fm u).fv i v _ ((P i hi).pr v _ x) = (D.fm u).fv i v c ((P i hi).pr v c ⟨_, hx⟩))
    (h6 : ∀ v', v' ≠ v → ∀ (z : ↥(Formalism.L2.Forms.Ld D u i hi c))
        (z' : ↥(Formalism.L2.Forms.Ld D u i hi ((D.fm u).up i v c (prH A P i v c y)))), z.1 = γ.1.1 *ᵥ z'.1 →
        (D.fm u).fv i v' _ ((P i hi).pr v' _ z') = (D.fm u).fv i v' c ((P i hi).pr v' c z)) :
    UpCl A P i v c y (gx i hi γ) := by

  let crdL := ((crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E))
  have inj : Function.Injective crdL := (crdN D i hi).injective
  have eCls : ∀ c' : (D.mem u).C.cls i, (D.clsLat u i c').map crdL = clsCrd D u i hi c' := fun _ => rfl
  have eLd : ∀ c' : (D.mem u).C.cls i, (Formalism.L2.Herm.Ld D u i c').map crdL = Formalism.L2.Forms.Ld D u i hi c' := fun c' =>
    dual_co D.sp.cm (D.sp.X i) (rankN D i hi) (D.clsLat u i c')
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro q hq hP hc
    haveI := hq.isPrime
    let q' : HeightOneSpectrum (𝓞 D.host.E) :=
      ⟨q, hq.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hq (RingOfIntegers.not_isField D.host.E)⟩
    apply Submodule.map_injective_of_injective inj
    rw [localization_map₂ hi, localization_map₂ hi, lc_gmap, eCls, eCls]
    exact hoff q' hP hc
  · apply Submodule.map_injective_of_injective inj
    rw [localization_map₂ hi, localization_map₂ hi, lc_gmap, eCls, eLd]
    exact h3
  · apply Submodule.map_injective_of_injective inj
    rw [localization_map₂ hi, localization_map₂ hi, lc_gmap, eLd, Submodule.map_sup, eLd, Submodule.map_span, Set.image_singleton]
    convert h4 using 4
    simp [crdL, toLd]
  · intro z hz
    rw [prH_eq A P hi v _ z, prH_eq A P hi v c ⟨_, hz⟩]
    have key : crdN D i hi (((D.mem u).A.T : D.host.E) • (gx i hi γ).1 (z : (D.sp.X i).V)) =
        (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ (toLd i hi _ z).1) := by
      rw [map_smul, crdN_gx]
      rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
      rfl
    have hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ (toLd i hi _ z).1) ∈ Formalism.L2.Forms.Ld D u i hi c :=
      key ▸ (mem_Ld i hi c _).1 hz
    have e : toLd i hi c ⟨_, hz⟩ = ⟨_, hx⟩ := Subtype.ext key
    rw [e]
    exact h5 _ hx
  · intro v' hv' z hz
    rw [prH_eq A P hi v' _ z, prH_eq A P hi v' c ⟨_, hz⟩]
    exact h6 v' hv' (toLd i hi c ⟨_, hz⟩) (toLd i hi _ z) (crdN_gx i hi γ _)

end G

section S

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}


set_option maxHeartbeats 4000000 in
theorem crd_up (T : FormsTiedSym D u Ch chOf) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT)
    (c : (D.mem u).C.cls i) (y : Formalism.L2.Herm.Ld D u i c)
    (hf : (D.fm u).fv i v c (prH T.atT T.lv i v c y) = 1)
    (hC : ∀ (h1 : 1 ≤ i) (h2 : i + 1 ≤ D.R.m) (c' : (D.mem u).C.cls i) (z : Formalism.L2.Forms.Ld D u i (le_of_succ_m h2) c')
      (z' : LdG D i (le_of_succ_m h2) (clsCrd D u i (le_of_succ_m h2) c')), z'.1 = z.1 →
        (T.lvC i h1 h2).pr v c' z' = (T.lv i (le_of_succ_m h2)).pr v c' z) :
    ∃ γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi),
      AdC T i hi c ((D.fm u).up i v c (prH T.atT T.lv i v c y)) γ.1 (T.atT.eV v).1 ∧
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ.1.1 (clsCrd D u i hi ((D.fm u).up i v c (prH T.atT T.lv i v c y)))) =
        Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Formalism.L2.Forms.Ld D u i hi c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ.1.1 (Formalism.L2.Forms.Ld D u i hi ((D.fm u).up i v c (prH T.atT T.lv i v c y)))) =
        Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Formalism.L2.Forms.Ld D u i hi c ⊔
          Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • (toLd i hi c y).1}) ∧
      ∀ (x : ↥(Formalism.L2.Forms.Ld D u i hi ((D.fm u).up i v c (prH T.atT T.lv i v c y))))
        (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ x.1) ∈ Formalism.L2.Forms.Ld D u i hi c),
        (D.fm u).fv i v _ ((T.lv i hi).pr v _ x) = (D.fm u).fv i v c ((T.lv i hi).pr v c ⟨_, hx⟩) := by
  have e1 : (T.lv i hi).pr v c (toLd i hi c y) = prH T.atT T.lv i v c y := (prH_eq T.atT T.lv hi v c y).symm
  rcases (show (i = 0 ∨ i = D.R.m) ∨ (1 ≤ i ∧ i + 1 ≤ D.R.m) by omega) with h | ⟨h1, h2⟩
  · have hz : (D.fm u).fv i v c ((T.lv i hi).pr v c (toLd i hi c y)) = 1 := by rw [e1]; exact hf
    have H0 := T.upN i hi h v c (toLd i hi c y) hz
    generalize (T.lv i hi).pr v c (toLd i hi c y) = t at H0 e1
    subst e1
    obtain ⟨γ, η, κ, hη, hy, h3, h4, h5, -⟩ := H0
    refine ⟨γ, ⟨fun h' => ⟨κ.1, κ.2, η.1, η.2, hη, hy⟩, fun h1 h2 => absurd h (by omega)⟩, h3, h4, h5⟩
  · have hl := le_of_succ_m h2
    have e0 : (T.lvC i h1 h2).pr v c (toLd i hi c y) = prH T.atT T.lv i v c y :=
      (hC h1 h2 c (toLd i hi c y) (toLd i hi c y) rfl).trans e1
    have hz : (D.fm u).fv i v c ((T.lvC i h1 h2).pr v c (toLd i hi c y)) = 1 := by rw [e0]; exact hf
    have H0 := T.upC i h1 h2 v (chOf i c) ⟨c, rfl⟩ (toLd i hi c y) hz
    generalize (T.lvC i h1 h2).pr v c (toLd i hi c y) = t at H0 e0
    subst e0
    obtain ⟨hβ, γ, η, κ, hη, hy, h3, h4, h5, -⟩ := H0
    refine ⟨γ, ⟨fun h => absurd h (by omega), fun h1' h2' => ⟨hβ, κ.1, κ.2, η.1, η.2, hη, hy⟩⟩, h3, h4, fun x hx => ?_⟩
    have := h5 x hx
    rwa [hC h1 h2 _ x x rfl, hC h1 h2 c ⟨_, hx⟩ ⟨_, hx⟩ rfl] at this

end S

end GlobalTheory.Mem.Col2.HAt.UpMove


open GlobalTheory.Mem.Col2.HAt.UpMove in
set_option maxHeartbeats 4000000 in
theorem GlobalTheory.Mem.Col2.HAt.UpMove.up_move : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i v (c : ((I.rec7 l Z).mem u).C.cls i) (y : Formalism.L2.Herm.Ld (I.rec7 l Z) u i c), ∃ γ, i ≤ (I.rec7 l Z).R.m → ((I.rec7 l Z).fm u).fv i v c (prH (F u).atT (F u).lv i v c y) = 1 → UpCl (F u).atT (F u).lv i v c y γ ∧ AdOf H u i c (((I.rec7 l Z).fm u).up i v c (prH (F u).atT (F u).lv i v c y)) γ v := by
  intro B X I hOk hPins l Z H F hStd hCar u i v c y
  by_cases hi : i ≤ (I.rec7 l Z).R.m
  swap
  · exact ⟨1, fun h => absurd h hi⟩
  by_cases hf : ((I.rec7 l Z).fm u).fv i v c (prH (F u).atT (F u).lv i v c y) = 1
  swap
  · exact ⟨1, fun _ h => absurd h hf⟩
  obtain ⟨γ, hAd, h3, h4, h5⟩ := crd_up (F u) i hi v c y hf
    (fun h1 h2 c' z z' e => (_root_.GlobalTheory.Mem.Col2.HAt.pr_lvC_eq_lv I hOk hPins l Z H F hStd hCar u i h1 h2 v c').1 z z' e)
  refine ⟨gx i hi γ, fun _ _ => ⟨upCl_of_crd (F u).atT (F u).lv i hi v c y γ ?_ h3 h4 h5 ?_,
    _root_.GlobalTheory.Mem.Col2.HAt.adOf_of_adC I hOk hPins l Z H F hStd hCar u i hi v c _ γ hAd⟩⟩
  · intro q hP hc
    refine _root_.GlobalTheory.Mem.Col2.SameOff.use₆ I hOk hPins l Z H F hStd hCar u i hi v c _ γ.1 hAd q fun hq => ?_
    rcases GlobalTheory.T.host_primes_over_level_place I hOk hPins l Z H F hStd hCar u v q hq with h | h
    · exact hP h
    · exact hc h
  · intro v' hv' z z' e
    exact _root_.GlobalTheory.Mem.Col2.HAt.FvOff.fv_eq_of_adC I hOk hPins l Z H F hStd hCar u i hi v v' c _ γ.1 hAd hv' z z' e
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertHeckeOperatorIndepOfInertDatum
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SatInd

section Field

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem indepDatum_memGU_iff (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)) {n : ℕ}
    (M : GL (Fin n) K) :
    Formalism.UG.bc (n := Fin n) (g : K →+* K) M ∈ Formalism.UG.GU σ' n ↔ M ∈ Formalism.UG.GU σ n := by
  show Formalism.UG.cT σ' (((M : Matrix (Fin n) (Fin n) K)).map (g : K →+* K)) * Formalism.UG.antiJ K n *
      ((M : Matrix (Fin n) (Fin n) K)).map (g : K →+* K) = Formalism.UG.antiJ K n ↔
    Formalism.UG.cT σ (M : Matrix (Fin n) (Fin n) K) * Formalism.UG.antiJ K n * (M : Matrix (Fin n) (Fin n) K) =
      Formalism.UG.antiJ K n
  have e : Formalism.UG.cT σ' (((M : Matrix (Fin n) (Fin n) K)).map (g : K →+* K)) * Formalism.UG.antiJ K n *
      ((M : Matrix (Fin n) (Fin n) K)).map (g : K →+* K) =
      (Formalism.UG.cT σ (M : Matrix (Fin n) (Fin n) K) * Formalism.UG.antiJ K n * (M : Matrix (Fin n) (Fin n) K)).map
        (g : K →+* K) := by
    rw [Matrix.map_mul, Matrix.map_mul, antiJ_map, cT_map (g : K →+* K) σ σ' hg]
  rw [e]
  constructor
  · intro h
    exact Matrix.map_injective g.injective (h.trans (antiJ_map (g : K →+* K) n).symm)
  · intro h
    rw [h, antiJ_map]

theorem indepDatum_intRange (g : K ≃+* K) (hint : ∀ x, x ∈ Formalism.UG.intL K → g x ∈ Formalism.UG.intL K) {n : ℕ}
    (M : GL (Fin n) K) (hM : M ∈ (Formalism.UG.bc (n := Fin n) (Formalism.UG.intL K).subtype).range) :
    Formalism.UG.bc (n := Fin n) (g : K →+* K) M ∈ (Formalism.UG.bc (n := Fin n) (Formalism.UG.intL K).subtype).range := by
  obtain ⟨p, rfl⟩ := hM
  refine ⟨Formalism.UG.bc (n := Fin n) ((g : K →+* K).restrict (Formalism.UG.intL K) (Formalism.UG.intL K)
    (fun x hx => hint x hx)) p, ?_⟩
  ext i j
  rfl

end Field

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}

theorem indepDatum_bc_e (Dv Dv' : InertDatum L n v w)
    (Y : GL (Fin n) (L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L))) :
    Formalism.UG.bc (n := Fin n) (Dv'.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+*
              w.adicCompletion L) Y =
      Formalism.UG.bc (n := Fin n) ((gEquiv Dv Dv' : w.adicCompletion L ≃+* w.adicCompletion L) :
        w.adicCompletion L →+* w.adicCompletion L)
        (Formalism.UG.bc (n := Fin n) (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+*
          w.adicCompletion L) Y) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  exact (gEquiv_e Dv Dv' _).symm

def indepDatumK (Dv Dv' : InertDatum L n v w) : GL (Fin n) (w.adicCompletion L) :=
  (Formalism.UG.bc (n := Fin n) ((gEquiv Dv Dv' : w.adicCompletion L ≃+* w.adicCompletion L) :
    w.adicCompletion L →+* w.adicCompletion L) Dv.P)⁻¹ * Dv'.P

theorem indepDatum_loc (Dv Dv' : InertDatum L n v w) (x : GAf L n) :
    Dv'.loc x = (indepDatumK Dv Dv')⁻¹ * Formalism.UG.bc (n := Fin n) ((gEquiv Dv Dv' :
      w.adicCompletion L ≃+* w.adicCompletion L) : w.adicCompletion L →+* w.adicCompletion L) (Dv.loc x) *
        indepDatumK Dv Dv' := by
  simp only [InertDatum.loc, indepDatumK, map_mul, map_inv, indepDatum_bc_e Dv Dv']
  group

theorem indepDatumK_memGU (Dv Dv' : InertDatum L n v w) : indepDatumK Dv Dv' ∈ Formalism.UG.GU Dv'.σw n := by
  set g : w.adicCompletion L →+* w.adicCompletion L := ((gEquiv Dv Dv' : w.adicCompletion L ≃+* w.adicCompletion L) :
    w.adicCompletion L →+* w.adicCompletion L) with hgdef
  set Q : Matrix (Fin n) (Fin n) (w.adicCompletion L) := ((Formalism.UG.bc (n := Fin n) g Dv.P :
    GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) with hQdef
  set Qi : Matrix (Fin n) (Fin n) (w.adicCompletion L) := (((Formalism.UG.bc (n := Fin n) g Dv.P)⁻¹ :
    GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) with hQidef
  have hQ : Formalism.UG.cT Dv'.σw Q * Q = Formalism.UG.antiJ (w.adicCompletion L) n := by
    have hmap : Q = (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)).map g := rfl
    rw [hmap, cT_map g Dv.σw Dv'.σw (gEquiv_comm Dv Dv'), ← Matrix.map_mul, Dv.Panti, antiJ_map]
  have h1 : Q * Qi = 1 := by rw [hQdef, hQidef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : Formalism.UG.cT Dv'.σw Qi * Formalism.UG.cT Dv'.σw Q = 1 := by rw [← Formalism.UG.cT_mul, h1, Formalism.UG.cT_one]
  show Formalism.UG.cT Dv'.σw (Qi * (Dv'.P : Matrix (Fin n) (Fin n) (w.adicCompletion L))) *
      Formalism.UG.antiJ (w.adicCompletion L) n * (Qi * (Dv'.P : Matrix (Fin n) (Fin n) (w.adicCompletion L))) =
    Formalism.UG.antiJ (w.adicCompletion L) n
  rw [← hQ, Formalism.UG.cT_mul]
  calc Formalism.UG.cT Dv'.σw (Dv'.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) * Formalism.UG.cT Dv'.σw Qi *
        (Formalism.UG.cT Dv'.σw Q * Q) * (Qi * (Dv'.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)))
      = Formalism.UG.cT Dv'.σw (Dv'.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) *
          (Formalism.UG.cT Dv'.σw Qi * Formalism.UG.cT Dv'.σw Q) * (Q * Qi) *
          (Dv'.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT Dv'.σw (Dv'.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) *
          (Dv'.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) := by
        rw [h1, h2, Matrix.mul_one, Matrix.mul_one]
    _ = Formalism.UG.cT Dv'.σw Q * Q := by rw [Dv'.Panti, hQ]

theorem indepDatumK_memKU (Dv Dv' : InertDatum L n v w) :
    (⟨indepDatumK Dv Dv', indepDatumK_memGU Dv Dv'⟩ : Formalism.UG.GU Dv'.σw n) ∈ Formalism.UG.KU Dv'.σw n := by
  rw [Formalism.UG.KU, Subgroup.mem_subgroupOf]
  refine ⟨indepDatumK_memGU Dv Dv', ?_⟩
  obtain ⟨p1, hp1⟩ := indepDatum_intRange (gEquiv Dv Dv') (fun x hx => (gEquiv_intL Dv Dv' x).1 hx) _ Dv.Pint
  obtain ⟨p2, hp2⟩ := Dv'.Pint
  refine ⟨p1⁻¹ * p2, ?_⟩
  rw [map_mul, map_inv, hp1, hp2]
  rfl

theorem indepDatum_hval (Dv Dv' : InertDatum L n v w) (h' : Formalism.UG.GU Dv'.σw n → ℂ)
    (hbi : IsBiInv (Formalism.UG.KU Dv'.σw n) h') (x : GAf L n) :
    Dv'.hval h' (Dv'.loc x) =
      Dv.hval (fun y => h' (guMap (gEquiv Dv Dv') (gEquiv_comm Dv Dv') n y)) (Dv.loc x) := by
  have hk := indepDatumK_memGU Dv Dv'
  have hloc := indepDatum_loc Dv Dv' x
  set g : w.adicCompletion L →+* w.adicCompletion L := ((gEquiv Dv Dv' : w.adicCompletion L ≃+* w.adicCompletion L) :
    w.adicCompletion L →+* w.adicCompletion L) with hgdef
  unfold InertDatum.hval
  by_cases hy : Dv.loc x ∈ Formalism.UG.GU Dv.σw n
  · have hgy : Formalism.UG.bc (n := Fin n) g (Dv.loc x) ∈ Formalism.UG.GU Dv'.σw n :=
      (indepDatum_memGU_iff (gEquiv Dv Dv') (gEquiv_comm Dv Dv') _).2 hy
    have hy' : Dv'.loc x ∈ Formalism.UG.GU Dv'.σw n := by
      rw [hloc]; exact mul_mem (mul_mem (inv_mem hk) hgy) hk
    rw [dite_eq_left hy', dite_eq_left hy]
    have hb := hbi (⟨⟨indepDatumK Dv Dv', hk⟩, indepDatumK_memKU Dv Dv'⟩ : Formalism.UG.KU Dv'.σw n)⁻¹
      ⟨⟨indepDatumK Dv Dv', hk⟩, indepDatumK_memKU Dv Dv'⟩
      (guMap (gEquiv Dv Dv') (gEquiv_comm Dv Dv') n ⟨Dv.loc x, hy⟩)
    refine Eq.trans (congrArg h' ?_) hb
    apply Subtype.ext
    change Dv'.loc x = _
    rw [hloc]
    rfl
  · have hy' : Dv'.loc x ∉ Formalism.UG.GU Dv'.σw n := by
      intro h
      apply hy
      rw [← indepDatum_memGU_iff (gEquiv Dv Dv') (gEquiv_comm Dv Dv')]
      have he : Formalism.UG.bc (n := Fin n) g (Dv.loc x) =
          indepDatumK Dv Dv' * Dv'.loc x * (indepDatumK Dv Dv')⁻¹ := by
        rw [hloc]; group
      rw [he]
      exact mul_mem (mul_mem hk h) (inv_mem hk)
    rw [dite_eq_right hy', dite_eq_right hy]

theorem heckeFunI_indepDatum : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv Dv' : InertDatum L n v w) (U : Subgroup (GAf L n)) (W : Type) [AddCommGroup W] [Module ℂ W]
    (h' : GU Dv'.σw n → ℂ), IsBiInv (KU Dv'.σw n) h' → ∀ f : GAf L n → W,
    heckeFunI L n U Dv' h' f =
      heckeFunI L n U Dv (fun y => h' (guMap (gEquiv Dv Dv') (gEquiv_comm Dv Dv') n y)) f := by
  intro L _ _ _ n v w Dv Dv' U W _ _ h' hbi f
  funext g
  unfold heckeFunI
  refine finsum_congr fun c => ?_
  by_cases hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x
  · rw [dite_eq_left hc, dite_eq_left hc, indepDatum_hval Dv Dv' h' hbi]
  · rw [dite_eq_right hc, dite_eq_right hc]

end GlobalTheory.SatInd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertSatakeParametersEqOfIso
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd

namespace GlobalTheory.SatIso

theorem heckeFunI_eq_sum {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}
    (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)) (h : GU Dv.σw n → ℂ)
    (hfin : Set.Finite {c : GAf L n ⧸ U | ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x ∧
      Dv.hval h (Dv.loc x) ≠ 0}) :
    ∃ (C : Finset (GAf L n ⧸ U)) (a : GAf L n ⧸ U → ℂ) (x : GAf L n ⧸ U → GAf L n),
      ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (φ : GAf L n → W),
        heckeFunI L n U Dv h φ = ∑ c ∈ C, a c • NG.rt L n (x c) φ := by
  classical
  refine ⟨hfin.toFinset,
    fun c => if hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x then
      Dv.hval h (Dv.loc hc.choose) else 0,
    fun c => if hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x then
      hc.choose else 1, fun W _ _ φ => ?_⟩
  funext g
  unfold heckeFunI
  rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
  · rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x
    · simp only [dif_pos hc]
      rfl
    · simp only [dif_neg hc, zero_smul]
      rfl
  · intro c hc0
    rw [Function.mem_support] at hc0
    by_cases hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x
    · rw [dif_pos hc] at hc0
      rw [Set.Finite.coe_toFinset]
      refine ⟨hc.choose, hc.choose_spec.1, hc.choose_spec.2, fun h0 => hc0 ?_⟩
      rw [h0, zero_smul]
    · exact absurd (dif_neg hc) hc0

theorem satAt_of_iso (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π π' : NG.AutRep L n)
    (hiso : π.Iso π') (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ)
    (hfin : ∀ (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) →
      ∀ h ∈ Hecke ℂ (KU Dv.σw n), Set.Finite {c : GAf L n ⧸ U | ∃ x : GAf L n,
        (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x ∧ Dv.hval h (Dv.loc x) ≠ 0})
    (hs : NG.SatAt π Dv α) : NG.SatAt π' Dv α := by
  obtain ⟨f, hfS, hf0, U, hU, hUv, hH⟩ := hs
  obtain ⟨T, hT⟩ := hiso.2
  refine ⟨(T ⟨f, hfS⟩ : π'.S), (T ⟨f, hfS⟩).2, ?_, U, ?_, hUv, ?_⟩
  · intro h0
    have h1 : T ⟨f, hfS⟩ = 0 := Subtype.ext h0
    have h2 : (⟨f, hfS⟩ : π.S) = 0 := T.map_eq_zero_iff.mp h1
    exact hf0 (congrArg Subtype.val h2)
  · intro κ hκ
    exact (hT κ ⟨f, hfS⟩ ⟨f, hfS⟩ (hU κ hκ).symm).symm
  · intro h hh
    obtain ⟨C, a, x, hC⟩ := heckeFunI_eq_sum Dv U h (hfin U hUv h hh)
    have e := hH h hh
    rw [hC] at e
    rw [hC]
    have e1 : (∑ c ∈ C, a c • (⟨NG.rt L n (x c) f, π.irrS.1.stable _ _ hfS⟩ : π.S)) =
        SatU Dv.ϖ (qV (maximalRealSubfield L) v) h α • (⟨f, hfS⟩ : π.S) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      exact e
    have e2 := congrArg (fun y => ((T y : π'.S) : GAf L n → π'.W)) e1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul] at e2
    rw [← e2]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hT (x c) ⟨f, hfS⟩ ⟨NG.rt L n (x c) f, π.irrS.1.stable _ _ hfS⟩ rfl]

end GlobalTheory.SatIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCentralGroupAlgebraIdempotentUniversal
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.HeightCounting.FormsStep

theorem eIdem_all : ∀ D : D7, EIdem D := by
  intro D
  haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  let φ : ↥D.LL0 →+* ℂ := D.what₂.embLL.comp (algebraMap ↥D.LL0 D.what₂.LL)
  have hφ : Function.Injective φ := φ.injective
  let M := MonoidAlgebra.mapRingHom (G0g D.nd) φ
  have hM : Function.Injective M := by
    intro x y h
    refine MonoidAlgebra.ext (Finsupp.ext fun g => hφ ?_)
    have := congrArg (fun z => z.coeff g) h
    simpa [M, MonoidAlgebra.mapRingHom] using this
  have he : M (eL D) = D.ntypes.e0 := by
    refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
    have := D.nStage_trivialCharacter_coeff_eq g
    simpa [M, eL, MonoidAlgebra.mapRingHom, φ] using this
  have hc : ∀ a, D.ntypes.e0 * a = a * D.ntypes.e0 := fun a => by
    rw [← GlobalTheory.RowLev.ES_good]; exact GlobalTheory.RowLev.ES_comm _ a
  have hi : D.ntypes.e0 * D.ntypes.e0 = D.ntypes.e0 := by
    rw [← GlobalTheory.RowLev.ES_good]; exact GlobalTheory.RowLev.ES_mul_self _
  have hs : ∀ g : G0g D.nd, M (MonoidAlgebra.of _ _ g) = MonoidAlgebra.of _ _ g := fun g => by
    simp [M, MonoidAlgebra.of_apply, MonoidAlgebra.mapRingHom]
  refine ⟨hM ?_, fun g => hM ?_⟩
  · rw [map_mul, he, hi]
  · rw [map_mul, map_mul, he, hs, hc]

end GlobalTheory.HeightCounting.FormsStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftedHeckeOperatorsAtGeneratorsCommute
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.HeckeLocCommute

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

theorem hLC_commute : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q), HeckeStdPlain → GenHyp M C.Q → (∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) → (∀ j w v k v' k', Commute (hLC (mt0 M) C.Q hR j w v k) (hLC (mt0 M) C.Q hR j w v' k')) := by
  classical
  intro D M C hR hstd hgen hsplit j w v k v' k'
  by_cases h : (1 ≤ j ∧ j ≤ D.R.m) ∧ GenAt0 D.host (D.what₂.places.resChar w) (C.Q w) v k
  swap
  · have : hLC (mt0 M) C.Q hR j w v k = 0 := by unfold hLC; rw [dite_eq_right h]
    rw [this]; exact Commute.zero_left _
  by_cases h' : (1 ≤ j ∧ j ≤ D.R.m) ∧ GenAt0 D.host (D.what₂.places.resChar w) (C.Q w) v' k'
  swap
  · have : hLC (mt0 M) C.Q hR j w v' k' = 0 := by unfold hLC; rw [dite_eq_right h']
    rw [this]; exact Commute.zero_right _
  obtain ⟨⟨h1, h2⟩, hg⟩ := h
  obtain ⟨-, hg'⟩ := h'
  obtain ⟨B, hB, hBv⟩ := hgen w j h1 h2
  obtain ⟨s, ϖ, hc, hu⟩ := hsplit v hg.1
  obtain ⟨s', ϖ', hc', hu'⟩ := hsplit v' hg'.1
  have hsB : s.v ∉ B := hBv v k s hg hc
  have hsB' : s'.v ∉ B := hBv v' k' s' hg' hc'
  have hstd' := hstd D.host.E D.R.nV (M (D.what₂.muTw w) j h1 h2).wt (M (D.what₂.muTw w) j h1 h2).J
    (M (D.what₂.muTw w) j h1 h2).χ B (M (D.what₂.muTw w) j h1 h2).J_open hB s ϖ k hsB hu hg.2.2.2.2.1 hg.2.2.2.2.2
  have hcomm := hstd'.2.2.1 s' ϖ' k' hsB' hu' hg'.2.2.2.2.1 hg'.2.2.2.2.2
  rw [commute_iff_eq]
  ext x
  apply Formalism.L2.Fam.NPC.LatticeFinitenessFree.jMt_injective
  apply (M (D.what₂.muTw w) j h1 h2).real_inj
  have hf : (M (D.what₂.muTw w) j h1 h2).real (D.what₂.jMt (D.what₂.muTw w) j x) ∈
      NG.TypeSp (M (D.what₂.muTw w) j h1 h2).wt.ρ (M (D.what₂.muTw w) j h1 h2).J (M (D.what₂.muTw w) j h1 h2).χ := by
    rw [← (M (D.what₂.muTw w) j h1 h2).real_range]; exact LinearMap.mem_range_self _ _
  have e1 := hLC_spec (mt0 M) C.Q hR j w v k h1 h2 hg s ϖ hc hu
  have e2 := hLC_spec (mt0 M) C.Q hR j w v' k' h1 h2 hg' s' ϖ' hc' hu'
  simp only [Module.End.mul_apply]
  change (mt0 M (D.what₂.muTw w) j h1 h2).real _ = (mt0 M (D.what₂.muTw w) j h1 h2).real _
  rw [e1, e2, e2, e1]
  exact hcomm _ hf

end GlobalTheory.HeckeLocCommute
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldOverPlaceAlgClosureStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_field_over_place_alg_closure : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → Nonempty (IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) := by
  first | exact @GlobalTheory.ResidueBar.residueField_ringEquiv_fbar | exact GlobalTheory.ResidueBar.residueField_ringEquiv_fbar | (intros; apply GlobalTheory.ResidueBar.residueField_ringEquiv_fbar <;> assumption)
end

