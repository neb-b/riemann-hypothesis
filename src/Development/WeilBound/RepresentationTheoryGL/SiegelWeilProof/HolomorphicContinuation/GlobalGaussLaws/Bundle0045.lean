module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0043
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0044
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0040
public import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ActsAwayNbar
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open AW

namespace AwayH

variable {D : D7} {n : ℕ}

def ActsAway {θ : InfFam D} {V : HSp D} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (τ : D.what₂.Tau)
    (fr : Matrix (Fin V.rank) (Fin V.rank) ℂ) (x : G D n) : Prop :=
  ∃ A : (Mx D V.rank n → ℂ) → (Mx D V.rank n → ℂ), ∀ Ψ (hΨ : AwayCls θ τ fr Ψ), AwayCls θ τ fr (A Ψ) ∧
    ∀ f (hf : IsSch f), (ω x ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr f (A Ψ)

section

variable {θ : InfFam D} {V : HSp D} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {τ : D.what₂.Tau}
  {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}

theorem mk_eq_tens {Φ : schwartzA θ V.rank n} {Ψ : Mx D V.rank n → ℂ} (hΨ : AwayCls θ τ fr Ψ)
    {f : (Fin V.rank → Fin n → ℂ) → ℂ} (hf : IsSch f) (h : Φ.1 = tens θ τ fr f Ψ) : Φ = ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩ :=
  Subtype.ext h

theorem actsAway_one : ActsAway ω τ fr 1 :=
  ⟨id, fun Ψ hΨ => ⟨hΨ, fun f hf => by simp [map_one]⟩⟩

theorem actsAway_mul {x y : G D n} (hx : ActsAway ω τ fr x) (hy : ActsAway ω τ fr y) : ActsAway ω τ fr (x * y) := by
  obtain ⟨Ax, hAx⟩ := hx
  obtain ⟨Ay, hAy⟩ := hy
  refine ⟨fun Ψ => Ax (Ay Ψ), fun Ψ hΨ => ⟨(hAx _ (hAy Ψ hΨ).1).1, fun f hf => ?_⟩⟩
  rw [map_mul, Module.End.mul_apply, mk_eq_tens (hAy Ψ hΨ).1 hf ((hAy Ψ hΨ).2 f hf), (hAx _ (hAy Ψ hΨ).1).2 f hf]

theorem awayCls_smul {Ψ : Mx D V.rank n → ℂ} (hΨ : AwayCls θ τ fr Ψ) (β : ℂ) :
    AwayCls θ τ fr (fun x => β * Ψ x) := by
  refine ⟨fun x x' h1 h2 => by show β * Ψ x = β * Ψ x'; rw [hΨ.1 x x' h1 h2], fun f hf => ?_⟩
  have : tens θ τ fr f (fun x => β * Ψ x) = β • tens θ τ fr f Ψ := by
    funext x; simp only [tens, Pi.smul_apply, smul_eq_mul]; ring
  rw [this]; exact Submodule.smul_mem _ β (hΨ.2 f hf)

variable {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {μ : Measure (Mx D V.rank n)}

theorem actsAway_n (hω : IsWeilSch ψ χ θ V μ ω) (hθ : IsInfFam θ) {x : G D n} (hx : IsTrivAt θ τ x) {b : Mx D n n}
    (h : mat x = blk4 1 b 0 1) : ActsAway ω τ fr x := by
  have hb := compAt_b_zero hx h
  let e : Mx D V.rank n → ℂ := fun x0 => ψ (halfTr (Matrix.trace (b ⬝ inner V x0 x0 : Mx D n n)))
  have key : ∀ Φ : schwartzA θ V.rank n, (ω x Φ).1 = fun x0 => e x0 * Φ.1 x0 :=
    fun Φ => funext fun x0 => hω.unip x b h Φ x0
  refine ⟨fun Ψ x0 => e x0 * Ψ x0, fun Ψ hΨ => ?_⟩
  have hform : ∀ f (hf : IsSch f),
      (ω x ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr f (fun x0 => e x0 * Ψ x0) := by
    intro f hf
    rw [key]
    funext x0
    simp only [tens]
    ring
  refine ⟨⟨fun x0 x0' h1 h2 => ?_, fun f hf => ?_⟩, hform⟩
  · show e x0 * Ψ x0 = e x0' * Ψ x0'
    have he : e x0 = e x0' := by
      show ψ _ = ψ _
      rw [unipArg_away hθ V hb ⟨h1, h2⟩]
    rw [he, hΨ.1 x0 x0' h1 h2]
  · rw [← hform f hf]; exact (ω x _).2

theorem actsAway_m (hω : IsWeilSch ψ χ θ V μ ω) {x : G D n} (hx : IsTrivAt θ τ x) {a d : Mx D n n}
    (h : mat x = blk4 a 0 0 d) : ActsAway ω τ fr x := by
  obtain ⟨a', ha', hd⟩ := levi_blocks x h
  have ha1 : compAt θ τ a'.1 = 1 := by rw [ha']; exact compAt_a_one hx h
  let cst : ℂ := (χ (Matrix.GeneralLinearGroup.det a') : ℂ) *
    npow (absA D (Matrix.GeneralLinearGroup.det a')) ((V.rank : ℂ) / 2)
  have hm : mat x = blk4 a'.1 0 0 (adj (a'⁻¹).1) := by rw [h, ha', hd]
  have key : ∀ Φ : schwartzA θ V.rank n, (ω x Φ).1 = fun x0 : Mx D V.rank n => cst * Φ.1 (x0 ⬝ a'.1) :=
    fun Φ => funext fun x0 => hω.levi x a' hm Φ x0
  refine ⟨fun Ψ (x0 : Mx D V.rank n) => cst * Ψ (x0 ⬝ a'.1), fun Ψ hΨ => ?_⟩
  have hform : ∀ f (hf : IsSch f),
      (ω x ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr f (fun x0 : Mx D V.rank n => cst * Ψ (x0 ⬝ a'.1)) := by
    intro f hf
    rw [key]
    funext x0
    simp only [tens]
    rw [compAt_mul_of_one x0 a'.1 ha1]
    ring
  refine ⟨⟨fun x0 x0' h1 h2 => ?_, fun f hf => ?_⟩, hform⟩
  · have hag := agree_mul_right a'.1 (⟨h1, h2⟩ : AgreeAway θ τ x0 x0')
    show cst * Ψ (x0 ⬝ a'.1) = cst * Ψ (x0' ⬝ a'.1)
    rw [hΨ.1 _ _ hag.1 hag.2]
  · rw [← hform f hf]; exact (ω x _).2

end

theorem actsAway_nbar (hFT : FTfact) {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {H : G D n → ℝ≥0}
    {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ν : Measure (GA D V)}
    {τ : D.what₂.Tau} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} {ι : GR n →* G D n}
    (hcx : Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι) {x : G D n} (hx : IsTrivAt θ τ x) {c : Mx D n n}
    (h : mat x = blk4 1 0 c 1) : ActsAway ω τ fr x := by
  obtain ⟨w, hw⟩ := exists_w D n
  have hy : mat (w⁻¹ * x * w) = blk4 1 (-c) 0 1 := mat_w_conj hw h
  have hyt : IsTrivAt θ τ (w⁻¹ * x * w) := trivAt_conj w hx
  obtain ⟨An, hAn⟩ := actsAway_n (fr := fr) hcx.hω hcx.hθ hyt hy
  obtain ⟨κ, A, A', hκ, hF⟩ := hFT D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx w hw
  have hxy : x = w * (w⁻¹ * x * w) * w⁻¹ := by group
  let S : ((Fin V.rank → Fin n → ℂ) → ℂ) → ((Fin V.rank → Fin n → ℂ) → ℂ) :=
    fun f u => κ * ftLoc ε (tLoc l τ) (fun u => κ⁻¹ * ftLoc ε (-tLoc l τ) f u) u
  have chain : ∀ (B : (Mx D V.rank n → ℂ) → (Mx D V.rank n → ℂ)) (z : G D n),
      (∀ Ψ (hΨ : AwayCls θ τ fr Ψ), AwayCls θ τ fr (B Ψ) ∧
        ∀ f (hf : IsSch f), (ω z ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr f (B Ψ)) →
      ∀ Ψ (hΨ : AwayCls θ τ fr Ψ) f (hf : IsSch f),
        (ω (w * z * w⁻¹) ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr (S f) (A (B (A' Ψ))) := by
    intro B z hB Ψ hΨ f hf
    obtain ⟨_, hA'1, hfs⟩ := hF Ψ hΨ
    obtain ⟨_, hs2, _, e2⟩ := hfs f hf
    have hB1 := hB (A' Ψ) hA'1
    obtain ⟨_, _, hfs2⟩ := hF (B (A' Ψ)) hB1.1
    obtain ⟨_, _, e3, _⟩ := hfs2 _ hs2
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, mk_eq_tens hA'1 hs2 e2,
      mk_eq_tens hB1.1 hs2 (hB1.2 _ hs2), e3]
  have ident : ∀ Ψ (hΨ : AwayCls θ τ fr Ψ) f (hf : IsSch f),
      tens θ τ fr f Ψ = tens θ τ fr (S f) (A (A' Ψ)) := by
    intro Ψ hΨ f hf
    have := chain id 1 (fun Ψ hΨ => ⟨hΨ, fun f hf => by simp [map_one]⟩) Ψ hΨ f hf
    simpa using this
  have hdet : IsUnit fr.det := hcx.hfr.1
  classical
  by_cases hex : ∃ Ψ0 : Mx D V.rank n → ℂ, AwayCls θ τ fr Ψ0 ∧ ∃ x0 : Mx D V.rank n, Ψ0 x0 ≠ 0
  · obtain ⟨Ψ0, h0, x0, hne⟩ := hex
    have hAA0 : AwayCls θ τ fr (A (A' Ψ0)) := (hF _ (hF Ψ0 h0).2.1).1
    obtain ⟨f0, hf0, hf0ne⟩ := exists_sch_ne (fr⁻¹ * compAt θ τ x0)
    have e0 := congrFun (ident Ψ0 h0 f0 hf0) x0
    simp only [tens] at e0
    have hα : A (A' Ψ0) x0 ≠ 0 := by
      intro h0'
      rw [h0', mul_zero] at e0
      exact mul_ne_zero hf0ne hne e0
    let β : ℂ := Ψ0 x0 / A (A' Ψ0) x0
    have hS : ∀ f, IsSch f → ∀ u, S f u = β * f u := by
      intro f hf u
      obtain ⟨z, hz⟩ := exists_compAt (τ := τ) hcx.hθ (fr * Matrix.of u)
      obtain ⟨x1, hx1, hag⟩ := exists_change_tau (τ := τ) hcx.hθ x0 z
      have hu : fr⁻¹ * compAt θ τ x1 = Matrix.of u := by
        rw [hx1, hz, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
      have e := congrFun (ident Ψ0 h0 f hf) x1
      simp only [tens] at e
      rw [hu, h0.1 x1 x0 hag.1 hag.2, hAA0.1 x1 x0 hag.1 hag.2] at e
      have e' : f u * Ψ0 x0 = S f u * A (A' Ψ0) x0 := e
      show S f u = Ψ0 x0 / A (A' Ψ0) x0 * f u
      field_simp
      linear_combination -e'
    refine ⟨fun Ψ x0 => β * A (An (A' Ψ)) x0, fun Ψ hΨ => ?_⟩
    have hA'1 := (hF Ψ hΨ).2.1
    have hAn1 := (hAn (A' Ψ) hA'1).1
    have hAA := (hF _ hAn1).1
    refine ⟨awayCls_smul hAA β, fun f hf => ?_⟩
    rw [hxy, chain An _ hAn Ψ hΨ f hf]
    funext x1
    simp only [tens]
    have hh : S f (fr⁻¹ * compAt θ τ x1) = β * f (fr⁻¹ * compAt θ τ x1) := hS f hf _
    rw [hh]
    ring
  · push Not at hex
    refine ⟨fun _ _ => 0, fun Ψ hΨ => ⟨⟨fun _ _ _ _ => rfl, fun f hf => ?_⟩, fun f hf => ?_⟩⟩
    · have : tens θ τ fr f (fun _ => (0 : ℂ)) = 0 := by funext x0; simp [tens]
      rw [this]; exact Submodule.zero_mem _
    · have h0 : (⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩ : schwartzA θ V.rank n) = 0 :=
        Subtype.ext (funext fun x0 => by simp [tens, hex Ψ hΨ x0])
      rw [h0, map_zero]
      funext x0
      simp [tens]

end AwayH

open AwayH

theorem awayAct_of : GenA → FTfact → DecompAway → AwayAct := by
  intro hG hFT hDA D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx x hx
  have hmem := mem_closure_AG hG hDA hcx.hθ hcx.hι x hx
  clear hx
  have key : ActsAway ω τ fr x := by
    induction hmem using Submonoid.closure_induction with
    | mem y hy =>
      obtain ⟨hyt, ⟨b, hb⟩ | ⟨a, d, hm⟩ | ⟨c, hc⟩⟩ := hy
      · exact actsAway_n hcx.hω hcx.hθ hyt hb
      · exact actsAway_m hcx.hω hyt hm
      · exact actsAway_nbar hFT hcx hyt hc
    | one => exact actsAway_one
    | mul y z _ _ hy hz => exact actsAway_mul hy hz
  exact key

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ContinuousKer
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTH

open PositivityTheory.Rg.Sw.Glob.FTP
open Classical

variable {D : D7} {n m : ℕ}

theorem norm_ker (ε : Fin m → Bool) (t : ℝ) (v u : Fin m → Fin n → ℂ) : ‖ker ε t v u‖ = 1 := by
  unfold ker
  rw [show Complex.I * ((2 * t : ℝ) : ℂ) * ((((Matrix.of v)ᴴ * Matrix.diagonal (sgn ε) * Matrix.of u).trace.re : ℝ) : ℂ) =
      ((2 * t * ((Matrix.of v)ᴴ * Matrix.diagonal (sgn ε) * Matrix.of u).trace.re : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem continuous_ker (ε : Fin m → Bool) (t : ℝ) (v : Fin m → Fin n → ℂ) : Continuous (ker ε t v) := by
  unfold ker
  refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp ?_)))
  have h2 : Continuous fun u : Fin m → Fin n → ℂ => Matrix.of u := continuous_id
  have h : Continuous fun u : Fin m → Fin n → ℂ => ((Matrix.of v)ᴴ * Matrix.diagonal (sgn ε) * Matrix.of u) :=
    continuous_const.matrix_mul h2
  exact h.matrix_trace

def Aw (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (θ : InfFam D) (τ : D.what₂.Tau)
    (fr : Matrix (Fin V.rank) (Fin V.rank) ℂ) (μ : Measure (Mx D V.rank n)) (Ψ : Mx D V.rank n → ℂ) :
    Mx D V.rank n → ℂ :=
  fun x => kap μ (piF θ τ fr) (Bw ψ V θ τ fr Ψ x)


set_option synthInstance.maxHeartbeats 400000 in
theorem weyl_tens {θ : InfFam D} (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    {l : D.what₂.Tau → ℝ} (hl : HasRealPar ψ θ l) {V : HSp D} {τ : D.what₂.Tau}
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ε : Fin V.rank → Bool}
    {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hfr : IsTauFrame V τ s ε fr) {χ : (AE D)ˣ →* Circle}
    (μ : Measure (Mx D V.rank n)) [μ.IsAddHaarMeasure] {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hω : IsWeilSch ψ χ θ V μ ω) (w : G D n) (hw : mat w = blk4 0 1 (-1) 0) (Ψ : Mx D V.rank n → ℂ)
    (hΨ : AwayCls θ τ fr Ψ) (f : (Fin V.rank → Fin n → ℂ) → ℂ) (hf : IsSch f) :
    (ω w ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 =
      tens θ τ fr (fun u => 1 * ftLoc ε (tLoc l τ) f u) (Aw ψ V θ τ fr μ Ψ) := by
  funext x
  rw [hω.weyl w hw]
  have e1 : ∀ y, (⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩ : schwartzA θ V.rank n).1 y * ψ (trA (Matrix.trace (inner V x y))) =
      (fun u => f u * ker ε (tLoc l τ) (piF θ τ fr x) u) (piF θ τ fr y) * Bw ψ V θ τ fr Ψ x y :=
    fun y => integrand_eq hθ hl hfr f Ψ x y
  simp_rw [e1]
  obtain ⟨S, hS⟩ := hf
  have hfc : Continuous f := hS ▸ S.continuous
  obtain ⟨C, hC⟩ := sch_decay f ⟨S, hS⟩
  have hk := kap_spec hθ hfr.1 μ hΨ hψ x (fun u => f u * ker ε (tLoc l τ) (piF θ τ fr x) u)
    ((hfc.mul (continuous_ker ε (tLoc l τ) (piF θ τ fr x))).measurable)
    ⟨C, fun u => by rw [norm_mul, norm_ker, mul_one]; exact hC u⟩
  rw [hk]
  simp only [tens, Aw, ftLoc_eq_ker, one_mul]
  rw [mul_comm]
  rfl

end PositivityTheory.Rg.Sw.Glob.FTH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLaw
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LocLawH

variable {D : D7} {n : ℕ}

theorem cnt_add {m : ℕ} (ε : Fin m → Bool) : cnt ε true + cnt ε false = m := by
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m))) (fun a => ε a = true)
  simp only [Finset.card_univ, Fintype.card_fin, Bool.not_eq_true] at this
  exact this

theorem pqOf_add {m : ℕ} (ε : Fin m → Bool) (l : D.what₂.Tau → ℝ) (τ : D.what₂.Tau) :
    (pqOf ε l τ).1 + (pqOf ε l τ).2 = m := by
  unfold pqOf
  split_ifs
  · exact cnt_add ε
  · rw [add_comm]; exact cnt_add ε

theorem npow_sq (z : ℂ) (m : ℕ) : npow (‖z‖₊ ^ 2) ((m : ℂ) / 2) = ((‖z‖ : ℝ) : ℂ) ^ (m : ℤ) := by
  simp only [npow, NNReal.coe_pow, coe_nnnorm]
  rw [show ((m : ℂ) / 2) = (((m : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (sq_nonneg _), ← Real.rpow_natCast ‖z‖ 2, ← Real.rpow_mul (norm_nonneg _),
    show ((2 : ℕ) : ℝ) * ((m : ℝ) / 2) = (m : ℝ) by push_cast; ring, Real.rpow_natCast, zpow_natCast,
    Complex.ofReal_pow]

set_option maxHeartbeats 400000 in
theorem scal {χ : (AE D)ˣ →* Circle} {θ : InfFam D} (hθ : IsInfFam θ) {σ : (D.what₂.Tau → ℂ) →+ AE D}
    (hσ : GlobalTheory.FockCompare.Chart θ σ) {τ : D.what₂.Tau} {m : ℕ} (k j : ℤ)
    (hk : ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → (∀ τ', τ' ≠ τ → θ τ' (infPart D (x : AE D)) = 1) →
      ((χ x : Circle) : ℂ) = (θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ)) ^ k)
    (hj : k - m = j + j) (p q : ℕ) (hpq : p + q = m) (y : PositivityTheory.Rg.Sw.GR n) (hy : (mR y).toBlocks₂₁ = 0) :
    (χ (Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy))) : ℂ) *
      npow (absA D (Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy)))) ((m : ℂ) / 2) = F0 p q (k - j) y := by
  have hv : (unitAt hσ τ (aOf y hy)).1 = baseColumnsAt σ τ (mR y).toBlocks₁₁ := by rw [unitAt_val, aOf_val]
  have hxv : ((Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy)) : (AE D)ˣ) : AE D) =
      (baseColumnsAt σ τ (mR y).toBlocks₁₁).det := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hv]
  have hf : finPart D (((Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy))) : (AE D)ˣ) : AE D) = 1 := by
    rw [hxv, RingHom.map_det, RingHom.mapMatrix_apply, finite_part_adelic_point_matrix hσ, Matrix.det_one]
  have hcomp : ∀ τ', θ τ' (infPart D (((Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy))) : (AE D)ˣ) : AE D)) = (compAt θ τ' (baseColumnsAt σ τ (mR y).toBlocks₁₁)).det := by
    intro τ'
    rw [hxv]
    show cf θ τ' (baseColumnsAt σ τ (mR y).toBlocks₁₁).det = _
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    rfl
  have hτ : θ τ (infPart D (((Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy))) : (AE D)ˣ) : AE D)) = ((mR y).toBlocks₁₁).det := by rw [hcomp, component_adelic_point_matrix hσ]
  have hne : ∀ τ', τ' ≠ τ → θ τ' (infPart D (((Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy))) : (AE D)ˣ) : AE D)) = 1 := fun τ' h => by
    rw [hcomp, component_adelic_point_ne hσ h, Matrix.det_one]
  have habs : absA D (Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy))) = ‖((mR y).toBlocks₁₁).det‖₊ ^ 2 := by
    rw [show absA D (Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy))) = ‖θ τ (infPart D (((Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy))) : (AE D)ˣ) : AE D))‖₊ ^ 2 from GlobalTheory.StabAtPlace.absE_single hθ (Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy))) τ hf hne, hτ]
  rw [hk _ hf hne, hτ, habs, npow_sq]
  have hZ := det_ne y hy
  have hu1 : u1 (mR y) = (mR y).toBlocks₂₂ := by simp only [u1, hy, smul_zero, zero_add]
  have hu2 : u2 (mR y) = (mR y).toBlocks₂₂ := by simp only [u2, hy, smul_zero, neg_zero, zero_add]
  have hdy : (mR y).det = ((mR y).toBlocks₁₁).det * ((mR y).toBlocks₂₂).det := by
    conv_lhs => rw [fromBlocks_of y hy]
    rw [Matrix.det_fromBlocks_zero₂₁]
  have hR : ((‖((mR y).toBlocks₁₁).det‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hZ)
  have hd : ((mR y).toBlocks₂₂).det = ((mR y).toBlocks₁₁).det / ((‖((mR y).toBlocks₁₁).det‖ : ℝ) : ℂ) ^ 2 := by
    have h1 : ((mR y).toBlocks₂₂).det = (star ((mR y).toBlocks₁₁).det)⁻¹ := eq_inv_of_mul_eq_one_right (det_rel y hy)
    have h2 : ((mR y).toBlocks₁₁).det * star ((mR y).toBlocks₁₁).det = ((‖((mR y).toBlocks₁₁).det‖ : ℝ) : ℂ) ^ 2 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    have h3 : star ((mR y).toBlocks₁₁).det ≠ 0 := star_ne_zero.2 hZ
    rw [h1, eq_div_iff (pow_ne_zero 2 hR), ← h2]
    field_simp
  simp only [F0, f0, hu1, hu2, hdy, hd]
  exact alg_id _ _ hZ hR k j p q m hpq hj

end PositivityTheory.Rg.Sw.Glob.LocLawH

namespace PositivityTheory.Rg.Sw.Glob

theorem lIlaw : LIlaw := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hC.hθ
  obtain ⟨k, ⟨j, hj⟩, hk⟩ := LocLawH.chi_exp hC.hθ hC.hχ hC.hη τ
  exact ⟨k - j, fun P y g hy => by
    rw [LocLawH.glob_law hC hL hσ P y g hy, LocLawH.scal hC.hθ hσ k j hk hj _ _ (LocLawH.pqOf_add ε l τ) y hy]⟩

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.MatLApply
section
noncomputable section

open Filter Topology MvPolynomial Set
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.Glob.SchDH

variable {m n : ℕ}

def matLin (M : Matrix (Fin m) (Fin m) ℂ) : (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ) where
  toFun y := fun a i => ∑ c, M a c * y c i
  map_add' y z := by funext a i; simp [mul_add, Finset.sum_add_distrib]
  map_smul' r y := by
    funext a i
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Complex.real_smul, Complex.real_smul]; ring

def matL (M : Matrix (Fin m) (Fin m) ℂ) : (Fin m → Fin n → ℂ) →L[ℝ] (Fin m → Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap (matLin M)

theorem matL_apply (M : Matrix (Fin m) (Fin m) ℂ) (y : Fin m → Fin n → ℂ) (a : Fin m) (i : Fin n) :
    matL M y a i = ∑ c, M a c * y c i := rfl

theorem matL_mul (M N : Matrix (Fin m) (Fin m) ℂ) (y : Fin m → Fin n → ℂ) : matL (M * N) y = matL M (matL N y) := by
  funext a i
  simp only [matL_apply, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem matL_one (y : Fin m → Fin n → ℂ) : matL (1 : Matrix (Fin m) (Fin m) ℂ) y = y := by
  funext a i
  simp [matL_apply, Matrix.one_apply]

theorem contDiff_A (X : Matrix (Fin m) (Fin m) ℂ) :
    ContDiff ℝ ∞ (fun t : ℝ => matL (n := n) (NormedSpace.exp ((t : ℂ) • X))) := by
  letI : NormedAddCommGroup (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedSpace
  letI : NormedRing (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedAlgebra
  let Lm : Matrix (Fin m) (Fin m) ℂ →ₗ[ℝ] ((Fin m → Fin n → ℂ) →L[ℝ] (Fin m → Fin n → ℂ)) :=
    { toFun := matL
      map_add' := fun M N => by ext y a i; simp [matL_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun r M => by
        ext y a i
        simp only [matL_apply, Matrix.smul_apply, RingHom.id_apply, ContinuousLinearMap.smul_apply, Pi.smul_apply,
          Finset.smul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Complex.real_smul, Complex.real_smul]; ring }
  have hexp : ContDiff ℝ ∞ (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) := by
    have e : (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) = NormedSpace.exp ∘ (fun t : ℝ => t • X) := by
      funext t; simp only [Function.comp_apply, Complex.coe_smul]
    rw [e]
    exact (contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt).comp
      (contDiff_id.smul contDiff_const)
  exact (LinearMap.toContinuousLinearMap Lm).contDiff.comp hexp

theorem hasDerivAt_entry (X : Matrix (Fin m) (Fin m) ℂ) (a c : Fin m) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) a c) (X a c) 0 := by
  letI : NormedAddCommGroup (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedSpace
  letI : NormedRing (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedAlgebra
  let ent : Matrix (Fin m) (Fin m) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun M => M a c, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ))
  have h2 := (LinearMap.toContinuousLinearMap ent).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  have e : (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) a c) =
      (LinearMap.toContinuousLinearMap ent) ∘ (fun u : ℝ => NormedSpace.exp (u • X)) := by
    funext t; simp only [Function.comp_apply, Complex.coe_smul]; rfl
  have h3 : HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) a c)
      ((LinearMap.toContinuousLinearMap ent) (NormedSpace.exp ((0 : ℝ) • X) * X)) 0 := by
    rw [e]; exact h2
  have h4 : (LinearMap.toContinuousLinearMap ent) (NormedSpace.exp ((0 : ℝ) • X) * X) = X a c := by
    rw [zero_smul, NormedSpace.exp_zero, one_mul]; rfl
  rw [h4] at h3
  exact h3

theorem exists_gs (c : ℝ) (hc : 0 < c) : ∃ g : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∀ u, g u = gs c u := by
  obtain ⟨g0, hg0⟩ := GlobalTheory.CompanionTheory.PolyGaussSchwartz.exists_gauss (m := m) (n := n)
  set s : ℝ := Real.sqrt (c / (2 * Real.pi)) with hs
  have hs0 : s ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  let L : (Fin m → Fin n → ℂ) ≃L[ℝ] (Fin m → Fin n → ℂ) :=
    (LinearEquiv.smulOfNeZero ℝ (Fin m → Fin n → ℂ) s hs0).toContinuousLinearEquiv
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L g0, fun u => ?_⟩
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hg0]
  have key : 2 * Real.pi * ∑ a, ∑ i, ‖(L u) a i‖ ^ 2 = c * ∑ a, ∑ i, ‖u a i‖ ^ 2 := by
    have h1 : ∀ a i, ‖(L u) a i‖ ^ 2 = s ^ 2 * ‖u a i‖ ^ 2 := fun a i => by
      change ‖(s • u) a i‖ ^ 2 = _
      rw [Pi.smul_apply, Pi.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    simp only [h1, ← Finset.mul_sum]
    rw [hs, Real.sq_sqrt (by positivity)]
    field_simp
  unfold gs
  rw [key]

theorem exists_fP (c : ℝ) (hc : 0 < c) (P : PX m n) :
    ∃ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∀ u, φ u = fP c P u := by
  obtain ⟨g, hg⟩ := exists_gs (m := m) (n := n) c hc
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun u => MvPolynomial.eval (fun k => GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord k u) P) g,
    fun u => ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply_apply (GlobalTheory.CompanionTheory.PolyGaussSchwartz.eval_temperate P), hg, smul_eq_mul]
  rfl

end PositivityTheory.Rg.Sw.Glob.SchDH
end
end

