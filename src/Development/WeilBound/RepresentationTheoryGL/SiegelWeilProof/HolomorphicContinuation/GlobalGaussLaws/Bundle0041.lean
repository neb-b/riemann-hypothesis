module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0039
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0497
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaAutomorphicOfConvergence
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0266
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0222

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRho
section
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 8000000

open RhoH in
theorem lIrho : LIrho := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL
  classical
  obtain ⟨𝓕, hμ⟩ := hC.hμ
  have hΨ0m : psi0 θ V n l s τ ∈ awayA θ V n l s τ := unitaryFinitePointsToGLFiniteAdeles_isUnitary θ V l s τ
  have hl0 : ∀ τ, l τ ≠ 0 := l_ne_zero D n V ψ hC.hψ χ hC.hχ hC.hη θ hC.hθ μ 𝓕 hμ ω hC.hω l hC.hl
  have hmem : ∀ P : PX V.rank n, tens θ τ fr (fP (cLoc l τ) P) (psi0 θ V n l s τ) ∈ schwartzA θ V.rank n ∧
      tens θ τ fr (fP (cLoc l τ) P) (psi0 θ V n l s τ) ∈ fockA θ V n l s :=
    fun P => hT D n V θ l s τ ε fr hC.hθ hl0 hC.hs hC.hfr _ hΨ0m P
  have hfP0 : fP (cLoc l τ) (0 : PX V.rank n) = 0 := by
    funext u
    simp [fP, evX]
  have htens0 : tens θ τ fr (0 : (Fin V.rank → Fin n → ℂ) → ℂ) (psi0 θ V n l s τ) = 0 := by
    funext x
    show (0 : ℂ) * _ = 0
    exact zero_mul _
  have hphi0 : phiS θ τ fr (cLoc l τ) (psi0 θ V n l s τ) 0 = 0 := by
    apply Subtype.ext
    rw [phiS_val (hmem 0).1, hfP0, htens0]
    rfl
  have hlin : ∀ (a : ℂ) (P Q : PX V.rank n), phiS θ τ fr (cLoc l τ) (psi0 θ V n l s τ) (a • P + Q) =
      a • phiS θ τ fr (cLoc l τ) (psi0 θ V n l s τ) P + phiS θ τ fr (cLoc l τ) (psi0 θ V n l s τ) Q := by
    intro a P Q
    apply Subtype.ext
    rw [Submodule.coe_add, Submodule.coe_smul, phiS_val (hmem _).1, phiS_val (hmem _).1, phiS_val (hmem _).1,
      fP_add_smul, tens_add_smul]
  let jL : PX V.rank n →ₗ[ℂ] schwartzA θ V.rank n :=
    { toFun := phiS θ τ fr (cLoc l τ) (psi0 θ V n l s τ)
      map_add' := fun P Q => by simpa using hlin 1 P Q
      map_smul' := fun a P => by
        have := hlin a P 0
        rw [add_zero, hphi0, add_zero] at this
        exact this }
  have hjinj : Function.Injective jL := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro R hR
    have h1 : (jL R).1 = 0 := by rw [hR]; rfl
    change (phiS θ τ fr (cLoc l τ) (psi0 θ V n l s τ) R).1 = 0 at h1
    rw [phiS_val (hmem R).1, ← htens0, ← hfP0] at h1
    exact fP_inj _ (tensor_gaussian_vacuum_injective hC.hθ hC.hfr l h1)
  have hexist : ∀ k : GR n, InK (mR k) → ∀ P, ∃ Q, L k (fP (cLoc l τ) P) = fP (cLoc l τ) Q := by
    intro k hk P
    have hΦ : (phiS θ τ fr (cLoc l τ) (psi0 θ V n l s τ) P).1 ∈ fockA θ V n l s := by
      rw [phiS_val (hmem P).1]
      exact (hmem P).2
    have hst := fock_stable D n V ψ hC.hψ χ hC.hχ hC.hη θ hC.hθ μ 𝓕 hμ ω hC.hω l hC.hl s hC.hs _ hΦ (ι k)
      (iota_mem_K hC.hθ hC.hι k hk)
    rw [hL k _ hΨ0m P] at hst
    exact tens_slice hC.hθ hC.hfr l _ hst
  have hLlin : ∀ k : GR n, InK (mR k) → ∀ (a : ℂ) (P Q : PX V.rank n),
      L k (fP (cLoc l τ) (a • P + Q)) = a • L k (fP (cLoc l τ) P) + L k (fP (cLoc l τ) Q) := by
    intro k hk a P Q
    apply tensor_gaussian_vacuum_injective hC.hθ hC.hfr l
    rw [tens_add_smul, ← hL k _ hΨ0m, ← hL k _ hΨ0m, ← hL k _ hΨ0m, hlin, map_add (f := _), map_smul]
    rfl
  let ρ0 : GR n → PX V.rank n → PX V.rank n := fun k P => if hk : InK (mR k) then (hexist k hk P).choose else P
  have hρ0 : ∀ (k : GR n) (hk : InK (mR k)) P, L k (fP (cLoc l τ) P) = fP (cLoc l τ) (ρ0 k P) := by
    intro k hk P
    simp only [ρ0, dif_pos hk]
    exact (hexist k hk P).choose_spec
  have hρlin : ∀ (k : GR n) (a : ℂ) (P Q : PX V.rank n), ρ0 k (a • P + Q) = a • ρ0 k P + ρ0 k Q := by
    intro k a P Q
    by_cases hk : InK (mR k)
    · apply fP_inj (cLoc l τ)
      rw [fP_add_smul, ← hρ0 k hk, ← hρ0 k hk, ← hρ0 k hk, hLlin k hk]
    · simp only [ρ0, dif_neg hk]
  have hρ00 : ∀ k : GR n, ρ0 k 0 = 0 := by
    intro k
    have := hρlin k 1 0 0
    simp only [one_smul, add_zero] at this
    have h2 : ρ0 k 0 + ρ0 k 0 = ρ0 k 0 + 0 := by rw [← this, add_zero]
    exact add_left_cancel h2
  let ρ : GR n → PX V.rank n →ₗ[ℂ] PX V.rank n := fun k =>
    { toFun := ρ0 k
      map_add' := fun P Q => by simpa using hρlin k 1 P Q
      map_smul' := fun a P => by
        have := hρlin k a P 0
        rw [add_zero, hρ00, add_zero] at this
        exact this }
  have hρ : ∀ (k : GR n) P, InK (mR k) → L k (fP (cLoc l τ) P) = fP (cLoc l τ) (ρ k P) :=
    fun k P hk => hρ0 k hk P
  have hjρ : ∀ (k : GR n), InK (mR k) → ∀ Q, jL (ρ k Q) = ω (ι k) (jL Q) := by
    intro k hk Q
    apply Subtype.ext
    show (phiS θ τ fr (cLoc l τ) (psi0 θ V n l s τ) (ρ0 k Q)).1 =
      (ω (ι k) (phiS θ τ fr (cLoc l τ) (psi0 θ V n l s τ) Q)).1
    rw [hL k _ hΨ0m Q, phiS_val (hmem _).1, ← hρ0 k hk Q]
  refine ⟨ρ, hρ, fun P => ?_⟩
  have hjmem : ∀ R, (jL R).1 ∈ fockA θ V n l s := by
    intro R
    show (phiS θ τ fr (cLoc l τ) (psi0 θ V n l s τ) R).1 ∈ fockA θ V n l s
    rw [phiS_val (hmem R).1]
    exact (hmem R).2
  have hfd := _root_.GlobalTheory.StdUnn.KFin.fock_kfinite D n V ψ hC.hψ χ hC.hχ hC.hη θ hC.hθ μ 𝓕 hμ ω hC.hω l hC.hl s hC.hs (jL P) (hjmem P)
  set S := Submodule.span ℂ {Ψ' : schwartzA θ V.rank n | ∃ k ∈ K D n, Ψ' = ω k (jL P)} with hS
  have hSstab : ∀ κ ∈ K D n, ∀ x ∈ S, ω κ x ∈ S := by
    intro κ hκ x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k', hk', rfl⟩ := hx
      refine Submodule.subset_span ⟨κ * k', (K D n).mul_mem hκ hk', ?_⟩
      rw [map_mul, Module.End.mul_apply]
    | zero => rw [map_zero]; exact S.zero_mem
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact S.add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact S.smul_mem a hx
  let W : Submodule ℂ (PX V.rank n) := S.comap jL
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · have : FiniteDimensional ℂ S := hfd
    exact Module.Finite.of_injective (jL.restrict (p := W) (q := S) fun x hx => hx)
      (fun x y h => Subtype.ext (hjinj (congrArg Subtype.val h)))
  · show jL P ∈ S
    exact Submodule.subset_span ⟨1, (K D n).one_mem, by rw [map_one]; rfl⟩
  · intro k hk Q hQ
    show jL (ρ k Q) ∈ S
    rw [hjρ k hk Q]
    exact hSstab _ (iota_mem_K hC.hθ hC.hι k hk) _ hQ
  · intro Q _ l'
    let e := LinearEquiv.ofInjective jL hjinj
    obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend (l' ∘ₗ e.symm.toLinearMap)
    have hΛj : ∀ R, Λ (jL R) = l' R := by
      intro R
      have := congrArg (fun F => F ⟨jL R, LinearMap.mem_range_self jL R⟩) hΛ
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, LinearEquiv.coe_coe] at this
      rw [this]
      exact congrArg l' (e.symm_apply_eq.2 (Subtype.ext (LinearEquiv.ofInjective_apply jL (h := hjinj) R).symm))
    have hcont := orbit_cont D n V ψ hC.hψ χ hC.hχ hC.hη θ hC.hθ μ 𝓕 hμ ω hC.hω l hC.hl s hC.hs (jL Q) (hjmem Q) Λ
    have hιc : ContinuousOn (fun k : GR n => ι k) {k | InK (mR k)} := hC.hι.1.continuousOn
    have hmaps : Set.MapsTo (fun k : GR n => ι k) {k | InK (mR k)} (K D n : Set (G D n)) :=
      fun k hk => iota_mem_K hC.hθ hC.hι k hk
    refine (hcont.comp hιc hmaps).congr ?_
    intro k hk
    simp only [Function.comp_apply]
    rw [← hΛj, hjρ k hk Q]

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.PhiSVal
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

theorem phiS_val {m : ℕ} {θ : InfFam D} {τ : D.what₂.Tau} {fr : Matrix (Fin m) (Fin m) ℂ} {c : ℝ}
    {Ψ : Mx D m n → ℂ} {Q : PX m n} (h : tens θ τ fr (fP c Q) Ψ ∈ schwartzA θ m n) :
    (phiS θ τ fr c Ψ Q).1 = tens θ τ fr (fP c Q) Ψ := by
  unfold phiS
  rw [dite_eq_left h]

theorem perPsi (hA : AbsThm) (hTM : TensMem) (hLo : LocOpEx) (hLi : LocInst) (hLS : LinSec) (hGS : GSplit)
    (hIa : GIauto) (hIk : GIk) (hIi : GIinv) (hId : GIdil) (hEis : EisStrong) (hLB : GLamBd) (hLsg : GLsing)
    (hCo : PositivityTheory.PfSWUS.CoefND) (hLZ : LNZ)
    {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {H : G D n → ℝ≥0}
    {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ν : Measure (GA D V)}
    {τ : D.what₂.Tau} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} {ι : GR n →* G D n}
    (hcx : Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι) {Ψ : Mx D V.rank n → ℂ} (hΨ : Ψ ∈ awayA θ V n l s τ)
    (Q : PX V.rank n) (g : G D n) :
    HolValueAt (PositivityTheory.PfSWUS.eis ω H (phiS θ τ fr (cLoc l τ) Ψ Q) g) (s0 V n)
      (thetaInt ω ν (phiS θ τ fr (cLoc l τ) Ψ Q) g) := by
  have hl0 := hLZ D ψ θ l hcx.hψ hcx.hθ hcx.hl
  have hmem := hTM D n V θ l s τ ε fr hcx.hθ hl0 hcx.hs hcx.hfr Ψ hΨ
  obtain ⟨L, hL⟩ := hLo D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx
  obtain ⟨sL, ρ, p, q, e, hgood, hLD, hsL, hρ⟩ := hLi D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL
  obtain ⟨sec, I, hsec, hI⟩ := hLS D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx Ψ hΨ
  have hstd1 : PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν (phiS θ τ fr (cLoc l τ) Ψ 1) :=
    ⟨hcx.hψ, hcx.hχ, hcx.hη, hcx.hθ, hcx.hμ, hcx.hω, hcx.hH, hcx.hl, hcx.hs, hcx.hν,
      by rw [phiS_val (hmem 1).1]; exact (hmem 1).2⟩
  have hsecSec : IsSection χ (s0 V n) (fun x => sec 1 x) := by
    obtain ⟨𝓕, h𝓕⟩ := hcx.hμ
    have := GlobalTheory.StdUnn.SiegelSection.fock_mem_degenerate D n V ψ hcx.hψ χ hcx.hχ hcx.hη θ hcx.hθ μ 𝓕 h𝓕 ω hcx.hω
      l hcx.hl s hcx.hs _ hstd1.hΦ
    rw [hsec 1]
    exact this
  have hn0 : 0 < n := hcx.hn
  have hGD : GlobData ε (cLoc l τ) sL ρ (G D n) (P D n) (GF D n) ι (s0 V n) H sec I (lamSet ψ) := {
    ιcont := hcx.hι.1
    split := by
      intro g
      obtain ⟨x, y, S, r, hr, hg, hx⟩ := hGS D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL Ψ hΨ g
      refine ⟨x, y, S, r, hr, hg, fun y' => ⟨(hx y').1, fun Q' => ?_⟩⟩
      rw [hsec Q', hsL Q' y']
      exact (hx y').2 Q'
    Icont := by
      rw [hI 1]
      exact (hIa D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx Ψ hΨ).1
    Ileft := by
      rw [hI 1]
      exact (hIa D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx Ψ hΨ).2
    Ik := by
      intro Q' g k hk
      rw [hI Q', hI (ρ k Q')]
      exact hIk D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL ρ hρ Ψ hΨ Q' g k hk
    Iinv := by
      intro g a b Q'
      rw [hI]
      exact hIi D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx Ψ hΨ g a b Q'
    Idil := by
      intro g X a ha
      obtain ⟨U, F, hU, hU', hFc, hF⟩ := hId D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx Ψ hΨ g X a ha
      refine ⟨U, F, hU, hU', hFc, fun y => ⟨(hF y).1, fun t => ?_, fun r => ?_⟩⟩
      · rw [hI]
        exact (hF y).2.1 t
      · rw [hI]
        exact (hF y).2.2 r
    eis := hEis D n hn0 χ V.rank hcx.hχ hcx.hη H hcx.hH (s0 V n) _ hsecSec (s0 V n)
    Λadd := fun L' hL' => (hLB D n ψ hcx.hψ L' hL').1
    Λbd := fun L' hL' => (hLB D n ψ hcx.hψ L' hL').2
    Λsing := fun F hF hinv hz => hLsg D n ψ θ τ ι hcx.hψ hcx.hθ hcx.hι F hF hinv hz
    Λval := by
      rintro L' ⟨nb, lam, 𝓖, β, g', hcd, hβ, rfl⟩
      have := hCo D n V ψ χ θ μ ω H l s ν _ hstd1 hcx.hr nb lam 𝓖 hcd β hβ g'
      rw [hI 1, hsec 1]
      exact this }
  have := hA V.rank n ε (cLoc l τ) (tLoc l τ) p q e sL ρ hLD hgood (G D n) (P D n) (GF D n) ι (s0 V n) H sec I
    (lamSet ψ) hGD Q g
  rw [hsec Q, hI Q] at this
  exact this

theorem main : MainSt := by
  intro hA hFr hEmb hSig hSp hTM hLo hLi hLS hGS hIa hIk hIi hId hEis hLB hLsg hCo hCR hTL hLZ
  intro D n V ψ χ θ μ ω H l s ν Φ hStd hR hn g
  obtain ⟨τ, hτ⟩ := hSig D n V s hR hStd.hs
  obtain ⟨ε, fr, hfr⟩ := hFr D V τ s (hStd.hs τ)
  obtain ⟨ι, hι⟩ := hEmb D n θ τ hStd.hθ
  have hcx : Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι :=
    ⟨hStd.hψ, hStd.hχ, hStd.hη, hStd.hθ, hStd.hμ, hStd.hω, hStd.hH, hStd.hl, hStd.hs, hStd.hν, hR, hn, hfr, hι,
      hτ ε fr hfr⟩
  have hl0 := hLZ D ψ θ l hStd.hψ hStd.hθ hStd.hl
  obtain ⟨k, Pi, Ψi, hΨ, hsum⟩ := hSp D n V θ l s τ ε fr hStd.hθ hfr Φ.1 hStd.hΦ
  have hmem : ∀ i, tens θ τ fr (fP (cLoc l τ) (Pi i)) (Ψi i) ∈ schwartzA θ V.rank n ∧
      tens θ τ fr (fP (cLoc l τ) (Pi i)) (Ψi i) ∈ fockA θ V n l s :=
    fun i => hTM D n V θ l s τ ε fr hStd.hθ hl0 hStd.hs hfr (Ψi i) (hΨ i) (Pi i)
  let Φi : Fin k → schwartzA θ V.rank n := fun i => phiS θ τ fr (cLoc l τ) (Ψi i) (Pi i)
  have hval : ∀ i, (Φi i).1 = tens θ τ fr (fP (cLoc l τ) (Pi i)) (Ψi i) := fun i => phiS_val (hmem i).1
  have hΦeq : Φ = ∑ i, Φi i := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [hval]
    exact hsum
  have hstdT : ∀ T : Finset (Fin k), PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν (∑ i ∈ T, Φi i) := fun T =>
    ⟨hStd.hψ, hStd.hχ, hStd.hη, hStd.hθ, hStd.hμ, hStd.hω, hStd.hH, hStd.hl, hStd.hs, hStd.hν, by
      rw [Submodule.coe_sum]
      exact Submodule.sum_mem _ fun i _ => by rw [hval]; exact (hmem i).2⟩
  have hstdi : ∀ i, PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν (Φi i) := fun i =>
    ⟨hStd.hψ, hStd.hχ, hStd.hη, hStd.hθ, hStd.hμ, hStd.hω, hStd.hH, hStd.hl, hStd.hs, hStd.hν, by
      rw [hval]; exact (hmem i).2⟩
  have key : ∀ i, HolValueAt (PositivityTheory.PfSWUS.eis ω H (Φi i) g) (s0 V n) (thetaInt ω ν (Φi i) g) := fun i =>
    perPsi hA hTM hLo hLi hLS hGS hIa hIk hIi hId hEis hLB hLsg hCo hLZ hcx (hΨ i) (Pi i) g
  have hth : ∀ T : Finset (Fin k), thetaInt ω ν (∑ i ∈ T, Φi i) g = ∑ i ∈ T, thetaInt ω ν (Φi i) g := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      have h0 := hTL D n V ψ χ θ μ ω H l s ν 0 0 (by simpa using hstdT ∅) (by simpa using hstdT ∅) hR g
      rw [add_zero] at h0
      simp only [Finset.sum_empty]
      linear_combination -h0
    | insert a T ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hTL D n V ψ χ θ μ ω H l s ν _ _ (hstdi a) (hstdT T) hR g, ih]
  choose σi hσi using fun i => hCR D n V ψ χ θ μ ω H l s ν (Φi i) (hstdi i) hR
  have hsect : ∀ z, sect ω H (∑ i, Φi i) z = fun x => ∑ i, sect ω H (Φi i) z x := by
    intro z
    funext x
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [sect, map_sum, Submodule.coe_sum, Finset.sum_apply, Finset.mul_sum]
  have heq : EqRight (fun z => ∑ i, PositivityTheory.PfSWUS.eis ω H (Φi i) g z) (PositivityTheory.PfSWUS.eis ω H Φ g) := by
    refine ⟨∑ i, |σi i|, fun z hz => ?_⟩
    have hz' : ∀ i, σi i < z.re := fun i =>
      lt_of_le_of_lt ((le_abs_self _).trans
        (Finset.single_le_sum (fun j _ => abs_nonneg (σi j)) (Finset.mem_univ i))) hz
    show ∑ i, PositivityTheory.PfSWUS.eis ω H (Φi i) g z = PositivityTheory.PfSWUS.eis ω H Φ g z
    rw [hΦeq]
    unfold PositivityTheory.PfSWUS.eis
    rw [hsect z, cosetSum_finsum _ _ _ _ _ (fun i _ => hσi i z (hz' i) g)]
  have hv : thetaInt ω ν Φ g = ∑ i, thetaInt ω ν (Φi i) g := by
    rw [hΦeq]
    exact hth Finset.univ
  rw [hv]
  exact (holValueAt_finsum Finset.univ fun i _ => key i).congr heq

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ThetaIntegralCompWeil
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GCommH

variable {D : D7} {n : ℕ}

theorem gComm {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {χ : (AE D)ˣ →* Circle}
    (hχ : IsHeckeChar D χ) (hη : ResEta D χ V.rank) {θ : InfFam D} (hθ : IsInfFam θ) {μ : Measure (Mx D V.rank n)}
    {𝓕 : Set (Mx D V.rank n)} (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕)
    {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω)
    (Φ Φh : schwartzA θ V.rank n) (h : GA D V) (hΦh : ∀ x, Φh.1 x = Φ.1 (mt V h ⬝ x)) (g : G D n) (x : Mx D V.rank n) :
    (ω g Φh).1 x = (ω g Φ).1 (mt V h ⬝ x) := by
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  obtain ⟨ψ₀, μ', lam, κ, omh, hs0, hsk, _, _, hκ, hW, hT⟩ := _root_.GlobalTheory.StdUnn.SchDatum.exists_datum D A V ψ hψ χ hχ hη θ hθ μ 𝓕 hμ ω hω
  obtain ⟨f, hf, hfΦ⟩ := (GlobalTheory.SchSchwartzAll.schSchwartz D ψ₀ hs0 θ hθ A V μ 𝓕 hμ).2.1 Φ.1 Φ.2
  have hlaw := fun F (hF : IsThetaFunO ψ₀ (dblSp A) V F) => (_root_.GlobalTheory.Core.Rk.SchLaws.sch_laws D ψ₀ A V χ⁻¹ omh hW μ 𝓕 hμ F hF).1
  have hf1 : IsThetaFunO ψ₀ (dblSp A) V (omh (1, h⁻¹) f) := hW.om_pres _ f hf
  have hΦh' : Φh.1 = sch ψ₀ A V μ 𝓕 (omh (1, h⁻¹) f) := by
    funext y
    rw [hΦh, hlaw f hf h⁻¹ y, inv_inv, hfΦ]
    rfl
  have key : ∀ g0 : GA D (dblSp A), (ω (κ g0) Φh).1 x = (ω (κ g0) Φ).1 (mt V h ⬝ x) := by
    intro g0
    have hc : omh (g0, 1) (omh (1, h⁻¹) f) = omh (1, h⁻¹) (omh (g0, 1) f) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk,
        one_mul, mul_one, one_mul, mul_one]
    have hg1 : IsThetaFunO ψ₀ (dblSp A) V (omh (g0, 1) f) := hW.om_pres _ f hf
    calc (ω (κ g0) Φh).1 x = sch ψ₀ A V μ 𝓕 (omh (g0, 1) (omh (1, h⁻¹) f)) x := congrFun (hT g0 _ hf1 Φh hΦh') x
      _ = sch ψ₀ A V μ 𝓕 (omh (1, h⁻¹) (omh (g0, 1) f)) x := by rw [hc]
      _ = sch ψ₀ A V μ 𝓕 (omh (g0, 1) f) (mt V h⁻¹⁻¹ ⬝ x) := hlaw _ hg1 h⁻¹ x
      _ = sch ψ₀ A V μ 𝓕 (omh (g0, 1) f) (mt V h ⬝ x) := by rw [inv_inv]
      _ = (ω (κ g0) Φ).1 (mt V h ⬝ x) := (congrFun (hT g0 f hf Φ hfΦ.symm) _).symm
  have e : κ (κ.symm g) = g := κ.apply_symm_apply g
  have k := key (κ.symm g)
  rw [e] at k
  exact k

end PositivityTheory.Rg.Sw.Glob.GCommH
end
end

