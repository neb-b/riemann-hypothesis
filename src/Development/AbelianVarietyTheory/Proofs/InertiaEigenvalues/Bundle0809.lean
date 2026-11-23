module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NotMemSpanOfCommute
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0788
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0798
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixCoefficientVacuaUnramifiedPlace
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0253
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0211

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjHalfInvariantFormIdemSumVacuumNeZero
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries.IdemSumForm

open GlobalTheory.SplitScalar
open scoped ComplexOrder

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem heisL_commute_of {a : AE D} (ha : cA D a * a = 0) {x y : WO S T} (hx : IsHalf a x) (hy : IsHalf a y) :
    Commute (heisL ψ S T x) (heisL ψ S T y) := by
  have add : ∀ {x y : WO S T}, IsHalf a x → IsHalf a y → heisL ψ S T (x + y) = heisL ψ S T x * heisL ψ S T y :=
    fun hx hy => LinearMap.ext fun f => heisO_add_of_orth ψ S T (symplO_eq_zero S T ha hx hy) f
  rw [Commute, SemiconjBy, ← add hx hy, ← add hy hx, add_comm]

theorem dual_half {Λ : AddSubgroup (WO S T)} {e : AE D} (he1 : e * e = e)
    (hfin : ∀ u : WO S T, IsHalf e u → u.map (infPart D) = 0)
    (hd : ∀ u : WO S T, u.map (infPart D) = 0 → (u ∈ Λ ↔ ∀ u' ∈ Λ, ψ (symplO S T u u') = 1))
    (hst : ∀ u ∈ Λ, cA D e • u ∈ Λ) {y : WO S T} (hy : IsHalf e y) (hyΛ : y ∉ Λ) :
    ∃ l ∈ Λ, IsHalf (cA D e) l ∧ ψ (symplO S T l y) ≠ 1 := by
  rw [hd y (hfin y hy)] at hyΛ
  push Not at hyΛ
  obtain ⟨u, hu, h⟩ := hyΛ
  refine ⟨cA D e • u, hst u hu, isHalf_smul (by rw [← RingHom.map_mul, he1]) u, psi_skew_ne ?_⟩
  rwa [← symplO_smul, (isHalf_iff _ _).1 hy]

theorem count_form {Λ : AddSubgroup (WO S T)} {e : AE D} (he1 : e * e = e) (he2 : cA D e * e = 0)
    (hfin : ∀ u : WO S T, IsHalf e u → u.map (infPart D) = 0)
    (hd : ∀ u : WO S T, u.map (infPart D) = 0 → (u ∈ Λ ↔ ∀ u' ∈ Λ, ψ (symplO S T u u') = 1))
    (hst : ∀ u ∈ Λ, cA D e • u ∈ Λ) {f : WO S T → ℂ} (hf0 : f ≠ 0)
    (hfe : ∀ l ∈ Λ, IsHalf e l → heisO ψ S T l f = f) (hfc : ∀ l ∈ Λ, IsHalf (cA D e) l → heisO ψ S T l f = f) :
    ∃ κ : (WO S T → ℂ) →ₗ[ℂ] ℂ, κ f = 1 ∧ ∀ y, IsHalf e y → 0 ≤ κ (heisO ψ S T y f) := by
  have he2' : cA D (cA D e) * cA D e = 0 := by rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm, he2]
  have h : f ∉ Submodule.span ℂ {x | ∃ y, IsHalf e y ∧ y ∉ Λ ∧ x = heisO ψ S T y f} := by
    refine notMem_span_of_commute
      {g | ∃ l ∈ Λ, ∃ z : ℂ, IsHalf (cA D e) l ∧ z ≠ 1 ∧ g = heisL ψ S T l - z • 1} ?_ _ ?_ f ?_
    · rintro _ ⟨l, -, z, hl, -, rfl⟩ _ ⟨l', -, z', hl', -, rfl⟩
      exact ((heisL_commute_of he2' hl hl').sub_right ((Commute.one_right _).smul_right _)).sub_left
        ((Commute.one_left _).smul_left _)
    · rintro _ ⟨y, hy, hyΛ, rfl⟩
      obtain ⟨l, hl, hl', hne⟩ := dual_half he1 hfin hd hst hy hyΛ
      refine ⟨_, ⟨l, hl, _, hl', hne, rfl⟩, ?_⟩
      rw [LinearMap.sub_apply, heisL_apply, heisO_comm, hfc l hl hl']
      exact sub_self _
    · have : ∀ B ∈ Submonoid.closure
          {g | ∃ l ∈ Λ, ∃ z : ℂ, IsHalf (cA D e) l ∧ z ≠ 1 ∧ g = heisL ψ S T l - z • 1},
          ∃ c : ℂ, c ≠ 0 ∧ B f = c • f := by
        intro B hB
        induction hB using Submonoid.closure_induction with
        | mem b hb =>
          obtain ⟨l, hl, z, hl', hz, rfl⟩ := hb
          refine ⟨1 - z, sub_ne_zero.2 hz.symm, ?_⟩
          rw [LinearMap.sub_apply, heisL_apply, hfc l hl hl', sub_smul, one_smul]
          rfl
        | one => exact ⟨1, one_ne_zero, (one_smul _ _).symm⟩
        | mul x y _ _ hx hy =>
          obtain ⟨c, hc, hx⟩ := hx
          obtain ⟨d, hd, hy⟩ := hy
          exact ⟨d * c, mul_ne_zero hd hc, by rw [Module.End.mul_apply, hy, map_smul, hx, smul_smul]⟩
      intro B hB
      obtain ⟨c, hc, h⟩ := this B hB
      rw [h]
      exact smul_ne_zero hc hf0
  obtain ⟨κ, hκ, hκ'⟩ := Submodule.exists_dual_map_eq_bot_of_notMem h inferInstance
  refine ⟨(κ f)⁻¹ • κ, by rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hκ], fun y hy => ?_⟩
  by_cases hyΛ : y ∈ Λ
  · rw [hfe y hyΛ hy, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hκ]
    exact zero_le_one
  · have : κ (heisO ψ S T y f) = 0 := by
      rw [← Submodule.mem_bot ℂ, ← hκ']
      exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨y, hy, hyΛ, rfl⟩)
    rw [LinearMap.smul_apply, this, smul_zero]

theorem invariant_form {Λ : AddSubgroup (WO S T)} {e : AE D} (he1 : e * e = e) (he2 : cA D e * e = 0)
    (hfin : ∀ u : WO S T, IsHalf e u → u.map (infPart D) = 0)
    (hd : ∀ u : WO S T, u.map (infPart D) = 0 → (u ∈ Λ ↔ ∀ u' ∈ Λ, ψ (symplO S T u u') = 1))
    (hst : ∀ u ∈ Λ, cA D e • u ∈ Λ) {f : WO S T → ℂ} (hf0 : f ≠ 0)
    (hfe : ∀ l ∈ Λ, IsHalf e l → heisO ψ S T l f = f) (hfc : ∀ l ∈ Λ, IsHalf (cA D e) l → heisO ψ S T l f = f) :
    ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, ℓ f ≠ 0 ∧
      ∀ y, IsHalf e y → ∀ φ, IsThetaFunO ψ S T φ → ℓ (heisO ψ S T y φ) = ℓ φ := by
  obtain ⟨κ, hκ1, hκ⟩ := count_form he1 he2 hfin hd hst hf0 hfe hfc
  have h : f ∉ Submodule.span ℂ
      {x | ∃ y φ, IsHalf e y ∧ IsThetaFunO ψ S T φ ∧ x = heisO ψ S T y φ - φ} := by
    refine notMem_span_of_commute
      {g | ∃ (y : WO S T) (N : ℕ), IsHalf e y ∧ g = ∑ k ∈ Finset.range (N + 1), heisL ψ S T (k • y)} ?_ _ ?_ f ?_
    · rintro _ ⟨y, N, hy, rfl⟩ _ ⟨y', N', hy', rfl⟩
      exact Commute.sum_left _ _ _ fun k _ => Commute.sum_right _ _ _ fun k' _ =>
        heisL_commute_of he2 (isHalf_nsmul hy k) (isHalf_nsmul hy' k')
    · rintro _ ⟨y, φ, hy, hφ, rfl⟩
      obtain ⟨U, hU, hUφ⟩ := hφ.level
      obtain ⟨N, hN, hNU⟩ := exists_nsmul_mem U hU (hfin y hy)
      obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
      refine ⟨_, ⟨y, N, hy, rfl⟩, ?_⟩
      have e1 : ∀ k : ℕ, heisL ψ S T (k • y) (heisO ψ S T y φ - φ) =
          heisO ψ S T ((k + 1) • y) φ - heisO ψ S T (k • y) φ := by
        intro k
        rw [map_sub, succ_nsmul, heisO_add_of_orth ψ S T (symplO_eq_zero S T he2 (isHalf_nsmul hy k) hy)]
        rfl
      rw [LinearMap.sum_apply, Finset.sum_congr rfl fun k _ => e1 k,
        Finset.sum_range_sub (fun k => heisO ψ S T (k • y) φ), zero_smul, heisO_zero,
        hUφ _ hNU (hfin _ (isHalf_nsmul hy _)), sub_self]
    · have : ∀ B ∈ Submonoid.closure
          {g | ∃ (y : WO S T) (N : ℕ), IsHalf e y ∧ g = ∑ k ∈ Finset.range (N + 1), heisL ψ S T (k • y)},
          (∀ y, IsHalf e y → 0 ≤ κ (B (heisO ψ S T y f))) ∧ 0 < κ (B f) := by
        intro B hB
        induction hB using Submonoid.closure_induction_right with
        | one => exact ⟨hκ, by rw [Module.End.one_apply, hκ1]; exact zero_lt_one⟩
        | mul_right B _ g hg ih =>
          obtain ⟨y', N, hy', rfl⟩ := hg
          refine ⟨fun y hy => ?_, ?_⟩
          set_option synthInstance.maxHeartbeats 100000 in
            · rw [Module.End.mul_apply, LinearMap.sum_apply, map_sum, map_sum]
              refine Finset.sum_nonneg fun k _ => ?_
              rw [heisL_apply, ← heisO_add_of_orth ψ S T (symplO_eq_zero S T he2 (isHalf_nsmul hy' k) hy)]
              exact ih.1 _ (isHalf_add (isHalf_nsmul hy' k) hy)
          set_option synthInstance.maxHeartbeats 100000 in
            · rw [Module.End.mul_apply, LinearMap.sum_apply, map_sum, map_sum]
              refine Finset.sum_pos' (fun k _ => ih.1 _ (isHalf_nsmul hy' k)) ⟨0, Finset.mem_range.2 N.succ_pos, ?_⟩
              rw [heisL_apply, zero_smul, heisO_zero]
              exact ih.2
      intro B hB h0
      have := (this B hB).2
      rw [h0, map_zero] at this
      exact lt_irrefl _ this
  obtain ⟨ℓ, hℓ, hℓ'⟩ := Submodule.exists_dual_map_eq_bot_of_notMem h inferInstance
  refine ⟨ℓ, hℓ, fun y hy φ hφ => ?_⟩
  rw [← sub_eq_zero, ← map_sub, ← Submodule.mem_bot ℂ, ← hℓ']
  exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨y, φ, hy, hφ, rfl⟩)

theorem fix_sum_smul {Λ : AddSubgroup (WO S T)} (hΛ : ∀ a : AE D, a * a = a → ∀ u ∈ Λ, a • u ∈ Λ)
    {f : WO S T → ℂ} (hf : IsLatVac (heisO ψ S T) Λ f) {ι : Type} [DecidableEq ι] (es : ι → AE D)
    {l : WO S T} (hl : l ∈ Λ) : ∀ s : Finset ι, (∀ P ∈ s, IsSplitIdem D (es P)) →
      (∀ P ∈ s, ∀ Q ∈ s, cA D (es P) * es Q = 0) → heisO ψ S T ((∑ P ∈ s, es P) • l) f = f := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro _ _; rw [Finset.sum_empty, zero_smul, heisO_zero]
  | insert a s ha ih =>
    intro hs ho
    have hs' : ∀ P ∈ s, IsSplitIdem D (es P) := fun P hP => hs P (Finset.mem_insert_of_mem hP)
    have ho' : ∀ P ∈ s, ∀ Q ∈ s, cA D (es P) * es Q = 0 := fun P hP Q hQ =>
      ho P (Finset.mem_insert_of_mem hP) Q (Finset.mem_insert_of_mem hQ)
    have hsa := hs a (Finset.mem_insert_self a s)
    have horth : symplO S T (es a • l) ((∑ P ∈ s, es P) • l) = 0 := by
      rw [symplO_smul, smul_smul, Finset.mul_sum,
        Finset.sum_eq_zero fun Q hQ => ho a (Finset.mem_insert_self a s) Q (Finset.mem_insert_of_mem hQ),
        zero_smul, symplO_zero_right]
    rw [Finset.sum_insert ha, add_smul, heisO_add_of_orth ψ S T horth, ih hs' ho',
      hf.2 (es a) hsa _ (hΛ _ hsa.1 l hl) (isHalf_smul hsa.1 l)]

end GlobalTheory.LevelSeries.IdemSumForm

namespace GlobalTheory.LevelSeries

open GlobalTheory.SplitScalar GlobalTheory.LevelSeries.IdemSumForm

theorem exists_invariant_form_idemSum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (eT : AE D), IsIdemSum eT T → ∃ ℓ : (WO V W → ℂ) →ₗ[ℂ] ℂ, ℓ f₀ ≠ 0 ∧ ∀ y : WO V W, IsHalf (cA D eT) y → ∀ φ : WO V W → ℂ, IsThetaFunO ψ V W φ → ℓ (heisO ψ V W y φ) = ℓ φ := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T eT hT
  obtain ⟨-, -, -, -, hΛV, hΛW, -, -, hψ, hvac⟩ := hP
  obtain ⟨⟨es, hes, rfl⟩, hTo⟩ := hT
  obtain ⟨hd, -, -⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ V W ΛV ΛW hψ hΛV hΛW
  have hΛ : ∀ a : AE D, a * a = a → ∀ u ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E))
      (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True), a • u ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E))
      (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True) := fun a ha =>
    GlobalTheory.LatticeStable.smul_mem_latO D V W _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha]))
  have hmul : ∀ P ∈ T, (∑ Q ∈ T, es Q) * es P = es P := by
    intro P hP
    rw [Finset.sum_mul, Finset.sum_eq_single_of_mem P hP]
    · exact (hes P hP).1.1
    · intro Q hQ hne
      exact GlobalTheory.Tow.idemAt_orth (hes Q hQ) (hes P hP) hne
  have hcross : ∀ P ∈ T, ∀ Q ∈ T, cA D (es P) * es Q = 0 := by
    intro P hP Q hQ
    rw [← hmul P hP, ← hmul Q hQ, RingHom.map_mul]
    calc cA D (∑ R ∈ T, es R) * cA D (es P) * ((∑ R ∈ T, es R) * es Q)
        = ((∑ R ∈ T, es R) * cA D (∑ R ∈ T, es R)) * (cA D (es P) * es Q) := by ring
      _ = 0 := by rw [hTo, zero_mul]
  have hsum1 : (∑ Q ∈ T, es Q) * (∑ Q ∈ T, es Q) = ∑ Q ∈ T, es Q := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hmul
  set eT := ∑ Q ∈ T, es Q with heT
  have hcsum : cA D eT = ∑ Q ∈ T, cA D (es Q) := map_sum _ _ _
  have hf0 : f₀ ≠ 0 := by
    rintro rfl
    obtain ⟨p, hp⟩ := hvac.norm.1
    have := hvac.norm.2 p hp
    simp [nrm2] at this
  have hfe : ∀ l ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True),
      IsHalf eT l → heisO ψ V W l f₀ = f₀ := by
    intro l hl hlh
    rw [← (isHalf_iff _ _).1 hlh]
    exact fix_sum_smul hΛ hvac.lat es hl T (fun P hP => (hes P hP).1) hcross
  have hfc : ∀ l ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True),
      IsHalf (cA D eT) l → heisO ψ V W l f₀ = f₀ := by
    intro l hl hlh
    rw [← (isHalf_iff _ _).1 hlh, hcsum]
    refine fix_sum_smul hΛ hvac.lat (fun Q => cA D (es Q)) hl T (fun P hP => isSplitIdem_conj (hes P hP).1) ?_
    intro P hP Q hQ
    rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm]
    exact hcross Q hQ P hP
  have hfin : ∀ u : WO V W, IsHalf (cA D eT) u → u.map (infPart D) = 0 := by
    intro u hu
    ext i j
    show infPart D (u i j) = 0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hu i j, RingHom.map_mul, hcsum, map_sum,
      Finset.sum_eq_zero fun Q hQ => infPart_splitIdem (isSplitIdem_conj (hes Q hQ).1), zero_mul]
  have he1 : cA D eT * cA D eT = cA D eT := by rw [← RingHom.map_mul, hsum1]
  have he2 : cA D (cA D eT) * cA D eT = 0 := by rw [GlobalTheory.DualPairCheck.cA_cA, hTo]
  exact invariant_form he1 he2 hfin hd (fun u hu => by rw [GlobalTheory.DualPairCheck.cA_cA]; exact hΛ _ hsum1 u hu) hf0
    (fun l hl hlh => hfc l hl hlh) (fun l hl hlh => hfe l hl (by rwa [GlobalTheory.DualPairCheck.cA_cA] at hlh))

end GlobalTheory.LevelSeries

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalPreimageOfSupportedAtPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift

theorem suppF_finIdem_mem_range : ∀ (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D), IsFinIdem D v f → ∀ k : GA D V, SuppF V f k → ∃ a : GlobalTheory.FinZeta.Gv V v, GlobalTheory.FinZeta.embV V v a = k := by
  intro D V v f hf k hk
  obtain ⟨ε, hε, rfl⟩ := hf
  obtain ⟨a, ha⟩ := (GlobalTheory.AdelicU.Supp.suppF_iff_mem_range V hε k).1 hk
  exact ⟨a, ha⟩

end GlobalTheory.RawLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNsmulMemOfSpan
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.LatSandwich

variable {E : Type} [Field E] [NumberField E]

theorem exists_nsmul_le {W : Type} [AddCommGroup W] [Module (𝓞 E) W] (s : Finset W) (M : Submodule (𝓞 E) W)
    (h : ∀ x ∈ s, ∃ k : ℕ, 0 < k ∧ k • x ∈ M) :
    ∃ k : ℕ, 0 < k ∧ ∀ x ∈ Submodule.span (𝓞 E) (s : Set W), k • x ∈ M := by
  classical
  choose! n hn hn' using h
  refine ⟨∏ t ∈ s, n t, Finset.prod_pos fun t ht => hn t ht, fun m hm => ?_⟩
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n (Finset.mem_coe.1 hx)
    rw [hk, mul_comm, mul_smul]
    exact M.nsmul_mem (hn' x (Finset.mem_coe.1 hx)) k
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact M.smul_mem a hx

theorem exists_nat_mul_isIntegral (z : E) : ∃ k : ℕ, 0 < k ∧ IsIntegral ℤ ((k : E) * z) := by
  have hal : IsAlgebraic ℤ z :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic z)
  obtain ⟨y, hy, hi⟩ := hal.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  have hc : ((y.natAbs : ℕ) : E) = ((y.natAbs : ℤ) : E) := (Int.cast_natCast _).symm
  rw [zsmul_eq_mul] at hi
  rcases Int.natAbs_eq y with e | e
  · rw [hc, ← e]; exact hi
  · rw [hc, show ((y.natAbs : ℤ)) = -y by omega, Int.cast_neg, neg_mul]; exact hi.neg

theorem mem_stdLat_iff {n : ℕ} (x : Fin n → E) : x ∈ Formalism.L2.Pj.stdLat E n ↔ ∀ i, IsIntegral ℤ (x i) := by
  simp only [Formalism.L2.Pj.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]
  refine forall_congr' fun i => ⟨?_, fun h => ⟨⟨x i, h⟩, rfl⟩⟩
  rintro ⟨y, hy⟩
  rw [← hy]
  exact RingOfIntegers.isIntegral_coe y

theorem exists_nsmul_mem_stdLat {n : ℕ} (v : Fin n → E) : ∃ k : ℕ, 0 < k ∧ k • v ∈ Formalism.L2.Pj.stdLat E n := by
  classical
  obtain ⟨k, hk, h⟩ := exists_nsmul_le (Finset.univ.image fun i => Pi.single i (v i)) (Formalism.L2.Pj.stdLat E n) (by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index, forall_apply_eq_imp_iff]
    intro i
    obtain ⟨k, hk, hi⟩ := exists_nat_mul_isIntegral (v i)
    refine ⟨k, hk, (mem_stdLat_iff _).2 fun j => ?_⟩
    by_cases e : j = i
    · subst e
      simpa [nsmul_eq_mul] using hi
    · simp [Pi.single_eq_of_ne e, isIntegral_zero])
  refine ⟨k, hk, h v ?_⟩
  have hs : ∑ i, Pi.single i (v i) ∈ Submodule.span (𝓞 E) ((Finset.univ.image fun i => Pi.single i (v i) : Finset (Fin n → E)) : Set (Fin n → E)) :=
    Submodule.sum_mem _ fun i _ => Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem (fun i => Pi.single i (v i)) (Finset.mem_univ i)))
  rwa [Finset.univ_sum_single v] at hs

theorem exists_nsmul_mem_of_span {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (hsp : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) (v : Fin n → E) : ∃ k : ℕ, 0 < k ∧ k • v ∈ Λ := by
  have hv : v ∈ Submodule.span E (Λ : Set (Fin n → E)) := by rw [hsp]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_pos, by rwa [one_smul]⟩
  | zero => exact ⟨1, one_pos, by rw [smul_zero]; exact zero_mem _⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hy⟩ := hy
    obtain ⟨b, hb, hz⟩ := hz
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Λ.nsmul_mem hy _
    · rw [mul_smul]; exact Λ.nsmul_mem hz _
  | smul a y _ hy =>
    obtain ⟨m, hm, hy⟩ := hy
    obtain ⟨c, hc, hi⟩ := exists_nat_mul_isIntegral a
    refine ⟨c * m, Nat.mul_pos hc hm, ?_⟩
    have h := Λ.smul_mem (⟨(c : E) * a, hi⟩ : 𝓞 E) hy
    convert h using 1
    funext j
    change (c * m) • (a * y j) = ((c : E) * a) * (m • y j)
    simp only [nsmul_eq_mul, Nat.cast_mul]
    ring

end GlobalTheory.LatSandwich

namespace GlobalTheory.LatSandwich

variable {E : Type} [Field E] [NumberField E]

theorem sandwich_of_fg {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ.FG)
    (hsp : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) :
    ∃ a : ℕ, 0 < a ∧ (∀ x ∈ Formalism.L2.Pj.stdLat E n, (a : 𝓞 E) • x ∈ Λ) ∧
      ∀ x ∈ Λ, (a : 𝓞 E) • x ∈ Formalism.L2.Pj.stdLat E n := by
  classical
  obtain ⟨T, hT⟩ := hfg
  obtain ⟨d, hd, hup⟩ := exists_nsmul_le T (Formalism.L2.Pj.stdLat E n) fun x _ => exists_nsmul_mem_stdLat x
  obtain ⟨d', hd', hlo⟩ := exists_nsmul_le (Finset.univ.image fun i : Fin n => (Pi.single i 1 : Fin n → E)) Λ
    fun x _ => exists_nsmul_mem_of_span Λ hsp x
  refine ⟨d * d', Nat.mul_pos hd hd', fun x hx => ?_, fun x hx => ?_⟩
  · rw [Nat.cast_smul_eq_nsmul, mul_smul]
    refine Λ.nsmul_mem (hlo x ?_) d
    have hint := (mem_stdLat_iff x).1 hx
    have hs : ∑ i, (⟨x i, hint i⟩ : 𝓞 E) • (Pi.single i 1 : Fin n → E) ∈ Submodule.span (𝓞 E)
        ((Finset.univ.image fun i : Fin n => (Pi.single i 1 : Fin n → E) : Finset (Fin n → E)) : Set (Fin n → E)) :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
        (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem (fun i : Fin n => (Pi.single i 1 : Fin n → E)) (Finset.mem_univ i))))
    have e : ∑ i, (⟨x i, hint i⟩ : 𝓞 E) • (Pi.single i 1 : Fin n → E) = x := by
      conv_rhs => rw [← Finset.univ_sum_single x]
      refine Finset.sum_congr rfl fun i _ => ?_
      funext j
      by_cases h : j = i
      · subst h
        change x j * (Pi.single j 1 : Fin n → E) j = _
        simp
      · change x i * (Pi.single i 1 : Fin n → E) j = _
        simp [Pi.single_eq_of_ne h]
    rwa [e] at hs
  · rw [Nat.cast_smul_eq_nsmul, mul_comm, mul_smul]
    exact nsmul_mem (hup x (hT ▸ hx)) d'

end GlobalTheory.LatSandwich

namespace GlobalTheory.LatSandwich

theorem sandwich : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), (∀ x, x ∈ Λ ↔ x ∈ L0c D V) →
    ∃ a : ℕ, 0 < a ∧ (∀ x ∈ Formalism.L2.Pj.stdLat D.host.E V.rank, (a : 𝓞 D.host.E) • x ∈ Λ) ∧
      ∀ x ∈ Λ, (a : 𝓞 D.host.E) • x ∈ Formalism.L2.Pj.stdLat D.host.E V.rank := by
  intro D V Λ hΛ
  have e : Λ = V.L0.map (V.frame.equivFun.restrictScalars (𝓞 D.host.E)).toLinearMap := by
    ext x
    rw [hΛ, Submodule.mem_map]
    constructor
    · intro hx
      refine ⟨V.frame.equivFun.symm x, ?_, V.frame.equivFun.apply_symm_apply x⟩
      rw [V.frame.equivFun_symm_apply]
      exact hx
    · rintro ⟨y, hy, rfl⟩
      change ∑ i, V.frame.equivFun y i • V.frame i ∈ V.L0
      rw [V.frame.sum_equivFun]
      exact hy
  refine sandwich_of_fg Λ (e ▸ V.standardTuple_isLattice.fg.map _) ?_
  have hs : (Λ : Set (Fin V.rank → D.host.E)) = V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) := by
    rw [e]; rfl
  have hspan : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
    classical
    let W := Submodule.span D.host.E (V.L0 : Set V.V)
    change W = ⊤
    by_contra h
    let e : V.V ≃ₗ⋆[D.host.E] V.V :=
      V.frame.equivFun.trans ((starLinearEquiv D.host.E).trans V.frame.equivFun.symm)
    let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
      (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
    have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) <
        Module.finrank D.host.E V.V := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt h
    obtain ⟨x, hx, hx₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    have hsmul (a : D.host.E) : a • e x ∈ V.L0 := by
      rw [← V.baseLattice_isUnimodular]
      simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual,
        Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
      intro y hy
      have hxy : V.hT (e x) y = 0 :=
        congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩)
          (LinearMap.mem_ker.mp hx)
      have hyx : V.hT y (e x) = 0 := V.herm.eq_iff.mp hxy
      simp [map_smul, hyx]
    let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
      ((LinearMap.toSpanSingleton D.host.E _ (e x)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
    let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
    let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective D.host.E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField D.host.E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 D.host.E) D.host.E) (Field.toIsField D.host.E))
  rw [hs, ← Submodule.map_span, hspan, Submodule.map_top, LinearEquiv.range]

end GlobalTheory.LatSandwich
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitSupportedRepFiniteUnitaryClass
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RankReps


set_option maxHeartbeats 1000000 in
theorem exists_rep_split_levJ : ∀ (D : D7) (ρ : Setup D.ntw), ρ.Good → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool), ∀ h ∈ GfC (Vc D j), ∃ (γ : GQ (Vc D j)) (s : Finset (Pl D.host.E)) (h' : GA D (Vc D j)) (k : (ρ.B i j b).levJ (ρ.tw i b 0 ∅ 1)), SplitSet s ∧ (∀ v ∈ s, ((ρ.bad i : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) ∧ h' ∈ GfC (Vc D j) ∧ SuppAt (idem s) (Vc D j) h' ∧ finPt (Vc D j) h = Bridge.ratF (Vc D j) γ * finPt (Vc D j) h' * (k : Bridge.Gf (Vc D j)) := by
  intro D ρ hρ i j b h hh
  obtain ⟨N₀, hN₀, hK⟩ := GlobalTheory.LevFinCong.exists_finCong_lev D (Vc D j) (ρ.B i j b).F.βS
    ((ρ.B i j b).levS (ρ.tw i b 0 ∅ 1))
  have hbad : 0 < ρ.bad i := Nat.pos_of_ne_zero (hρ.bad_ne i)
  have hK' : ∀ k ∈ GfC (Vc D j), GlobalTheory.Member.FinCong (Vc D j) N₀ k → FWT.fin (Vc D j) k ∈ (ρ.B i j b).levJ (ρ.tw i b 0 ∅ 1) :=
    fun k hk hc => ((ρ.B i j b).finPt_mem_levJ _ hk).2 (hK k hk hc).1
  obtain ⟨h', ⟨hh', hs⟩, γ, k, e⟩ := GlobalTheory.SplitReps.exists_split_rep (Vc D j) hN₀ hK' hbad (finPt (Vc D j) h)
  have hsb := GlobalTheory.SplitReps.splitOffBad_of_suppSplit (Vc D j) (ρ.bad i) h' hh' hs
  obtain ⟨-, e', P, hP, hoff, hsupp⟩ := hsb
  refine ⟨γ, P, h', k, ⟨e', hP⟩, hoff, hh', ?_, e⟩
  rw [idem_eq hP]
  exact hsupp

end GlobalTheory.RankReps
end

