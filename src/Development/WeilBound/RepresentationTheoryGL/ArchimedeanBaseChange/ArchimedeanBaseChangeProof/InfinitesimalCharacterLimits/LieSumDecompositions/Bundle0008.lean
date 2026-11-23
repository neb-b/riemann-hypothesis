module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CapelliDetDiagonalBlockActsByInfinitesimalCharac
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0368
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAuxiliaryStatementB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1205
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0329
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksFgA
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SqIntCritHolds

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.ActFinApply
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Affgl PositivityTheory.Rg.Rs GlobalTheory.BlockCap
open PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockDerivatives

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockSlices

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem act_fin_apply {a : ℕ} (h : GL (Fin a) (Af E)) (F : Sm E a) (x : GA E a) :
    (act (.fin h) F).1 x = F.1 (x * finGL E a h) := rfl

theorem act_cpt_apply {a : ℕ} (k : Kinf E a) (F : Sm E a) (x : GA E a) :
    (act (.cpt k) F).1 x = F.1 (x * infGL E a (Unitary.toUnits k)) := rfl

variable {r s : ℕ}

theorem yp_one : yp (E := E) (a := r + s) 1 1 = 1 := by
  simp [yp]

theorem base_one {U : Submodule ℂ (Sm E (r + s))} (hU : IsAutSt U) {c : ℂ} {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)}
    (hT : IsSliceMap U c T) {ψ : Sm E (r + s)} (hψ : ψ ∈ U) (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) :
    ∃ ψ' ∈ U, ∀ x, (T ψ').1 x = (T ψ).1 (x * yp k g) := by
  refine ⟨act (.cpt k) (act (.fin g) ψ), hU.1 _ _ (hU.1 _ _ hψ), fun x => ?_⟩
  rw [hT.equiv _ _ (hU.1 _ _ hψ), hT.equiv _ _ hψ]
  exact InducedTensorMap.A.act_cf k g (T ψ) x

theorem mem_LS_of {U : Submodule ℂ (Sm E (r + s))} {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)} {ψ : Sm E (r + s)}
    (hψ : ψ ∈ U) (ℓ : Sm E r) (m₂ : GA E s) (h : ∀ m₁, ℓ.1 m₁ = (T ψ).1 (lev (Ad E) r s (m₁, m₂))) : ℓ ∈ LS U T :=
  Submodule.subset_span ⟨ψ, hψ, 1, 1, m₂, fun m₁ => by rw [h, yp_one, mul_one]⟩

theorem mem_RS_of {U : Submodule ℂ (Sm E (r + s))} {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)} {ψ : Sm E (r + s)}
    (hψ : ψ ∈ U) (ℓ : Sm E s) (m₁ : GA E r) (h : ∀ m₂, ℓ.1 m₂ = (T ψ).1 (lev (Ad E) r s (m₁, m₂))) : ℓ ∈ RS U T :=
  Submodule.subset_span ⟨ψ, hψ, 1, 1, m₁, fun m₂ => by rw [h, yp_one, mul_one]⟩

omit [IsCMField E] in
theorem upd0 (m₁ y : GA E r) (m₂ : GA E s) :
    Function.update (CapFactor.levPair (n := ![r, s]) (m₁, m₂)) 0 y = CapFactor.levPair (n := ![r, s]) (y, m₂) := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

omit [IsCMField E] in
theorem upd1 (m₁ : GA E r) (m₂ y : GA E s) :
    Function.update (CapFactor.levPair (n := ![r, s]) (m₁, m₂)) 1 y = CapFactor.levPair (n := ![r, s]) (m₁, y) := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

section Step

variable {U : Submodule ℂ (Sm E (r + s))} (hU : IsAutSt U) {c : ℂ} {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)}
  (hT : IsSliceMap U c T)
include hU hT

theorem act_left {ψ : Sm E (r + s)} (hψ : ψ ∈ U) (ℓ : Sm E r) (m₂ : GA E s)
    (h : ∀ m₁, ℓ.1 m₁ = (T ψ).1 (lev (Ad E) r s (m₁, m₂))) (o : Op E r) : act o ℓ ∈ LS U T := by
  cases o with
  | fin h' =>
    refine mem_LS_of (hU.1 (.fin (lev (Af E) r s (h', 1))) ψ hψ) _ m₂ fun m₁ => ?_
    have e : lev (Ad E) r s (finGL E r h', 1) = finGL E (r + s) (lev (Af E) r s (h', 1)) := by
      rw [← Slice1.lev_finGL, map_one]
    rw [act_fin_apply, h, hT.equiv _ _ hψ, act_fin_apply, Slice1.lev_mul_one, e]
  | cpt κ =>
    refine mem_LS_of (hU.1 (.cpt (Slice1.levK E r s κ)) ψ hψ) _ m₂ fun m₁ => ?_
    rw [act_cpt_apply, h, hT.equiv _ _ hψ, act_cpt_apply, Slice1.lev_mul_one, Slice1.infGL_levK]
  | lie X =>
    let n : Fin 2 → ℕ := ![r, s]
    have h2 : ∑ i, n i = n 0 + n 1 := CapFactor.two_sum n
    refine mem_LS_of (hU.1 (.lie (blockCLM (stdBlocks n h2) 0 X)) ψ hψ) _ m₂ fun m₁ => ?_
    have key := LinearMap.congr_fun
      (restrLin_lie (E := E) (stdBlocks n h2) (CapFactor.levPair (n := n) ((1 : GA E r), m₂)) 0 X) (T ψ)
    have hℓ : ℓ = restrLin (stdBlocks n h2) (CapFactor.levPair (n := n) ((1 : GA E r), m₂)) 0 (T ψ) :=
      Subtype.ext (funext fun y => by
        rw [h y]
        change _ = (T ψ).1 (leviEmb (Ad E) (stdBlocks n h2)
          (Function.update (CapFactor.levPair (n := n) ((1 : GA E r), m₂)) 0 y))
        rw [upd0, ← CapFactor.lev_eq_leviEmb]
        rfl)
    have key2 : (restrLin (stdBlocks n h2) (CapFactor.levPair (n := n) ((1 : GA E r), m₂)) 0
        (lie E (r + s) (blockCLM (stdBlocks n h2) 0 X) (T ψ))).1 m₁ = (lie E r X ℓ).1 m₁ := by
      rw [hℓ]
      exact congrArg (fun φ : Sm E (n 0) => φ.1 m₁) key
    rw [hT.equiv _ _ hψ]
    change (lie E r X ℓ).1 m₁ = (lie E (r + s) (blockCLM (stdBlocks n h2) 0 X) (T ψ)).1 (lev (Ad E) r s (m₁, m₂))
    rw [← key2]
    change (lie E (r + s) (blockCLM (stdBlocks n h2) 0 X) (T ψ)).1 (leviEmb (Ad E) (stdBlocks n h2)
      (Function.update (CapFactor.levPair (n := n) ((1 : GA E r), m₂)) 0 m₁)) = _
    rw [upd0, ← CapFactor.lev_eq_leviEmb]
    rfl

theorem act_right {ψ : Sm E (r + s)} (hψ : ψ ∈ U) (ℓ : Sm E s) (m₁ : GA E r)
    (h : ∀ m₂, ℓ.1 m₂ = (T ψ).1 (lev (Ad E) r s (m₁, m₂))) (o : Op E s) : act o ℓ ∈ RS U T := by
  cases o with
  | fin h' =>
    refine mem_RS_of (hU.1 (.fin (lev (Af E) r s (1, h'))) ψ hψ) _ m₁ fun m₂ => ?_
    rw [act_fin_apply, h, hT.equiv _ _ hψ, act_fin_apply, Slice2.lev_mul_right, Slice2.lev_finGL_one]
  | cpt κ =>
    refine mem_RS_of (hU.1 (.cpt (Slice2.levK E r s κ)) ψ hψ) _ m₁ fun m₂ => ?_
    rw [act_cpt_apply, h, hT.equiv _ _ hψ, act_cpt_apply, Slice2.lev_mul_right, Slice2.lev_infGL_one,
      Slice2.toUnits_levK]
  | lie X =>
    let n : Fin 2 → ℕ := ![r, s]
    have h2 : ∑ i, n i = n 0 + n 1 := CapFactor.two_sum n
    refine mem_RS_of (hU.1 (.lie (blockCLM (stdBlocks n h2) 1 X)) ψ hψ) _ m₁ fun m₂ => ?_
    have key := LinearMap.congr_fun
      (restrLin_lie (E := E) (stdBlocks n h2) (CapFactor.levPair (n := n) (m₁, (1 : GA E s))) 1 X) (T ψ)
    have hℓ : ℓ = restrLin (stdBlocks n h2) (CapFactor.levPair (n := n) (m₁, (1 : GA E s))) 1 (T ψ) :=
      Subtype.ext (funext fun y => by
        rw [h y]
        change _ = (T ψ).1 (leviEmb (Ad E) (stdBlocks n h2)
          (Function.update (CapFactor.levPair (n := n) (m₁, (1 : GA E s))) 1 y))
        rw [upd1, ← CapFactor.lev_eq_leviEmb]
        rfl)
    have key2 : (restrLin (stdBlocks n h2) (CapFactor.levPair (n := n) (m₁, (1 : GA E s))) 1
        (lie E (r + s) (blockCLM (stdBlocks n h2) 1 X) (T ψ))).1 m₂ = (lie E s X ℓ).1 m₂ := by
      rw [hℓ]
      exact congrArg (fun φ : Sm E (n 1) => φ.1 m₂) key
    rw [hT.equiv _ _ hψ]
    change (lie E s X ℓ).1 m₂ = (lie E (r + s) (blockCLM (stdBlocks n h2) 1 X) (T ψ)).1 (lev (Ad E) r s (m₁, m₂))
    rw [← key2]
    change (lie E (r + s) (blockCLM (stdBlocks n h2) 1 X) (T ψ)).1 (leviEmb (Ad E) (stdBlocks n h2)
      (Function.update (CapFactor.levPair (n := n) (m₁, (1 : GA E s))) 1 m₂)) = _
    rw [upd1, ← CapFactor.lev_eq_leviEmb]
    rfl

theorem LS_stable : _root_.GlobalTheory.CuspRep.IsStable (LS U T) := by
  intro o φ hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ψ, hψ, k, g, m₂, hx⟩ := hx
    obtain ⟨ψ', hψ', e⟩ := base_one hU hT hψ k g
    exact act_left hU hT hψ' x m₂ (fun m₁ => by rw [hx, ← e]) o
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

theorem RS_stable : _root_.GlobalTheory.CuspRep.IsStable (RS U T) := by
  intro o φ hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ψ, hψ, k, g, m₁, hx⟩ := hx
    obtain ⟨ψ', hψ', e⟩ := base_one hU hT hψ k g
    exact act_right hU hT hψ' x m₁ (fun m₂ => by rw [hx, ← e]) o
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx


omit hU in
theorem LS_aut : ∀ φ ∈ LS U T, IsAutForm φ := by
  intro φ hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ψ, hψ, k, g, m₂, hx⟩ := hx
    obtain ⟨ψ₁, hA, h1, -⟩ := hT.left ψ hψ k g m₂
    have : x = ψ₁ := Subtype.ext (funext fun m₁ => (hx m₁).trans (h1 m₁).symm)
    exact this ▸ hA
  | zero => exact GlobalTheory.HCF.FormsSub.isAutForm_zero
  | add x y _ _ hx hy => exact GlobalTheory.CompanionTheory.AffglAssembly.isAutForm_add hx hy
  | smul a x _ hx => exact GlobalTheory.CompanionTheory.AffglAssembly.isAutForm_smul a hx


omit hU in
theorem RS_aut : ∀ φ ∈ RS U T, IsAutForm φ := by
  intro φ hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ψ, hψ, k, g, m₁, hx⟩ := hx
    obtain ⟨ψ₂, hA, h1, -⟩ := hT.right ψ hψ k g m₁
    have : x = ψ₂ := Subtype.ext (funext fun m₂ => (hx m₂).trans (h1 m₂).symm)
    exact this ▸ hA
  | zero => exact GlobalTheory.HCF.FormsSub.isAutForm_zero
  | add x y _ _ hx hy => exact GlobalTheory.CompanionTheory.AffglAssembly.isAutForm_add hx hy
  | smul a x _ hx => exact GlobalTheory.CompanionTheory.AffglAssembly.isAutForm_smul a hx

theorem memInd2 : ∀ ψ ∈ U, MemInd2 (LS U T) (RS U T) (T ψ) := by
  intro ψ hψ
  refine ⟨hT.unipInv ψ hψ, fun k g => ?_⟩
  obtain ⟨n, b, q, hb, hq, he⟩ := expand hU hT ψ hψ k g
  have e : (fun m => (T ψ).1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) =
      fun m => ∑ i, (b i).1 m.1 * (q i).1 m.2 := funext he
  rw [e]
  exact ParabolicProjection.sum_mem_tens2 (fun i => Submodule.span_le.2 (lsF_sub_LS hψ k g) (hb i))
    (fun i => rsF_sub_RS hψ k g (hq i))

end Step

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockSlices

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksFgB
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs GlobalTheory.SmGL

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration

set_option linter.unusedSectionVars false

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section Curve

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

def ecurve {N : ℕ} (Z : Matrix (Fin N) (Fin N) (Cinf E)) (t : ℝ) : Matrix (Fin N) (Fin N) (Cinf E) :=
  NormedSpace.exp (t • Z)

theorem hasDerivAt_ecurve {N : ℕ} (Z : Matrix (Fin N) (Fin N) (Cinf E)) : HasDerivAt (ecurve Z) Z 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Z (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact h

theorem ecurve_zero {N : ℕ} (Z : Matrix (Fin N) (Fin N) (Cinf E)) : ecurve Z 0 = 1 := by
  simp [ecurve]

theorem ecurve_mem {N : ℕ} (Z : Matrix (Fin N) (Fin N) (Cinf E)) (hZ : Zᴴ = -Z) (t : ℝ) :
    ecurve Z t ∈ Matrix.unitaryGroup (Fin N) (Cinf E) := by
  have hc : (t • Z)ᴴ = -(t • Z) := by
    rw [conjTranspose_smul, hZ]; simp
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ecurve, ← Matrix.exp_conjTranspose, hc,
    ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • Z)).neg_right]
  simp

def toLclm (N : ℕ) : Matrix (Fin N) (Fin N) (Cinf E) →L[ℝ] Lie E N :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => toL A, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

theorem hasDerivAt_toL_ecurve {N : ℕ} (Z : Matrix (Fin N) (Fin N) (Cinf E)) :
    HasDerivAt (fun t => (toL (ecurve Z t) : Lie E N)) (toL Z) 0 := by
  have h := ((toLclm (E := E) N).hasFDerivAt (x := ecurve Z 0)).comp_hasDerivAt (0 : ℝ) (hasDerivAt_ecurve Z)
  exact h

end Curve

def kcurve {N : ℕ} (Z : Matrix (Fin N) (Fin N) (Cinf E)) (hZ : Zᴴ = -Z) (t : ℝ) : Kinf E N :=
  ⟨ecurve Z t, ecurve_mem Z hZ t⟩

theorem lie_mem_orbSpan {N : ℕ} (φ : Sm E N) [FiniteDimensional ℂ (GlobalTheory.CuspRep.LocEx.orbSpan φ)]
    (Z : Matrix (Fin N) (Fin N) (Cinf E)) (hZ : Zᴴ = -Z) :
    lie E N (toL Z) φ ∈ GlobalTheory.CuspRep.LocEx.orbSpan φ := by
  set A : Submodule ℂ (GA E N → ℂ) := (GlobalTheory.CuspRep.LocEx.orbSpan φ).map (Sm E N).subtype with hA
  have : FiniteDimensional ℂ A := inferInstance
  obtain ⟨S, a, ha⟩ := SliceTensor.interp A
  let c : ℝ → GL (Fin N) (Cinf E) := fun t => Unitary.toUnits (kcurve Z hZ t)
  have h0 : c 0 = 1 := Units.ext (ecurve_zero Z)
  have hc : HasDerivAt (fun t => toL (c t).val) (toL Z) 0 := hasDerivAt_toL_ecurve Z
  have hmem : ∀ t, (cptRep E N (kcurve Z hZ t) φ).1 ∈ A := fun t =>
    ⟨_, Submodule.subset_span ⟨kcurve Z hZ t, rfl⟩, rfl⟩
  have hval : ∀ t g, (cptRep E N (kcurve Z hZ t) φ).1 g = φ.1 (g * infGL E N (c t)) := fun _ _ => rfl
  have key : ∀ g, lieD (toL Z) φ.1 g = ∑ κ : S, lieD (toL Z) φ.1 κ.1 * (a κ : GA E N → ℂ) g := by
    intro g
    have e : ∀ t, φ.1 (g * infGL E N (c t)) = ∑ κ : S, φ.1 (κ.1 * infGL E N (c t)) * (a κ : GA E N → ℂ) g := by
      intro t
      have := congrFun (ha _ (hmem t)) g
      rw [hval, Finset.sum_apply] at this
      rw [this]
      refine Finset.sum_congr rfl fun κ _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, hval]
    have d1 := hasDerivAt_curve φ g c (toL Z) h0 hc
    have d2 : HasDerivAt (fun t => ∑ κ : S, φ.1 (κ.1 * infGL E N (c t)) * (a κ : GA E N → ℂ) g)
        (∑ κ : S, lieD (toL Z) φ.1 κ.1 * (a κ : GA E N → ℂ) g) 0 :=
      HasDerivAt.fun_sum fun κ _ => (hasDerivAt_curve φ κ.1 c (toL Z) h0 hc).mul_const _
    rw [show (fun t => φ.1 (g * infGL E N (c t))) = fun t =>
      ∑ κ : S, φ.1 (κ.1 * infGL E N (c t)) * (a κ : GA E N → ℂ) g from funext e] at d1
    exact d1.unique d2
  have hL : (lie E N (toL Z) φ).1 ∈ A := by
    have e : (lie E N (toL Z) φ).1 = ∑ κ : S, lieD (toL Z) φ.1 κ.1 • (a κ : GA E N → ℂ) := by
      funext g
      rw [GlobalTheory.CuspRep.lie_apply, key g, Finset.sum_apply]
      rfl
    rw [e]
    exact A.sum_mem fun κ _ => A.smul_mem _ (a κ).2
  obtain ⟨y, hy, e⟩ := hL
  have : y = lie E N (toL Z) φ := Subtype.ext e
  rw [← this]
  exact hy

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.UntwExp
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux.Tw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

omit [IsCMField E] in
theorem re_tw {z : ℂ} (hz : z.re = 0) : (z / (N * (Module.finrank ℚ E : ℂ))).re = 0 := by
  rw [Complex.div_re]
  simp [hz]

theorem untw_cen (hN : 0 < N) {z : ℂ} {φ : Sm E N}
    (hc : ∀ (t : ℝ) g, φ.1 (splitCentre E N t * g) = Complex.exp (z * t) * φ.1 g) (t : ℝ) (g : GA E N) :
    (mulChi N (Model.absC E (-(z / (N * (Module.finrank ℚ E : ℂ))))) φ).1 (splitCentre E N t * g) =
      (mulChi N (Model.absC E (-(z / (N * (Module.finrank ℚ E : ℂ))))) φ).1 g := by
  have hd : (Module.finrank ℚ E : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  set w := z / (N * (Module.finrank ℚ E : ℂ)) with hw
  have hcd : ∀ t : ℝ, ((chiDet N (Model.absC E (-w)) (splitCentre E N t) : ℂˣ) : ℂ) = Complex.exp (-(z * t)) := by
    intro t
    rw [ExponentTwist.splitCentre_eq, ExponentTwist.chiDet_aT le_rfl]
    congr 1
    rw [hw]
    field_simp
  rw [mulChi_apply, mulChi_apply, hc t g, map_mul, Units.val_mul, hcd t]
  have e : Complex.exp (z * t) * Complex.exp (-(z * t)) = 1 := by
    rw [← Complex.exp_add]; simp
  linear_combination (φ.1 g * ((chiDet N (Model.absC E (-w)) g : ℂˣ) : ℂ)) * e

theorem untw_exp {z : ℂ} (hz : z.re = 0) {φ : Sm E N} (hA : IsAutForm φ) (r : ℕ) (hr : 0 < r) (hrN : r < N) (c : ℂ)
    (hc : c ∈ Exp r (mulChi N (Model.absC E (-(z / (N * (Module.finrank ℚ E : ℂ))))) φ).1) :
    ∃ c' ∈ Exp r φ.1, pE E N r c = pE E N r c' := by
  have hd : (Module.finrank ℚ E : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  set w := z / (N * (Module.finrank ℚ E : ℂ)) with hw
  have h1 := expTw_holds E N φ (-w) hA r hr hrN c hc
  refine ⟨_, h1, ?_⟩
  have e : -w * (r : ℂ) * (Module.finrank ℚ E : ℂ) = (((-(r : ℝ) / N) : ℝ) : ℂ) * z := by
    rw [hw]; push_cast; field_simp
  have hre : (c - -w * (r : ℂ) * (Module.finrank ℚ E : ℂ)).re = c.re := by
    rw [e, Complex.sub_re, Complex.re_ofReal_mul, hz, mul_zero, sub_zero]
  unfold pE
  rw [hre]

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux.Tw

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux

open Tw ParabolicProjection in
theorem leaf_of (hC : Core) (hP : GrowPHolds) : Leaf := by
  intro E _ _ _ N τ hN U hU φ hφU hneg hφ0
  obtain ⟨⟨hst, hA⟩, -, hNP, ⟨z, hz, hcent⟩, -⟩ := hU
  have aut_tw {a : ℕ} {ψ : Sm E a} (h : IsAutForm ψ) (χ : HChar E) :
      IsAutForm (mulChi a χ ψ) := by
    exact {
      left γ g := by simp [h.left, chiDet_ratGL]
      level := isOpen_stab_of_mem_nhds _ _ <| Filter.mem_of_superset
        ((h.level.inter (isOpen_ker_chiDet χ)).mem_nhds ⟨by simp, by simp⟩) fun k hk => by
          have h1 : rt E a (finGL E a k) ψ = ψ := hk.1
          have h2 : chiDet a χ (finGL E a k) = 1 := hk.2
          change rt E a (finGL E a k) _ = _
          rw [rt_mulChi, h1, h2, Units.val_one, one_smul]
      kfin := by
        have := h.kfin
        refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E a k ψ)).map
          (GlobalTheory.CuspRep.mulChi a χ).toLinearMap) (Submodule.span_le.2 ?_)
        rintro _ ⟨k, rfl⟩
        exact ⟨_, Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩), (rt_mulChi χ _ ψ).symm⟩
      zfin := by
        have := h.zfin
        refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z ψ) ''
          Zalg E a)).map (GlobalTheory.CuspRep.mulChi a χ).toLinearMap) (Submodule.span_le.2 ?_)
        rintro _ ⟨z, hz, rfl⟩
        obtain ⟨z', h1, h2⟩ := Zalg_mulChi χ hz
        exact ⟨_, Submodule.subset_span ⟨z', h1, rfl⟩, (h2 ψ).symm⟩
      growth g := by
        obtain ⟨C, N, h1⟩ := h.growth g
        obtain ⟨C', N', h2⟩ := chiDet_growth (a := a) χ
        refine ⟨C * (‖((chiDet a χ g : ℂˣ) : ℂ)‖ * C'), N + N', fun y => ?_⟩
        rw [mulChi_apply, map_mul, Units.val_mul, norm_mul, norm_mul]
        refine (mul_le_mul (h1 y) (mul_le_mul_of_nonneg_left (h2 y) (norm_nonneg _)) (by positivity)
          ((norm_nonneg _).trans (h1 y))).trans_eq ?_
        ring }
  set w := z / (N * (Module.finrank ℚ E : ℂ)) with hw
  have hU'st : _root_.GlobalTheory.CuspRep.IsStable (tw U (-w)) := isStable_tw hst (-w)
  have hU'A : ∀ χ ∈ tw U (-w), IsAutForm χ := by
    rintro _ ⟨ψ, hψ, rfl⟩
    exact aut_tw (hA ψ hψ) _
  have hU'P : ∀ χ ∈ tw U (-w), GrowP χ.1 := by
    rintro _ ⟨ψ, hψ, rfl⟩
    refine hP E N _ (aut_tw (hA ψ hψ) _) (untw_cen hN (hcent ψ hψ)) fun r hr hrN c hc => ?_
    obtain ⟨c', hc', e⟩ := untw_exp hz (hA ψ hψ) r hr hrN c hc
    rw [e]
    exact hNP ψ hψ r hr hrN c' hc'
  have hφ'A2 : mulChi N (Model.absC E (-w)) φ ∈ A2 E N := by
    refine Submodule.subset_span ⟨aut_tw (hA φ hφU) _, sqIntCrit_holds E N _ (aut_tw (hA φ hφU) _)
      (untw_cen hN (hcent φ hφU)) fun r hr hrN c hc => ?_⟩
    obtain ⟨c', hc', e⟩ := untw_exp hz (hA φ hφU) r hr hrN c hc
    rw [e]
    exact hneg r hr hrN c' hc'
  have hφ'0 : mulChi N (Model.absC E (-w)) φ ≠ 0 := by
    rw [Ne, LinearEquiv.map_eq_zero_iff]; exact hφ0
  obtain ⟨V, p, hV, hpV, hpe, hp0⟩ :=
    hC E N (tw U (-w)) hU'st hU'A hU'P _ ⟨φ, hφU, rfl⟩ hφ'A2 hφ'0
  have hUle : ∀ ψ ∈ U, ψ ∈ tw (tw U (-w)) w := fun ψ hψ => ⟨_, ⟨ψ, hψ, rfl⟩, mulChi_absC_neg' N w ψ⟩
  refine ⟨.leaf V w, twMap N w p, Or.inr ⟨hN, hV, re_tw hz⟩, hN,
    fun o ψ hψ => twMap_equiv hU'st hpe o ψ (hUle ψ hψ), fun ψ hψ => twMap_mem hpV ψ (hUle ψ hψ), ?_⟩
  rw [twMap_apply, Ne, LinearEquiv.map_eq_zero_iff]
  exact hp0

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux

end
end

