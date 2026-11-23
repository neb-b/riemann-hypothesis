module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0327
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0291
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0331
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0188
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0330
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0033
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0200

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterTwistAbsPow
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.Dblock

theorem smul_of_equiv_nu {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ G V} {σ : Representation ℂ G W} (φ : π.Equiv σ) (g : G) (c : ℂ)
    (h : ∀ v, π g v = c • v) (w : W) : σ g w = c • w := by
  rw [← Representation.Equiv.conj_apply_self g φ, LinearEquiv.conj_apply]
  simp [h]
  congr 1
  exact φ.right_inv w

theorem scalarBy_nu : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : IrrGL (k := k)) (s : ℂ) (t : kˣ) (c : ℂ), Zl.ScalarBy x t c →
      Zl.ScalarBy (x.nu s) t (c * ((absPow k s (t ^ x.1) : ℂˣ) : ℂ)) := by
  intro k _ _ _ _ x s t c hx v
  have hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin x.1) t) = t ^ x.1 := by
    ext
    simp [Matrix.GeneralLinearGroup.scalar]
  refine smul_of_equiv_nu (x.twEquiv (absPow k s) (isSmoothChar_absPow s))
    (Matrix.GeneralLinearGroup.scalar (Fin x.1) t) _ (fun u => ?_) v
  rw [GlobalTheory.SmGL.twist_apply, GlobalTheory.SmGL.detChar_apply, hx u, smul_smul, hdet, mul_comm]

end GlobalTheory.CompanionTheory.Dblock
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartStarInvT
section
open NumberField IsDedekindDomain Topology Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec GlobalTheory.SmGL GlobalTheory.ThetaPull
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.DualAct

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem map_invT {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (g : GL (Fin a) R) :
    GeneralLinearGroup.map p (invT a R g) = invT a S (GeneralLinearGroup.map p g) := by
  ext i j
  change p (((g⁻¹ : GL (Fin a) R).val) j i) = ((GeneralLinearGroup.map p g)⁻¹ : GL (Fin a) S).val j i
  rw [← map_inv]
  rfl

theorem invT_infGL (y : GL (Fin a) (Cinf E)) :
    invT a (Ad E) (infGL E a y) = infGL E a (invT a (Cinf E) y) :=
  ga_ext (by rw [map_invT, pInf_infGL, pInf_infGL])
    (by rw [map_invT, pFin_infGL, pFin_infGL, map_one])

theorem invT_finGL (k : GL (Fin a) (Af E)) :
    invT a (Ad E) (finGL E a k) = finGL E a (invT a (Af E) k) :=
  ga_ext (by rw [map_invT, pInf_finGL, pInf_finGL, map_one])
    (by rw [map_invT, pFin_finGL, pFin_finGL])

theorem invT_toUnits (k : Kinf E a) :
    invT a (Cinf E) (Unitary.toUnits k) = Unitary.toUnits (barK k) := by
  ext i j
  rfl


omit [_root_.NumberField.IsTotallyComplex E] in
variable (E a) in
def trL : Lie E a →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => toL (Matrix.of X)ᵀ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

omit [_root_.NumberField.IsTotallyComplex E] in
theorem trL_apply (X : Lie E a) : trL E a X = toL (Matrix.of X)ᵀ := rfl


omit [_root_.NumberField.IsTotallyComplex E] in
theorem toL_invT (y : GL (Fin a) (Cinf E)) :
    toL (invT a (Cinf E) y).val = trL E a (GlobalTheory.ThetaPull.invL (toL y.val)) := by
  rw [trL_apply, GlobalTheory.ThetaPull.invL]
  change toL ((y⁻¹ : GL (Fin a) (Cinf E)).val)ᵀ = toL (Matrix.of (Matrix.of.symm (Matrix.of.symm y.val |> Matrix.of)⁻¹))ᵀ
  change toL ((y⁻¹ : GL (Fin a) (Cinf E)).val)ᵀ = toL (y.val⁻¹)ᵀ
  rw [Matrix.coe_units_inv]

theorem chart_star_invT (φ : GA E a → ℂ) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    chart (fun g => star (φ (invT a (Ad E) g))) g x =
      star (chart φ (invT a (Ad E) g) (trL E a (GlobalTheory.ThetaPull.invL x))) := by
  obtain ⟨u, hu⟩ := id hx
  obtain rfl : x = toL u.val := hu.symm
  rw [← toL_invT, chart_val, chart_val, map_mul, invT_infGL]

theorem lieD_star_invT (X : Lie E a) {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) (g : GA E a) :
    lieD X (fun g => star (φ (invT a (Ad E) g))) g =
      star (lieD (toL (-(Matrix.of X)ᵀ)) φ (invT a (Ad E) g)) := by
  have e : chart (fun g => star (φ (invT a (Ad E) g))) g =ᶠ[𝓝 (oneL E a)]
      (Complex.conjCLE : ℂ →L[ℝ] ℂ) ∘ chart φ (invT a (Ad E) g) ∘ trL E a ∘ GlobalTheory.ThetaPull.invL :=
    Filter.eventually_of_mem (isOpen_invSet.mem_nhds isUnit_one) fun x hx => chart_star_invT φ g hx
  have h1 : (trL E a ∘ GlobalTheory.ThetaPull.invL) (oneL E a) = oneL E a :=
    (toL_invT 1).symm.trans (by rw [map_one]; rfl)
  have h2 := HasFDerivAt.comp (oneL E a) (f := trL E a ∘ GlobalTheory.ThetaPull.invL)
    (by rw [h1]; exact (differentiableAt_chart hφ (invT a (Ad E) g)).hasFDerivAt)
    ((trL E a).hasFDerivAt.comp (oneL E a) GlobalTheory.ThetaPull.invL_smooth.2)
  have h3 := (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp (oneL E a) h2
  unfold lieD
  rw [e.fderiv_eq, h3.fderiv]
  have e2 : toL (-(Matrix.of X)ᵀ) = -(toL (Matrix.of X)ᵀ : Lie E a) := rfl
  simp [trL_apply]

theorem act_star_invT (o : Op E a) (φ ψ χ : Sm E a)
    (hψ : ∀ g, ψ.1 g = star (φ.1 (invT a (Ad E) g)))
    (hχ : ∀ g, χ.1 g = star ((act (invTOp o) φ).1 (invT a (Ad E) g))) :
    act o ψ = χ := by
  refine Subtype.ext <| funext fun g => ?_
  rw [hχ]
  cases o with
  | fin k =>
    change ψ.1 (g * finGL E a k) = star (φ.1 (invT a (Ad E) g * finGL E a (invT a (Af E) k)))
    rw [hψ, map_mul, invT_finGL]
  | cpt k =>
    change ψ.1 (g * infGL E a (Unitary.toUnits k)) =
      star (φ.1 (invT a (Ad E) g * infGL E a (Unitary.toUnits (barK k))))
    rw [hψ, map_mul, invT_infGL, invT_toUnits]
  | lie X =>
    have e : ψ.1 = fun g => star (φ.1 (invT a (Ad E) g)) := funext hψ
    change lieD X ψ.1 g = star (lieD (toL (-(Matrix.of X)ᵀ)) φ.1 (invT a (Ad E) g))
    rw [e, lieD_star_invT X φ.2 g]

end GlobalTheory.CompanionTheory.DualAct
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoherentExtensionSurjectionOpenStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coherent_extension_surjection_open : ∀ {X : Scheme.{0}} [IsNoetherian X] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ (O : X.Opens) (E : (O : Scheme.{0}).Modules), IsCoherent E → ∃ P : X.Modules, IsCoherent P ∧ ∃ f : P.restrict O.ι ⟶ E, Epi f := by
  first | exact @GlobalTheory.CompanionTheory.GE.Present.exists_coherent_epi_restrict | exact GlobalTheory.CompanionTheory.GE.Present.exists_coherent_epi_restrict | (intros; apply GlobalTheory.CompanionTheory.GE.Present.exists_coherent_epi_restrict <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactOpenExhaustionStabilizes
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BaireCoset

open scoped Pointwise

theorem baire_double_coset : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] (P : Subgroup G), IsClosed (P : Set G) → ∀ Kc : Set G, IsCompact Kc → (∀ g, ∃ p ∈ P, ∃ c ∈ Kc, g = p * c) → ∀ L : ℕ → Subgroup G, Monotone L → (∀ j, IsCompact (L j : Set G)) → ∀ (x : G) (S : Set G), IsOpen S → (∀ p ∈ P, ∀ g ∈ S, p * g ∈ S) → IsClosed (S ∩ {g | ∃ p ∈ P, ∃ j, ∃ n ∈ L j, g = p * x * n}) → ∃ j, ∀ g ∈ S, (∃ p ∈ P, ∃ j', ∃ n ∈ L j', g = p * x * n) → ∃ p ∈ P, ∃ n ∈ L j, g = p * x * n := by
  intro G _ _ _ _ _ P hP Kc hKc hcov L hL hLc x S hS hSP hT
  set C : Set G := {g | ∃ p ∈ P, ∃ j, ∃ n ∈ L j, g = p * x * n} with hC
  let A : ℕ → Set G := fun j => {g | ∃ p ∈ P, ∃ n ∈ L j, g = p * x * n}
  have hAmono : ∀ {i j}, i ≤ j → A i ⊆ A j := by
    rintro i j hij g ⟨p, hp, n, hn, rfl⟩
    exact ⟨p, hp, n, hL hij hn, rfl⟩
  have hCA : ∀ g ∈ C, ∃ j, g ∈ A j := by
    rintro g ⟨p, hp, j, n, hn, rfl⟩
    exact ⟨j, p, hp, n, hn, rfl⟩
  have hAclosed : ∀ j, IsClosed (A j) := by
    intro j
    have hc : IsCompact ((fun n : G => x * n) '' (L j : Set G)) :=
      (hLc j).image (continuous_const.mul continuous_id)
    have hEq : A j = (P : Set G) * ((fun n : G => x * n) '' (L j : Set G)) := by
      ext g
      constructor
      · rintro ⟨p, hp, n, hn, rfl⟩
        exact Set.mem_mul.2 ⟨p, hp, x * n, ⟨n, hn, rfl⟩, (mul_assoc _ _ _).symm⟩
      · intro h
        obtain ⟨p, hp, _, ⟨n, hn, rfl⟩, rfl⟩ := Set.mem_mul.1 h
        exact ⟨p, hp, n, hn, (mul_assoc _ _ _).symm⟩
    rw [hEq]
    exact hP.mul_right_of_isCompact hc
  have hCP : ∀ p ∈ P, ∀ g ∈ C, p * g ∈ C := by
    rintro p hp g ⟨q, hq, j, n, hn, rfl⟩
    exact ⟨p * q, P.mul_mem hp hq, j, n, hn, by simp only [mul_assoc]⟩
  have hCL : ∀ j, ∀ m ∈ L j, ∀ g ∈ C, g * m ∈ C := by
    rintro j m hm g ⟨q, hq, i, n, hn, rfl⟩
    exact ⟨q, hq, max i j, n * m,
      (L (max i j)).mul_mem (hL (le_max_left i j) hn) (hL (le_max_right i j) hm),
      by simp only [mul_assoc]⟩
  by_cases hne : (S ∩ C).Nonempty
  · haveI : Nonempty ↥(S ∩ C) := hne.to_subtype
    haveI : LocallyCompactSpace ↥(S ∩ C) := hT.isClosedEmbedding_subtypeVal.locallyCompactSpace
    obtain ⟨j0, y, hy⟩ := nonempty_interior_of_iUnion_of_closed
      (f := fun j => ((↑) : ↥(S ∩ C) → G) ⁻¹' A j)
      (fun j => (hAclosed j).preimage continuous_subtype_val)
      (by
        refine Set.eq_univ_of_forall fun t => ?_
        obtain ⟨j, hj⟩ := hCA t t.2.2
        exact Set.mem_iUnion.2 ⟨j, hj⟩)
    obtain ⟨V, hV, hVeq⟩ := isOpen_induced_iff.1
      (isOpen_interior (s := ((↑) : ↥(S ∩ C) → G) ⁻¹' A j0))
    have hyV : (y : G) ∈ V := by
      have h : y ∈ ((↑) : ↥(S ∩ C) → G) ⁻¹' V := by rw [hVeq]; exact hy
      exact h
    have hVA : ∀ g ∈ V, g ∈ S → g ∈ C → g ∈ A j0 := by
      intro g hgV hgS hgC
      have h : (⟨g, hgS, hgC⟩ : ↥(S ∩ C)) ∈ ((↑) : ↥(S ∩ C) → G) ⁻¹' V := hgV
      rw [hVeq] at h
      have h2 : (⟨g, hgS, hgC⟩ : ↥(S ∩ C)) ∈ ((↑) : ↥(S ∩ C) → G) ⁻¹' A j0 := interior_subset h
      exact h2
    obtain ⟨p, hp, n, hn, hyeq⟩ := hVA y hyV y.2.1 y.2.2
    let V₁ : Set G := (fun g => p * g * n) ⁻¹' (V ∩ S)
    have hV₁o : IsOpen V₁ :=
      (hV.inter hS).preimage ((continuous_const.mul continuous_id).mul continuous_const)
    have hxV₁ : x ∈ V₁ := by
      show p * x * n ∈ V ∩ S
      rw [← hyeq]
      exact ⟨hyV, y.2.1⟩
    have hnL : ∀ g ∈ V₁, g ∈ C → g ∈ A j0 := by
      intro g hgV hgC
      obtain ⟨p₂, hp₂, n₂, hn₂, e⟩ := hVA (p * g * n) hgV.1 hgV.2 (hCL j0 n hn _ (hCP p hp g hgC))
      refine ⟨p⁻¹ * p₂, P.mul_mem (P.inv_mem hp) hp₂, n₂ * n⁻¹,
        (L j0).mul_mem hn₂ ((L j0).inv_mem hn), ?_⟩
      calc g = p⁻¹ * (p * g * n) * n⁻¹ := by group
        _ = p⁻¹ * (p₂ * x * n₂) * n⁻¹ := by rw [e]
        _ = p⁻¹ * p₂ * x * (n₂ * n⁻¹) := by group
    let O : ℕ → Set G := fun j => ⋃₀ {W | IsOpen W ∧ W ∩ C ⊆ A j}
    have hOo : ∀ j, IsOpen (O j) := fun j => isOpen_sUnion fun W hW => hW.1
    have hOm : Monotone O := fun i j hij =>
      Set.sUnion_subset_sUnion fun W hW => ⟨hW.1, hW.2.trans (hAmono hij)⟩
    have hOA : ∀ j, O j ∩ C ⊆ A j := by
      rintro j g ⟨⟨W, hW, hgW⟩, hgC⟩
      exact hW.2 ⟨hgW, hgC⟩
    have hAO : ∀ j, j0 ≤ j → A j ⊆ O j := by
      rintro j hj _ ⟨p', hp', m, hm, rfl⟩
      refine ⟨(fun g => p'⁻¹ * g * m⁻¹) ⁻¹' V₁,
        ⟨hV₁o.preimage ((continuous_const.mul continuous_id).mul continuous_const), ?_⟩, ?_⟩
      · rintro g ⟨hgW, hgC⟩
        have hu : p'⁻¹ * g * m⁻¹ ∈ C :=
          hCL j _ ((L j).inv_mem hm) _ (hCP _ (P.inv_mem hp') g hgC)
        have hu' : p'⁻¹ * g * m⁻¹ ∈ A j := hAmono hj (hnL _ hgW hu)
        obtain ⟨p₂, hp₂, n₂, hn₂, e⟩ := hu'
        refine ⟨p' * p₂, P.mul_mem hp' hp₂, n₂ * m, (L j).mul_mem hn₂ hm, ?_⟩
        calc g = p' * (p'⁻¹ * g * m⁻¹) * m := by group
          _ = p' * (p₂ * x * n₂) * m := by rw [e]
          _ = p' * p₂ * x * (n₂ * m) := by group
      · show p'⁻¹ * (p' * x * m) * m⁻¹ ∈ V₁
        have : p'⁻¹ * (p' * x * m) * m⁻¹ = x := by group
        rw [this]
        exact hxV₁
    obtain ⟨i, hi⟩ := (hKc.inter_right hT).elim_directed_cover O hOo
      (by
        rintro g ⟨_, hgS, hgC⟩
        obtain ⟨j, hj⟩ := hCA g hgC
        exact Set.mem_iUnion.2 ⟨max j j0,
          hAO _ (le_max_right j j0) (hAmono (le_max_left j j0) hj)⟩)
      hOm.directed_le
    refine ⟨i, fun g hgS hgC => ?_⟩
    obtain ⟨q, hq, c, hc, rfl⟩ := hcov g
    have hcS : c ∈ S := by
      have := hSP q⁻¹ (P.inv_mem hq) _ hgS
      rwa [inv_mul_cancel_left] at this
    have hcC : c ∈ C := by
      have := hCP q⁻¹ (P.inv_mem hq) _ hgC
      rwa [inv_mul_cancel_left] at this
    obtain ⟨p₂, hp₂, n₂, hn₂, e⟩ := hOA i ⟨hi ⟨hc, hcS, hcC⟩, hcC⟩
    exact ⟨q * p₂, P.mul_mem hq hp₂, n₂, hn₂, by rw [e]; simp only [mul_assoc]⟩
  · refine ⟨0, fun g hgS hgC => ?_⟩
    exact absurd ⟨g, hgS, hgC⟩ hne

end GlobalTheory.CompanionTheory.BaireCoset
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConcatApplyEquiv
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegCoarse

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def topCut (Δ : Segment k) {s : ℕ} (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) : Fin s → Segment k := fun a =>
  Segment.ofFirst (Δ.first.nu ((∑ b ∈ Finset.univ.filter (fun b => a < b), c b : ℕ) : ℂ)) (Δ.isCusp_first.nu _)
    (c a) (hc a)

theorem isTopCut_topCut (Δ : Segment k) {s : ℕ} (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) (h : ∑ a, c a = Δ.len) :
    IsTopCut Δ (topCut Δ c hc) :=
  ⟨h, fun _ => rfl⟩

theorem eq_topCut {Δ : Segment k} {s : ℕ} {Γ : Fin s → Segment k} (h : IsTopCut Δ Γ) :
    Γ = topCut Δ (fun a => (Γ a).len) (fun a => (Γ a).len_pos) :=
  funext fun a => Segment.ext_first (by rw [h.2 a]; rfl) rfl

theorem sum_split {s : ℕ} (c : Fin s → ℕ) (a : Fin s) :
    ∑ b, c b = (∑ t : Fin a, c (Fin.castLE a.2.le t)) + c a + ∑ b ∈ Finset.univ.filter (fun b => a < b), c b := by
  have h1 : ∑ t : Fin a, c (Fin.castLE a.2.le t) = ∑ b ∈ Finset.univ.filter (fun b : Fin s => b < a), c b := by
    refine Finset.sum_bij (fun t _ => Fin.castLE a.2.le t)
      (fun t _ => Finset.mem_filter.2 ⟨Finset.mem_univ _, Fin.lt_def.2 t.2⟩)
      (fun t _ u _ h => Fin.castLE_injective _ h) (fun b hb => ?_) (fun _ _ => rfl)
    have hb' : (b : ℕ) < a := Fin.lt_def.1 (Finset.mem_filter.1 hb).2
    exact ⟨⟨b, hb'⟩, Finset.mem_univ _, rfl⟩
  rw [h1]
  have h2 : ∑ b, c b = ∑ b, ((if b < a then c b else 0) + (if b = a then c b else 0) + (if a < b then c b else 0)) := by
    refine Finset.sum_congr rfl fun b _ => ?_
    rcases lt_trichotomy b a with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.2 h.le]
  rw [h2, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter,
    ← Finset.sum_filter, Finset.filter_eq', if_pos (Finset.mem_univ _), Finset.sum_singleton]

theorem concat_dec_topCut (Δ : Segment k) {s : ℕ} (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) (h : ∑ a, c a = Δ.len)
    (i : Fin (∑ a, c a)) : concat c (fun a => dec (topCut Δ c hc a)) i = dec Δ (Fin.cast h i) := by
  show dec (topCut Δ c hc (finSigmaFinEquiv.symm i).1) (finSigmaFinEquiv.symm i).2 = dec Δ (Fin.cast h i)
  rcases hq : finSigmaFinEquiv.symm i with ⟨a, j⟩
  have hi : (i : ℕ) = (∑ t : Fin a, c (Fin.castLE a.2.le t)) + j := by
    rw [← Equiv.apply_symm_apply finSigmaFinEquiv i, hq, finSigmaFinEquiv_apply]
  have hs := sum_split c a
  have hj : (j : ℕ) < c a := j.2
  simp only [dec, Segment.term, topCut, Segment.first_ofFirst, IrrGL.nu_nu]
  congr 1
  simp only [Fin.val_rev, Fin.val_cast, Segment.len_ofFirst]
  have key : Δ.len - (i + 1) = (∑ b ∈ Finset.univ.filter (fun b => a < b), c b) + (c a - (j + 1)) := by
    rw [← h]; omega
  rw [key]
  push_cast
  congr 1

theorem concat_injective {s : ℕ} {c : Fin s → ℕ} {x x' : ∀ a, Fin (c a) → IrrGL (k := k)} (h : concat c x = concat c x') :
    x = x' := by
  funext a j
  have := congrFun h (finSigmaFinEquiv ⟨a, j⟩)
  change (fun p : (b : Fin s) × Fin (c b) => x p.1 p.2) (finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨a, j⟩)) =
    (fun p : (b : Fin s) × Fin (c b) => x' p.1 p.2) (finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨a, j⟩)) at this
  rw [Equiv.symm_apply_apply] at this
  exact this

theorem concat_apply_equiv {s : ℕ} (c : Fin s → ℕ) (x : ∀ a, Fin (c a) → IrrGL (k := k)) (p : (a : Fin s) × Fin (c a)) :
    concat c x (finSigmaFinEquiv p) = x p.1 p.2 := by
  change (fun q : (b : Fin s) × Fin (c b) => x q.1 q.2) (finSigmaFinEquiv.symm (finSigmaFinEquiv p)) = _
  rw [Equiv.symm_apply_apply]

theorem sum_concat {s : ℕ} (c : Fin s → ℕ) (x : ∀ a, Fin (c a) → IrrGL (k := k)) :
    ∑ i, (concat c x i).1 = ∑ a, ∑ j, (x a j).1 := by
  rw [← Equiv.sum_comp finSigmaFinEquiv, Fintype.sum_sigma]
  simp only [concat_apply_equiv]

theorem sum_dec (Δ : Segment k) : ∑ a, (dec Δ a).1 = Δ.deg := by
  rw [← Segment.sum_term_fst]
  exact Equiv.sum_comp Fin.revPerm (fun a => (Δ.term a).1)

theorem deg_topCut (Δ : Segment k) {s : ℕ} (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) (a : Fin s) :
    (topCut Δ c hc a).deg = c a * Δ.d := rfl

theorem jm_reindex {n m N : ℕ} (h : n = m) (x : Fin n → IrrGL (k := k)) (x' : Fin m → IrrGL (k := k))
    (hx : ∀ i, x i = x' (Fin.cast h i)) (hd : ∑ a, (x a).1 = N) (hd' : ∑ a, (x' a).1 = N) {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) : jm x hd π = jm x' hd' π := by
  subst h
  obtain rfl : x = x' := funext fun i => by simpa using hx i
  rfl

theorem eq_of_isLSeg {Γ : Segment k} {x x' : IrrGL (k := k)} (h : IsLSeg Γ x.rep) (h' : IsLSeg Γ x'.rep) : x = x' := by
  obtain ⟨n, c⟩ := x
  obtain ⟨n', c'⟩ := x'
  have e1 := h.deg_eq
  have e2 := h'.deg_eq
  obtain rfl : n = n' := e1.symm.trans e2
  obtain ⟨φ⟩ := h.unique h'
  have := (IrrGL.of_eq_of (π := IrrGL.rep (k := k) ⟨n, c'⟩) (σ := IrrGL.rep (k := k) ⟨n, c⟩)
    (hs := c'.rep.smooth) (hi := c'.rep.irr) (hs' := c.rep.smooth) (hi' := c.rep.irr)).2 ⟨φ⟩
  rw [IrrGL.of_rep, IrrGL.of_rep] at this
  exact this.symm

end GlobalTheory.CompanionTheory.SegCoarse

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeMeasureLocallyFinite
section
noncomputable section

open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise

open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ConeHaar.Fin

variable {n : ℕ}

theorem continuous_hOf : Continuous (hOf (n := n)) := by
  unfold hOf
  refine continuous_finsetSum _ fun p _ => ?_
  exact (Complex.continuous_ofReal.comp (continuous_apply p)).smul continuous_const

theorem continuous_detRe : Continuous fun v : Fin n × Fin n → ℝ => (hOf v).det.re :=
  Complex.continuous_re.comp (continuous_hOf.matrix_det)

theorem detRe_pos {v : Fin n × Fin n → ℝ} (hv : v ∈ cone n) : 0 < (hOf v).det.re := by
  have h : 0 < (hOf v).det := Matrix.PosDef.det_pos hv
  exact (Complex.pos_iff.1 h).1

theorem measurable_coneW : Measurable (coneW n) := by
  unfold coneW
  exact ENNReal.measurable_ofReal.comp ((continuous_detRe.measurable.pow_const n).inv)

theorem exists_hOf_eq_one : ∃ v : Fin n × Fin n → ℝ, hOf v = 1 := by
  refine ⟨fun p => ((1 * hb p : Mat n).trace).re, ?_⟩
  have hre : ∀ p : Fin n × Fin n, ((((1 * hb p : Mat n).trace).re : ℝ) : ℂ) = (1 * hb p : Mat n).trace := by
    intro p
    apply Complex.conj_eq_iff_re.1
    have h1 : star (hb p : Mat n).trace = (hb p : Mat n).trace := by
      rw [← Matrix.trace_conjTranspose, GlobalTheory.CompanionTheory.TwistHomotopy.hb_conjTranspose]
    simpa using h1
  have h := (GlobalTheory.CompanionTheory.TopClass.hbB n).sum_repr (1 : Mat n)
  simp only [GlobalTheory.CompanionTheory.TopClass.hbB_repr, GlobalTheory.CompanionTheory.TopClass.hbB_apply] at h
  conv_rhs => rw [← h]
  simp only [hOf, hre]

theorem cone_nonempty : (cone n).Nonempty := by
  obtain ⟨v, hv⟩ := exists_hOf_eq_one (n := n)
  refine ⟨v, ?_⟩
  show (hOf v).PosDef
  rw [hv]
  exact Matrix.PosDef.one

theorem coneW_pos {v : Fin n × Fin n → ℝ} (hv : v ∈ cone n) : coneW n v ≠ 0 := by
  unfold coneW
  have : 0 < ((hOf v).det.re ^ n)⁻¹ := inv_pos.2 (pow_pos (detRe_pos hv) n)
  exact (ENNReal.ofReal_pos.2 this).ne'

theorem coneMeas_ne_zero : coneMeas n ≠ 0 := by
  intro h0
  have hz := (withDensity_eq_zero measurable_coneW.aemeasurable h0)
  have hopen : IsOpen (cone n) := _root_.GlobalTheory.CompanionTheory.ConeHaar.isOpen_cone n
  have hvol : 0 < volume (cone n) := hopen.measure_pos volume cone_nonempty
  rw [Filter.EventuallyEq, ae_restrict_iff' hopen.measurableSet] at hz
  have hnull : volume (cone n) = 0 := by
    refine measure_mono_null (t := {v | ¬ (v ∈ cone n → coneW n v = (0 : (Fin n × Fin n → ℝ) → ℝ≥0∞) v)}) ?_ hz
    intro v hv
    simpa using ⟨hv, coneW_pos hv⟩
  exact hvol.ne' hnull

theorem coneMeas_lt_top (C : Set (Fin n × Fin n → ℝ)) (hC : IsCompact C) (hCc : C ⊆ cone n) :
    coneMeas n C < ⊤ := by
  have hcont : ContinuousOn (fun v : Fin n × Fin n → ℝ => ((hOf v).det.re ^ n)⁻¹) C :=
    ContinuousOn.inv₀ (continuous_detRe.pow n).continuousOn
      fun v hv => (pow_pos (detRe_pos (hCc hv)) n).ne'
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hcont
  have hle : ∀ v ∈ C, coneW n v ≤ ENNReal.ofReal M := fun v hv =>
    ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hM v hv))
  unfold coneMeas
  rw [withDensity_apply _ hC.measurableSet]
  calc ∫⁻ v in C, coneW n v ∂(volume.restrict (cone n))
      ≤ ∫⁻ _ in C, ENNReal.ofReal M ∂(volume.restrict (cone n)) :=
        setLIntegral_mono' hC.measurableSet hle
    _ = ENNReal.ofReal M * (volume.restrict (cone n)) C := by simp
    _ ≤ ENNReal.ofReal M * volume C := by
        gcongr
        exact Measure.restrict_le_self
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC.measure_lt_top

theorem coneMeas_ne_zero_and_lt_top : ∀ n : ℕ, coneMeas n ≠ 0 ∧ ∀ C : Set (Fin n × Fin n → ℝ), IsCompact C →
    C ⊆ PositivityTheory.RgBcC.cone n → coneMeas n C < ⊤ :=
  fun _ => ⟨coneMeas_ne_zero, coneMeas_lt_top⟩

end GlobalTheory.CompanionTheory.ConeHaar.Fin
end
end

