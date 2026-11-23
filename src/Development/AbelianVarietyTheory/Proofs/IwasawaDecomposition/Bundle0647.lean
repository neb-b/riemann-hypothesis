module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0566
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0591
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0611
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0630
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0631
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0597
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0637
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0751
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0735
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0638
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0867
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0844
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0848
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0840
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0860
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtremalVectorMemLowestKType
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0616
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0606
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0629
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0628

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteRationalPolyhedralCellsUptoAut
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolCell

theorem exists_cells : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g q : ℕ) (φs : InvFun ℤ) (𝓜 : Finset ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], IsPolFan (id : ℤ → ℤ) g φs → Module.finrank ℚ E * q ≤ g → Module.finrank (𝓞 E) X ≤ q → HasRedCover H.bar X → ∃ S : Set (LinearMap.BilinForm ℤ X), S.Finite ∧ ∀ B ∈ psdCone (bar := H.bar) (X := X), ∃ (e : X ≃ₗ[𝓞 E] X) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ), IsCell H.bar (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) γ ∧ (∀ i, γ i ∈ S) ∧ (∀ i, 0 ≤ c i) ∧ pullR e.toLinearMap B = ∑ i, c i • toReal (γ i) := by
  intro E _ _ _ H g q φs 𝓜 X _ _ _ _ hφ hg hq hcov
  have LG : ∀ (E : Type) [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.Finite ℤ X ∧ Module.Projective ℤ X ∧ Module.finrank ℤ X = Module.finrank ℚ E * Module.finrank (𝓞 E) X := _root_.GlobalTheory.finite_projective_int_of_ringOfIntegers
  have LN : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (φ : InvFun ℤ), IsPolFanOn (id : ℤ → ℤ) φ X → ∃ N : ℕ, 0 < N ∧ ∀ B ∈ psdCone (bar := (id : ℤ → ℤ)) (X := X), ∃ (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (w : (X × X) →₀ ℤ), IsCone (id : ℤ → ℤ) φ u ∧ StrictWith (id : ℤ → ℤ) φ N (linW w) u ∧ B ∈ rcone u := GlobalTheory.T.exists_common_denominator_strictness_smooth_fan
  have LCov : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (φ : InvFun ℤ) (N p : ℕ) (P : Fin p → LinearMap.BilinForm ℤ X), IsPolFanOn (id : ℤ → ℤ) φ X → (∀ B ∈ psdCone (bar := (id : ℤ → ℤ)) (X := X), ∃ (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (w : (X × X) →₀ ℤ), IsCone (id : ℤ → ℤ) φ u ∧ StrictWith (id : ℤ → ℤ) φ N (linW w) u ∧ B ∈ rcone u) → (∀ i y z, P i y z = P i z y) → (∀ i y, 0 ≤ P i y y) → ∃ (s : ℕ) (m : Fin s → ℕ) (u : ∀ k, Fin (m k) → LinearMap.BilinForm ℤ X) (w : Fin s → (X × X) →₀ ℤ), (∀ k, IsCone (id : ℤ → ℤ) φ (u k) ∧ StrictWith (id : ℤ → ℤ) φ N (linW (w k)) (u k)) ∧ ∀ B ∈ rcone P, B ∈ psdCone (bar := (id : ℤ → ℤ)) (X := X) → ∃ k, B ∈ rcone (u k) := GlobalTheory.T.exists_finite_polFanCones_cover_realCone
  have LDick : ∀ {ι : Type} (n : ℕ) (f : ι → Fin n → ℕ), ∃ F : Finset ι, ∀ i, ∃ j ∈ F, f j ≤ f i := _root_.GlobalTheory.dickson_finite_below_every
  have LPsi : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : ℕ) (φs : InvFun ℤ) (𝓜 : Finset ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Finite ℤ X] (N m n : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (w : (X × X) →₀ ℤ) (r : (Fin n → ℤ) →ₗ[ℤ] X) (a : ∀ M : ℕ, (Fin n → ZMod (M + 1)) → Fin n → ℤ), 0 < D → IsPolFanOn (id : ℤ → ℤ) φs X → 0 < N → IsCone (id : ℤ → ℤ) φs u → StrictWith (id : ℤ → ℤ) φs N (linW w) u → Function.Surjective r → (∀ M y, redV M (a M y) = y) → ∃ A : Set (Fin m → ℤ), A.Finite ∧ (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → (kDen N n 𝓜 : ℝ) * (baseFun (𝓞 E) D φs 𝓜).evalZ β ≤ evalW (lamW D N n 𝓜 r w a) (toReal β)) ∧ (∀ B ∈ psdCone (bar := H.bar) (X := X), (kDen N n 𝓜 : ℝ) * evalR (baseFun (𝓞 E) D φs 𝓜) B = evalW (lamW D N n 𝓜 r w a) B → ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i) ∧ (∀ v ∈ A, ∑ i, (v i : ℝ) * t i ≤ 0) ∧ B = ∑ i, t i • toReal (u i)) ∧ (∀ t : Fin m → ℝ, (∀ i, 0 ≤ t i) → (∀ v ∈ A, ∑ i, (v i : ℝ) * t i ≤ 0) → (kDen N n 𝓜 : ℝ) * evalR (baseFun (𝓞 E) D φs 𝓜) (∑ i, t i • toReal (u i)) = evalW (lamW D N n 𝓜 r w a) (∑ i, t i • toReal (u i))) ∧ ∀ B ∈ rcone u, (∀ M ∈ 𝓜, ∀ y, classMin M (fun x z => B (r x) (r z)) y = B (r (a M y)) (r (a M y))) → (kDen N n 𝓜 : ℝ) * evalR (baseFun (𝓞 E) D φs 𝓜) B = evalW (lamW D N n 𝓜 r w a) B := GlobalTheory.T.exists_intForm_dominating_polFanBase_classMinMeans
  have LACL : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (ψ : InvFun O) (K : ℕ) (Λ : (X × X) →₀ ℤ) (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (A : Set (Fin m → ℤ)), A.Finite → 0 < K → (∀ i y z, u i y z = u i z y) → (∀ i y, 0 ≤ u i y y) → (∀ (β : LinearMap.BilinForm ℤ X) (t : Fin m → ℝ), toReal β = ∑ i, t i • toReal (u i) → ∀ i, ∃ z : ℤ, t i = z) → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → (K : ℝ) * ψ.evalZ β ≤ evalW Λ (toReal β)) → (∀ B ∈ psdCone (bar := bar) (X := X), (K : ℝ) * evalR ψ B = evalW Λ B → ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i) ∧ (∀ v ∈ A, ∑ i, (v i : ℝ) * t i ≤ 0) ∧ B = ∑ i, t i • toReal (u i)) → (∀ t : Fin m → ℝ, (∀ i, 0 ≤ t i) → (∀ v ∈ A, ∑ i, (v i : ℝ) * t i ≤ 0) → ∑ i, t i • toReal (u i) ∈ realForms bar X → (K : ℝ) * evalR ψ (∑ i, t i • toReal (u i)) = evalW Λ (∑ i, t i • toReal (u i))) → ∃ (s : ℕ) (γ : Fin s → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ ∀ B ∈ psdCone (bar := bar) (X := X), (K : ℝ) * evalR ψ B = evalW Λ B → B ∈ rcone γ := GlobalTheory.T.exists_cell_of_contactSet_intInequalities
  have LInt : ∀ (X : Type) [AddCommGroup X] (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (hu : ∀ i, u i ∈ balForms (id : ℤ → ℤ) X), IsPartOfBasis (fun i => (⟨u i, hu i⟩ : balForms (id : ℤ → ℤ) X)) → ∀ (β : LinearMap.BilinForm ℤ X) (t : Fin m → ℝ), toReal β = ∑ i, t i • toReal (u i) → ∀ i, ∃ z : ℤ, t i = z := _root_.GlobalTheory.cone_coords_int_of_isPartOfBasis
  have LPsd : ∀ (O : Type) [CommRing O] [Module.Finite ℤ O] [Module.Free ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X], psdCone (bar := bar) (X := X) ⊆ psdCone (bar := (id : ℤ → ℤ)) (X := X) := GlobalTheory.T.balancedPsdRationalRadicalCone_subset_intCone

  obtain ⟨hfin, hproj, hrk⟩ := LG E X
  haveI := hfin
  haveI := hproj
  have hφX : IsPolFanOn (id : ℤ → ℤ) φs X := hφ X (by rw [hrk]; exact (Nat.mul_le_mul_left _ hq).trans hg)
  obtain ⟨N, hN, hD⟩ := LN X φs hφX
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' ℤ X
  obtain ⟨k, nP, P, hPs, hPp, hPc⟩ := hcov
  choose s mm u w huw hcj using fun j => LCov X φs N (nP j) (P j) hφX hD (hPs j) (hPp j)
  have hcls : ∀ (j : Fin k) (M : ℕ) (y : Fin n → ZMod (M + 1)), ∃ F : Finset (Fin n → ℤ), (∀ a ∈ F, redV M a = y) ∧
      ∀ B ∈ rcone (P j), ∃ a ∈ F, classMin M (fun x z => B (r x) (r z)) y = B (r a) (r a) := by
    intro j M y
    obtain ⟨F, hF⟩ := LDick (ι := {a : Fin n → ℤ // redV M a = y}) (nP j) fun a i => (P j i (r a.1) (r a.1)).toNat
    refine ⟨F.map (Function.Embedding.subtype _), fun a ha => ?_, ?_⟩
    · obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 ha
      exact a.2
    · rintro B ⟨t, ht, rfl⟩
      have hval : ∀ a : Fin n → ℤ, (∑ i, t i • toReal (P j i)) (r a) (r a) = ∑ i, t i * (P j i (r a) (r a) : ℝ) := fun a => by
        simp [LinearMap.sum_apply]
      obtain ⟨a0, ha0, -⟩ := hF ⟨_, (redV_surjective M n y).choose_spec⟩
      obtain ⟨a1, ha1, hmin⟩ := Finset.exists_min_image (F.map (Function.Embedding.subtype _))
        (fun a => (∑ i, t i • toReal (P j i)) (r a) (r a)) ⟨_, Finset.mem_map_of_mem _ ha0⟩
      refine ⟨a1, ha1, IsLeast.csInf_eq ⟨⟨a1, ?_, rfl⟩, ?_⟩⟩
      · obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 ha1
        exact a.2
      · rintro x ⟨a, ha, rfl⟩
        obtain ⟨a', ha', hle⟩ := hF ⟨a, ha⟩
        refine (hmin _ (Finset.mem_map_of_mem _ ha')).trans ?_
        simp only [Function.Embedding.subtype_apply, hval]
        refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (ht i)
        have h1 := hle i
        have h2 := hPp j i (r a'.1)
        have h3 := hPp j i (r a)
        simp only at h1
        exact_mod_cast (by omega : P j i (r a'.1) (r a'.1) ≤ P j i (r a) (r a))
  choose F hFred hFmin using hcls
  let toA : ∀ j, (∀ M : 𝓜, ∀ y : Fin n → ZMod (M.1 + 1), ↥(F j M.1 y)) → ∀ M : ℕ, (Fin n → ZMod (M + 1)) → Fin n → ℤ :=
    fun j c M y => if h : M ∈ 𝓜 then (c ⟨M, h⟩ y).1 else (redV_surjective M n y).choose
  have toA_red : ∀ j c M y, redV M (toA j c M y) = y := fun j c M y => by
    simp only [toA]
    split_ifs with h
    · exact hFred j M y _ (c ⟨M, h⟩ y).2
    · exact (redV_surjective M n y).choose_spec
  have hK : 0 < kDen N n 𝓜 := Nat.mul_pos hN (Finset.prod_pos fun _ _ => by positivity)
  have cell : ∀ (mu : ℕ) (uu : Fin mu → LinearMap.BilinForm ℤ X) (ww : (X × X) →₀ ℤ)
      (a : ∀ M : ℕ, (Fin n → ZMod (M + 1)) → Fin n → ℤ), IsCone (id : ℤ → ℤ) φs uu →
      StrictWith (id : ℤ → ℤ) φs N (linW ww) uu → (∀ M y, redV M (a M y) = y) →
      ∃ (sγ : ℕ) (γ : Fin sγ → LinearMap.BilinForm ℤ X), IsCell H.bar (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) γ ∧
        ∀ B ∈ psdCone (bar := H.bar) (X := X), B ∈ rcone uu →
          (∀ M ∈ 𝓜, ∀ y, classMin M (fun x z => B (r x) (r z)) y = B (r (a M y)) (r (a M y))) → B ∈ rcone γ := by
    intro mu uu ww a hc hs ha
    obtain ⟨A, hA, hle, hcon, hback, hgen⟩ :=
      LPsi E H (fineDen g 𝓜) φs 𝓜 X N mu n uu ww r a (fineDen_pos g 𝓜) hφX hN hc hs hr ha
    obtain ⟨sγ, γ, hγ, hγc⟩ := LACL (𝓞 E) H.bar X (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) (kDen N n 𝓜)
      (lamW (fineDen g 𝓜) N n 𝓜 r ww a) mu uu A hA hK (fun i => (hc.mem i).1) hc.nonneg
      (LInt X mu uu hc.mem hc.basis) hle hcon (fun t ht hA' _ => hback t ht hA')
    exact ⟨sγ, γ, hγ, fun B hB hBu hBc => hγc B hB (hgen B hBu hBc)⟩
  choose sγ γ hγ hγc using fun (j : Fin k) (d : Fin (s j) × (∀ M : 𝓜, ∀ y : Fin n → ZMod (M.1 + 1), ↥(F j M.1 y))) =>
    cell (mm j d.1) (u j d.1) (w j d.1) (toA j d.2) (huw j d.1).1 (huw j d.1).2 (toA_red j d.2)
  refine ⟨⋃ j, ⋃ d, Set.range (γ j d), Set.finite_iUnion fun j => Set.finite_iUnion fun d => Set.finite_range _,
    fun B hB => ?_⟩
  obtain ⟨e, j, c, hc0, hce⟩ := hPc B hB
  have hB' : pullR e.toLinearMap B ∈ psdCone (bar := H.bar) (X := X) := pullR_mem_psdCone e.surjective hB
  have hBP : pullR e.toLinearMap B ∈ rcone (P j) := ⟨c, hc0, hce⟩
  obtain ⟨kk, hkk⟩ := hcj j _ hBP (LPsd (𝓞 E) H.bar X hB')
  choose a0 ha0F ha0 using fun (M : 𝓜) y => hFmin j M.1 y _ hBP
  let d : Fin (s j) × (∀ M : 𝓜, ∀ y : Fin n → ZMod (M.1 + 1), ↥(F j M.1 y)) := (kk, fun M y => ⟨a0 M y, ha0F M y⟩)
  obtain ⟨c', hc', hBc⟩ := hγc j d _ hB' hkk fun M hM y => by
    simp only [toA, d, dif_pos hM]
    exact ha0 ⟨M, hM⟩ y
  exact ⟨e, _, γ j d, c', hγ j d, fun i => Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨d, i, rfl⟩⟩, hc', hBc⟩

end GlobalTheory.PolCell
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitReductionStandardFrameConj
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting GlobalTheory.CenFrame
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameRedSplit

theorem conj_red_core {R K k ι : Type} [CommRing R] [Field K] [CommRing k] {m : ℕ} (S : Subring R) (O : ValuationSubring K)
    (pr : R →+* K) (φ : O →+* k) (res : S →+* k) (hres : ∀ z : S, ∃ h : pr z ∈ O, res z = φ ⟨_, h⟩)
    (β : GL (Fin m) R) (B B' : Matrix (Fin m) (Fin m) R) (hBB : B * B' = 1)
    (U : Set ι) (Km : ι → Matrix (Fin m) (Fin m) R) (Z : ∀ κ ∈ U, GL (Fin m) S)
    (hZ : ∀ κ (hκ : κ ∈ U), β.1 * (Z κ hκ).1.map S.subtype * (β⁻¹).1 = B * Km κ * B')
    (hsurj : ∀ u : GL (Fin m) O, ∃ κ, ∃ hκ : κ ∈ U, (Km κ).map pr = u.1.map O.subtype) :
    ∃ b : GL (Fin m) k, ∀ κ (hκ : κ ∈ U) (y : GL (Fin m) O), (Km κ).map pr = y.1.map O.subtype →
      (Z κ hκ).1.map res = (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).1 := by
  classical
  obtain ⟨γ, hγ⟩ : ∃ γ : Matrix (Fin m) (Fin m) R, γ = (β⁻¹).1 * B := ⟨_, rfl⟩
  obtain ⟨γ', hγ'⟩ : ∃ γ' : Matrix (Fin m) (Fin m) R, γ' = B' * β.1 := ⟨_, rfl⟩
  have g1 : γ * γ' = 1 := by
    rw [hγ, hγ', Matrix.mul_assoc, ← Matrix.mul_assoc B, hBB, Matrix.one_mul, Units.inv_mul]
  have g2 : γ' * γ = 1 := mul_eq_one_comm.mp g1
  have hZ' : ∀ κ (hκ : κ ∈ U), (Z κ hκ).1.map S.subtype = γ * Km κ * γ' := by
    intro κ hκ
    have e : γ * Km κ * γ' = (β⁻¹).1 * (B * Km κ * B') * β.1 := by
      rw [hγ, hγ']; simp only [Matrix.mul_assoc]
    rw [e, ← hZ κ hκ]
    simp only [Matrix.mul_assoc]
    rw [Units.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  let c : GL (Fin m) K := ⟨γ.map pr, γ'.map pr, by rw [← Matrix.map_mul, g1, Matrix.map_one _ (map_zero _) (map_one _)],
    by rw [← Matrix.map_mul, g2, Matrix.map_one _ (map_zero _) (map_one _)]⟩
  have hc : ∀ κ (hκ : κ ∈ U), (c.1 * (Km κ).map pr * (c⁻¹).1) = ((Z κ hκ).1.map S.subtype).map pr := by
    intro κ hκ
    rw [hZ' κ hκ, Matrix.map_mul, Matrix.map_mul]
    rfl
  have hent : ∀ u : GL (Fin m) O, ∀ a b, (c * Matrix.GeneralLinearGroup.map O.subtype u * c⁻¹).1 a b ∈ O := by
    intro u a b
    obtain ⟨κ, hκ, hK⟩ := hsurj u
    have e : (c * Matrix.GeneralLinearGroup.map O.subtype u * c⁻¹).1 = c.1 * (Km κ).map pr * (c⁻¹).1 := by
      rw [hK]; rfl
    rw [e, hc κ hκ, Matrix.map_apply, Matrix.map_apply]
    exact (hres _).1
  have hnorm : ∀ u ∈ Formalism.UG.GLint (Fin m) O.toSubring, c * u * c⁻¹ ∈ Formalism.UG.GLint (Fin m) O.toSubring := by
    rintro _ ⟨u, rfl⟩
    refine GlobalTheory.HeckeStdFacts.mem_GLint_iff.2 ⟨fun a b => hent u a b, fun a b => ?_⟩
    have e : (c * Formalism.UG.bc O.toSubring.subtype u * c⁻¹)⁻¹ = c * Matrix.GeneralLinearGroup.map O.subtype u⁻¹ * c⁻¹ := by
      rw [map_inv]
      group
      rfl
    rw [e]
    exact hent u⁻¹ a b
  obtain ⟨h, ⟨h₀, rfl⟩, hconj⟩ := GlobalTheory.HeckeStdFacts.exists_int_of_normalizes O.valuation O.toSubring
    (fun x => (O.valuation_le_one_iff x).symm) c hnorm
  suffices H : ∀ h₁ : GL (Fin m) O, (∀ x, c * x * c⁻¹ = Matrix.GeneralLinearGroup.map O.subtype h₁ * x *
      (Matrix.GeneralLinearGroup.map O.subtype h₁)⁻¹) → ∃ b : GL (Fin m) k, ∀ κ (hκ : κ ∈ U) (y : GL (Fin m) O),
      (Km κ).map pr = y.1.map O.subtype → (Z κ hκ).1.map res = (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).1 from H h₀ hconj
  intro h₁ hconj'
  refine ⟨Matrix.GeneralLinearGroup.map φ h₁, fun κ hκ y hy => ?_⟩
  ext a b
  obtain ⟨hm, hr⟩ := hres ((Z κ hκ).1 a b)
  have e1 : pr ((Z κ hκ).1 a b : R) = (c * Matrix.GeneralLinearGroup.map O.subtype y * c⁻¹).1 a b := by
    have := congrFun (congrFun (hc κ hκ) a) b
    rw [hy] at this
    exact this.symm
  have e2 : (c * Matrix.GeneralLinearGroup.map O.subtype y * c⁻¹) =
      Matrix.GeneralLinearGroup.map O.subtype (h₁ * y * h₁⁻¹) := by
    rw [hconj']
    simp only [map_mul, map_inv]
  have e3 : (⟨_, hm⟩ : O) = (h₁ * y * h₁⁻¹).1 a b := by
    apply Subtype.ext
    show pr _ = _
    rw [e1, e2]
    rfl
  have e4 : Matrix.GeneralLinearGroup.map φ h₁ * Matrix.GeneralLinearGroup.map φ y * (Matrix.GeneralLinearGroup.map φ h₁)⁻¹ =
      Matrix.GeneralLinearGroup.map φ (h₁ * y * h₁⁻¹) := by
    simp only [map_mul, map_inv]
  rw [Matrix.map_apply, hr, e3, e4]
  rfl

theorem resS_eq_phiR (D : D7) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (y : Formalism.L2.Herm.intAf D.host.F D.host.E) :
    ∃ h : s.proj (y : EAf D) ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E),
      resS D.host.F s.w y = GlobalTheory.MtRed.phiR s ⟨_, h⟩ := by
  have hmem : s.proj (y : EAf D) ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (GlobalTheory.RowGood.proj_le_one s y.2)
  refine ⟨hmem, ?_⟩
  obtain ⟨a, ha, hφ⟩ := GlobalTheory.MtRed.exists_approx s ⟨_, hmem⟩
  rw [hφ]
  exact GlobalTheory.RowGood.res_eq (rfl : maximalRealSubfield D.host.E = _) s (y : EAf D) y (GlobalTheory.RowGood.tr_rfl _).symm a ha


set_option maxHeartbeats 1600000 in
theorem frameRed_exists : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), R3.StdFrame hF P → IsBaseFrame V β Λ 1 → ∀ s : ReciprocityTheory.Aut.SplitPlace D.host.E, ∃ (φ : Os s →+* kP s.w) (b : GL (Fin n) (kP s.w)), IsResidue s φ ∧ FrameRed hn P β s φ b := by
  intro D V n hn hF P β Λ hP hβ s
  subst hn
  obtain ⟨⟨β₀, β₀', h01, h10, hmat⟩, hK⟩ := hP
  have hSt : ∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E V.rank, finE V (P.ψ κ) ∈ St β := fun κ hκ =>
    (GlobalTheory.FinZeta.LevelOff.finE_mem_St_iff hβ (P.into κ)).2 ((hK κ).1 hκ)
  have hfin : ∀ κ : Formalism.AUTREP.GAf D.host.E V.rank, (finE V (P.ψ κ)).1 =
      β₀.map (GlobalTheory.LevSplit.swp D.host.F D.host.E) * (κ.1.1.map (GlobalTheory.RowGood.tr hF)) *
        β₀'.map (GlobalTheory.LevSplit.swp D.host.F D.host.E) := by
    intro κ
    have e := congrArg (fun M => Matrix.map M (GlobalTheory.LevSplit.swp D.host.F D.host.E)) (hmat κ)
    refine e.trans ?_
    simp only [Matrix.map_mul]
    rfl
  have hBB : β₀.map (GlobalTheory.LevSplit.swp D.host.F D.host.E) * β₀'.map (GlobalTheory.LevSplit.swp D.host.F D.host.E) = 1 := by
    rw [← Matrix.map_mul, h01, Matrix.map_one _ (map_zero _) (map_one _)]
  have hZ : ∀ (κ : Formalism.AUTREP.GAf D.host.E V.rank) (hκ : κ ∈ {κ | κ ∈ ReciprocityTheory.Aut.Umax D.host.E V.rank}),
      β.1 * (pullFr β ⟨_, hSt κ hκ⟩).1.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype * (β⁻¹).1 =
        β₀.map (GlobalTheory.LevSplit.swp D.host.F D.host.E) * (κ.1.1.map (GlobalTheory.RowGood.tr hF)) *
          β₀'.map (GlobalTheory.LevSplit.swp D.host.F D.host.E) := by
    intro κ hκ
    exact (congrArg (fun g : GL (Fin V.rank) (EAf D) => g.1) (frGL_pullFr β ⟨_, hSt κ hκ⟩)).trans (hfin κ)
  have hpr : ∀ κ : Formalism.AUTREP.GAf D.host.E V.rank, (κ.1.1.map (GlobalTheory.RowGood.tr hF)).map s.proj = (s.loc V.rank κ).1 := by
    intro κ
    ext i j
    simp only [Matrix.map_apply]
    rw [GlobalTheory.RowGood.tr_rfl]
    rfl
  have hsurj : ∀ u : GL (Fin V.rank) (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)),
      ∃ κ : Formalism.AUTREP.GAf D.host.E V.rank, ∃ _ : κ ∈ {κ | κ ∈ ReciprocityTheory.Aut.Umax D.host.E V.rank},
        (κ.1.1.map (GlobalTheory.RowGood.tr hF)).map s.proj =
          u.1.map (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).subtype := by
    intro u
    obtain ⟨x, hx, hloc⟩ := GlobalTheory.SplitSec.exists_trivOutside_loc D.host.E V.rank s
      (Matrix.GeneralLinearGroup.map (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).subtype u)
    refine ⟨x, (GlobalTheory.HeckeStdFacts.loc_mem_GLint_iff s hx).1 ⟨u, ?_⟩, ?_⟩
    · exact hloc.symm
    · rw [hpr, hloc]; rfl
  obtain ⟨b, hb⟩ := conj_red_core (R := EAf D) (K := s.v.adicCompletion (maximalRealSubfield D.host.E)) (k := kP s.w)
    (ι := Formalism.AUTREP.GAf D.host.E V.rank) (m := V.rank) (S := Formalism.L2.Herm.intAf D.host.F D.host.E)
    (O := s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) (pr := s.proj) (φ := GlobalTheory.MtRed.phiR s)
    (res := resS D.host.F s.w) (hres := resS_eq_phiR D s) (β := β) (hBB := hBB)
    (U := {κ | κ ∈ ReciprocityTheory.Aut.Umax D.host.E V.rank})
    (Km := fun κ => κ.1.1.map (GlobalTheory.RowGood.tr hF))
    (Z := fun κ hκ => pullFr β ⟨_, hSt κ hκ⟩) (hZ := hZ) (hsurj := hsurj)
  refine ⟨GlobalTheory.MtRed.phiR s, b, ⟨GlobalTheory.MtRed.phiR_surj s, GlobalTheory.MtRed.phiR_eq_zero s⟩, fun κ hκ y hy a c => ?_⟩
  have hy' : (κ.1.1.map (GlobalTheory.RowGood.tr hF)).map s.proj =
      y.1.map (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).subtype := by
    rw [hpr]
    exact Matrix.ext fun i j => (hy i j).symm
  have e := congrFun (congrFun (hb κ hκ y hy') a) c
  have hr : redFn β s.w (finE V (P.ψ κ)) = Formalism.UG.bc (resS D.host.F s.w) (pullFr β ⟨_, hSt κ hκ⟩) := by
    have h1 := redFn_frGL β s.w (pullFr β ⟨_, hSt κ hκ⟩)
    rwa [frGL_pullFr] at h1
  rw [← e, hr]
  rfl

end GlobalTheory.FrameRedSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExportTieMove
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2 (NExpTied)
open Formalism.AUTREP (GAf)
open GlobalTheory.HeightCounting GlobalTheory.HeightCounting.SideCopy GlobalTheory.TwInputs.Move.Forms

namespace GlobalTheory.HeightCounting.SerCarry

variable {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}

theorem exportTie_move (h : CopyTw D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι) {S : NX.RatDat D.ntw}
    (YS : NX.NExpRealS X.R X.cG S)
    (hsup : ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : D.nexp.Fm i j b), x ∈ D.nexp.Bsup i j b ↔ YS.eF i j b h1 h2 x ∈ NX.Bsup S i j b)
    (Z : ExportTie YS X.geo.v₀) :
    ∃ Z' : ExportTie (Forms.tie h m YS hsup) X'.geo.v₀, SameSetup Z.ρ Z'.ρ ∧
      ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' → ∀ (j : Fin D.R.m) b,
        Z'.ν i' (h.cm j) b = Z.ν i j b ∧ HEq (Z.tie i j b).rdV (Z'.tie i' (h.cm j) b).rdV := by
  obtain ⟨ρ', hs, hg, hp⟩ := setup_move h m Z.ρ Z.good Z.pin
  have hrd := Forms.rdRel_move h m YS hsup Z.ρ ρ' hs Z.good hg
  have hm : D'.R.m = D.R.m := (congrArg Ranks.m h.gal.R).symm
  let ν' : D'.ntw.Tw → Fin D'.R.m → Bool → ℂ := fun i' j' b => Z.ν (cast h.Tw_eq.symm i') (Fin.cast hm j') b
  have hν : ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' → ∀ (j : Fin D.R.m) b, ν' i' (h.cm j) b = Z.ν i j b := by
    intro i i' hi j b
    have e1 : cast h.Tw_eq.symm i' = i := eq_of_heq ((cast_heq _ _).trans hi.symm)
    have e2 : Fin.cast hm (h.cm j) = j := Fin.ext rfl
    change Z.ν (cast h.Tw_eq.symm i') (Fin.cast hm (h.cm j)) b = _
    rw [e1, e2]
  have back : ∀ (i' : D'.ntw.Tw) (j' : Fin D'.R.m), ∃ i : D.ntw.Tw, ∃ j : Fin D.R.m, HEq i i' ∧ h.cm j = j' :=
    fun i' j' => ⟨cast h.Tw_eq.symm i', Fin.cast hm j', cast_heq _ _, Fin.ext rfl⟩
  have hrdZ : RdRel h (fun i j b => realRd YS X.geo.v₀ Z.good i j b (Z.ν i j b))
      (fun i j b => realRd (Forms.tie h m YS hsup) X'.geo.v₀ hg i j b (ν' i j b)) := by
    intro i i' hi j b f
    have := hrd (Z.ν i j b) i i' hi j b f
    change HEq (realRd (Forms.tie h m YS hsup) X'.geo.v₀ hg i' (h.cm j) b (ν' i' (h.cm j) b) _) _
    rw [hν i i' hi j b]
    exact this
  obtain ⟨T', hT'⟩ := TieUp.tie_move h hs Z.good hg _ _ hrdZ Z.tie
  have hv := isExtremalVector_of_realSideBaseChange h m Z.vec
  have hsc : ∀ i' j' b, IsScalar (Forms.tie h m YS hsup) X'.geo.v₀ hg i' j' b (ν' i' j' b) := by
    intro i' j' b
    obtain ⟨i, j, hi, rfl⟩ := back i' j'
    rw [hν i i' hi j b]
    exact scalar_move h m hs Z.good hg Z.pin hp Z.vec hv hrd i i' hi j b _ (Z.scalar i j b)
  have hhk : ∀ i' j' b, HeckeTie (realRd (Forms.tie h m YS hsup) X'.geo.v₀ hg i' j' b (ν' i' j' b)) := by
    intro i' j' b
    obtain ⟨i, j, hi, rfl⟩ := back i' j'
    exact heckeTie_move h hs _ _ hrdZ i i' hi j b (Z.hecke i j b)
  exact ⟨ExportTie.mk ρ' hg hp hv ν' hsc T' hhk (GlobalTheory.UnivCharCopy.isUnivChar_copy h Z.univ), hs,
    fun i i' hi j b => ⟨hν i i' hi j b, hT' i i' hi j b⟩⟩

theorem serAt_move (h : CopyAll D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι) {S : NX.RatDat D.ntw}
    (YS : NX.NExpRealS X.R X.cG S) {Xe : NExpTied D} {Xe' : NExpTied D'} (hX : ExpMove Xe Xe')
    {PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV} {PV' : ∀ i : Fin D'.R.m, principalLevelFrame.RowPsi (Vc D' i) D'.R.nV}
    (hp : KeepsMat fun i => (PV i).ψ) (hp' : KeepsMat fun i => (PV' i).ψ) {cf : CharFrame D} {cf' : CharFrame D'}
    (hcf : SameFrame cf cf') {Pq Pq'} (hPq : HEq Pq Pq') (Z : SerAt YS X.geo.v₀ Xe PV cf Pq) :
    Nonempty (SerAt (Forms.tie h.cp m YS Z.sup) X'.geo.v₀ Xe' PV' cf' Pq') := by
  obtain ⟨Z', hs, hr⟩ := exportTie_move h.cp m YS Z.sup Z.ex
  obtain ⟨lam, l1, l2, l3, l4, l5⟩ := LamCopy.lam_copy h hcf ⟨Z.lam, Z.lam_ok, Z.lam_teich, Z.lam_C, Z.lam_q, Z.lam_tie⟩
  refine ⟨{ ex := Z'
            bad := (low_copy h.cp).2.1 _ _ hs.bad Z.bad
            ch := (pq_copy h.cp Pq Pq' hPq).1 _ _ hs.ch Z.ch
            join := fun i' j' b k Q' ψ' hA' hT' => ?_
            sup := sup_move h.cp m YS Z.sup
            off := (low_copy h.cp).2.2 Z.off
            lam := lam
            lam_ok := l1
            lam_teich := l2
            lam_C := l3
            lam_q := l4
            lam_tie := l5 }⟩
  obtain ⟨j, rfl⟩ : ∃ j, h.cp.cm j = j' := ⟨⟨j', lt_m h.cp j'.2⟩, rfl⟩
  obtain ⟨i, Q, ψ, hi, hQ, hψ, hT, e1, e2, e3, e4⟩ := join_copy h.cp i' j (h.cp.cm j) rfl b k Q' ψ' hT'
  obtain ⟨e5, e6⟩ := e4 _ _ hs.ek
  obtain ⟨hA, -, -, hR⟩ := hX i i' hi ((j : ℕ) + 1) b k Q Q' hQ ψ ψ' hψ (Nat.le_add_left _ _) j.2 (h.cp.cm j).2 hA'
  exact hR _ _ e5 _ _ e1 e2 e3 _ _ (e6 _ _ (hr i i' hi j b).2 _ _ (keepsMat_heq h.cp _ _ hp hp' j (h.cp.cm j) rfl))
    (Z.join i j b k Q ψ hA hT)

theorem series_move (h : CopyAll D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι)
    (g₀ : GlobalTheory.RealGeo.GeoHalf X.core X.R.toRealDat fun _ => 1) (g₁ : GlobalTheory.RealGeo.GeoHalf X'.core X'.R.toRealDat fun _ => 1)
    {kKs hk} (kKs' hk') (YS : NX.NExpRealS X.R X.cG (NX.ratDatR X.R X.cG kKs hk)) (hfi : ∀ i x, HEq ((YS.fi i).e x) x)
    (hl : LowIn D) {Sb Sb'} (hSb : OverSet D Sb (lowAll D)) (hSb' : OverSet D' Sb' (lowAll D'))
    {hL hL'} (H : HkAd X Sb hL) (H' : HkAd X' Sb' hL') {hs c} (hs') {c'} (hc : SameUnits c c') (L : HkLaw D _ YS.eF hL hs c)
    {cf : CharFrame D} {cf' : CharFrame D'} (hcf : SameFrame cf cf') (s : CharSide D cf) (s' : CharSide D' cf')
    {PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV} {PV' : ∀ i : Fin D'.R.m, principalLevelFrame.RowPsi (Vc D' i) D'.R.nV}
    (hp : KeepsMat fun i => (PV i).ψ) (hp' : KeepsMat fun i => (PV' i).ψ) {Pq Pq'} (hPq : HEq Pq Pq')
    {Xe : NExpTied D} (hq : PqLaw Xe Pq) (hτ : TauTrue Xe) (Z : SerAt YS g₀.v₀ Xe PV cf Pq) :
    ∃ (YS' : NX.NExpRealS X'.R X'.cG (NX.ratDatR X'.R X'.cG kKs' hk')) (Xe' : NExpTied D'), PqLaw Xe' Pq' ∧
      HkLaw D' (NX.ratDatR X'.R X'.cG kKs' hk') YS'.eF hL' hs' c' ∧ (∀ i x, HEq ((YS'.fi i).e x) x) ∧
      Nonempty (SerAt YS' g₁.v₀ Xe' PV' cf' Pq') ∧ TauTrue Xe' := by
  obtain rfl : kKs' = m.kKsOf (e := e) YS (NX.idxOf D 0) :=
    RingHom.ext fun x => Subtype.ext ((hk' x).trans (m.kKsOf_spec h.cp YS _ x).symm)
  obtain ⟨Xe', ht, hX⟩ := GlobalTheory.HeightCounting.ExpCopy.expTied_copy h hcf s s' Xe
  obtain ⟨Z₁⟩ := GlobalTheory.SerVec.serAt_vec X g₀ X.geo YS _ _ _ _ Z
  obtain ⟨Z₂⟩ := serAt_move h m YS hX hp hp' hcf hPq Z₁
  exact ⟨Forms.tie h.cp m YS Z₁.sup, Xe', pqLaw_move h.cp hX hPq hq,
    hkLaw_move h.cp m YS hfi hl ((low_copy h.cp).1 hl) hSb hSb' H H' Z₁.sup hs' hc L, fun i x => fiOfEq_heq X' _ x,
    GlobalTheory.SerVec.serAt_vec X' X'.geo g₁ _ _ _ _ _ Z₂, ht hτ⟩

end GlobalTheory.HeightCounting.SerCarry

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrassmannProductIntegralEqFlagDegreeWeight
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

namespace GlobalTheory.GrassTop

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem rho_eq_flagMap (H : Host E) (Dw : Datum H) : rho H Dw = GlobalTheory.Schubert.flagMap Dw := rfl

theorem degFl_rho_antisymm (H : Host E) (Dw : Datum H) (Q : MvPolynomial (Root Dw.mult) ℝ) :
    Formalism.DegreeFormula.degFl (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q)
      (rho H Dw (GlobalTheory.GoodMetric.antisymm Q)) =
      (∏ τ, ((Dw.mult τ).factorial : ℝ)) * Formalism.DegreeFormula.degFl (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (rho H Dw Q) := by
  rw [rho_eq_flagMap]
  unfold GlobalTheory.GoodMetric.antisymm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← GlobalTheory.Schubert.flagLin_apply, map_sum]
  have hterm : ∀ w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ)),
      GlobalTheory.Schubert.flagLin (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (GlobalTheory.Schubert.flagMap Dw
        ((((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ)) • rename (fun x : Root Dw.mult =>
          (⟨x.1, w x.1 x.2⟩ : Root Dw.mult)) Q)) =
        Formalism.DegreeFormula.degFl (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (GlobalTheory.Schubert.flagMap Dw Q) := by
    intro w
    rw [map_zsmul, map_zsmul, GlobalTheory.Schubert.flagLin_apply,
      GlobalTheory.Schubert.degFl_flagMap_rename_perm, zsmul_eq_mul, ← mul_assoc]
    have hs : ((((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : ℝ)) *
        (((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : ℝ) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp
    rw [hs, one_mul]
  rw [Finset.sum_congr rfl fun w _ => hterm w, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_pi]
  push_cast
  simp only [Fintype.card_perm, Fintype.card_fin]

theorem prod_factorial_mult (H : Host E) (Dw : Datum H) :
    (∏ τ, ((Dw.mult τ).factorial : ℝ)) =
      ((Dw.p.factorial * Dw.q.factorial : ℝ)) ^ Fintype.card (GlobalTheory.AllWt.Psi H) := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)]
  have e1 : ∀ τ : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0}, ((Dw.mult τ.1).factorial : ℝ) = Dw.p.factorial := by
    intro τ; simp [Datum.mult, τ.2]
  have e2 : ∀ τ : {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0}, ((Dw.mult τ.1).factorial : ℝ) = Dw.q.factorial := by
    intro τ; simp [Datum.mult, τ.2]
  simp only [e1, e2, Finset.prod_const, Finset.card_univ, mul_pow]
  congr 2
  exact Fintype.card_congr
    { toFun := fun τ => (⟨conjEmb τ.1, GlobalTheory.AllWt.conj_mem τ.2⟩ : GlobalTheory.AllWt.Psi H)
      invFun := fun τ => ⟨conjEmb τ.1, GlobalTheory.AllWt.conj_not_mem τ⟩
      left_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb τ.1)
      right_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb τ.1) }

theorem intGr_eq_flagDeg : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (la : GlobalTheory.AllWt.Weight Dw) (R : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) (D : ℕ),
    D = Fintype.card (GlobalTheory.AllWt.Psi H) * ((Dw.p + Dw.q) * (Dw.p + Dw.q - 1) / 2) →
    GlobalTheory.GoodMetric.antisymm
      ((∑ x : Root Dw.mult, MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) * MvPolynomial.X x) ^ D) =
      chernRoots Dw.mult R * rootDiscr Dw.mult →
    intGr H Dw R = Formalism.DegreeFormula.flagDeg (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (fun τ i => (la τ i : ℝ)) := by
  intro E _ _ _ H Dw la R D hD hA
  unfold intGr
  rw [← hA, degFl_rho_antisymm, prod_factorial_mult, map_pow, rho_eq_flagMap,
    GlobalTheory.Schubert.chernRootSubstitution_weightLineBundle_eq_linRoot, hD]
  have hpos : ((Dw.p.factorial * Dw.q.factorial : ℝ)) ^ Fintype.card (GlobalTheory.AllWt.Psi H) ≠ 0 := by
    apply pow_ne_zero; exact_mod_cast (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)).ne'
  rw [mul_div_cancel_left₀ _ hpos]
  rfl

end GlobalTheory.GrassTop
end

