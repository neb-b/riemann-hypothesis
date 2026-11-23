module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0795
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0763
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0717
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0833
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0820
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0834
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0757
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaDecompositionOffFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0890

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingCharacterAdmissibleGaloisTwistGood
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistGood

theorem ramExactly_conj {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N) {M : Type} [CommGroup M]
    (ψ : G D.host.E N.Om →* M) (Q : Set (Pl D.host.E)) (hA : AntiHom X.cc ψ) (hR : RamExactly ψ Q) :
    ∀ P ∈ Q, ∀ P' : Pl D.host.E, IsConjPl D.host P P' → P' ∈ Q := by
  intro P hP P' hPP
  have : IsCMField D.host.E := D.host.isCMField_hostE
  have hst : ∀ x : D.host.E, IsCMField.complexConj D.host.E x = D.host.conj x :=
    bridge_star_holds D.R D.host
  obtain ⟨⟨j, hj⟩, -⟩ := X.cc_cm
  have hκ : ∀ x, D.host.conj (D.host.conj x) = x := fun x => by
    rw [← hst, ← hst, IsCMField.complexConj_apply_apply]
  have hc : ∀ x, X.cc (algebraMap D.host.E N.Om x) = algebraMap D.host.E N.Om (D.host.conj x) := fun x => by
    apply j.injective
    rw [hj, ← hst]
    exact (IsCMField.complexEmbedding_complexConj D.host.E (j.comp (algebraMap D.host.E N.Om)) x).symm
  have hs : ∀ x, X.cc.symm (algebraMap D.host.E N.Om x) = algebraMap D.host.E N.Om (D.host.conj x) := fun x => by
    rw [RingEquiv.symm_apply_eq, hc, hκ]
  have hpl : IsPlaceOver (N.plOm.1 P) P := N.plOm.2 P
  obtain ⟨σ, hσ, hne⟩ := (hR P _ hpl).2 hP
  obtain ⟨σ', h1, h2⟩ := GlobalTheory.AntiRam.exists_conj_mem_Ine X.cc (fun x => D.host.conj x) hc hκ _ σ hσ
  refine (hR P' _ (fun y => ?_)).1 ⟨σ', h2, ?_⟩
  · have hint : IsIntegral ℤ (D.host.conj (y : D.host.E)) := by
      rw [← hst]
      exact (RingOfIntegers.isIntegral_coe y).map ((IsCMField.complexConj D.host.E).toRingEquiv.toRingHom.toIntAlgHom)
    rw [GlobalTheory.AntiRam.valuation_comap_lt_one, hs, ← hPP ⟨_, hint⟩ y (hκ _).symm]
    exact hpl ⟨_, hint⟩
  · rw [hA σ σ' h1]
    exact inv_ne_one.2 hne

theorem tw_good : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (ρ : Setup X), ρ.Good → ∀ (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E)) (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ), Formalism.MainNotions.IntegralHeckeForms.TwOK i k Q ψ → (ρ.tw i b k Q ψ).Good ∧ (ρ.B i j b).admitted (ρ.tw i b k Q ψ).Q ∧ ∀ x, ∃ u : (X.Ok i k)ˣ, (((ρ.tw i b k Q ψ).chi x : Circle) : ℂ) = ρ.eOk i b k u := by
  intro D N X ρ hρ i j b k Q ψ hψ
  classical
  obtain ⟨hsplit, hdisj, hopen, hanti, hzk, hram, -⟩ := hψ
  have hadm : (ρ.B i j b).admitted (half (ρ.ch i) Q) := _root_.GlobalTheory.ChoiceAdm.adm_half_of_good_of_split_disjoint D N X ρ hρ i j b Q hsplit hdisj
  let g : (X.Ok i k)ˣ →* Circle := unitPart.comp (Units.map (ρ.eOk i b k).toMonoidHom)
  have hkey : charOf ρ.rc (ρ.eOk i b k) ψ = ρ.rc.pull (g.comp ψ) := by
    rw [Recip.pull_comp _ hopen]
    rfl
  have hz : X.zk i k ^ (X.l i ^ k) = 1 := Units.ext (by simpa using (X.zk_prim i k).pow_eq_one)
  have hpow : ∀ σ, ψ σ ^ (X.l i ^ k) = 1 := by
    intro σ
    obtain ⟨m, hm⟩ := hzk σ
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  refine ⟨?_, hadm, ?_⟩
  · show (⟨half (ρ.ch i) Q, charOf ρ.rc (ρ.eOk i b k) ψ, resOf (charOf ρ.rc (ρ.eOk i b k) ψ)⟩ : Twist D Circle).Good
    rw [hkey]
    refine GlobalTheory.T.artinPullback_isGoodTwist_of_anticyclotomic_tame D N X ρ.rc hρ.rc Circle (g.comp ψ) (X.l i) (X.lPrime i).out
      (fun σ => ⟨k, by rw [MonoidHom.comp_apply, ← map_pow, hpow, map_one]⟩) ?_ ?_ _ ?_ ?_ ?_
    · exact Subgroup.isOpen_mono (H₁ := ψ.ker) (fun x hx => by
        rw [MonoidHom.mem_ker] at hx ⊢
        rw [MonoidHom.comp_apply, hx, map_one]) hopen
    · intro x x' hx
      show g (ψ x') = (g (ψ x))⁻¹
      rw [hanti x x' hx, map_inv]
    · obtain ⟨P, -, h2, h3⟩ := hadm.1.split
      exact h3.mono (Finset.subset_union_right.trans h2)
    · intro P hP hl
      exact Finset.disjoint_left.1 hdisj (mem_half.1 hP).1 (X.twistExcludedPlaces_contains_residueChar i (show P ∈ placesOver D.host.E (X.l i) from hl))
    · intro v hv hnc B hB σ hσ
      have hvQ : v ∉ Q := by
        intro hvQ
        by_cases hc : v ∈ ρ.ch i
        · exact hv (mem_half.2 ⟨hvQ, hc⟩)
        · obtain ⟨v', hv'⟩ := GlobalTheory.TwistDet.exists_isConjPl v
          have hv'Q : v' ∈ Q := ramExactly_conj X ψ _ hanti hram v hvQ v' hv'
          have hne := ne_of_split (hsplit v hvQ) hv'
          have hv'c : v' ∈ ρ.ch i := by
            by_contra h
            exact hc (((hρ.ch i).pair v v' hv' hne).2 h)
          exact hnc v' (mem_half.2 ⟨hv'Q, hv'c⟩) (GlobalTheory.TwistDet.isConjPl_symm hv')
      have h1 : ψ σ = 1 := by
        by_contra h
        exact hvQ ((hram v B hB).1 ⟨σ, hσ, h⟩)
      rw [MonoidHom.comp_apply, h1, map_one]
  · intro x
    obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym x
    exact ⟨ψ σ, charOf_eq ρ.rc (ρ.eOk i b k) hopen hσ (pow_ne_zero _ (X.lPrime i).out.ne_zero) (hpow σ)⟩

end GlobalTheory.TwistGood

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedIntegrandMeasurableInvariantBounded
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

open GlobalTheory.RSJ

namespace GlobalTheory.ZEulProps

theorem norm_prod_le (W W' c₁ c₂ c₃ : ℂ) :
    ‖W * conj W' * c₁ * c₂ * c₃‖ ≤ (‖W * conj W * c₁ * c₂ * c₃‖ + ‖W' * conj W' * c₁ * c₂ * c₃‖) / 2 := by
  simp only [norm_mul, Complex.norm_conj]
  have hK : 0 ≤ ‖c₁‖ * ‖c₂‖ * ‖c₃‖ := by positivity
  nlinarith [mul_nonneg (sq_nonneg (‖W‖ - ‖W'‖)) hK]

theorem psiN_mul_conj {E : Type} [Field E] [NumberField E] {a : ℕ} (u : GA E a) :
    GlobalTheory.JSW.psiN u * conj (GlobalTheory.JSW.psiN u) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp [GlobalTheory.JSW.psiN, Circle.norm_coe]

theorem lastRow_unip {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ} {u : GA E (m + 1)}
    (hu : u ∈ GlobalTheory.CellDec.NA E (m + 1)) (g : GA E (m + 1)) :
    GlobalTheory.ZEul.lastRow (u * g) = GlobalTheory.ZEul.lastRow g := by
  have h := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu
  refine GlobalTheory.ZUnf.lastRow_mul_of_row fun l => ?_
  by_cases hl : l = Fin.last m
  · subst hl; rw [h.2, Matrix.one_apply_eq]
  · have hlt : l < Fin.last m := lt_of_le_of_ne (Fin.le_last l) hl
    rw [h.1 _ _ hlt, Matrix.one_apply_ne (Ne.symm hl)]

theorem detPow_unip {E : Type} [Field E] [NumberField E] {a : ℕ} {u : GA E a} (hu : u ∈ GlobalTheory.CellDec.NA E a) (x : ℝ) :
    GlobalTheory.RSJ.detPow E a x u = 1 := by
  have hd : Matrix.GeneralLinearGroup.det u = 1 := Units.ext (GlobalTheory.RSLocalPart.det_eq_one hu)
  unfold GlobalTheory.RSJ.detPow chiDet
  rw [MonoidHom.comp_apply, hd, map_one]
  simp

end GlobalTheory.ZEulProps

theorem GlobalTheory.ZEulProps.uInt_props : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (φ φ' : GA E (m + 1) → ℂ)
    (Φ : (Fin (m + 1) → Cinf E) → ℂ) (N : ℕ) (x : ℝ),
    Continuous (GlobalTheory.JSW.whit φ) → Continuous (GlobalTheory.JSW.whit φ') →
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g) →
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ' (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ' g) →
    Continuous Φ → (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) →
    Measurable (GlobalTheory.ZEul.uInt φ φ' Φ N x) ∧
    (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, GlobalTheory.ZEul.uInt φ φ' Φ N x (u * g) = GlobalTheory.ZEul.uInt φ φ' Φ N x g) ∧
    ∀ g, ‖GlobalTheory.ZEul.uInt φ φ' Φ N x g‖ ≤ (‖GlobalTheory.ZEul.uInt φ φ Φ N x g‖ + ‖GlobalTheory.ZEul.uInt φ' φ' Φ N x g‖) / 2 := by
  intro E _ _ _ m φ φ' Φ N x hW hW' hl hl' hΦ _
  refine ⟨?_, fun u hu g => ?_, fun g => ?_⟩
  · exact GlobalTheory.ZUnfTheta.measurable_integrand hW.measurable hW'.measurable hΦ N x
  · have hu' : u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)) := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu
    unfold GlobalTheory.ZEul.uInt
    rw [GlobalTheory.ZEulProps.lastRow_unip hu g, mul_assoc u g, hl u hu', hl' u hu', GlobalTheory.RSJ.Model.detPow_mul,
      GlobalTheory.ZEulProps.detPow_unip hu x, one_mul, map_mul]
    have h1 := GlobalTheory.ZEulProps.psiN_mul_conj u
    linear_combination (GlobalTheory.JSW.whit φ (g * infGL E (m + 1) (secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i))) *
      conj (GlobalTheory.JSW.whit φ' (g * infGL E (m + 1) (secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i)))) *
      Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) * indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) *
      (GlobalTheory.RSJ.detPow E (m + 1) x g : ℂ)) * h1
  · unfold GlobalTheory.ZEul.uInt
    exact GlobalTheory.ZEulProps.norm_prod_le _ _ _ _ _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedRankinSelbergIntegrandContinuousInvarian
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.RSCellB

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem row_mul_of_mem_NA {ℓ : Fin a} (hℓ : (ℓ : ℕ) + 1 = a) {u : GA E a} (hu : u ∈ GlobalTheory.CellDec.NA E a)
    (g : GA E a) : (u * g).val ℓ = g.val ℓ := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu
  funext j
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single ℓ]
  · rw [h2 ℓ, one_mul]
  · intro k _ hk
    have hlt : k < ℓ := by
      rcases lt_or_gt_of_ne hk with h | h
      · exact h
      · exact absurd k.2 (by have : (ℓ : ℕ) < k := h; omega)
    rw [h1 ℓ k hlt, zero_mul]
  · intro h; exact absurd (Finset.mem_univ ℓ) h

theorem det_of_mem_NA {u : GA E a} (hu : u ∈ GlobalTheory.CellDec.NA E a) : GeneralLinearGroup.det u = 1 := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, Units.val_one, Matrix.det_of_upperTriangular (fun i j h => h1 i j h)]
  simp [h2]

end GlobalTheory.RSCellB

namespace GlobalTheory.RSCellB

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem rsPsi_self_mul (ℓ : Fin a) {W : GA E a → ℂ} {u : GA E a} (hW : ∀ g, ‖W (u * g)‖ = ‖W g‖)
    (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (g : GA E a)
    (y : Fin a → Ad E) :
    GlobalTheory.RSTheta.rsPsi ℓ W W Φ J η (u * g) y = GlobalTheory.RSTheta.rsPsi ℓ W W Φ J η g y := by
  simp only [GlobalTheory.RSTheta.rsPsi, GlobalTheory.ThetaPoisson.thetaFn, GlobalTheory.RSTheta.rsInf, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, mul_assoc u g, hW]

theorem bInt_continuous_invariant_finite : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ℓ : Fin a), (ℓ : ℕ) + 1 = a →
    ∀ (F : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E),
    Continuous (GlobalTheory.JSW.whit F) → (∀ u ∈ GlobalTheory.CellDec.NA E a, ∀ g, ‖GlobalTheory.JSW.whit F (u * g)‖ = ‖GlobalTheory.JSW.whit F g‖) →
    Continuous Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ →
    Continuous (fun p : ℝ × GA E a => GlobalTheory.RSCell.bInt ℓ F Φ J η p.1 p.2) ∧
      (∀ x, ∀ u ∈ GlobalTheory.CellDec.NA E a, ∀ g, GlobalTheory.RSCell.bInt ℓ F Φ J η x (u * g) = GlobalTheory.RSCell.bInt ℓ F Φ J η x g) ∧
      ∀ x g, GlobalTheory.RSCell.bInt ℓ F Φ J η x g ≠ ⊤ := by
  intro E _ _ _ a ℓ hℓ F Φ J η hWc hWu hΦc hΦs
  have hdet : Continuous fun g : GA E a => (ideleModule E (GeneralLinearGroup.det g) : ℝ) :=
    continuous_subtype_val.comp (continuous_ideleModule.comp (GroundTheory.Automorphic.AdelicGLn.continuous_det E a))
  refine ⟨?_, ?_, ?_⟩
  · have h1 : Continuous fun p : ℝ × GA E a => (p.2, p.2.val ℓ) :=
      continuous_snd.prodMk ((continuous_apply ℓ).comp ((Units.continuous_val (M := Matrix (Fin a) (Fin a) (Ad E))).comp continuous_snd))
    have h2 := (GlobalTheory.RSTheta.continuous_rsPsi hWc hWc hΦc hΦs J η).comp h1
    have h3 : Continuous fun p : ℝ × GA E a => (ideleModule E (GeneralLinearGroup.det p.2) : ℝ) ^ p.1 :=
      (hdet.comp continuous_snd).rpow continuous_fst fun p => Or.inl (ideleModule E (GeneralLinearGroup.det p.2)).2.ne'
    exact h2.enorm.ennreal_mul (ENNReal.continuous_ofReal.comp h3) (fun _ => Or.inr ENNReal.ofReal_ne_top)
      (fun _ => Or.inr enorm_ne_top)
  · intro x u hu g
    simp only [GlobalTheory.RSCell.bInt, row_mul_of_mem_NA hℓ hu, map_mul, det_of_mem_NA hu, one_mul]
    rw [rsPsi_self_mul ℓ (hWu u hu)]
  · intro x g
    exact ENNReal.mul_ne_top enorm_ne_top ENNReal.ofReal_ne_top

end GlobalTheory.RSCellB

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedRankinSelbergIntegrandNeZeroIdentity
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.RSCell

theorem bInt_tl_last_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (F : GA E (m + 1) → ℂ) (Φ : (Fin (m + 1) → Cinf E) → ℂ)
    (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (l₀ : GlobalTheory.CellDec.abelian₂ E (m + 1) T), (∀ w, l₀.1 w (Fin.last m) = 0) →
    GlobalTheory.JSW.whit F (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 → Φ (Pi.single (Fin.last m) 1) ≠ 0 → ∀ x : ℝ, GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 := by
  intro E _ _ _ m T ϖ F Φ J l₀ hl hW hΦ x
  have h0 : Finsupp.mapRange (fun y : Fin (m+1) → ℤ => y (Fin.last m)) rfl l₀.1 = 0 := by
    ext w; simp [hl w]
  have hadl : GlobalTheory.CellDec.adl ϖ (Finsupp.mapRange (fun y : Fin (m+1) → ℤ => y (Fin.last m)) rfl l₀.1) = 1 := by
    rw [h0]; apply Units.ext; apply FiniteAdeleRing.ext; intro v
    simp [GlobalTheory.CellDec.adl]; rfl
  have hrow : (GlobalTheory.CellDec.tl (m+1) ϖ l₀.1).val (Fin.last m) = Pi.single (Fin.last m) 1 := by
    rw [GlobalTheory.CellDec.tl_eq_diagT, GlobalTheory.SmGL.val_diagT]
    funext j
    simp [Matrix.diagonal_apply, Pi.single_apply, hadl, eq_comm]
  set g := GlobalTheory.CellDec.tl (m+1) ϖ l₀.1 with hg
  have hpi : (fun i => pInf E ((Pi.single (Fin.last m) (1 : Ad E) : Fin (m+1) → Ad E) i)) = Pi.single (Fin.last m) 1 := by
    funext i; by_cases h : i = Fin.last m
    · subst h; simp
    · simp [h]
  have hpf : (fun i => pFin E ((Pi.single (Fin.last m) (1 : Ad E) : Fin (m+1) → Ad E) i)) = Pi.single (Fin.last m) 1 := by
    funext i; by_cases h : i = Fin.last m
    · subst h; simp
    · simp [h]
  have hlat : (0 : Fin (m+1) → Af E) ∈ GlobalTheory.ThetaPoisson.latt (m+1) J := fun i => zero_mem _
  have hpsi : GlobalTheory.RSTheta.rsPsi (Fin.last m) (GlobalTheory.JSW.whit F) (GlobalTheory.JSW.whit F) Φ J (Pi.single (Fin.last m) 1) g (g.val (Fin.last m))
      = GlobalTheory.JSW.whit F g * (starRingEnd ℂ) (GlobalTheory.JSW.whit F g) * Φ (Pi.single (Fin.last m) 1) := by
    rw [hrow, GlobalTheory.RSTheta.rsPsi, GlobalTheory.ThetaPoisson.thetaFn, hpi, hpf, sub_self, Set.indicator_of_mem hlat,
      GlobalTheory.RSTheta.rsInf, GlobalTheory.RSTheta.rowGL_single, map_one, inv_one, mul_one]
    simp
  rw [bInt, hpsi]
  refine mul_ne_zero ?_ ?_
  · rw [enorm_ne_zero]
    exact mul_ne_zero (mul_ne_zero hW (by simpa using hW)) hΦ
  · rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Real.rpow_pos_of_pos (ideleModule E _).2 x

end GlobalTheory.RSCell
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDiagonalUniformizerEqZeroOfNotAntitone
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.CellVanish

theorem eq_zero_of_not_antitone : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (w : HeightOneSpectrum (𝓞 E)), w ∉ S →
    (∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) →
    ∀ (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ), IsUnifV E w (ϖ w : w.adicCompletion E) →
    ∀ (W : GA E (m + 1) → ℂ), (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) →
    (∀ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J, ∀ g, W (g * finGL E (m + 1) κ) = W g) →
    ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℤ)), ¬ Antitone (l w) →
    ∀ p : GA E (m + 1), Matrix.GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p = 1 →
    W (p * GlobalTheory.CellDec.tl (m + 1) ϖ l) = 0 := by
  intro E _ _ _ m S J w hwS hψ ϖ hϖ W hWN hWK l hl p hp
  set t := GlobalTheory.CellDec.tl (m + 1) ϖ l with ht
  set D : GL (Fin (m + 1)) (w.adicCompletion E) := GlobalTheory.CellDec.compV E (m + 1) w t with hD
  have hDv : (D : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) =
      Matrix.diagonal fun a => ((ϖ w ^ l w a : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
    rw [hD, ht, GlobalTheory.CellDec.tl, GlobalTheory.CellDec.compV_finGL]
    refine Matrix.ext fun i j => ?_
    change pLoc E w (((GlobalTheory.SmGL.diagT (Af E) (Fin (m + 1)) _ : GL (Fin (m + 1)) (Af E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Af E)) i j) = _
    rw [GlobalTheory.SmGL.val_diagT]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq]
      change ((ϖ w ^ (Finsupp.mapRange (fun x : Fin (m + 1) → ℤ => x i) rfl l) w : (w.adicCompletion E)ˣ) : w.adicCompletion E) = _
      simp
    · simp [Matrix.diagonal_apply_ne _ hij]
  set t' := t * (finGL E (m + 1) (locGL E (m + 1) w D))⁻¹ with ht'
  have ht'w : Matrix.GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t' = 1 := by
    change GlobalTheory.CellDec.compV E (m + 1) w t' = 1
    rw [ht', map_mul, map_inv, GlobalTheory.CellDec.compV_finGL_locGL_same, ← hD, mul_inv_cancel]
  have htt : t' * finGL E (m + 1) (locGL E (m + 1) w D) = t := by rw [ht', inv_mul_cancel_right]
  have hlev : ∀ k ∈ GlobalTheory.LFun.KGL w (n := (m + 1)), locGL E (m + 1) w k ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J := by
    intro k hk
    refine ⟨fun v => ?_, fun v hv i j => ?_⟩
    · by_cases hvw : v = w
      · subst hvw; rw [pLoc_locGL]; exact hk
      · rw [pLoc_locGL_of_ne hvw]; exact one_mem _
    · have hvw : v ≠ w := fun h => hwS (h ▸ hv)
      have h1 := congrArg (fun x : GL (Fin (m + 1)) (v.adicCompletion E) => (x : Matrix (Fin (m + 1)) (Fin (m + 1)) (v.adicCompletion E)) i j)
        (pLoc_locGL_of_ne hvw k)
      have h0 : ((locGL E (m + 1) w k).val - 1) i j v = 0 := by
        change pLoc E v (((locGL E (m + 1) w k).val - 1) i j) = 0
        rw [Matrix.sub_apply, map_sub]
        change (Matrix.GeneralLinearGroup.map (pLoc E v) (locGL E (m + 1) w k)).val i j - _ = 0
        rw [h1]
        simp [Matrix.one_apply]
      rw [h0, map_zero]
      exact zero_le'
  let f : GL (Fin (m + 1)) (w.adicCompletion E) → ℂ := fun g => W (p * t' * finGL E (m + 1) (locGL E (m + 1) w g))
  have hfD : f D = W (p * t) := by
    simp only [f]
    rw [mul_assoc, htt]
  have hpt : Matrix.GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (p * t') = 1 := by
    rw [map_mul, hp, ht'w, mul_one]
  have hfN : ∀ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin (m + 1)), ∀ g,
      f (u * g) = GlobalTheory.JSW.psiLocChar w (GlobalTheory.Whittaker.superDiag u) * f g := by
    intro u hu g
    simp only [f]
    rw [map_mul, map_mul, ← mul_assoc (p * t'), GlobalTheory.JSW.commute_finGL_locGL w hpt, mul_assoc,
      hWN _ (GlobalTheory.JSW.CutTransfer.finGL_locGL_mem_NA' w hu), GlobalTheory.JSW.CutTransfer.psiN_finGL_locGL]
    rfl
  have hfK : ∀ g, ∀ k ∈ GlobalTheory.LFun.KGL w (n := (m + 1)), f (g * k) = f g := by
    intro g k hk
    simp only [f]
    rw [map_mul, map_mul, ← mul_assoc]
    exact hWK _ (hlev k hk) _
  have h := GlobalTheory.WhitTorus.eq_zero_of_not_antitone_int E w (m + 1) (GlobalTheory.JSW.psiLocChar w) hψ f hfN hfK (ϖ w) hϖ (l w) hl D hDv
  rwa [hfD] at h

end GlobalTheory.CellVanish
end
end

