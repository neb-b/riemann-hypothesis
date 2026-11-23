module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusDerivationFactorsThroughKaehler
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftsOfSeparable
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHOfIsFrob
section
open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem exists_isH_of_isFrob : ∀ {K Kt : Type} [CommRing K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p]
    (π : Kt →+* K) (F F' : Kt →+* Kt), IsFlatLift p π → IsFrob p π F → IsFrob p π F' →
    ∃ h, IsH p π F F' h := by
  intro K Kt _ _ p _ _ π F F' hL hF hF'
  have hex : ∀ z, ∃ w, F' z = F z + p * w := by
    intro z
    obtain ⟨w, hw⟩ := (hL.ker (F' z - F z)).1 (by rw [map_sub, hF, hF', sub_self])
    exact ⟨w, by rw [← hw]; ring⟩
  have huniq : ∀ z w w', F' z = F z + p * w → F' z = F z + p * w' → π w = π w' := by
    intro z w w' h1 h2
    have h3 : (p : Kt) * (w - w') = 0 := by rw [mul_sub]; linear_combination h2 - h1
    have h4 := (hL.ann (w - w')).1 h3
    rw [map_sub] at h4
    exact sub_eq_zero.1 h4
  let g : Kt → K := fun z => π (Classical.choose (hex z))
  have hg : ∀ z w, F' z = F z + p * w → g z = π w := fun z w hw =>
    huniq z _ w (Classical.choose_spec (hex z)) hw
  have hgadd : ∀ z z', g (z + z') = g z + g z' := by
    intro z z'
    obtain ⟨w, h1⟩ := hex z
    obtain ⟨w', h2⟩ := hex z'
    rw [hg z w h1, hg z' w' h2, hg (z + z') (w + w') (by rw [map_add (f := _), map_add (f := _), h1, h2]; ring), map_add (f := _)]
  have hgp : ∀ y, g (p * y) = 0 := by
    intro y
    obtain ⟨w, h1⟩ := hex y
    rw [hg (p * y) (p * w) (by rw [map_mul, map_mul, map_natCast, map_natCast, h1]; ring), map_mul,
      map_natCast, CharP.cast_eq_zero, zero_mul]
  have hgmul : ∀ z z', g (z * z') = π z' ^ p * g z + π z ^ p * g z' := by
    intro z z'
    obtain ⟨w, h1⟩ := hex z
    obtain ⟨w', h2⟩ := hex z'
    rw [hg z w h1, hg z' w' h2, hg (z * z') (w * F z' + F z * w' + p * w * w')
      (by rw [map_mul, map_mul, h1, h2]; ring)]
    simp only [map_add (f := _), map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, add_zero]
    rw [hF z, hF z']
    ring
  have hwd : ∀ z z', π z = π z' → g z = g z' := by
    intro z z' hzz
    obtain ⟨y, hy⟩ := (hL.ker (z - z')).1 (by rw [map_sub, hzz, sub_self])
    have : z = z' + p * y := by rw [← hy]; ring
    rw [this, hgadd, hgp, add_zero]
  let φ : K →+ K := AddMonoidHom.mk' (fun x => g (Function.surjInv hL.surj x)) (by
    intro a b
    show g _ = g _ + g _
    rw [← hgadd]
    apply hwd
    rw [map_add (f := _), Function.surjInv_eq hL.surj, Function.surjInv_eq hL.surj, Function.surjInv_eq hL.surj])
  have hφ : ∀ z, φ (π z) = g z := by
    intro z
    show g _ = g _
    exact hwd _ _ (Function.surjInv_eq hL.surj _)
  obtain ⟨f, hfs, hfD⟩ := _root_.GlobalTheory.DI.frobDeriv_factors_kaehler (M := K) p φ (by
    intro a b
    obtain ⟨z, rfl⟩ := hL.surj a
    obtain ⟨z', rfl⟩ := hL.surj b
    rw [← map_mul, hφ, hφ, hφ, hgmul, smul_eq_mul, smul_eq_mul]; ring)
  refine ⟨f, fun c v => by rw [hfs, smul_eq_mul], fun z w hzw => ?_⟩
  rw [hfD, hφ, hg z w hzw]

end GlobalTheory.DI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicGraphUnitaryIsUnitLowerBlock
section
open scoped Matrix

namespace GlobalTheory

theorem exists_isotropic_graph_isUnit_lowerRow : ∀ (O : Type) [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    (∃ x : O, IsUnit (c x - x)) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
    ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, IsUnit g.det →
      gᵀ * Matrix.fromBlocks 0 J J 0 * g.map c = Matrix.fromBlocks 0 J J 0 →
      ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ IsUnit (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det := by
  have hfield := _root_.GlobalTheory.exists_isotropic_graph_det_lowerRow_ne_zero_field
  have hlift := _root_.GlobalTheory.lift_mod_maximal_skew

  intro O _ _ c hc h2 hx0 n J hJ hJdet g hg hgu
  obtain ⟨x, hx⟩ := hx0
  haveI : IsLocalHom c := ⟨fun a ha => by simpa [hc] using ha.map c⟩
  set π := IsLocalRing.residue O with hπ
  set σ : IsLocalRing.ResidueField O →+* IsLocalRing.ResidueField O := IsLocalRing.ResidueField.map c with hσ
  have hσπ : ∀ a, σ (π a) = π (c a) := fun a => IsLocalRing.ResidueField.map_residue c a
  have hσσ : ∀ y, σ (σ y) = y := by
    intro y; obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y; rw [hσπ, hσπ, hc]
  have hε : ∃ ε, ε ≠ 0 ∧ σ ε = -ε := ⟨π (c x - x), (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hx, by
    rw [hσπ, map_sub, hc, ← neg_sub, map_neg]⟩
  have hmapc : ∀ {m : Type} (M : Matrix m m O), (M.map c).map π = (M.map π).map σ := by
    intro m M; ext i j; simp [hσπ]
  have hJ' : ∀ i j, σ (J.map π j i) = J.map π i j := by intro i j; simp [hσπ, hJ]
  have hJdet' : (J.map π).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hJdet
  have hg' : (g.map π).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hg
  have hgu' : (g.map π)ᵀ * Matrix.fromBlocks 0 (J.map π) (J.map π) 0 * (g.map π).map σ
      = Matrix.fromBlocks 0 (J.map π) (J.map π) 0 := by
    have := congrArg (fun M => M.map π) hgu
    simpa only [Matrix.map_mul, Matrix.transpose_map, hmapc, Matrix.fromBlocks_map,
      Matrix.map_zero _ (map_zero π)] using this
  obtain ⟨Zb, hZb, hdet⟩ := hfield _ σ hσσ hε n _ hJ' hJdet' _ hg' hgu'
  obtain ⟨Z₀, hZ₀⟩ : ∃ Z₀ : Matrix (Fin n) (Fin n) O, Z₀.map π = Zb :=
    ⟨fun i j => (IsLocalRing.residue_surjective (Zb i j)).choose, by
      ext i j; exact (IsLocalRing.residue_surjective (Zb i j)).choose_spec⟩
  have hZ₀m : ∀ i j, (Z₀ᵀ * J + J * Z₀.map c) i j ∈ IsLocalRing.maximalIdeal O := by
    intro i j
    rw [← IsLocalRing.residue_eq_zero_iff]
    have := congrArg (fun M => M i j) hZb
    simp only [Matrix.zero_apply] at this
    rw [← this, ← hZ₀, ← hmapc, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add π)]
    rfl
  obtain ⟨Z, hZ, hZm⟩ := hlift O c hc h2 n J hJ hJdet Z₀ hZ₀m
  refine ⟨Z, hZ, ?_⟩
  have hZπ : Z.map π = Zb := by
    rw [← hZ₀]; ext i j
    simp only [Matrix.map_apply]
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact hZm i j
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← hπ, RingHom.map_det, RingHom.mapMatrix_apply,
    Matrix.map_add _ (map_add π), Matrix.map_mul, hZπ]
  exact hdet

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftsOfSeparableStatement
section
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lifts_of_separable_reduction : ∀ (D : ℕ) (P : Polynomial (MvPowerSeries (Fin D) ℂ)), P.Monic → (P.map (MvPowerSeries.constantCoeff (σ := Fin D) (R := ℂ))).Separable → ∃ θ : Fin P.natDegree → MvPowerSeries (Fin D) ℂ, Function.Injective θ ∧ ∀ j, P.IsRoot (θ j) := by
  first | exact @GlobalTheory.HenselSplitPS.exists_lifts_of_separable | exact GlobalTheory.HenselSplitPS.exists_lifts_of_separable | (intros; apply GlobalTheory.HenselSplitPS.exists_lifts_of_separable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalPushoutUnramifiedCharZeroStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_pushout_unramified_charZero : ∀ (A V V' : Type) [CommRing A] [CommRing V] [IsLocalRing V] [CommRing V'] [IsLocalRing V'] (f : A →+* V) (f' : A →+* V'), f'.Flat → (maximalIdeal V).comap f = (maximalIdeal V').comap f' → ((maximalIdeal V).comap f).map f = maximalIdeal V → ((maximalIdeal V').comap f').map f' = maximalIdeal V' → CharZero (ResidueField V) → ∃ (B : Type) (_ : CommRing B) (_ : IsLocalRing B) (g : V →+* B) (g' : V' →+* B), g.comp f = g'.comp f' ∧ g.Flat ∧ (maximalIdeal V).map g = maximalIdeal B ∧ (maximalIdeal V').map g' = maximalIdeal B := by
  first | exact @GlobalTheory.UnramPushout.exists_local_pushout | exact GlobalTheory.UnramPushout.exists_local_pushout | (intros; apply GlobalTheory.UnramPushout.exists_local_pushout <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalStageTensorPolynomialOrigin
section
open IsLocalRing Polynomial

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LocalStage

theorem mem_originIdeal_iff {T : Type} [CommRing T] [IsLocalRing T] (f : Polynomial T) :
    f ∈ GlobalTheory.KeyOriginCut.originIdeal T ↔ f.coeff 0 ∈ maximalIdeal T := by
  constructor
  · intro hf
    have hle : GlobalTheory.KeyOriginCut.originIdeal T ≤
        (maximalIdeal T).comap (Polynomial.constantCoeff : Polynomial T →+* T) := by
      refine sup_le ?_ ?_
      · rw [Ideal.map_le_iff_le_comap]
        intro x hx
        simpa using hx
      · rw [Ideal.span_le]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        simp
    simpa using hle hf
  · intro hf
    rw [← Polynomial.X_mul_divX_add f]
    refine Ideal.add_mem _ ?_ ?_
    · exact Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
    · exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf)

theorem comap_originIdeal {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    (φ : R →+* S) [IsLocalHom φ] :
    (GlobalTheory.KeyOriginCut.originIdeal S).comap (Polynomial.mapRingHom φ) =
      GlobalTheory.KeyOriginCut.originIdeal R := by
  ext f
  rw [Ideal.mem_comap, mem_originIdeal_iff, mem_originIdeal_iff]
  simp only [Polynomial.coe_mapRingHom, Polynomial.coeff_map]
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    mem_nonunits_iff, isUnit_map_iff]

theorem localStage : ∀ (T O : Type) [CommRing T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O],
    (maximalIdeal O).comap (algebraMap (Polynomial T) O) = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (A : Type) [CommRing A] [IsLocalRing A] (i : A →+* T), IsLocalHom i →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (A' : Type) [CommRing A'] [IsLocalRing A'] (ι : A →+* A') (α : A' →+* T), α.comp ι = i → IsLocalHom α →
    ∃ (E' : Type) (_ : CommRing E') (_ : Algebra (Polynomial A') E') (_ : Algebra.Etale (Polynomial A') E')
      (Q' : Ideal E') (_ : Q'.IsPrime),
      Q'.comap (algebraMap (Polynomial A') E') = GlobalTheory.KeyOriginCut.originIdeal A' ∧
      ∃ (β : Localization.AtPrime QA →+* Localization.AtPrime Q') (γ : Localization.AtPrime Q' →+* O),
        ((algebraMap (Polynomial A') (Localization.AtPrime Q')).comp Polynomial.C).comp ι =
          β.comp ((algebraMap (Polynomial A) (Localization.AtPrime QA)).comp Polynomial.C) ∧
        γ.comp β = jA ∧
        γ.comp ((algebraMap (Polynomial A') (Localization.AtPrime Q')).comp Polynomial.C) =
          (algebraMap T O).comp α := by
  intro T O _ _ _ _ _ _ _ hO A _ _ i hi EA _ _ _ QA _ hQA jA hjA A' _ _ ι α hαι hα
  letI : Algebra (Polynomial A) (Polynomial A') := (Polynomial.mapRingHom ι).toAlgebra
  letI : Algebra (Polynomial A) O := ((algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i)).toAlgebra
  haveI : Algebra.Etale (Polynomial A') (Polynomial A' ⊗[Polynomial A] EA) :=
    Algebra.Etale.baseChange (Polynomial A) EA (Polynomial A')
  let f : Polynomial A' →ₐ[Polynomial A] O :=
    { toRingHom := (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom α)
      commutes' := by
        intro p
        change (algebraMap (Polynomial T) O) (Polynomial.map α (Polynomial.map ι p)) =
          (algebraMap (Polynomial T) O) (Polynomial.map i p)
        rw [Polynomial.map_map, hαι] }
  let g : EA →ₐ[Polynomial A] O :=
    { toRingHom := jA.comp (algebraMap EA (Localization.AtPrime QA))
      commutes' := by
        intro p
        change jA (algebraMap EA (Localization.AtPrime QA) (algebraMap (Polynomial A) EA p)) =
          (algebraMap (Polynomial T) O) (Polynomial.map i p)
        rw [← IsScalarTower.algebraMap_apply]
        exact congrArg (fun h => h p) hjA }
  let F : (Polynomial A' ⊗[Polynomial A] EA) →+* O :=
    (Algebra.TensorProduct.productMap f g).toRingHom
  have hF : ∀ a b, F (a ⊗ₜ b) = f a * g b := fun a b => by
    simp [F, Algebra.TensorProduct.productMap_apply_tmul]
  let Q' : Ideal (Polynomial A' ⊗[Polynomial A] EA) := (maximalIdeal O).comap F
  refine ⟨Polynomial A' ⊗[Polynomial A] EA, inferInstance, inferInstance, inferInstance, Q',
    Ideal.comap_isPrime _ _, ?_, ?_⟩
  · have hcomp : F.comp (algebraMap (Polynomial A') (Polynomial A' ⊗[Polynomial A] EA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom α) := by
      refine RingHom.ext fun p => ?_
      rw [RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply, hF, map_one, mul_one]
      rfl
    change ((maximalIdeal O).comap F).comap _ = _
    rw [Ideal.comap_comap, hcomp, ← Ideal.comap_comap, hO, comap_originIdeal]
  let h : EA →+* (Polynomial A' ⊗[Polynomial A] EA) :=
    (Algebra.TensorProduct.includeRight : EA →ₐ[Polynomial A] _).toRingHom
  have hh : ∀ x, F (h x) = jA (algebraMap EA (Localization.AtPrime QA) x) := fun x => by
    change F (1 ⊗ₜ x) = _
    rw [hF, map_one, one_mul]
    rfl
  have hy : QA.primeCompl ≤ Q'.primeCompl.comap h := by
    intro x hx
    have hu : IsUnit (jA (algebraMap EA (Localization.AtPrime QA) x)) :=
      (IsLocalization.map_units (Localization.AtPrime QA) (⟨x, hx⟩ : QA.primeCompl)).map jA
    change h x ∉ Q'
    intro hmem
    have hmem' : F (h x) ∈ maximalIdeal O := hmem
    rw [hh] at hmem'
    exact ((mem_maximalIdeal _).mp hmem') hu
  have hγ : ∀ y : Q'.primeCompl, IsUnit (F y) := by
    intro y
    by_contra hc
    exact y.2 ((mem_maximalIdeal _).mpr hc)
  let β : Localization.AtPrime QA →+* Localization.AtPrime Q' :=
    IsLocalization.map (M := QA.primeCompl) (S := Localization.AtPrime QA) (Localization.AtPrime Q')
      (g := h) (T := Q'.primeCompl) hy
  let γ : Localization.AtPrime Q' →+* O :=
    IsLocalization.lift (M := Q'.primeCompl) (S := Localization.AtPrime Q') (g := F) hγ
  refine ⟨β, γ, ?_, ?_, ?_⟩
  · refine RingHom.ext fun a => ?_
    simp only [RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply (Polynomial A) EA (Localization.AtPrime QA),
      IsScalarTower.algebraMap_apply (Polynomial A') (Polynomial A' ⊗[Polynomial A] EA)
        (Localization.AtPrime Q')]
    change _ = β (algebraMap EA (Localization.AtPrime QA) _)
    rw [IsLocalization.map_eq]
    congr 1
    change algebraMap (Polynomial A') (Polynomial A' ⊗[Polynomial A] EA) (Polynomial.C (ι a)) =
      (1 : Polynomial A') ⊗ₜ algebraMap (Polynomial A) EA (Polynomial.C a)
    rw [Algebra.TensorProduct.algebraMap_apply, ← Algebra.TensorProduct.algebraMap_apply',
      Algebra.TensorProduct.algebraMap_apply]
    congr 1
    change _ = Polynomial.map ι (Polynomial.C a)
    rw [Polynomial.map_C]
    rfl
  · refine IsLocalization.ringHom_ext QA.primeCompl (RingHom.ext fun x => ?_)
    simp only [RingHom.comp_apply]
    change γ (β (algebraMap EA (Localization.AtPrime QA) x)) = _
    rw [IsLocalization.map_eq, IsLocalization.lift_eq, hh]
  · refine RingHom.ext fun a => ?_
    simp only [RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply (Polynomial A') (Polynomial A' ⊗[Polynomial A] EA)
        (Localization.AtPrime Q'), IsLocalization.lift_eq, Algebra.TensorProduct.algebraMap_apply,
      hF, map_one, mul_one]
    change algebraMap (Polynomial T) O (Polynomial.map α (Polynomial.C a)) = _
    rw [Polynomial.map_C, IsScalarTower.algebraMap_apply T (Polynomial T) O]
    rfl

end GlobalTheory.LocalStage
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalOverClosedPointClosedFibre
section
open IsLocalRing Polynomial

namespace GlobalTheory

theorem exists_maximal_over_closedPt : ∀ (T E : Type) [CommRing T] [IsLocalRing T] [CommRing E] [Algebra (Polynomial T) E]
    [Algebra.FiniteType (Polynomial T) E] (Q : Ideal E) [Q.IsPrime],
    Q.comap (algebraMap (Polynomial T) E) =
      (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) →
    ∃ y : Ideal E, y.IsMaximal ∧ Q ≤ y ∧
      y.comap (algebraMap (Polynomial T) E) ≠
        (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) ∧
      (y.comap (algebraMap (Polynomial T) E)).comap (Polynomial.C : T →+* Polynomial T) =
        IsLocalRing.maximalIdeal T := by
  intro T E _ _ _ _ _ Q hQp hQ
  set P : Ideal T[X] := (maximalIdeal T).map (C : T →+* T[X]) with hPdef
  set f := algebraMap T[X] E with hfdef
  obtain ⟨y, hy, hQy⟩ := Ideal.exists_le_maximal Q hQp.ne_top
  have hPy : P ≤ y.comap f := hQ ▸ Ideal.comap_mono hQy

  letI : Field (T ⧸ maximalIdeal T) := Ideal.Quotient.field _
  have eP := Ideal.polynomialQuotientEquivQuotientPolynomial (maximalIdeal T)
  haveI : IsJacobsonRing (T[X] ⧸ P) := isJacobsonRing_of_surjective ⟨eP.toRingHom, eP.surjective⟩
  have hPnf : ¬ P.IsMaximal := by
    intro hm
    have hf : IsField (T[X] ⧸ P) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient P).1 hm
    exact Polynomial.not_isField (T ⧸ maximalIdeal T) (MulEquiv.isField hf eP.toMulEquiv)

  let φ : T[X] ⧸ P →+* E ⧸ y := Ideal.quotientMap y f hPy
  have hcomp : φ.comp (Ideal.Quotient.mk P) = (Ideal.Quotient.mk y).comp f := Ideal.quotientMap_comp_mk hPy
  have hft : φ.FiniteType := by
    apply RingHom.FiniteType.of_comp_finiteType (f := Ideal.Quotient.mk P)
    rw [hcomp]
    exact RingHom.FiniteType.comp (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective)
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  letI : Field (E ⧸ y) := Ideal.Quotient.field y
  letI : Algebra (T[X] ⧸ P) (E ⧸ y) := φ.toAlgebra
  haveI : Algebra.FiniteType (T[X] ⧸ P) (E ⧸ y) := hft
  haveI : Module.Finite (T[X] ⧸ P) (E ⧸ y) := finite_of_finite_type_of_isJacobsonRing _ _
  have hker : (RingHom.ker φ).IsMaximal := by
    have := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := T[X] ⧸ P) (⊥ : Ideal (E ⧸ y))
    change (Ideal.comap φ ⊥).IsMaximal at this
    rwa [← RingHom.ker_eq_comap_bot] at this
  have hyc : y.comap f = (RingHom.ker φ).comap (Ideal.Quotient.mk P) := by
    ext x
    rw [Ideal.mem_comap, Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, hcomp, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem]
  have hymax : (y.comap f).IsMaximal := by
    rw [hyc]; exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  refine ⟨y, hy, hQy, fun h => hPnf (h ▸ hymax), ?_⟩
  have hle : maximalIdeal T ≤ (y.comap f).comap C := by
    intro a ha
    exact hPy (Ideal.mem_map_of_mem _ ha)
  have hne : (y.comap f).comap (C : T →+* T[X]) ≠ ⊤ := (Ideal.comap_isPrime C (y.comap f)).ne_top
  exact ((maximalIdeal.isMaximal T).eq_of_le hne hle).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormOneConstRatioOfCommonRatio
section
namespace GlobalTheory

theorem exists_norm_one_const_ratio_of_common_ratio :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (I : Type) (S : Set V),
      IsOpen S → IsPreconnected S → ∀ (A B : I → V → ℂ) (t : V → ℂ), (∀ i, DifferentiableOn ℂ (A i) S) →
      (∀ i, DifferentiableOn ℂ (B i) S) → (∀ i, ∀ x ∈ S, A i x = t x * B i x) →
      (∀ i, ∀ x ∈ S, ‖A i x‖ = ‖B i x‖) → ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ i, ∀ x ∈ S, A i x = ε * B i x := by
  intro V _ _ _ I S hS hc A B t hA hB ht hn
  by_cases h0 : ∀ i, ∀ x ∈ S, B i x = 0
  · refine ⟨1, norm_one, fun i x hx => ?_⟩
    rw [ht i x hx, h0 i x hx, mul_zero, mul_zero]
  · simp only [not_forall] at h0
    obtain ⟨i₀, x₀, hx₀, hne⟩ := h0
    obtain ⟨_, c, hcc⟩ := exists_eq_const_mul_of_forall_exists_norm_eq V Unit S hS hc ⟨x₀, hx₀⟩ (A i₀)
      (fun _ => B i₀) (hA i₀) (fun _ => hB i₀) (fun x hx => ⟨(), hn i₀ x hx⟩)
    refine ⟨c, ?_, fun i x hx => ?_⟩
    · have h1 := hn i₀ x₀ hx₀
      rw [hcc x₀ hx₀, norm_mul] at h1
      exact mul_right_cancel₀ (norm_ne_zero_iff.mpr hne) (by rw [one_mul]; exact h1)
    · have hd : DifferentiableOn ℂ (fun y => A i y - c * B i y) S := (hA i).sub ((hB i).const_mul c)
      have := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_mul_eq_zero hS hc (hB i₀) hd (fun y hy => by
        have e1 := ht i y hy
        have e2 := ht i₀ y hy
        have e3 : A i₀ y = c * B i₀ y := hcc y hy
        show B i₀ y * (A i y - c * B i y) = 0
        rw [e1]
        linear_combination (B i y) * (e3 - e2)) hx₀ hne x hx
      exact sub_eq_zero.mp this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsParameterFunctionOfFibreDerivZero
section
set_option autoImplicit false

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace Filter Topology

namespace GlobalTheory.AnPer.Charts

theorem exists_glue_fn {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F)
    (hK : K.Rich) (a : ∀ k, Hol (K.W k)) (ha : ∀ k k' (e : K.le 0 k' k), K.sh e (a k) = a k') :
    ∃ G : Tot I g → ℂ, ∀ k, ∀ q ∈ K.W k, G q = (a k).fn q := by
  classical
  have key : ∀ k₁ k₂ q, q ∈ K.W k₁ → q ∈ K.W k₂ → (a k₁).fn q = (a k₂).fn q := by
    intro k₁ k₂ q h₁ h₂
    obtain ⟨k, hk, e₁, e₂⟩ := hK.2 0 k₁ k₂ q h₁ (by rw [F.shift_zero]; exact h₂)
    have r₁ := fn_sh e₁ (a k₁) hk
    have r₂ := fn_sh e₂ (a k₂) hk
    rw [ha, F.shift_zero] at r₁ r₂
    rw [← r₁, ← r₂]
  refine ⟨fun q ↦ if h : ∃ k, q ∈ K.W k then (a h.choose).fn q else 0, fun k q hq ↦ ?_⟩
  have h : ∃ k, q ∈ K.W k := ⟨k, hq⟩
  simp only [dif_pos h]
  exact key _ _ q h.choose_spec hq

theorem exists_cst_of_dw_eq_zero : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F), K.Rich → ∀ (a : ∀ k, Hol (K.W k)), (∀ k k' (e : K.le 0 k' k), K.sh e (a k) = a k') →
    (∀ k i, dw i (a k) = 0) → ∃ p : Hol F.V, ∀ k, a k = K.cst k p := by
  intro I _ g Λ _ F K hK a ha hd
  obtain ⟨G, hG⟩ := exists_glue_fn K hK a ha
  have ev : ∀ k, ∀ q ∈ K.W k, G =ᶠ[𝓝 q] (a k).fn := fun k q hq ↦ by
    filter_upwards [(K.W k).isOpen.mem_nhds hq] with r hr using hG k r hr
  have an : ∀ q : Tot I g, q.1 ∈ F.V → AnalyticAt ℂ G q := fun q hq ↦ by
    obtain ⟨k, hk⟩ := hK.1 q hq
    exact ((a k).analytic q hk).congr (ev k q hk).symm
  have d0 : ∀ q : Tot I g, q.1 ∈ F.V → ∀ i, fderiv ℂ G q ((0, Pi.single i 1) : Tot I g) = 0 := fun q hq i ↦ by
    obtain ⟨k, hk⟩ := hK.1 q hq
    rw [(ev k q hk).fderiv_eq, ← Hol.fn_der _ _ hk]
    change (dw i (a k)).fn q = 0
    rw [hd, ← Hol.ev_apply q hk, map_zero]
  have cs : ∀ z ∈ F.V, ∀ w, G (z, w) = G (z, 0) := fun z hz w ↦ by
    have hf : ∀ w : Fin g → ℂ, HasFDerivAt (fun w ↦ G (z, w))
        ((fderiv ℂ G (z, w)).comp (ContinuousLinearMap.inr ℂ (I → ℂ) (Fin g → ℂ))) w := fun w ↦
      (an (z, w) hz).differentiableAt.hasFDerivAt.comp w (hasFDerivAt_prodMk_right z w)
    refine is_const_of_fderiv_eq_zero (𝕜 := ℂ) (f := fun w ↦ G (z, w)) (fun w ↦ (hf w).differentiableAt)
      (fun w ↦ ?_) w 0
    rw [(hf w).fderiv]
    ext v
    have hv : ((0, v) : Tot I g) = ∑ i, v i • ((0, Pi.single i 1) : Tot I g) := by
      ext j
      · simp [Prod.fst_sum]
      · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
    change fderiv ℂ G (z, w) (0, v) = 0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hv, map_sum]
    exact Finset.sum_eq_zero fun i _ ↦ by rw [map_smul, d0 (z, w) hz i, smul_zero]
  refine ⟨Hol.mk (fun z ↦ G (z, 0)) fun z hz ↦
    AnalyticAt.comp (g := G) (f := fun z ↦ ((z, 0) : Tot I g)) (an (z, 0) hz)
      (analyticAt_id.prod analyticAt_const), fun k ↦ Hol.ext_fn fun q hq ↦ ?_⟩
  rw [fn_cst _ _ _ hq, ← hG k q hq]
  exact (cs q.1 (K.base k q hq) q.2).trans (Hol.fn_mk (fun z ↦ G (z, 0)) _ (K.base k q hq)).symm

end GlobalTheory.AnPer.Charts
end

