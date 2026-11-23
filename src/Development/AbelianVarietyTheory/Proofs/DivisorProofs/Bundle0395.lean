module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0354
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0339
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TypicalCurveStructureConstants
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0344
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0365
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0360
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0323

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafComplexSemilinearMapCompBijective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.OpComp

theorem ev_comp_ofHom' {R : Type} [CommRing R] {E : Spc} {I K : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n)
    (u : I ⟶ K) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (R := R) (α.comp (Cochain.ofHom u) (add_zero n)) p s h U x =
      Sec.map (u.f s) (ev (R := R) α p s h U x) := by
  simp only [ev, Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  rfl

def invSemi {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J)
    (hb : ∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (ρ.app U s)) : SemiMap J I where
  app U s := (AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm.toAddMonoidHom
  nat g s a := by
    apply (hb _ s).1
    change ρ.app _ s (Sec.res g ((AddEquiv.ofBijective (ρ.app _ s) (hb _ s)).symm a)) =
      ρ.app _ s ((AddEquiv.ofBijective (ρ.app _ s) (hb _ s)).symm (Sec.res g a))
    rw [← ρ.nat]
    have e1 := (AddEquiv.ofBijective (ρ.app _ s) (hb _ s)).apply_symm_apply a
    have e2 := (AddEquiv.ofBijective (ρ.app _ s) (hb _ s)).apply_symm_apply (Sec.res g a)
    simp only [AddEquiv.ofBijective_apply] at e1 e2
    rw [e1, e2]
  comm U s t a := by
    apply (hb U t).1
    change ρ.app U t (Sec.map (I.d s t) ((AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm a)) =
      ρ.app U t ((AddEquiv.ofBijective (ρ.app U t) (hb U t)).symm (Sec.map (J.d s t) a))
    rw [← ρ.comm]
    have e1 := (AddEquiv.ofBijective (ρ.app U s) (hb U s)).apply_symm_apply a
    have e2 := (AddEquiv.ofBijective (ρ.app U t) (hb U t)).apply_symm_apply (Sec.map (J.d s t) a)
    simp only [AddEquiv.ofBijective_apply] at e1 e2
    rw [e1, e2]

theorem invSemi_app {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J)
    (hb : ∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (ρ.app U s)) (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U) :
    (invSemi ρ hb).app U s (ρ.app U s a) = a := by
  change (AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm (AddEquiv.ofBijective (ρ.app U s) (hb U s) a) = a
  exact (AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm_apply_apply a

theorem app_invSemi {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J)
    (hb : ∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (ρ.app U s)) (U : Scheme.{0}) (s : ℤ) (b : Sec (J.X s) U) :
    ρ.app U s ((invSemi ρ hb).app U s b) = b := by
  change AddEquiv.ofBijective (ρ.app U s) (hb U s) ((AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm b) = b
  exact (AddEquiv.ofBijective (ρ.app U s) (hb U s)).apply_symm_apply b

theorem op_comp_bij : ∀ (S R : Type) [CommRing S] [CommRing R] {I : Cx S} {J J' : Cx R} (ρ : SemiMap I J) (ρ' : SemiMap I J') (u : J ⟶ J'), (∀ (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U), ρ'.app U s a = Sec.map (u.f s) (ρ.app U s a)) → (∀ (E : Spc) (n : ℤ) x, ρ'.op.app E n x = cpush _ u n (ρ.op.app E n x)) ∧ ((∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (ρ.app U s)) → ∀ (E : Spc) (n : ℤ), Function.Bijective (ρ.op.app E n)) := by
  intro S R _ _ I J J' ρ ρ' u hu
  refine ⟨fun E n x => ?_, fun hb E n => ?_⟩
  · obtain ⟨α, rfl⟩ := x.mk_surjective
    obtain ⟨β, hβ⟩ := ρ.image_exists E n α
    rw [ρ.op_spec E n α β hβ]
    change _ = CohomologyClass.mk (zcomp β (Cocycle.ofHom u) (add_zero n))
    refine ρ'.op_spec E n α _ (fun p s h U y => ?_)
    change ev (R := R) (β.1.comp (Cochain.ofHom u) (add_zero n)) p s h U y = _
    rw [ev_comp_ofHom', hβ, hu]
  · set σ := invSemi ρ hb
    have h1 : ∀ x, σ.op.app E n (ρ.op.app E n x) = x := by
      intro x
      obtain ⟨α, rfl⟩ := x.mk_surjective
      obtain ⟨β, hβ⟩ := ρ.image_exists E n α
      rw [ρ.op_spec E n α β hβ]
      refine σ.op_spec E n β α (fun p s h U y => ?_)
      rw [hβ, invSemi_app]
    have h2 : ∀ y, ρ.op.app E n (σ.op.app E n y) = y := by
      intro y
      obtain ⟨β, rfl⟩ := y.mk_surjective
      obtain ⟨α, hα⟩ := σ.image_exists E n β
      rw [σ.op_spec E n β α hα]
      refine ρ.op_spec E n α β (fun p s h U y => ?_)
      rw [hα, app_invSemi]
    exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

end GlobalTheory.EtC.OpComp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanDLiftClearDenominators
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.span_D_lift_clear_denominators : ∀ (k K L : Type) [Field k] [CharZero k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] (B : Subalgebra k K) [Algebra.FiniteType k B] (Q : Ideal B), Q.IsPrime → ∀ s : B, s ∈ Q → s ≠ 0 → (∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) → ∀ (m : ℕ) (y : Fin m → B), IsTranscendenceBasis k (fun j => Ideal.Quotient.mk Q (y j)) → ∀ v : B, ∃ r : B, r ∉ Q ∧ ∃ c : Fin (m + 1) → B, algebraMap K L (r : K) • D k L (algebraMap K L (v : K)) = ∑ l, algebraMap K L (c l : K) • (Fin.cons (D k L (algebraMap K L (s : K))) (fun j => D k L (algebraMap K L (y j : K))) : Fin (m + 1) → Ω[L⁄k]) l := by
  intro k K L _ _ _ _ _ _ _ _ B _ Q hQ s hsQ hs0 hgen m y hy v
  classical
  let R := Localization.AtPrime Q
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  haveI : IsNoetherianRing R := IsLocalization.isNoetherianRing Q.primeCompl R inferInstance
  have hinj : Function.Injective (algebraMap B R) :=
    IsLocalization.injective R Q.primeCompl_le_nonZeroDivisors
  have hmax : IsLocalRing.maximalIdeal R = Ideal.span {algebraMap B R s} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro z hz
      obtain ⟨c, r, hr, hrc⟩ := hgen z hz
      rw [Ideal.mem_comap, Ideal.mem_span_singleton']
      refine ⟨IsLocalization.mk' R c (⟨r, hr⟩ : Q.primeCompl), ?_⟩
      have hu := IsLocalization.map_units R (⟨r, hr⟩ : Q.primeCompl)
      apply hu.mul_left_cancel
      rw [← mul_assoc, IsLocalization.mk'_spec', ← map_mul, ← map_mul]
      exact congrArg _ hrc.symm
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem _ hsQ
  have hs0' : algebraMap B R s ≠ 0 := fun h => hs0 (hinj (by rw [h, map_zero]))
  have hnf : ¬ IsField R := by
    intro hf
    have h1 := IsLocalRing.isField_iff_maximalIdeal_eq.1 hf
    rw [hmax, Ideal.span_singleton_eq_bot] at h1
    exact hs0' h1
  have hprin : Submodule.IsPrincipal (IsLocalRing.maximalIdeal R) := ⟨⟨_, hmax⟩⟩
  haveI : IsDiscreteValuationRing R := ((IsDiscreteValuationRing.TFAE R hnf).out 1 5).2 hprin
  have hirr : Irreducible (algebraMap B R s) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmax
  haveI : IsDomain (B ⧸ Q) := Ideal.Quotient.isDomain Q
  haveI : Nontrivial (B ⧸ Q) := IsDomain.toNontrivial
  haveI : Algebra.IsAlgebraic (B ⧸ Q) Q.ResidueField :=
    IsLocalization.isAlgebraic (R := B ⧸ Q) (S := Q.ResidueField) (M := nonZeroDivisors (B ⧸ Q))
  haveI : FaithfulSMul (B ⧸ Q) Q.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective _ _)
  have htb : IsTranscendenceBasis k (fun j => IsLocalRing.residue R (algebraMap B R (y j))) := by
    have h2 := hy.algebraMap_comp (A := Q.ResidueField)
    convert h2 using 1
    rfl
  have hspan := GlobalTheory.span_D_uniformizer_transcendenceBasis k R (algebraMap B R s) hirr m
    (fun j => algebraMap B R (y j)) htb
  have hunit : ∀ z : Q.primeCompl, IsUnit (algebraMap B K z) := fun z => by
    refine isUnit_iff_ne_zero.2 fun h => z.2 ?_
    have hz : (z : B) = 0 := Subtype.ext h
    rw [hz]; exact Q.zero_mem
  let ψ : R →+* K := IsLocalization.lift hunit
  letI : Algebra R L := ((algebraMap K L).comp ψ).toAlgebra
  have hRL : ∀ x : B, algebraMap R L (algebraMap B R x) = algebraMap K L (x : K) := fun x => by
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, IsLocalization.lift_eq]
    rfl
  haveI : IsScalarTower k R L := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply k B R, hRL, IsScalarTower.algebraMap_apply k K L]
    rfl
  haveI : SMulCommClass k R L := inferInstance
  let Φ := KaehlerDifferential.map k k R L
  let g : Fin (m + 1) → Ω[R⁄k] := Fin.cons (D k R (algebraMap B R s)) (fun j => D k R (algebraMap B R (y j)))
  have hDv : D k R (algebraMap B R v) ∈ Submodule.span R (Set.range g) := by
    rw [Fin.range_cons, hspan]; exact Submodule.mem_top
  obtain ⟨c', hc'⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hDv
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples Q.primeCompl (Finset.univ : Finset (Fin (m + 1))) c'
  have hb' : ∀ l, ∃ x : B, algebraMap B R x = algebraMap B R (b : B) * c' l := fun l => by
    obtain ⟨x, hx⟩ := hb l (Finset.mem_univ l)
    exact ⟨x, by rw [hx, Algebra.smul_def]⟩
  choose c hc using hb'
  have hΦD : ∀ x : B, Φ (D k R (algebraMap B R x)) = D k L (algebraMap K L (x : K)) := fun x => by
    rw [KaehlerDifferential.map_D, hRL]
  have hΦg : ∀ l, Φ (g l) = (Fin.cons (D k L (algebraMap K L (s : K))) (fun j => D k L (algebraMap K L (y j : K))) : Fin (m + 1) → Ω[L⁄k]) l := by
    intro l
    refine Fin.cases ?_ (fun j => ?_) l
    · simp only [g, Fin.cons_zero]; exact hΦD s
    · simp only [g, Fin.cons_succ]; exact hΦD (y j)
  refine ⟨b, b.2, c, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hRL, ← hΦD, algebraMap_smul, ← map_smul, ← hc', Finset.smul_sum, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← hRL, ← hΦg, algebraMap_smul L (algebraMap B R (c l)) (Φ (g l)), ← map_smul Φ]
  congr 1
  rw [hc, mul_smul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanTangentOfType
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.DepthStages

namespace GlobalTheory

theorem span_tangent_of_type : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (p d h : ℕ) (ty : Fin d → ZMod h)
    (G : LogFGL v d) (γ : Fin d → Fin d → PowerSeries C), IsBasis G p ty γ →
    ∀ (t : ZMod h) (w : Fin d → C), (∀ c, ty c ≠ t → w c = 0) →
      w ∈ Submodule.span C (Set.range fun b : {b // ty b = t} => tangent (γ b.1)) := by
  intro C _ v p d h ty G γ hB t w hw
  obtain ⟨hγ, hγty, hdet⟩ := hB
  have hdet' : v (PTb.tmat γ).det = 0 := hdet
  have ht : ∀ b c, ty c ≠ ty b → tangent (γ b) c = 0 := by
    intro b c hc
    rw [PTb.tangent_eq_lc_zero G p (fun e => (hγ b e).1)]
    exact (hγty b).2 0 c (by simpa using hc)
  set x : Fin d → C := Matrix.vecMul w (PTb.tmat γ)⁻¹ with hx
  have hxw : Matrix.vecMul x (PTb.tmat γ) = w := PTb.vecMul_inv_tmat hdet' w
  have hsupp : ∀ b, ty b ≠ t → x b = 0 :=
    PTb.vecMul_tmat_support ty hdet' ht x t (fun c hc => by rw [hxw]; exact hw c hc)
  have hsum : w = ∑ b, x b • tangent (γ b) := by rw [PTb.sum_smul_tangent, hxw]
  rw [hsum]
  refine Submodule.sum_mem _ fun b _ => ?_
  by_cases hb : ty b = t
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨b, hb⟩, rfl⟩)
  · rw [hsupp b hb, zero_smul]; exact Submodule.zero_mem _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareZeroLocalLiftsCorrectedAgreeOnOverlaps
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SecGlue

theorem lifts_corrected_agree_on_overlaps : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (κ : Type) [Finite κ] (f : κ → R), Ideal.span (Set.range f) = ⊤ → ∀ V : κ → X.left.Opens, (∀ k, IsAffineOpen (V k)) →
    (∀ k, GlobalTheory.SecLift.LiftIn π X g₀ (f k) (V k)) →
    ∃ e : ∀ k, Sp (Localization.Away (f k)) ⟶ X.left,
      (∀ k, e k ≫ X.hom = spMap (algebraMap R (Localization.Away (f k)))) ∧
      (∀ k, spMap (Localization.awayMap π (f k)) ≫ e k = spMap (algebraMap R₀ (Localization.Away (π (f k)))) ≫ g₀) ∧
      ∀ j k, spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f k)) (f j) (f k)) ≫ e j =
        spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f k)) (f k) (f j)) ≫ e k := by
  intro R R₀ _ _ π hπ hI X hX g₀ hg₀ κ _ f hf V hV hL
  classical
  have : Fintype κ := Fintype.ofFinite κ
  choose e he1 he2 he3 using hL
  choose N₀ hN₀ using fun k j => GlobalTheory.T.exists_squareZeroLift_basicOpen_pair_agree R R₀ π hπ hI X hX g₀ hg₀ (f j) (f k) (V j) (hV j) (e j) (he1 j) (he2 j) (he3 j) (e k) (he1 k) (he2 k)
  have hN : ∀ k j, N₀ k j ≤ Finset.univ.sup (fun p : κ × κ => N₀ p.1 p.2) := fun k j =>
    Finset.le_sup (f := fun p : κ × κ => N₀ p.1 p.2) (Finset.mem_univ (k, j))
  choose t ht1 ht2 ht3 ht4 using fun k j => hN₀ k j _ (hN k j)
  choose n s W hs hW hWl using fun j l => _root_.GlobalTheory.SecGlue.exists_basicOpen_cover_affine _ _ (spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ e j)
  obtain ⟨M, t', h1, h2, h3, h4⟩ := GlobalTheory.T.exists_pow_cocycle_alt R R₀ π hπ hI X hX g₀ hg₀ κ f V hV e he1 he2 he3 _ t ht1 ht2 ht3 ht4 n s W hs hW hWl
  exact GlobalTheory.T.exists_lifts_agree_of_cocycle_alt R R₀ π hπ hI X g₀ hg₀ κ f hf V hV e he1 he2 he3 _ t' h1 h2 h3 n s W hs hW hWl h4

end GlobalTheory.SecGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAffineOpenRingPolynomialEquiv
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

namespace GlobalTheory.PD


set_option autoImplicit false in
open KaehlerDifferential in
theorem _root_.GlobalTheory.PD.rA_single_polyEquiv : ∀ (k : Type) [Field k] (F : Type) [Field F]
    [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F), _root_.GlobalTheory.PD.IsPd k x →
    ∀ i : Fin (d + 1), ∃ e : MvPolynomial (Fin d) k ≃ₐ[k] _root_.GlobalTheory.PD.rA k x {i},
      ∀ j, (e (MvPolynomial.X j) : F) = x (i.succAbove j) / x i := by
  intro k _ F _ _ d x hP i
  refine ⟨_root_.GlobalTheory.PD.Model.chartEquiv k x hP i, fun j => ?_⟩
  simp [_root_.GlobalTheory.PD.Model.chartEquiv, _root_.GlobalTheory.PD.Model.yc,
    AlgebraicIndependent.aevalEquiv_apply_coe]

end GlobalTheory.PD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardOpenCoordinateRingIsFractionRingIsNoetheStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing : ∀ (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F), IsPd k x → ∀ I : Finset (Fin (d + 1)), I.Nonempty → IsFractionRing (rA k x I) F ∧ IsNoetherianRing (rA k x I) := by
  first | (exact @GlobalTheory.PD.rA_isFractionRing_isNoetherianRing) | (exact GlobalTheory.PD.rA_isFractionRing_isNoetherianRing) | (intros; apply GlobalTheory.PD.rA_isFractionRing_isNoetherianRing  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistModuleFreeAndGeneratorSummand
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.TwFree

variable (q : ℕ) [NeZero q] (A : Type) [CommRing A]

theorem pow_val_mul (ζ : Prim q A) (a b : (ZMod q)ˣ) :
    (ζ.1 ^ (a : ZMod q).val) ^ (b : ZMod q).val = ζ.1 ^ ((a * b : (ZMod q)ˣ) : ZMod q).val := by
  rw [← pow_mul, Units.val_mul, ZMod.val_mul, ← pow_eq_pow_mod _ ((GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties q A).1 ζ)]

theorem pow_val_one (ζ : Prim q A) : ζ.1 ^ ((1 : (ZMod q)ˣ) : ZMod q).val = ζ.1 := by
  rw [Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ ((GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties q A).1 ζ), pow_one]

def orbRel : Setoid (Prim q A) where
  r ζ ξ := ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val
  iseqv :=
    { refl := fun ζ => ⟨1, (pow_val_one q A ζ).symm⟩
      symm := fun {ζ ξ} ⟨a, h⟩ => ⟨a⁻¹, by rw [h, pow_val_mul, mul_inv_cancel, pow_val_one]⟩
      trans := fun {ζ ξ η} ⟨a, h⟩ ⟨b, h'⟩ => ⟨a * b, by rw [h', h, pow_val_mul]⟩ }

abbrev Orb := Quotient (orbRel q A)

abbrev orb (ζ : Prim q A) : Orb q A := Quotient.mk (orbRel q A) ζ

def rep (O : Orb q A) : Prim q A := Quotient.out O

theorem exists_coef (ζ : Prim q A) : ∃ a : (ZMod q)ˣ, ζ.1 = (rep q A (orb q A ζ)).1 ^ (a : ZMod q).val :=
  Quotient.exact (Quotient.out_eq (orb q A ζ))

def coef (ζ : Prim q A) : (ZMod q)ˣ := (exists_coef q A ζ).choose

theorem coef_spec (ζ : Prim q A) : ζ.1 = (rep q A (orb q A ζ)).1 ^ (coef q A ζ : ZMod q).val :=
  (exists_coef q A ζ).choose_spec

variable [Nontrivial A]

theorem units_eq_of_pow (r : Prim q A) (a b : (ZMod q)ˣ)
    (h : r.1 ^ (a : ZMod q).val = r.1 ^ (b : ZMod q).val) : a = b := by
  by_contra hne
  have hm : ¬ (a : ZMod q).val ≡ (b : ZMod q).val [MOD q] := by
    intro hm
    apply hne
    apply Units.ext
    apply ZMod.val_injective
    rw [Nat.ModEq, Nat.mod_eq_of_lt (ZMod.val_lt _), Nat.mod_eq_of_lt (ZMod.val_lt _)] at hm
    exact hm
  have hu := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties q A).2.2.1 r _ _ hm
  rw [h, sub_self] at hu
  exact not_isUnit_zero hu

theorem orb_coef_of_pow (ζ ξ : Prim q A) (a : (ZMod q)ˣ) (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    orb q A ξ = orb q A ζ ∧ coef q A ξ = coef q A ζ * a := by
  have ho : orb q A ξ = orb q A ζ := (Quotient.sound (s := orbRel q A) (a := ζ) (b := ξ) ⟨a, h⟩).symm
  refine ⟨ho, units_eq_of_pow q A (rep q A (orb q A ξ)) _ _ ?_⟩
  rw [← coef_spec, h, coef_spec q A ζ, pow_val_mul, ho]

theorem orb_coef_rep (O : Orb q A) : orb q A (rep q A O) = O ∧ coef q A (rep q A O) = 1 := by
  have ho : orb q A (rep q A O) = O := Quotient.out_eq O
  refine ⟨ho, units_eq_of_pow q A (rep q A O) _ _ ?_⟩
  have h := coef_spec q A (rep q A O)
  rw [ho] at h
  rw [← h, pow_val_one]

variable (i : ℤ)

def coordMap : (Prim q A →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] (Orb q A →₀ ULift.{1} (ZMod q)) :=
  Finsupp.linearCombination _ (fun ζ => Finsupp.single (orb q A ζ) (ULift.up ((coef q A ζ ^ i : (ZMod q)ˣ) : ZMod q)))

theorem twRel_le_ker : twRel q i A ≤ LinearMap.ker (coordMap q A i) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨ζ, ξ, a, h, rfl⟩
  obtain ⟨ho, hc⟩ := orb_coef_of_pow q A ζ ξ a h
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, coordMap, Finsupp.linearCombination_single,
    Finsupp.smul_single, smul_eq_mul, one_mul, ho, hc, sub_eq_zero]
  congr 1
  apply ULift.ext
  simp [mul_zpow, mul_comm]

def coordQ : ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) →ₗ[ULift.{1} (ZMod q)] (Orb q A →₀ ULift.{1} (ZMod q)) :=
  (twRel q i A).liftQ (coordMap q A i) (twRel_le_ker q A i)

def basisMap : (Orb q A →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) :=
  Finsupp.linearCombination _ (fun O => Submodule.Quotient.mk (Finsupp.single (rep q A O) 1))

theorem coordQ_mk_single (ζ : Prim q A) :
    coordQ q A i (Submodule.Quotient.mk (Finsupp.single ζ 1)) =
      Finsupp.single (orb q A ζ) (ULift.up ((coef q A ζ ^ i : (ZMod q)ˣ) : ZMod q)) := by
  simp [coordQ, coordMap, Finsupp.linearCombination_single]

def twEquiv : ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) ≃ₗ[ULift.{1} (ZMod q)] (Orb q A →₀ ULift.{1} (ZMod q)) :=
  LinearEquiv.ofLinear (coordQ q A i) (basisMap q A i)
    (by
      refine Finsupp.lhom_ext' fun O => LinearMap.ext_ring ?_
      obtain ⟨ho, hc⟩ := orb_coef_rep q A O
      simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply, basisMap,
        Finsupp.linearCombination_single, one_smul, coordQ_mk_single, ho, hc, one_zpow, LinearMap.id_coe, id_eq]
      rfl)
    (by
      refine Submodule.linearMap_qext _ (Finsupp.lhom_ext' fun ζ => LinearMap.ext_ring ?_)
      simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply, Submodule.mkQ_apply,
        coordQ_mk_single, basisMap, Finsupp.linearCombination_single, LinearMap.id_coe, id_eq]
      rw [← Submodule.Quotient.mk_smul, Finsupp.smul_single, smul_eq_mul, mul_one, eq_comm,
        Submodule.Quotient.eq]
      exact Submodule.subset_span ⟨rep q A (orb q A ζ), ζ, coef q A ζ, coef_spec q A ζ, rfl⟩)

theorem twist_free : ∀ (q : ℕ) [NeZero q] (i : ℤ) (A : Type) [CommRing A] [Nontrivial A],
    Module.Free (ULift.{1} (ZMod q)) ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) ∧
    ∀ ζ : Prim q A, ∃ f : ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q),
      f (Submodule.Quotient.mk (Finsupp.single ζ 1)) = 1 := by
  intro q _ i A _ _
  refine ⟨Module.Free.of_equiv (twEquiv q A i).symm, fun ζ => ?_⟩
  refine ⟨ULift.up (((coef q A ζ ^ i)⁻¹ : (ZMod q)ˣ) : ZMod q) •
    (Finsupp.lapply (orb q A ζ) ∘ₗ coordQ q A i), ?_⟩
  rw [LinearMap.smul_apply, LinearMap.comp_apply, coordQ_mk_single, Finsupp.lapply_apply,
    Finsupp.single_eq_same, smul_eq_mul]
  apply ULift.ext
  simp

end GlobalTheory.TwFree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFibreDimQuotientPDivGroupLevel
section
open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

namespace GlobalTheory.TorsDim

theorem fibreDim_quot_torsionIdeal : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (k m : ℕ), 1 ≤ k → ∀ (B : Type) [CommRing B] [HopfAlgebra O B] [IsCocomm O B] [Module.Finite O B] [Module.Projective O B] (j : B →ₐc[O] G.A (k + m)) (ρ : G.A (k + m) →ₗ[O] B), (∀ b, ρ (j b) = b) → torsionIdeal (R := O) (A := G.A (k + m)) p ≤ kerIdeal j → ∀ q : PrimeSpectrum O, fibreDim (B ⧸ torsionIdeal (R := O) (A := B) (p ^ m)) q = p ^ (m * G.height) := by
  intro p _ O _ G k m hk B _ _ _ _ _ j ρ hρ hj q
  have hmulPow := G.exists_mulPow_fibreRank_eq p O k m
  obtain ⟨r, μ, hr, hker, hμ, hμq⟩ := hmulPow
  have hjq : fibreRank (j : B →ₐ[O] G.A (k + m)).toLinearMap q = fibreDim B q :=
    (_root_.GlobalTheory.FibreRanks.fibre_ranks O B (G.A (k + m)) (G.A (k + m)) (j : B →ₐ[O] G.A (k + m)).toLinearMap).1 ρ hρ q
  have h1 := fibreDim_eq_ker_mul_range j q
  rw [hjq, G.fibreDim_eq] at h1
  have h2 := fibreDim_eq_ker_mul_range (r.comp j) q
  rw [G.fibreDim_eq] at h2
  have hle : RingHom.ker r ≤ kerIdeal j := by
    rw [hker]
    exact (torsionIdeal_le_of_dvd (dvd_pow_self p (by omega))).trans (by simpa using hj)
  let J : Ideal (G.A k) := kerIdeal (r.comp j)
  let φ : G.A (k + m) →ₐ[O] G.A k ⧸ J := (Ideal.Quotient.mkₐ O J).comp (r : G.A (k + m) →ₐ[O] G.A k)
  have hφ : Function.Surjective φ := (Ideal.Quotient.mkₐ_surjective O J).comp hr
  have hkerφ : RingHom.ker φ = kerIdeal j := by
    have h5 : RingHom.ker φ = J.comap (r : G.A (k + m) →ₐ[O] G.A k) := by
      ext a
      simp [φ, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
    rw [h5, show J = Ideal.map (r : G.A (k + m) →ₐ[O] G.A k) (kerIdeal j) from kerIdeal_comp r j,
      Ideal.comap_map_of_surjective (r : G.A (k + m) →ₐ[O] G.A k) hr, sup_eq_left]
    exact fun a ha => hle ha
  let e : (G.A (k + m) ⧸ kerIdeal j) ≃ₗ[O] (G.A k ⧸ J) :=
    ((Ideal.quotientEquivAlgOfEq O hkerφ).symm.trans (Ideal.quotientKerAlgEquivOfSurjective hφ)).toLinearEquiv
  rw [← fibreDim_congr e q] at h2
  have h3 := fibreDim_eq_ker_mul_range (mulBy O B (p ^ m)) q
  have hlin : (j : B →ₐ[O] G.A (k + m)).toLinearMap ∘ₗ (mulBy O B (p ^ m) : B →ₐ[O] B).toLinearMap =
      (μ : G.A k →ₐ[O] G.A (k + m)).toLinearMap ∘ₗ ((r.comp j) : B →ₐ[O] G.A k).toLinearMap := by
    ext b
    change j (mulBy O B (p ^ m) b) = μ (r (j b))
    rw [map_mulBy, hμ]
  have h4 : fibreRank (mulBy O B (p ^ m) : B →ₐ[O] B).toLinearMap q =
      fibreRank ((r.comp j) : B →ₐ[O] G.A k).toLinearMap q := by
    rw [← (_root_.GlobalTheory.FibreRanks.fibre_ranks O B B (G.A (k + m)) _).2.1 _ q hjq, hlin,
      (_root_.GlobalTheory.FibreRanks.fibre_ranks O B (G.A k) (G.A (k + m)) _).2.1 _ q (hμq q)]
  change fibreDim (B ⧸ kerIdeal (mulBy O B (p ^ m))) q = _
  rw [h4] at h3
  have hp : 0 < p ^ (k * G.height) := pow_pos (Fact.out : p.Prime).pos _
  have h6 : p ^ ((k + m) * G.height) = p ^ (m * G.height) * p ^ (k * G.height) := by
    rw [← pow_add]; congr 1; ring
  refine (Nat.eq_of_mul_eq_mul_right hp ?_).symm
  rw [← h6, h1, h3, h2]
  ring

end GlobalTheory.TorsDim
end

