module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Formalism.LocalToGlobal.LatticeGeometry.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsRootNear
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0033

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmoothForms.RealPts

theorem infEmb_unique {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (τ : E →+* ℂ) (θ θ' : Ainf F ⊗[F] E →+* ℂ) (h : IsInfEmb τ θ) (h' : IsInfEmb τ θ') :
    θ = θ' :=
  by apply _root_.UpperTheory.Reformulated.B.Qh26.isInfEmb_unique <;> assumption

theorem tauE_injective (D : D7) : Function.Injective (tauE D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem tauE_cm (D : D7) (σ : D.host.E →+* ℂ) :
    (∃ τ, tauE D τ = σ) ↔ ¬ ∃ τ, tauE D τ = ComplexEmbedding.conjugate σ := by
  obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 σ
  have hc : ComplexEmbedding.conjugate (D.host.emb g) = D.host.emb (g * D.R.cc) := by
    rw [Formalism.L2.Geo.emb_mul_cc_comp]
    refine RingHom.ext fun x => ?_
    have hcm := D.host.isCMField_hostE
    have h : IsCMField.complexConj D.host.E x = D.host.conj x := by
      apply D.host.φ₀.injective
      rw [IsCMField.complexEmbedding_complexConj]
      exact (D.host.toHostAx.conjE_apply _ x).symm
    show starRingEnd ℂ (D.host.emb g x) = D.host.emb g (D.host.conj x)
    rw [← h, IsCMField.complexEmbedding_complexConj]
  have h : ∀ g, (∃ τ, tauE D τ = D.host.emb g) ↔ g ∈ D.R.Psi := fun g => by
    rw [← Formalism.L2.Geo.exists_tauEmb_iff D g]
    exact exists_congr fun τ => eq_comm
  rw [hc, h, h]
  exact Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g

theorem gramAt_herm {D : D7} (V : HSp D) (τ : D.what₂.Tau) : (gramAt D V τ)ᴴ = gramAt D V τ := by
  ext i j
  have hcm := D.host.isCMField_hostE
  have h1 : star (V.hT (V.frame j) (V.frame i)) = V.hT (V.frame i) (V.frame j) := V.herm.eq _ _
  simp only [conjTranspose_apply, gramAt, map_apply, HSpace.gram]
  rw [← h1]
  exact (IsCMField.complexEmbedding_complexConj _ (tauE D τ) _).symm

theorem gramAt_unit {D : D7} (V : HSp D) (τ : D.what₂.Tau) : IsUnit (gramAt D V τ).det := by
  have : (gramAt D V τ).det = tauE D τ V.gram.det := (RingHom.map_det _ _).symm
  rw [this, isUnit_iff_ne_zero]
  exact (map_ne_zero _).2 (GlobalTheory.UnitaryGlue.gram_det_ne_zero V)

theorem infMat_eq {D : D7} (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (g : GA D V) :
    infMat D.sp.cm.sig V.gram θ g = (infHom V g).1.map θ := rfl

theorem finMat_eq {D : D7} (V : HSp D) (g : GA D V) :
    finMat D.sp.cm.sig V.gram g = (finHom V g).1 := rfl

theorem glue {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ) (V : HSp D) :
    (∀ g : GA D V, (∀ τ, infMat D.sp.cm.sig V.gram (θ τ) g = 1) → g ∈ GfC V) ∧
    ∀ u : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, u τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) →
      ∃ g ∈ GinfC V, ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) g = u τ := by
  classical
  let Ψ : Finset (D.host.E →+* ℂ) := Finset.univ.image (tauE D)
  have hm : ∀ σ, σ ∈ Ψ ↔ ∃ τ, tauE D τ = σ := fun σ => by simp [Ψ]
  choose s hs using fun σ : Ψ => (hm σ.1).1 σ.2
  have hst : ∀ τ, s ⟨tauE D τ, (hm _).2 ⟨τ, rfl⟩⟩ = τ := fun τ => tauE_injective D (hs _)
  obtain ⟨h1, -, -, h4⟩ := (GlobalTheory.UnitaryGlue.adelic_glue D V).2 Ψ (fun σ => θ (s σ))
    (fun σ => by rw [hm, hm]; exact tauE_cm D σ) (fun σ => by rw [← hs σ]; exact hθ (s σ))
  refine ⟨fun g hg => h1 g fun σ => hg (s σ), fun u hu => ?_⟩
  obtain ⟨h, hh, hhu⟩ := h4 (fun σ => u (s σ)) (fun σ => by rw [← hs σ]; exact hu (s σ))
  refine ⟨h, hh, fun τ => ?_⟩
  have := hhu ⟨tauE D τ, (hm _).2 ⟨τ, rfl⟩⟩
  simp only [hst] at this
  exact this

theorem realPoints : ∀ D : D7, (∀ θ θ' : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), IsInfFam θ → IsInfFam θ' → θ = θ') ∧ ∀ θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), IsInfFam θ → ∀ V : HSp D, RealPoints θ V := by
  intro D
  refine ⟨fun θ θ' h h' => funext fun ρ => infEmb_unique _ _ _ (h ρ) (h' ρ), fun θ hθ V => ?_⟩
  obtain ⟨g1, g2⟩ := glue θ hθ V
  obtain ⟨s1, s2, s3, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D V
  have hmul : ∀ g g' τ, infMat D.sp.cm.sig V.gram (θ τ) (g * g') =
      infMat D.sp.cm.sig V.gram (θ τ) g * infMat D.sp.cm.sig V.gram (θ τ) g' := fun g g' τ => by
    rw [infMat_eq V, infMat_eq V, infMat_eq V, map_mul, Units.val_mul, Matrix.map_mul]
  have hfin : ∀ k ∈ GfC V, ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) k = 1 := fun k hk τ => by
    have hk' : infHom V k = 1 := hk
    rw [infMat_eq V, hk', Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨fun τ => ⟨gramAt_herm V τ, gramAt_unit V τ⟩, g2, fun g hg g' hg' h => ?_, hmul, hfin, s2,
    fun g => ?_, fun g a ha => ?_⟩
  · refine mul_inv_eq_one.1 (s3 _ (mul_mem hg (inv_mem hg')) (g1 _ fun τ => ?_))
    rw [hmul, h, ← hmul, mul_inv_cancel, hfin 1 (one_mem _)]
  · obtain ⟨a, ha, k, hk, e⟩ := s1 g
    exact ⟨k, hk, a, ha, e.trans (s2 a ha k hk)⟩
  · have ha' : finHom V a = 1 := ha
    rw [finMat_eq V, finMat_eq V, map_mul, ha', mul_one]

end GlobalTheory.SmoothForms.RealPts

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCoeffDeltaOKOfCover
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem exists_coeff_deltaOK_of_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0) (p : ℕ) (I : Ideal (𝓞 E)), CoverOK d p I → RootOK d → (∃ ψ, ψ ≠ 1 ∧ d.PsiTie ψ) → ∃ φ : ∀ n, (Fin n → LevQ Dw d.l₂) → c.F, ∀ n, DeltaOK (GlobalTheory.FormTies.withCoeff d (φ n)) p I := by
  intro E _ _ _ H Dw l Xo c d p I hc hr ⟨ψ, hψ, ht⟩
  have key : ∀ n, ∃ φ : (Fin n → LevQ Dw d.l₂) → c.F, DeltaOK (GlobalTheory.FormTies.withCoeff d φ) p I := by
    intro n
    by_cases hn : Dw.p + Dw.q ≤ n
    · obtain ⟨φ, ph, x₀, h⟩ := GlobalTheory.exists_phiPin_of_character E H Dw l Xo c n
        (GlobalTheory.FormTies.withCoeff d (0 : (Fin n → LevQ Dw d.l₂) → c.F)) hc.2.2.1 hn ψ
      exact ⟨φ, hc, hr, fun _ => ⟨ph, ψ, x₀, hψ, h, ht⟩⟩
    · exact ⟨0, hc, hr, fun h => absurd h hn⟩
  choose φ hφ using key
  exact ⟨φ, hφ⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.PowClassNumberIntegral
section
noncomputable section

namespace GlobalTheory.NormOneChar

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.CharFin
open scoped TensorProduct nonZeroDivisors

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def diag : E →+* RA F E :=
  (Algebra.TensorProduct.includeRight (R := F) (A := FiniteAdeleRing (𝓞 F) F) (B := E)).toRingHom

omit [NumberField E] in
theorem diag_apply (a : E) : diag F E a = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] a := rfl

def diagInt : 𝓞 E →+* hatRing F E :=
  ((diag F E).comp (algebraMap (𝓞 E) E)).codRestrict _ fun x => one_tmul_mem_adelicCompletionOfElementSet F ⟨x, rfl⟩

theorem exists_denom (z : RA F E) : ∃ N : ℕ, 0 < N ∧ (N : RA F E) * z ∈ hatRing F E := by
  obtain ⟨x, h, hh, rfl⟩ := GlobalTheory.AdIdem.exists_eq_one_tmul_add F E z
  obtain ⟨N, hN, hx⟩ := GlobalTheory.AdIdem.exists_nat_mul_integral E x
  refine ⟨N, hN, ?_⟩
  rw [mul_add]
  refine add_mem ?_ (mul_mem (natCast_mem _ N) hh)
  have := one_tmul_mem_adelicCompletionOfElementSet F hx
  rw [← diag_apply, map_mul, map_natCast] at this
  exact this

omit [NumberField E] in
theorem isUnit_diag {a : E} (ha : a ≠ 0) : IsUnit (diag F E a) := (IsUnit.mk0 a ha).map _

theorem isUnit_nat {N : ℕ} (hN : 0 < N) : IsUnit (N : RA F E) := by
  have := isUnit_diag F E (a := (N : E)) (by exact_mod_cast hN.ne')
  rwa [map_natCast] at this

theorem pow_classNumber_integral (x : hatRing F E) (hx : IsUnit (x : RA F E)) :
    ∃ b : 𝓞 E, b ≠ 0 ∧ ∃ s t : hatRing F E, x ^ classNumber E = diagInt F E b * s ∧ s * t = 1 := by
  obtain ⟨u, hu⟩ := hx
  obtain ⟨M, hM, hMu⟩ := exists_denom F E (u⁻¹ : (RA F E)ˣ)
  let I : Ideal (𝓞 E) := (Ideal.span {x}).comap (diagInt F E)
  have hMx : (M : hatRing F E) ∈ Ideal.span {x} := by
    rw [Ideal.mem_span_singleton]
    refine ⟨⟨_, hMu⟩, Subtype.ext ?_⟩
    simp only [← hu, Subring.coe_natCast, Subring.coe_mul]
    rw [mul_left_comm, Units.mul_inv, mul_one]
  have hMI : (M : 𝓞 E) ∈ I := by
    rw [Ideal.mem_comap, map_natCast]; exact hMx
  have hI : I.map (diagInt F E) = Ideal.span {x} := by
    refine le_antisymm Ideal.map_comap_le ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    obtain ⟨a, w, hw, e⟩ := exists_int_add_nsmul F E M hM x x.2
    have e' : x = diagInt F E a + (M : hatRing F E) * ⟨w, hw⟩ := by
      apply Subtype.ext
      rw [e, nsmul_eq_mul]; simp; rfl
    have ha : a ∈ I := by
      rw [Ideal.mem_comap, ← sub_eq_iff_eq_add.2 e']
      exact sub_mem (Ideal.mem_span_singleton_self _) (Ideal.mul_mem_right _ _ hMx)
    have hM' := Ideal.mem_map_of_mem (diagInt F E) hMI
    rw [map_natCast] at hM'
    rw [SetLike.mem_coe, e']
    exact add_mem (Ideal.mem_map_of_mem _ ha) (Ideal.mul_mem_right _ _ hM')
  have hI0 : I ∈ (Ideal (𝓞 E))⁰ := by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro h
    rw [h] at hMI
    exact (Nat.cast_ne_zero.2 hM.ne') (Ideal.mem_bot.1 hMI)
  have hp : (I ^ classNumber E).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff (pow_mem hI0 _)]
    have : (⟨I ^ classNumber E, pow_mem hI0 _⟩ : (Ideal (𝓞 E))⁰) = ⟨I, hI0⟩ ^ classNumber E := rfl
    rw [this, map_pow]
    exact pow_card_eq_one
  obtain ⟨b, hb⟩ := hp
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact mem_nonZeroDivisors_iff_ne_zero.1 (pow_mem hI0 (classNumber E)) (by rw [hb]; simp)
  have h3 : Ideal.span {x ^ classNumber E} = Ideal.span {diagInt F E b} := by
    rw [← Ideal.span_singleton_pow, ← hI, ← Ideal.map_pow, hb, Ideal.submodule_span_eq, Ideal.map_span,
      Set.image_singleton]
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.1 (h3 ▸ Ideal.mem_span_singleton_self (x ^ classNumber E))
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.1 (h3.symm ▸ Ideal.mem_span_singleton_self (diagInt F E b))
  refine ⟨b, hb0, s, t, hs, Subtype.ext ?_⟩
  have hx' : IsUnit ((x ^ classNumber E : hatRing F E) : RA F E) := by
    rw [SubmonoidClass.coe_pow, ← hu]; exact u.isUnit.pow _
  apply hx'.mul_left_cancel
  have : x ^ classNumber E * (s * t) = x ^ classNumber E * 1 := by
    linear_combination (-s) * ht - hs
  exact congrArg Subtype.val this

theorem pow_classNumber (x : (RA F E)ˣ) : ∃ b : E, b ≠ 0 ∧ ∃ s t : hatRing F E,
    (x : RA F E) ^ classNumber E = diag F E b * s ∧ s * t = 1 := by
  obtain ⟨N, hN, hx⟩ := exists_denom F E x
  obtain ⟨b, hb, s, t, e, hst⟩ := pow_classNumber_integral F E ⟨_, hx⟩ ((isUnit_nat F E hN).mul x.isUnit)
  have hN' : (N : E) ^ classNumber E ≠ 0 := pow_ne_zero _ (by exact_mod_cast hN.ne')
  refine ⟨(b : E) / (N : E) ^ classNumber E, div_ne_zero (by simpa using hb) hN', s, t, ?_, hst⟩
  apply (isUnit_diag F E hN').mul_left_cancel
  rw [← mul_assoc, ← map_mul, mul_div_cancel₀ _ hN', map_pow, map_natCast, ← mul_pow]
  exact congrArg Subtype.val e


variable {F E} (c : E ≃ₐ[F] E)

abbrev bar : RA F E →ₐ[F] RA F E := sg (FiniteAdeleRing (𝓞 F) F) c

omit [NumberField E] in
theorem bar_tmul (a : FiniteAdeleRing (𝓞 F) F) (y : E) : bar c (a ⊗ₜ[F] y) = a ⊗ₜ[F] c y := rfl

omit [NumberField E] in
theorem bar_bar (hc : ∀ y, c (c y) = y) (z : RA F E) : bar c (bar c z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => rw [bar_tmul, bar_tmul, hc]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

omit [NumberField E] in
theorem bar_mem {z : RA F E} (hz : z ∈ hatRing F E) : bar c z ∈ hatRing F E := by
  refine galoisAut_mem_adelicCompletionOfElementSet F c ?_ hz
  rintro _ ⟨x, rfl⟩
  exact ⟨⟨_, (RingOfIntegers.isIntegral_coe x).map c.toRingEquiv.toRingHom.toIntAlgHom⟩, rfl⟩

def ratOne : Subgroup (RA F E)ˣ where
  carrier := {x | (∃ a : E, (x : RA F E) = diag F E a) ∧ (x : RA F E) * bar c x = 1}
  one_mem' := ⟨⟨1, by simp⟩, by simp⟩
  mul_mem' := by
    rintro x y ⟨⟨a, ha⟩, hx⟩ ⟨⟨b, hb⟩, hy⟩
    refine ⟨⟨a * b, by rw [Units.val_mul, ha, hb, map_mul]⟩, ?_⟩
    rw [Units.val_mul, map_mul, mul_mul_mul_comm, hx, hy, mul_one]
  inv_mem' := by
    rintro x ⟨⟨a, ha⟩, hx⟩
    have h : ((x⁻¹ : (RA F E)ˣ) : RA F E) = bar c x := Units.inv_eq_of_mul_eq_one_right hx
    refine ⟨⟨c a, by rw [h, ha]; rfl⟩, ?_⟩
    nth_rewrite 1 [h]
    rw [← map_mul, Units.mul_inv, map_one]

def congOne (N : ℕ) : Subgroup (RA F E)ˣ where
  carrier := {x | (∃ w ∈ hatRing F E, (x : RA F E) - 1 = N * w) ∧ (x : RA F E) * bar c x = 1}
  one_mem' := ⟨⟨0, zero_mem _, by simp⟩, by simp⟩
  mul_mem' := by
    rintro x y ⟨⟨a, ha, ea⟩, hx⟩ ⟨⟨b, hb, eb⟩, hy⟩
    refine ⟨⟨a + b + N * (a * b), add_mem (add_mem ha hb) (mul_mem (natCast_mem _ N) (mul_mem ha hb)), ?_⟩, ?_⟩
    · rw [Units.val_mul]
      linear_combination (y : RA F E) * ea + (1 + N * a) * eb
    · rw [Units.val_mul, map_mul, mul_mul_mul_comm, hx, hy, mul_one]
  inv_mem' := by
    rintro x ⟨⟨a, ha, ea⟩, hx⟩
    have h : ((x⁻¹ : (RA F E)ˣ) : RA F E) = bar c x := Units.inv_eq_of_mul_eq_one_right hx
    refine ⟨⟨bar c a, bar_mem c ha, ?_⟩, ?_⟩
    · have := congrArg (bar c) ea
      rwa [map_sub, map_one, map_mul, map_natCast, ← h] at this
    · nth_rewrite 1 [h]
      rw [← map_mul, Units.mul_inv, map_one]

theorem exists_exponent (hc : ∀ y, c (c y) = y) (N : ℕ) (hN : 0 < N) : ∃ m : ℕ, 0 < m ∧
    ∀ x : (RA F E)ˣ, (x : RA F E) * bar c x = 1 → x ^ m ∈ ratOne c ⊔ congOne c N := by
  have := finite_quotient_hatRing F E N hN
  let k := Nat.card (hatRing F E ⧸ Ideal.span {(N : hatRing F E)})ˣ
  refine ⟨classNumber E * 2 * k, Nat.mul_pos (Nat.mul_pos (classNumber_pos E) two_pos) Nat.card_pos,
    fun x hx => ?_⟩
  obtain ⟨b, hb, s, t, e, hst⟩ := pow_classNumber F E x
  have hst' : (s : RA F E) * t = 1 := congrArg Subtype.val hst
  have hbst : bar c s * bar c t = 1 := by rw [← map_mul, hst', map_one]
  have hcb : c b ≠ 0 := by simpa using hb
  have hq : b / c b ≠ 0 := div_ne_zero hb hcb
  let r : (RA F E)ˣ := (isUnit_diag F E hq).unit
  have hr : r ∈ ratOne c := by
    refine ⟨⟨_, rfl⟩, ?_⟩
    change diag F E (b / c b) * diag F E (c (b / c b)) = 1
    rw [← map_mul, map_div₀, hc, div_mul_div_comm, mul_comm b, div_self (mul_ne_zero hcb hb), map_one]
  let v : (hatRing F E)ˣ := Units.mkOfMulEqOne (s * ⟨_, bar_mem c t.2⟩) (t * ⟨_, bar_mem c s.2⟩)
    (Subtype.ext (by
      change (s : RA F E) * bar c t * (t * bar c s) = 1
      linear_combination (bar c s * bar c t) * hst' + hbst))
  let u : (RA F E)ˣ := Units.map (hatRing F E).subtype.toMonoidHom v
  have hu : (u : RA F E) = s * bar c t := rfl
  have hun : (u : RA F E) * bar c u = 1 := by
    rw [hu, map_mul, bar_bar c hc]
    linear_combination (bar c s * bar c t) * hst' + hbst
  have hx2 : x ^ (classNumber E * 2) = r * u := by
    apply Units.ext
    have h1 : (x : RA F E) ^ classNumber E * bar c ((x : RA F E) ^ classNumber E) = 1 := by
      rw [map_pow, ← mul_pow, hx, one_pow]
    have h2 : diag F E (b / c b) * diag F E (c b) = diag F E b := by
      rw [← map_mul, div_mul_cancel₀ _ hcb]
    have h3 : bar c (diag F E b) = diag F E (c b) := rfl
    rw [e, map_mul, h3] at h1
    rw [Units.val_pow_eq_pow_val, pow_mul, e, Units.val_mul, hu]
    change _ = diag F E (b / c b) * _
    linear_combination (diag F E (b / c b) * s * bar c t) * h1 - (diag F E b * s * s) * h2
      - (diag F E (b / c b) * diag F E (c b) * diag F E b * s * s) * hbst
  have huk : u ^ k ∈ congOne c N := by
    refine ⟨?_, by rw [Units.val_pow_eq_pow_val, map_pow, ← mul_pow, hun, one_pow]⟩
    have h1 : (Units.map (Ideal.Quotient.mk (Ideal.span {(N : hatRing F E)})).toMonoidHom v) ^ k = 1 :=
      pow_card_eq_one'
    have h2 : Ideal.Quotient.mk (Ideal.span {(N : hatRing F E)}) ((v : hatRing F E) ^ k) =
        Ideal.Quotient.mk _ 1 := by
      rw [map_pow, map_one]
      exact (Units.val_pow_eq_pow_val _ _).symm.trans (congrArg Units.val h1)
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 h2)
    refine ⟨w, w.2, ?_⟩
    have := congrArg (hatRing F E).subtype hw
    rwa [map_sub, map_one, map_mul, map_natCast, map_pow] at this
  rw [pow_mul, hx2, mul_pow]
  exact Subgroup.mul_mem_sup (pow_mem hr k) huk

theorem mem_of_pow_eq_one {K : IntermediateField ℚ ℂ} {m : ℕ} (hm : 0 < m)
    (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta m ∈ K) {z : ℂ} (hz : z ^ m = 1) : z ∈ K := by
  have : NeZero m := ⟨hm.ne'⟩
  obtain ⟨i, -, rfl⟩ := (Complex.isPrimitiveRoot_exp m hm.ne').eq_pow_of_pow_eq_one hz
  exact pow_mem h i

end GlobalTheory.NormOneChar

namespace GlobalTheory.NormOneChar

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.FinalJoin
open scoped TensorProduct

end GlobalTheory.NormOneChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.RamOverZRealPos
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory

theorem ramOverZ_real_pos {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    (0 : ℝ) < (ramOverZ la : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (Formalism.MainNotions.ModuliIntegralCharts.H1.H1algLink.ramOverZ_ne_zero la)

theorem numerical_h_one_of_weighted_bound : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j), ∀ (large₂ : SizeData₂ D) (wL : WeightFamilies.Wt D j) (nus : HeightOneSpectrum (𝓞 T.Q.c.F) → ℝ), Formalism.MainNotions.Gaps.EtaleWeightGaps.WeightedPrimeSumBoundAlt large₂ (recPJ h j hj) wL nus → NumericalH1Condition T.Q.c (fun la => nus la / (ramOverZ la : ℝ)) (WeightAlgebra.PN D large₂) wL.size ∧ nuOf T.Q.c (fun la => nus la / (ramOverZ la : ℝ)) = nus := by
  intro D T h j hj large₂ wL nus hH
  obtain ⟨h0, h1, h2⟩ := hH
  have he : ∀ la : HeightOneSpectrum (𝓞 T.Q.c.F),
      (ramOverZ la : ℝ) * (nus la / (ramOverZ la : ℝ)) = nus la := fun la =>
    mul_div_cancel₀ _ (ramOverZ_real_pos la).ne'
  refine ⟨⟨fun la => div_nonneg (h0 la) (Nat.cast_nonneg _), h1.subset ?_, ?_⟩, funext he⟩
  · intro la hla h'
    exact hla (by simp only [show nus la = 0 from h', zero_div])
  · refine le_of_eq_of_le ?_ h2
    have hs : (Function.support fun la : HeightOneSpectrum (𝓞 T.Q.c.F) =>
        nus la * ReciprocityTheory.ChartRestriction.G.T0.logNorm la).Finite :=
      h1.subset fun la hla h' => hla (by simp only [show nus la = 0 from h', zero_mul])
    simp only [he]
    rw [div_eq_mul_inv, finsum_mul' _ _ hs]
    refine finsum_congr fun la => ?_
    rw [abs_of_nonneg (h0 la), mul_assoc, ← div_eq_mul_inv]
    rfl

end GlobalTheory
end

