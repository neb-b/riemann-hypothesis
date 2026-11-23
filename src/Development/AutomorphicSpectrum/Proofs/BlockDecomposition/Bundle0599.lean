module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle0002
public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.PullHEq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HdgAffIso
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0236
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0468
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0514
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0544
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0253
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0575
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0568
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0589
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0574
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0576
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0559
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1352
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ToComplBijective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0583
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0554

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedFieldStructure
section
noncomputable section

namespace GlobalTheory.CompanionTheory.FixedPointsCM

open NumberField IsDedekindDomain HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct

theorem exists_eq_algebraMap_of_sigR_eq {F E K : Type} [Field F] [CharZero F] [Field E] [Algebra F E]
    [CommRing K] [Algebra F K] (σ : E →ₐ[F] E) (hfin : Module.finrank F E = 2)
    (hσ : ∀ x, σ (σ x) = x) (u : E) (hu : σ u ≠ u) (x : K ⊗[F] E) (hx : sigR K σ x = x) :
    ∃ c : K, x = algebraMap K (K ⊗[F] E) c := by
  have hli : LinearIndependent F ![(1 : E), u] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h2 : s • (1 : E) + t • σ u = 0 := by
      have := congrArg σ h
      simpa [map_add (f := _), map_smul] using this
    have h3 : t • (σ u - u) = 0 := by
      have : t • (σ u - u) = (s • (1 : E) + t • σ u) - (s • (1 : E) + t • u) := by module
      rw [this, h, h2, sub_zero]
    have ht : t = 0 := by
      rcases smul_eq_zero.mp h3 with h4 | h4
      · exact h4
      · exact absurd (sub_eq_zero.mp h4) hu
    subst ht
    refine ⟨?_, rfl⟩
    simpa using h
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by simp [hfin]
  let b : Module.Basis (Fin 2) F E := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = u := by simp [b]
  obtain ⟨p, q, hsu⟩ : ∃ p q : F, σ u = p • (1 : E) + q • u := by
    refine ⟨b.repr (σ u) 0, b.repr (σ u) 1, ?_⟩
    have := b.sum_repr (σ u)
    rw [Fin.sum_univ_two, hb0, hb1] at this
    exact this.symm
  have hrel : (p + q * p) • (1 : E) + (q * q - 1) • u = 0 := by
    have h1 : u = p • (1 : E) + q • σ u := by
      have := hσ u
      rw [hsu] at this
      simpa [map_add (f := _), map_smul] using this.symm
    rw [hsu] at h1
    have : (p + q * p) • (1 : E) + (q * q - 1) • u = (p • (1 : E) + q • (p • (1 : E) + q • u)) - u := by module
    rw [this, ← h1, sub_self]
  obtain ⟨hp, hq⟩ := LinearIndependent.pair_iff.mp hli _ _ hrel
  have hq' : q = -1 := by
    have : (q - 1) * (q + 1) = 0 := by linear_combination hq
    rcases mul_eq_zero.mp this with h | h
    · exfalso
      have hq1 : q = 1 := sub_eq_zero.mp h
      subst hq1
      have hp0 : p = 0 := by
        have : (2 : F) * p = 0 := by linear_combination hp
        simpa using this
      apply hu
      rw [hsu, hp0]
      simp
    · linear_combination h
  subst hq'
  let B := Algebra.TensorProduct.basis K b
  have hB0 : B 0 = (1 : K) ⊗ₜ[F] (1 : E) := by simp [B, hb0]
  have hB1 : B 1 = (1 : K) ⊗ₜ[F] u := by simp [B, hb1]
  obtain ⟨a, c, hac⟩ : ∃ a c : K, x = a ⊗ₜ[F] (1 : E) + c ⊗ₜ[F] u := by
    refine ⟨B.repr x 0, B.repr x 1, ?_⟩
    have := B.sum_repr x
    rw [Fin.sum_univ_two, hB0, hB1] at this
    simpa [TensorProduct.smul_tmul'] using this.symm
  have hs : sigR K σ x = a ⊗ₜ[F] (1 : E) + c ⊗ₜ[F] σ u := by
    rw [hac]
    simp [sigR]
  have hkey : (algebraMap F K p * c) • B 0 = (c + c) • B 1 := by
    rw [hB0, hB1]
    have h1 : a ⊗ₜ[F] (1 : E) + c ⊗ₜ[F] σ u = a ⊗ₜ[F] (1 : E) + c ⊗ₜ[F] u := by rw [← hs, hx, hac]
    have h2 := add_left_cancel h1
    rw [hsu, TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul, neg_smul, one_smul] at h2
    have e0 : (algebraMap F K p * c) • ((1 : K) ⊗ₜ[F] (1 : E)) = p • (c ⊗ₜ[F] (1 : E)) := by
      rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul']
      congr 1
      simp [Algebra.smul_def]
    have e1 : (c + c) • ((1 : K) ⊗ₜ[F] u) = c ⊗ₜ[F] u + c ⊗ₜ[F] u := by
      rw [TensorProduct.smul_tmul', ← TensorProduct.add_tmul]
      simp
    rw [e0, e1]
    exact add_neg_eq_iff_eq_add.mp h2
  have hc : c = 0 := by
    have h1 := congrArg (fun y => B.repr y 1) hkey
    simp at h1
    have h2 : (2 : F) • c = 0 := by rw [two_smul]; exact h1.symm
    rcases smul_eq_zero.mp h2 with h | h
    · simp at h
    · exact h
  refine ⟨a, ?_⟩
  rw [hac, hc, Algebra.TensorProduct.algebraMap_apply]
  simp

theorem fixedK : PositivityTheory.SiegelWeilFormula.Gunr.FixedK := by
  intro F E _ _ _ _ _ σ h v x hx
  obtain ⟨-, hC, hfin, hconj⟩ := h
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hσ : ∀ y, σ (σ y) = y := fun y => τ.injective (by rw [hconj, hconj, star_star])
  obtain ⟨u, hu⟩ : ∃ u, σ u ≠ u := by
    by_contra hall
    push Not at hall
    apply IsTotallyComplex.complexEmbedding_not_isReal τ
    rw [ComplexEmbedding.isReal_iff]
    ext y
    rw [ComplexEmbedding.conjugate_coe_eq]
    have := hconj τ y
    rw [hall y] at this
    exact this.symm
  exact exists_eq_algebraMap_of_sigR_eq σ hfin hσ u hu x hx

end GlobalTheory.CompanionTheory.FixedPointsCM
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormsRestrictOpenBijective
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

noncomputable section
namespace GlobalTheory.CompanionTheory.FormOpen

variable {K : Type} [CommRing K]

theorem mOm_bijective {A B : Type} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    {φ : A →+* B} (hφ : SemiHom (RingHom.id K) φ) (hb : Function.Bijective φ) (j : ℕ) :
    Function.Bijective (hφ.mOm j) := by
  let e : A ≃+* B := RingEquiv.ofBijective φ hb
  have he : ∀ a, e a = φ a := fun _ ↦ rfl
  have hψ : SemiHom (RingHom.id K) (e.symm : B →+* A) := fun r b ↦ by
    apply e.injective
    change e (e.symm (r • b)) = e (RingHom.id K r • e.symm b)
    rw [RingEquiv.apply_symm_apply, he, RingHom.id_apply, show φ (r • e.symm b) = _ from hφ r _,
      ← he, RingEquiv.apply_symm_apply, RingHom.id_apply]
  have hA : SemiHom (RingHom.id K) (RingHom.id A) := fun _ _ ↦ rfl
  have hB : SemiHom (RingHom.id K) (RingHom.id B) := fun _ _ ↦ rfl
  have l : Function.LeftInverse (hψ.mOm j) (hφ.mOm j) := fun x ↦
    (SemiHom.mOm_mOm (ρ := RingHom.id K) hφ hψ hA (fun a ↦ e.symm_apply_apply a) x).trans
      (hA.mOm_id (fun _ ↦ rfl) x)
  have r : Function.RightInverse (hψ.mOm j) (hφ.mOm j) := fun x ↦
    (SemiHom.mOm_mOm (ρ := RingHom.id K) hψ hφ hB (fun a ↦ e.apply_symm_apply a) x).trans
      (hB.mOm_id (fun _ ↦ rfl) x)
  exact ⟨l.injective, r.surjective⟩

variable {X : Scheme.{0}}

theorem app_map_eq (V : X.Opens) (h : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V) :
    V.ι.app V ≫ V.toScheme.presheaf.map (homOfLE h).op = V.topIso.inv := by
  simp only [Scheme.Opens.topIso, Scheme.Opens.ι_app, Scheme.Opens.toScheme_presheaf_map,
    Iso.op_inv, Functor.mapIso_inv, eqToIso.inv, ← Functor.map_comp, ← op_comp]
  rfl

theorem res_appSec_bijective (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens)
    (h : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V) :
    Function.Bijective ((Sec.res (V.ι ≫ q) h : Sec (V.ι ≫ q) (V.ι ⁻¹ᵁ V) →+* Sec (V.ι ≫ q) ⊤).comp
      (appSec q (V.ι ≫ q) V.ι V)) := by
  have e : ((Sec.res (V.ι ≫ q) h : Sec (V.ι ≫ q) (V.ι ⁻¹ᵁ V) →+* Sec (V.ι ≫ q) ⊤).comp (appSec q (V.ι ≫ q) V.ι V) :
      Sec q V → Sec (V.ι ≫ q) ⊤) = V.topIso.inv.hom := by
    rw [← app_map_eq V h]; rfl
  rw [e]
  exact ConcreteCategory.bijective_of_isIso V.topIso.inv

theorem formRes_formPull_open_bijective {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (a : ℕ) :
    Function.Bijective fun x : OmU q V a => formRes (V.ι ≫ q) (show (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V by simp) a
      (formPull (f := V.ι) rfl V a x) := by
  have h : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := by simp
  have hγ : SemiHom (RingHom.id K) ((Sec.res (V.ι ≫ q) h : Sec (V.ι ≫ q) (V.ι ⁻¹ᵁ V) →+* Sec (V.ι ≫ q) ⊤).comp
      (appSec q (V.ι ≫ q) V.ι V)) :=
    (semiHom_appSec rfl V).comp (SemiHom.of_algHom (Sec.res (V.ι ≫ q) h))
  have e : (fun x : OmU q V a => formRes (V.ι ≫ q) h a (formPull (f := V.ι) rfl V a x)) =
      hγ.mOm a := funext fun x ↦
    SemiHom.mOm_mOm (semiHom_appSec rfl V) (SemiHom.of_algHom (Sec.res (V.ι ≫ q) h)) hγ
      (fun _ ↦ rfl) x
  rw [e]
  exact mOm_bijective hγ (res_appSec_bijective q V h) a

end GlobalTheory.CompanionTheory.FormOpen
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobPowRead
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt

theorem frob_pow_read {l : ℕ} [Fact l.Prime] (N : ℕ) (a y : Tl l) (b : ℕ → Tl l) (D : ℕ) :
    (a - ∑ i ∈ Finset.range D, b i * y ^ i) ^ l ^ N =
      a ^ l ^ N - ∑ i ∈ Finset.range D, b i ^ l ^ N * (y ^ l ^ N) ^ i := by
  rw [sub_pow_char_pow, sum_pow_char_pow]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm i]

theorem oc_eq {l : ℕ} [Fact l.Prime] (K : FinExt l) (c : ↥(OL K)) : oc K c = omC (((c : ↥K.1) : Om l)) := rfl

theorem sys_pow_iter {l : ℕ} [Fact l.Prime] {f : ℕ} {u : ℕ → Tl l} (h : ∀ n, u (n + 1) ^ l ^ f = u n)
    (n m : ℕ) : u (n + m) ^ l ^ (f * m) = u n := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : u (n + (m + 1)) ^ l ^ (f * (m + 1)) = (u (n + m + 1) ^ l ^ f) ^ l ^ (f * m) := by
      rw [← pow_mul, ← pow_add, ← add_assoc]
      congr 2
      ring
    rw [e, h, ih]

theorem fix_ringHom {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)) (f : ℕ) (hf : 0 < f)
    (hl : ‖(l : ℂ_[l])‖ ≤ ‖oc K π‖) (h1 : ‖oc K π‖ < 1)
    (hfer : ∀ c : ↥(OL K), ‖oc K c ^ l ^ f - oc K c‖ ≤ ‖oc K π‖) :
    ∃ r₀ : ↥(OL K) →+* Tl l, (∀ c, r₀ c ^ l ^ f = r₀ c) ∧ ∀ c, ‖sh (r₀ c) - oc K c‖ ≤ ‖oc K π‖ := by
  have hex : ∀ c : ↥(OL K), ∃ y : Tl l, y ^ l ^ f = y ∧ ‖sh y - oc K c‖ ≤ ‖oc K π‖ := fun c =>
    _root_.GlobalTheory.CompanionTheory.LTPer.Tilt.exists_fixed_near f _ hf hl h1 (oc K c) (norm_oc_le_one K c) (hfer c)
  choose F hF1 hF2 using hex
  have huniq : ∀ (x : Tl l) (A : ↥(OL K)), x ^ l ^ f = x → ‖sh x - oc K A‖ ≤ ‖oc K π‖ → F A = x := by
    intro x A hx hA
    apply fixed_unique hf (hF1 A) hx
    refine lt_of_le_of_lt (norm_sub_le_of_near hl ?_) h1
    have e : sh (F A) - sh x = (sh (F A) - oc K A) - (sh x - oc K A) := by ring
    rw [e]
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hF2 A) (by rw [norm_neg]; exact hA))
  refine ⟨{ toFun := F, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hF1, hF2⟩
  · exact huniq 1 1 (one_pow _) (by rw [map_one, sh_one, sub_self, norm_zero]; exact norm_nonneg _)
  · intro a b
    refine huniq _ _ (by rw [mul_pow, hF1, hF1]) ?_
    rw [map_mul]
    exact near_mul (norm_oc_le_one K b) (hF2 a) (hF2 b)
  · exact huniq 0 0 (zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero))
      (by rw [map_zero, sh_zero, sub_self, norm_zero]; exact norm_nonneg _)
  · intro a b
    refine huniq _ _ (by rw [add_pow_char_pow, hF1, hF1]) ?_
    rw [map_add (f := _)]
    exact near_add hl (hF2 a) (hF2 b)

theorem tch_eq {l : ℕ} [Fact l.Prime] (f : ℕ) (hf : 0 < f) (x : Tl l) (hx : x ^ l ^ f = x) (y : Om l)
    (hy : sh x = omC y) : tch l x = rB l y := by
  have hq2 : 2 ≤ l ^ f := by
    have := Nat.pow_le_pow_right (Fact.out : l.Prime).pos hf
    have h2 := (Fact.out : l.Prime).two_le
    simp only [pow_one] at this
    omega
  have hyf : y ^ l ^ f = y := by
    apply omC.injective
    rw [map_pow, ← hy, ← sh_pow, hx]
  exact _root_.GlobalTheory.CompanionTheory.LTPer.Tilt.tch_eq_rB_of_sh_eq (l ^ f) hq2 (dvd_pow_self l hf.ne') x y hx hyf hy

theorem exp_twist {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)) (f : ℕ) (hf : 0 < f) (hqf : qOf π = l ^ f)
    (hl : ‖(l : ℂ_[l])‖ ≤ ‖oc K π‖) (h1 : ‖oc K π‖ < 1) (hπ0 : π ≠ 0)
    (hmax : (Ideal.span {π}).IsMaximal) (hfin : Finite (↥(OL K) ⧸ Ideal.span {π}))
    (r₀ : ↥(OL K) →+* Tl l) (hr1 : ∀ c, r₀ c ^ l ^ f = r₀ c) (hr2 : ∀ c, ‖sh (r₀ c) - oc K c‖ ≤ ‖oc K π‖)
    (hrπ : r₀ π = 0) (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) :
    ∃ i : ℕ, ∀ c, ∃ c' : ↥(OL K), sh (r₀ c ^ l ^ i) = omC (μ ((c + π * c' : ↥(OL K)) : ↥K.1)) := by
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.CompanionTheory.LTPer.Tilt.exists_gal_extending_embedding K μ
  haveI := hmax
  haveI := hfin
  letI : Field (↥(OL K) ⧸ Ideal.span {π}) := Ideal.Quotient.field _
  have hker : ∀ a ∈ Ideal.span {π}, r₀ a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, hrπ, mul_zero]
  let α : (↥(OL K) ⧸ Ideal.span {π}) →+* Tl l := Ideal.Quotient.lift _ r₀ hker
  obtain ⟨i, hi⟩ := _root_.GlobalTheory.CompanionTheory.LTPer.Tilt.exists_frobenius_pow_of_ringHoms (l := l) (k := ↥(OL K) ⧸ Ideal.span {π}) (D := Tl l) α ((actT g).comp α)
  refine ⟨i, fun c => ?_⟩
  obtain ⟨c', hc'⟩ := _root_.GlobalTheory.CompanionTheory.LTPer.Tilt.sh_root_near_integer K π f hf hqf hl h1 hπ0 (r₀ c) c (hr1 c) (hr2 c)
  refine ⟨c', ?_⟩
  have h : actT g (r₀ c) = r₀ c ^ l ^ i := hi (Ideal.Quotient.mk _ c)
  rw [← h, sh_actT, hc', oc_eq, galCp_omC, hg]

theorem tch_clause {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)) (f : ℕ) (hf : 0 < f)
    (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) (r₀ : ↥(OL K) →+* Tl l) (hr1 : ∀ c, r₀ c ^ l ^ f = r₀ c) (i : ℕ)
    (hic : ∀ c, ∃ c' : ↥(OL K), sh (r₀ c ^ l ^ i) = omC (μ ((c + π * c' : ↥(OL K)) : ↥K.1))) :
    ∀ c, ∃ c', tch l (((iterateFrobenius (Tl l) l i).comp r₀) c) = oB K μ (c + π * c') := by
  intro c
  obtain ⟨c', hc'⟩ := hic c
  refine ⟨c', ?_⟩
  rw [RingHom.comp_apply, iterateFrobenius_def]
  have hfix : (r₀ c ^ l ^ i) ^ l ^ f = r₀ c ^ l ^ i := by
    rw [← pow_mul, mul_comm, pow_mul, hr1]
  rw [tch_eq f hf _ hfix _ hc']
  simp only [oB, RingHom.comp_apply]
  rfl

theorem gal_clause {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] (g : GQ l) (r₀ : R →+* Tl l) (i : ℕ)
    (x : Tl l) (c : ℕ → R) (D : ℕ) (hd : x ^ D ∣ actT g x - ∑ j ∈ Finset.range D, r₀ (c j) * x ^ j) :
    (x ^ l ^ i) ^ D ∣ actT g (x ^ l ^ i) -
      ∑ j ∈ Finset.range D, ((iterateFrobenius (Tl l) l i).comp r₀) (c j) * (x ^ l ^ i) ^ j := by
  have h := pow_dvd_pow_of_dvd hd (l ^ i)
  rw [frob_pow_read] at h
  have e1 : (x ^ l ^ i) ^ D = (x ^ D) ^ l ^ i := by rw [← pow_mul, ← pow_mul, mul_comm]
  have e2 : actT g (x ^ l ^ i) = actT g x ^ l ^ i := map_pow _ _ _
  have e3 : ∀ j, ((iterateFrobenius (Tl l) l i).comp r₀) (c j) = r₀ (c j) ^ l ^ i := fun j => by
    rw [RingHom.comp_apply, iterateFrobenius_def]
  simp only [e1, e2, e3]
  exact h

end GlobalTheory.CompanionTheory.LTPer.Tilt


open GlobalTheory.CompanionTheory.LTPer.Tilt in
theorem GlobalTheory.CompanionTheory.LTPer.Tilt.tilt_period : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l),
    LTData K χ π z → ∀ μ : ↥K.1 →ₐ[ℚ_[l]] Om l,
    ∃ (r : ↥(OL K) →+* Tl l) (v : ℕ → Tl l),
      (∀ n, v (n + 1) ^ qOf π = v n) ∧ v 0 ≠ 0 ∧ ‖thB l (tch l (v 0))‖ < 1 ∧
      (∀ c, ∃ c', tch l (r c) = oB K μ (c + π * c')) ∧
      (∀ (g : GQ l) (hg : g ∈ GK K) (φ : PowerSeries ↥(OL K)), PowerSeries.constantCoeff φ = 0 →
        ((PowerSeries.coeff 1 φ : ↥(OL K)) : ↥K.1) = ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1) →
        PowerSeries.subst φ (ltSeries π) = PowerSeries.subst (ltSeries π) φ →
        ∀ n D, v n ^ D ∣ actT g (v n) - ∑ i ∈ Finset.range D, r (PowerSeries.coeff i φ) * v n ^ i) ∧
      (μ = K.1.val → ∀ n, ‖thB l (tch l (v n)) - ((z n : Om l) : ℂ_[l])‖ ≤ ‖(((π : ↥K.1) : Om l) : ℂ_[l])‖) := by
  intro l _ K χ π z hLT μ
  obtain ⟨hirr, hz0, hz1, hrec, hgal⟩ := hLT
  obtain ⟨hq2, hlq, hπl, hπ1, -⟩ := GlobalTheory.CompanionTheory.LTPer.uniformiser_facts K π hirr
  obtain ⟨hmax, hfin, f, hf, hqf⟩ := _root_.GlobalTheory.CompanionTheory.LTPer.Tilt.resfield_of_irreducible K π hirr
  have hπ1' : ‖oc K π‖ < 1 := by rw [oc_apply]; exact hπ1
  have hl : ‖(l : ℂ_[l])‖ ≤ ‖oc K π‖ := by
    obtain ⟨a, ha⟩ := hπl
    have e : (l : ℂ_[l]) = oc K π * oc K a := by rw [← map_mul, ← ha, map_natCast]
    rw [e, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_oc_le_one K a)
  have hπ0 : π ≠ 0 := hirr.ne_zero
  obtain ⟨hzlt, hzgt⟩ := _root_.GlobalTheory.CompanionTheory.LTPer.Tilt.Normz.norm_z_bounds K χ π z ⟨hirr, hz0, hz1, hrec, hgal⟩ hq2 hπ1'
  have hrec' : ∀ n, z (n + 1) ^ l ^ f + ((π : ↥K.1) : Om l) * z (n + 1) = z n := by
    intro n
    have h := hrec n
    rwa [show Nat.card (↥(OL K) ⧸ Ideal.span {π}) = l ^ f from hqf] at h
  have hZ : ∀ n, ‖omC (z (n + 1)) ^ l ^ f - omC (z n)‖ ≤ ‖oc K π‖ := by
    intro n
    have e : omC (z (n + 1)) ^ l ^ f - omC (z n) = -(oc K π * omC (z (n + 1))) := by
      rw [← hrec' n, map_add (f := _), map_mul, map_pow, oc_eq]
      ring
    rw [e, norm_neg, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hzlt _).le
  obtain ⟨u, hu1, hu2⟩ := GlobalTheory.T.teichmuller_compatible_sequence_approximation f ‖oc K π‖ hf hl hπ1' (fun n => omC (z n)) (fun n => (hzlt n).le) hZ
  have hu0 : ∀ n, u n ≠ 0 := by
    have h2 : ∀ n, 2 ≤ n → u n ≠ 0 := by
      intro n hn h0
      have h := hu2 n
      rw [h0, sh_zero, zero_sub, norm_neg] at h
      exact absurd (hzgt n hn) (not_lt.2 h)
    intro n
    rw [← sys_pow_iter hu1 n 2]
    exact pow_ne_zero _ (h2 _ (by omega))
  have hfer : ∀ c : ↥(OL K), ‖oc K c ^ l ^ f - oc K c‖ ≤ ‖oc K π‖ := by
    intro c
    obtain ⟨a, ha⟩ := _root_.GlobalTheory.CompanionTheory.LTPer.Tilt.dvd_pow_qOf_sub_self K π hmax hfin c
    rw [hqf] at ha
    rw [← map_pow, ← map_sub, ha, map_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_oc_le_one K a)
  obtain ⟨r₀, hr1, hr2⟩ := fix_ringHom K π f hf hl hπ1' hfer
  have hrπ : r₀ π = 0 := by
    apply fixed_unique hf (hr1 π) (zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero))
    refine lt_of_le_of_lt (norm_sub_le_of_near hl ?_) hπ1'
    rw [sh_zero, sub_zero]
    have e : sh (r₀ π) = (sh (r₀ π) - oc K π) + oc K π := by ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hr2 π) le_rfl)
  have hexp : ∃ i : ℕ, (μ = K.1.val → i = 0) ∧
      ∀ c, ∃ c' : ↥(OL K), sh (r₀ c ^ l ^ i) = omC (μ ((c + π * c' : ↥(OL K)) : ↥K.1)) := by
    by_cases hμ : μ = K.1.val
    · refine ⟨0, fun _ => rfl, fun c => ?_⟩
      obtain ⟨c', hc'⟩ := _root_.GlobalTheory.CompanionTheory.LTPer.Tilt.sh_root_near_integer K π f hf hqf hl hπ1' hπ0 (r₀ c) c (hr1 c) (hr2 c)
      refine ⟨c', ?_⟩
      rw [pow_zero, pow_one, hc', hμ]
      rfl
    · obtain ⟨i, hi⟩ := exp_twist K π f hf hqf hl hπ1' hπ0 hmax hfin r₀ hr1 hr2 hrπ μ
      exact ⟨i, fun h => absurd h hμ, hi⟩
  obtain ⟨i, hi0, hic⟩ := hexp
  refine ⟨(iterateFrobenius (Tl l) l i).comp r₀, fun n => u n ^ l ^ i, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    show (u (n + 1) ^ l ^ i) ^ qOf π = u n ^ l ^ i
    rw [hqf, ← pow_mul, mul_comm, pow_mul, hu1]
  · exact pow_ne_zero _ (hu0 0)
  · show ‖thB l (tch l (u 0 ^ l ^ i))‖ < 1
    rw [thB_tch, sh_pow, norm_pow]
    have h := hu2 0
    rw [hz0, map_zero, sub_zero] at h
    exact pow_lt_one₀ (norm_nonneg _) (h.trans_lt hπ1') (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
  · exact tch_clause K π f hf μ r₀ hr1 i hic
  · intro g hg φ h0 h1 hcomm n D
    have hs := hgal ⟨g, hg⟩ φ h0 h1 hcomm
    have hd := _root_.GlobalTheory.CompanionTheory.LTPer.Tilt.GalDiv.galdiv K π z f hf hl hπ1' hzlt hzgt u hu1 hu2 r₀ hr1 hr2 hu0 g
      (fun k => PowerSeries.coeff k φ) hs n D
    exact gal_clause g r₀ i (u n) (fun k => PowerSeries.coeff k φ) D hd
  · intro hμ n
    show ‖thB l (tch l (u n ^ l ^ i)) - _‖ ≤ _
    rw [hi0 hμ, pow_zero, pow_one, thB_tch, ← omC_apply, ← oc_apply]
    exact hu2 n
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianFormPolynomialIn
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

namespace GlobalTheory.CompanionTheory.FormRatio

theorem exists_eq_mul_aeval (K : Type) [Field K] (σ : K →+* K) (n : ℕ)
    (A H₀ H : Matrix (Fin n) (Fin n) K) (_hA : IsUnit A.det) (hs : A.charpoly.Separable)
    (hH₀ : H₀.det ≠ 0) (e₀ : cT σ A * H₀ * A = H₀) (e : cT σ A * H * A = H) :
    ∃ m : K[X], H = H₀ * aeval A m := by
  have hH₀' : IsUnit H₀.det := isUnit_iff_ne_zero.mpr hH₀
  have hB : IsUnit (cT σ A).det := by
    refine isUnit_iff_ne_zero.mpr fun h0 => hH₀ ?_
    have h1 := congrArg Matrix.det e₀
    rw [Matrix.det_mul, Matrix.det_mul, h0, zero_mul, zero_mul] at h1
    exact h1.symm
  have k1 : H * A = (cT σ A)⁻¹ * H := by
    calc H * A = ((cT σ A)⁻¹ * cT σ A) * H * A := by
          rw [Matrix.nonsing_inv_mul _ hB, one_mul]
      _ = (cT σ A)⁻¹ * (cT σ A * H * A) := by simp only [mul_assoc]
      _ = (cT σ A)⁻¹ * H := by rw [e]
  have k0 : H₀ * A = (cT σ A)⁻¹ * H₀ := by
    calc H₀ * A = ((cT σ A)⁻¹ * cT σ A) * H₀ * A := by
          rw [Matrix.nonsing_inv_mul _ hB, one_mul]
      _ = (cT σ A)⁻¹ * (cT σ A * H₀ * A) := by simp only [mul_assoc]
      _ = (cT σ A)⁻¹ * H₀ := by rw [e₀]
  have k2 : A * H₀⁻¹ = H₀⁻¹ * (cT σ A)⁻¹ := by
    calc A * H₀⁻¹ = H₀⁻¹ * (H₀ * A) * H₀⁻¹ := by
          rw [← mul_assoc H₀⁻¹ H₀ A, Matrix.nonsing_inv_mul _ hH₀', one_mul]
      _ = H₀⁻¹ * ((cT σ A)⁻¹ * H₀) * H₀⁻¹ := by rw [k0]
      _ = H₀⁻¹ * (cT σ A)⁻¹ * (H₀ * H₀⁻¹) := by simp only [mul_assoc]
      _ = H₀⁻¹ * (cT σ A)⁻¹ := by rw [Matrix.mul_nonsing_inv _ hH₀', mul_one]
  have hc : Commute A (H₀⁻¹ * H) := by
    show A * (H₀⁻¹ * H) = H₀⁻¹ * H * A
    calc A * (H₀⁻¹ * H) = A * H₀⁻¹ * H := (mul_assoc _ _ _).symm
      _ = H₀⁻¹ * (cT σ A)⁻¹ * H := by rw [k2]
      _ = H₀⁻¹ * (H * A) := by rw [k1, mul_assoc]
      _ = H₀⁻¹ * H * A := (mul_assoc _ _ _).symm
  obtain ⟨m, hm⟩ := ClsFin.exists_aeval_of_comm A (H₀⁻¹ * H) hs hc
  refine ⟨m, ?_⟩
  rw [← hm, ← mul_assoc, Matrix.mul_nonsing_inv _ hH₀', one_mul]

end GlobalTheory.CompanionTheory.FormRatio
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityOfEquivStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_multiplicity_of_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W), Nonempty (π.Equiv σ) → jm x hd π = jm x hd σ := by
  first | exact @GlobalTheory.CompanionTheory.JacquetCongr.jm_congr_of_equiv | exact GlobalTheory.CompanionTheory.JacquetCongr.jm_congr_of_equiv | (intros; apply GlobalTheory.CompanionTheory.JacquetCongr.jm_congr_of_equiv <;> assumption)
end

