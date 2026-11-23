module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmallTorsionKilledByPrimePowers

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonemptyClosedValuedExtensionOfCDVR
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct

namespace GlobalTheory.CharDepth

theorem nonempty_valExt :
    ∀ (T : CDVR) (p : ℕ) [Fact p.Prime], ¬ IsUnit (p : T.V) → Nonempty (ValExt T p) := by
  intro T p hp hu
  have hp0 : (p : T.V) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hr0 : (0 : ℝ) < (p : ℝ)⁻¹ := by positivity
  have hr1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  obtain ⟨C, _, _, _, _, _, hC, hCp⟩ :=
    exists_complete_isAlgClosed_of_isDiscreteValuationRing T.V T.Fr hp0
      ((IsLocalRing.mem_maximalIdeal _).2 hu) hr0 hr1
  rw [map_natCast] at hCp
  have : CharZero T.Fr := charZero_of_injective_ringHom (IsFractionRing.injective T.V T.Fr)
  have : CharZero C := charZero_of_injective_ringHom (algebraMap T.Fr C).injective
  have hCp' : ‖(p : C)‖ = (p : ℝ)⁻¹ := by rwa [map_natCast] at hCp
  let v : Valuation C NNReal := NormedField.valuation
  have hO : v.Integers v.integer := Valuation.integer.integers v
  have hmem : ∀ x : C, ‖x‖ ≤ 1 → x ∈ v.integer := fun x hx => by
    change ‖x‖₊ ≤ 1
    exact_mod_cast hx
  have hpO : ‖algebraMap v.integer C (p : v.integer)‖ < 1 := by
    rw [map_natCast, hCp']; exact hr1
  haveI : Fact (¬ IsUnit (p : v.integer)) :=
    ⟨fun h => hpO.ne ((NormIntegers.isUnit_iff_norm_eq_one hO).1 h)⟩
  haveI := NormIntegers.isAdicComplete_span_singleton hO hpO
  haveI := NormIntegers.isLocalRing hO
  obtain ⟨j, hj⟩ := exists_padic_isometry (C := C) p hCp'
  letI : Algebra ℤ_[p] v.integer :=
    ((j.comp PadicInt.Coe.ringHom).codRestrict v.integer fun x =>
      hmem _ ((hj _).trans_le x.2)).toAlgebra
  have hf : ∀ a : T.V, ‖algebraMap T.Fr C (algebraMap T.V T.Fr a)‖ ≤ 1 := fun a => (hC _).2 ⟨a, rfl⟩
  let ι : T.V →+* v.integer :=
    ((algebraMap T.Fr C).comp (algebraMap T.V T.Fr)).codRestrict v.integer fun a => hmem _ (hf a)
  have hι : IsLocalHom ι := by
    refine ⟨fun a ha => ?_⟩
    have h1 : ‖algebraMap T.Fr C (algebraMap T.V T.Fr a)‖ = 1 :=
      (NormIntegers.isUnit_iff_norm_eq_one hO).1 ha
    have ha0 : algebraMap T.V T.Fr a ≠ 0 := fun h => by simp [h] at h1
    obtain ⟨b, hb⟩ := (hC (algebraMap T.V T.Fr a)⁻¹).1 (by rw [map_inv₀, norm_inv, h1, inv_one])
    refine IsUnit.of_mul_eq_one b (IsFractionRing.injective T.V T.Fr ?_)
    rw [map_mul, hb, mul_inv_cancel₀ ha0, map_one]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  have hpF : (p : T.Fr) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hzp := ArcQ.norm_map_eq_zpow_vV (algebraMap T.Fr C) hf hπ hpF
  have he : (vV T.V (p : T.Fr) : ℝ) ≠ 0 := by
    intro h
    have h' : vV T.V (p : T.Fr) = 0 := by exact_mod_cast h
    rw [h', zpow_zero, hCp] at hzp
    exact hr1.ne hzp
  refine ⟨{ C := C, v := v, O := v.integer, ints := hO, ι := ι, ι_local := hι,
            ιF := algebraMap T.Fr C, comp := fun _ => rfl, val := fun x hx => ?_ }⟩
  change ‖algebraMap T.Fr C x‖ = ‖(p : C)‖ ^ _
  rw [← map_natCast (algebraMap T.Fr C) p, hzp, ArcQ.norm_map_eq_zpow_vV (algebraMap T.Fr C) hf hπ hx,
    ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_mul (norm_nonneg _), mul_div_cancel₀ _ he]

end GlobalTheory.CharDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ProductsShortOfOneFactor
section
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.FormTies

theorem pow_mul_short_le {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j)
    (ka wL : WeightFamilies.Wt D j) (hka : ka.n = D.R.nV)
    (step : ∀ w : WeightFamilies.Wt D j, D.R.r ≤ w.n → (w.n = D.R.nV → wL.n = 0) →
      X.emb wL (X.thAll wL) * X.emb w (X.shortTh w) ≤ X.emb (WeightAlgebra.wadd w wL) (X.shortTh (WeightAlgebra.wadd w wL))) :
    ∀ (t : ℕ) (w : WeightFamilies.Wt D j), D.R.r ≤ w.n → deg w + t • deg wL = deg ka →
      X.emb wL (X.thAll wL) ^ t * X.emb w (X.shortTh w) ≤ X.emb ka (X.shortTh ka) := by
  intro t
  induction t with
  | zero =>
    intro w _ e
    rw [zero_smul, add_zero] at e
    obtain rfl := deg_inj e
    rw [pow_zero, one_mul]
  | succ t ih =>
    intro w hr e
    have hn : w.n + (t + 1) * wL.n = ka.n := congrArg (fun x : Deg D j => x.2.2) e
    rw [pow_succ, mul_assoc]
    refine le_trans (mul_le_mul' le_rfl (step w hr fun h0 => ?_)) (ih (WeightAlgebra.wadd w wL) (hr.trans (Nat.le_add_right _ _)) ?_)
    · have h1 : (t + 1) * wL.n = 0 := by omega
      exact (Nat.mul_eq_zero.1 h1).resolve_left (Nat.succ_ne_zero t)
    · rw [deg_wadd, ← e, succ_nsmul]
      abel

theorem emb_mul_le {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j)
    {w w' w'' : WeightFamilies.Wt D j} {N : Submodule (𝓞 B.KO) (B.Cusp j w)} {N' : Submodule (𝓞 B.KO) (B.Cusp j w')}
    {N'' : Submodule (𝓞 B.KO) (B.Cusp j w'')}
    (h : ∀ G ∈ N', ∀ F ∈ N, ∃ H ∈ N'', X.inc w'' H = X.inc w' G * X.inc w F) :
    X.emb w N * X.emb w' N' ≤ X.emb w'' N'' := by
  rw [mul_comm, Submodule.mul_le]
  rintro _ ⟨G, hG, rfl⟩ _ ⟨F, hF, rfl⟩
  exact h G hG F hF

theorem mul_mem_span_of_gen {O R : Type} [CommRing O] [CommRing R] [Algebra O R] {s t : Set R} {N : Submodule O R}
    (h : ∀ g ∈ s, ∀ f ∈ t, g * f ∈ N) {x y : R} (hx : x ∈ Submodule.span O s) (hy : y ∈ Submodule.span O t) :
    x * y ∈ N := by
  have hle : Submodule.span O s * Submodule.span O t ≤ N := by
    rw [Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨g, hg, f, hf, rfl⟩
    exact h g hg f hf
  exact hle (Submodule.mul_mem_mul hx hy)

theorem productsShort_of_oneFactor (one : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j), LawsSh T → OneCover T j → (T.dδ j 0).l₂.A = 1 → ∀ (w wL : WeightFamilies.Wt D j), D.R.r ≤ w.n → (w.n = D.R.nV → wL.n = 0) → ∀ g ∈ T.sh j w, ∀ f ∈ T.th j wL, g * f ∈ Submodule.span (𝓞 T.Q.c.F) (T.sh j (WeightAlgebra.wadd w wL))) : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j), LawsSh T → OneCover T j → (T.dδ j 0).l₂.A = 1 → ∀ (ka wL wF : WeightFamilies.Wt D j) (Tn : ℕ), WeightAlgebra.IsF' ka wL wF Tn wF.n → ka.n = wF.n + Tn * wL.n → WeightFamilies.dimY D j ≤ Tn → D.R.r ≤ wF.n → ka.n = D.R.nV → ProductsShort (recPJ h j hj) ka wL wF Tn := by
  intro hC D T h j hj hsh hone hA ka wL wF Tn hF hn hD hr hka
  have step : ∀ w : WeightFamilies.Wt D j, D.R.r ≤ w.n → (w.n = D.R.nV → wL.n = 0) →
      (recPJ h j hj).emb wL ((recPJ h j hj).thAll wL) * (recPJ h j hj).emb w ((recPJ h j hj).shortTh w) ≤
        (recPJ h j hj).emb (WeightAlgebra.wadd w wL) ((recPJ h j hj).shortTh (WeightAlgebra.wadd w wL)) := by
    intro w hw h0
    refine emb_mul_le (recPJ h j hj) fun G hG F hF' => ?_
    have hc : (G.1 : T.R j) * F.1 ∈ cutR T.C j (WeightAlgebra.wadd w wL) := by
      rw [cutR_eq T.C hj]
      exact h.toLawsCore.mul j hj w wL _ (cutR_le T.C j w G.2) _ (cutR_le T.C j wL F.2)
    refine ⟨⟨_, hc⟩, ?_, ?_⟩
    · exact mul_mem_span_of_gen (one hC D T h j hj hsh hone hA w wL hw h0) hG hF'
    · exact (incG_mul deg (cutR T.C j) (deg_wadd w wL) G F _).symm
  have key := pow_mul_short_le (recPJ h j hj) ka wL hka step
  have hdeg : deg wF + Tn • deg wL = deg ka := by
    obtain ⟨_, hP, hM⟩ := hF
    refine Prod.ext (funext fun τ => funext fun i => ?_) (Prod.ext (funext fun τ => funext fun i => ?_) hn.symm)
    · change wF.aP τ i + Tn * wL.aP τ i = ka.aP τ i
      have := hP τ i
      zify
      linarith
    · change wF.aM τ i + Tn * wL.aM τ i = ka.aM τ i
      have := hM τ i
      zify
      linarith
  refine sup_le (sup_le (key Tn wF hr hdeg) (key _ _ (hr.trans (Nat.le_add_right _ _)) ?_)) le_rfl
  have e : deg ((recPJ h j hj).wF0 wL wF) = deg wF + WeightFamilies.dimY D j • deg wL := rfl
  rw [e, add_assoc, ← add_nsmul, Nat.add_sub_of_le hD, hdeg]

end GlobalTheory.FormTies
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ScaledThetaTranslationQuotientElliptic
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.ScaledQuot

theorem not_inOK_neg_half (d : ℕ) (hd : 0 < d) : ¬ InOK d ((0 : ℂ) - 1 / 2) := by
  rintro ⟨u, v, h⟩
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp [wK] at him hre
  have hv : v = 0 := by
    rcases him with h | h
    · exact h
    · exact absurd h hd.ne'
  subst hv
  have h2 : (2 * u : ℝ) = -1 := by
    simp at hre
    linarith
  have h3 : (2 * u : ℤ) = -1 := by exact_mod_cast h2
  omega

theorem inOK_nat_mul (d s : ℕ) {l : ℂ} (hl : InOK d l) : InOK d ((s : ℂ) * l) := by
  obtain ⟨u, v, rfl⟩ := hl
  exact ⟨s * u, s * v, by push_cast; ring⟩

theorem inOK_nat (d s : ℕ) : InOK d (s : ℂ) := ⟨s, 0, by simp⟩

theorem zero_iff_of_fixed {d : ℕ} {θ : ℂ → ℂ} {x : ℂ} (h : W1 d x θ = θ) (z : ℂ) :
    θ (z + x) = 0 ↔ θ z = 0 := by
  have := congrFun h z
  rw [← this]
  simp [W1, U1, Complex.exp_ne_zero]

theorem scaled_quotient_elliptic : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → ∀ (t : ℂ) (s : ℕ), 0 < s → Nat.Coprime s q → InOK d ((s : ℂ) * t) → let φ : ℂ → ℂ := fun z => U1 d t θ ((s : ℂ) * z) / θ ((s : ℂ) * z); Ell M.L φ ∧ AnalyticAt ℂ φ 0 ∧ (∀ p, θ ((s : ℂ) * p) ≠ 0 → AnalyticAt ℂ φ p) ∧ (∀ p r, PrimeTo d q r → ¬ InOK d (r - 1 / 2) → θ ((s : ℂ) * p + r) = 0 → ¬ M.Small p) ∧ Bdd (hat M.ι (C ω * logS) φ) := by
  intro d q _ M ω θ hd hd7 hsp hL hch hθ t s hs hsq hst φ
  obtain ⟨hdiff, h0, -, hW, hz⟩ := hθ
  obtain ⟨-, -, hUd, -, -, hper, -, -⟩ := _root_.GlobalTheory.MomOne.heisenbergOne d hd.pos
  obtain ⟨-, -, -, -, -, hint, -⟩ := GlobalTheory.MomOne.okArith d q M.ι hd hd7 hsp
  obtain ⟨-, -, -, hsm⟩ := _root_.GlobalTheory.MomOne.smallTors d q M ω hd hd7 hsp hL hch
  have hlin : Differentiable ℂ (fun z : ℂ => (s : ℂ) * z) := by fun_prop
  have hN : ∀ p, AnalyticAt ℂ (fun z => U1 d t θ ((s : ℂ) * z)) p := fun p =>
    ((hUd t θ hdiff).1.comp hlin).analyticAt p
  have hD : ∀ p, AnalyticAt ℂ (fun z => θ ((s : ℂ) * z)) p := fun p =>
    (hdiff.comp hlin).analyticAt p
  have han : ∀ p, θ ((s : ℂ) * p) ≠ 0 → AnalyticAt ℂ φ p := fun p hp =>
    (hN p).div (hD p) hp
  have hE : Ell M.L φ := by
    refine ⟨fun p => (hN p).meromorphicAt.div (hD p).meromorphicAt, ?_⟩
    intro l hl z
    have hl' : InOK d l := (hL l).1 hl
    have hWl := hW _ (inOK_nat_mul d s hl')
    have hk : kap1 d ((s : ℂ) * l) t = 1 := by
      obtain ⟨k, hk⟩ := hint l _ hl' hst
      have e : h1 d ((s : ℂ) * l) t = h1 d l ((s : ℂ) * t) := by
        simp only [h1, map_mul, Complex.conj_natCast]; ring
      rw [kap1, e, hk]
      have := Complex.exp_int_mul_two_pi_mul_I (-k)
      rw [← this]
      congr 1
      push_cast; ring
    have hp := hper θ t ((s : ℂ) * l) ((s : ℂ) * z) hWl
    rw [hk, one_mul] at hp
    show U1 d t θ ((s : ℂ) * (z + l)) / θ ((s : ℂ) * (z + l)) = U1 d t θ ((s : ℂ) * z) / θ ((s : ℂ) * z)
    rw [mul_add]
    by_cases hz0 : θ ((s : ℂ) * z) = 0
    · rw [hz0, (zero_iff_of_fixed hWl _).2 hz0, div_zero, div_zero]
    · have hz1 : θ ((s : ℂ) * z + (s : ℂ) * l) ≠ 0 := fun h => hz0 ((zero_iff_of_fixed hWl _).1 h)
      rw [div_eq_div_iff hz1 hz0]
      exact hp
  have hA0 : AnalyticAt ℂ φ 0 := han 0 (by rw [mul_zero, h0]; exact one_ne_zero)
  have hpole : ∀ p r, PrimeTo d q r → ¬ InOK d (r - 1 / 2) → θ ((s : ℂ) * p + r) = 0 → ¬ M.Small p := by
    intro p r hr hr2 hθ0 hsmall
    exact hr2 (hsm p s r (inOK_nat d s) (by exact_mod_cast hs.ne') hr (hz _ hθ0) hsmall).2
  refine ⟨hE, hA0, han, hpole, _root_.GlobalTheory.MomOne.EllBdd.bdd_hat_of_ell q M _ φ hch hE hA0 ?_⟩
  intro p hp
  have hθp : θ ((s : ℂ) * p) = 0 := by
    by_contra hne
    exact absurd hp (not_lt.mpr (han p hne).meromorphicOrderAt_nonneg)
  exact hpole p 0 ⟨1, one_pos, Nat.coprime_one_left q, ⟨0, 0, by simp⟩⟩ (not_inOK_neg_half d hd.pos) (by rw [add_zero]; exact hθp)

end GlobalTheory.MomOne.ScaledQuot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SupLatticeIsLatInStable
section
set_option autoImplicit false

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.FormTies

section General

variable {F : Type} [Field F] {K : Type} [Field K] [NumberField K] [Algebra F K]
  {C : Type} [AddCommGroup C] [Module F C] [Module (𝓞 F) C] [IsScalarTower (𝓞 F) F C] {n : ℕ}


omit [NumberField K] [Module (𝓞 F) C] [IsScalarTower (𝓞 F) F C] in
theorem coord_one_tmul_smul (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C) (r : F) (f : C) :
    z.symm (1 ⊗ₜ[F] (r • f)) = algebraMap F K r • z.symm (1 ⊗ₜ[F] f) := by
  rw [← map_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
    Algebra.smul_def, smul_eq_mul]

theorem spanK_span (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C) (s : Set C) :
    spanK z (Submodule.span (𝓞 F) s : Set C) = spanK z s := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨f, hf, rfl⟩
    induction hf using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [TensorProduct.tmul_add, map_add (f := _)]
      exact Submodule.add_mem _ hx hy
    | smul r x _ hx =>
      have hi : IsIntegral ℤ (algebraMap F K (r : F)) :=
        (RingOfIntegers.isIntegral_coe r).map (algebraMap F K).toIntAlgHom
      have e : z.symm (1 ⊗ₜ[F] (r • x)) = (⟨algebraMap F K (r : F), hi⟩ : 𝓞 K) • z.symm (1 ⊗ₜ[F] x) := by
        rw [← algebraMap_smul F r x, coord_one_tmul_smul]
        rfl
      simp only [e]
      exact Submodule.smul_mem _ _ hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem spanK_isLatIn (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C) (M : Submodule (𝓞 F) C) (hfg : M.FG)
    (htop : Submodule.span F (M : Set C) = ⊤) : Formalism.EigenvalueLevelCeiling.IsLatIn ⊤ (spanK z (M : Set C)) := by
  constructor
  · obtain ⟨s, rfl⟩ := hfg
    rw [spanK_span]
    exact Submodule.fg_span (s.finite_toSet.image _)
  · have h1 : ∀ f : C, z.symm (1 ⊗ₜ[F] f) ∈ Submodule.span K (spanK z (M : Set C) : Set (Fin n → K)) := by
      intro f
      have hf : f ∈ Submodule.span F (M : Set C) := htop ▸ Submodule.mem_top
      induction hf using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span (Submodule.subset_span ⟨x, hx, rfl⟩)
      | zero => simp
      | add x y _ _ hx hy =>
        simp only [TensorProduct.tmul_add, map_add (f := _)]
        exact Submodule.add_mem _ hx hy
      | smul r x _ hx =>
        rw [coord_one_tmul_smul]
        exact Submodule.smul_mem _ _ hx
    rw [eq_top_iff]
    intro x _
    obtain ⟨t, rfl⟩ := z.symm.surjective x
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul k f =>
      have e : (k ⊗ₜ[F] f : K ⊗[F] C) = k • (1 ⊗ₜ[F] f) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [e, map_smul]
      exact Submodule.smul_mem _ _ (h1 f)
    | add x y hx hy =>
      rw [map_add (f := _)]
      exact Submodule.add_mem _ (hx trivial) (hy trivial)

end General

theorem supLattice_isLatIn_stable : ∀ (D : D7) (B : WeightFamilies.Prov D) (P6 : ModuliIntegralCharts.Prov D) (j : ℕ) (X : WeightAlgebra.PJ D B P6 j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra B.KO K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (v : HeightOneSpectrum (𝓞 K)) (i : Bs.J) (z : (Fin (O.nZ i) → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j ka) (act : P → B.Cusp j ka → B.Cusp j ka), FormTie X hinj EX p ka wL wF T O v i z act → Submodule.IsFullLattice B.KO (B.Mlat j ka) → (∀ g, ∀ F ∈ B.Mlat j ka, act g F ∈ B.Mlat j ka) → Formalism.EigenvalueLevelCeiling.IsLatIn ⊤ (O.Ms i) ∧ ∀ g : P, (O.Ms i).map ((O.ρ i g).restrictScalars (𝓞 K)) ≤ O.Ms i := by
  intro D B P6 j X hinj EX p ka wL wF T K _ _ _ _ Bs Df S P _ _ oc O v i z act h hL hact
  rw [h.Ms_eq]
  refine ⟨spanK_isLatIn z _ hL.toIsLattice.fg hL.span_eq_top, fun g => ?_⟩
  rw [Submodule.map_le_iff_le_comap]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, hf, rfl⟩
  show O.ρ i g (z.symm (1 ⊗ₜ f)) ∈ spanK z _
  rw [h.rho_eq]
  exact Submodule.subset_span ⟨act g f, hact g f hf, rfl⟩

end GlobalTheory.FormTies
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaScaledSpanLeSigmaSmulUnscaledSpan
section
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.ScaledSpan

section General

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A]

def sc (s : R) (N : Submodule R A) : Submodule R A := N.map (s • LinearMap.id)

theorem mem_sc {s : R} {N : Submodule R A} {x : A} : x ∈ sc s N ↔ ∃ y ∈ N, x = s • y := by
  simp [sc, eq_comm]

theorem sc_mul_le {s t : R} {M M' N N' : Submodule R A} (h : M ≤ sc s M') (h' : N ≤ sc t N') :
    M * N ≤ sc (s * t) (M' * N') := by
  refine Submodule.mul_le.2 fun m hm n hn => ?_
  obtain ⟨a, ha, rfl⟩ := mem_sc.1 (h hm)
  obtain ⟨b, hb, rfl⟩ := mem_sc.1 (h' hn)
  exact mem_sc.2 ⟨a * b, Submodule.mul_mem_mul ha hb, smul_mul_smul_comm s a t b⟩

theorem sc_pow_le {s : R} {M M' : Submodule R A} (h : M ≤ sc s M') (n : ℕ) :
    M ^ n ≤ sc (s ^ n) (M' ^ n) := by
  induction n with
  | zero => intro x hx; exact mem_sc.2 ⟨x, by simpa using hx, by simp⟩
  | succ n ih => rw [pow_succ, pow_succ, pow_succ]; exact sc_mul_le ih h

theorem sc_le_of_dvd {s t : R} {M N : Submodule R A} (hd : t ∣ s) (h : M ≤ N) : sc s M ≤ sc t N := by
  obtain ⟨c, rfl⟩ := hd
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_sc.1 hx
  exact mem_sc.2 ⟨c • y, N.smul_mem c (h hy), mul_smul t c y⟩

end General

variable {D : D7} {B : WeightFamilies.Prov D} {P6 : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem emb_WWc_le (X : WeightAlgebra.PJ D B P6 j) (s : 𝓞 B.KO) (w : WeightFamilies.Wt D j) :
    X.emb w (X.WWc s w) ≤ sc s (X.emb w (X.thAll w)) := by
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  exact mem_sc.2 ⟨_, ⟨y, hy, rfl⟩, by simp⟩

theorem emb_Thc_le (X : WeightAlgebra.PJ D B P6 j) (s : 𝓞 B.KO) (w : WeightFamilies.Wt D j) :
    X.emb w (X.Thc s w) ≤
      sc (s * ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 B.KO) ^ (D.R.f * D.R.r * w.n)) (X.emb w (X.shortTh w)) := by
  rintro _ ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
  refine mem_sc.2 ⟨_, ⟨y, hy, rfl⟩, ?_⟩
  simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul, mul_smul]
  exact smul_comm _ _ _

theorem nnW_eq (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
    {ka wL wF : WeightFamilies.Wt D j} {T n : ℕ} (h : WeightAlgebra.IsF' ka wL wF T n) :
    nnW B hinj EX ka = nnW B hinj EX wL ^ T * nnW B hinj EX wF := by
  obtain ⟨-, hP, hM⟩ := h
  have hP' : ∀ τ i, ka.aP τ i = wL.aP τ i * T + wF.aP τ i := fun τ i => by
    have := hP τ i
    zify
    linarith
  have hM' : ∀ τ i, ka.aM τ i = wL.aM τ i * T + wF.aM τ i := fun τ i => by
    have := hM τ i
    zify
    linarith
  have h1 : Dplus ka = Dplus wL * T + Dplus wF := by
    simp only [Dplus, hP', Finset.sum_add_distrib, Finset.sum_mul]
  have h2 : Dminus ka = Dminus wL * T + Dminus wF := by
    simp only [Dminus, hM', Finset.sum_add_distrib, Finset.sum_mul]
  simp only [nnW, h1, h2, Fin.prod_univ_two]
  ring

theorem nnW_ne_zero (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
    (w : WeightFamilies.Wt D j) : nnW B hinj EX w ≠ 0 := by
  have hn : ∀ i, EX.piG i * piBarO EX i = (D.host.g i : 𝓞 D.host.E) := fun i => by
    apply Subtype.ext
    exact EX.piG_norm i
  have hn' : ∀ i, iE D hinj B (EX.piG i) * iE D hinj B (piBarO EX i) ≠ 0 := fun i => by
    rw [← map_mul, hn, map_natCast]
    exact_mod_cast (D.host.g_prime i).ne_zero
  exact Finset.prod_ne_zero_iff.2 fun i _ =>
    mul_ne_zero (pow_ne_zero _ (left_ne_zero_of_mul (hn' i))) (pow_ne_zero _ (right_ne_zero_of_mul (hn' i)))

theorem theta_le_sigma_smul : ∀ (D : D7) (B : WeightFamilies.Prov D) (P6 : ModuliIntegralCharts.Prov D) (j : ℕ) (X : WeightAlgebra.PJ D B P6 j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ), WeightAlgebra.IsF' ka wL wF T wF.n → ka.n = wF.n + T * wL.n → WeightFamilies.dimY D j ≤ T → sigRec B hinj EX ka wL wF T ≠ 0 ∧ ∀ F ∈ X.Theta (scalOfP B hinj EX p ka wL wF T) ka wL wF T, ∃ G ∈ thetaPlain X ka wL wF T, F = sigRec B hinj EX ka wL wF T • G := by
  intro D B P6 j X hinj EX p ka wL wF T hF hn hT
  refine ⟨?_, fun F hF' => mem_sc.1 (?_ : F ∈ sc _ _)⟩
  · refine mul_ne_zero (nnW_ne_zero B hinj EX ka) (Nat.cast_ne_zero.2 ?_)
    have hq : D.host.q ≠ 0 := (D.host.hyp.1 : D.host.q.Prime).ne_zero
    have hd : D.host.d ≠ 0 := (D.host.hyp.2.1 : D.host.d.Prime).ne_zero
    have h0 := (D.host.g_prime 0).ne_zero
    have h1 := (D.host.g_prime 1).ne_zero
    have hS : D.host.QS ≠ 0 := D.host.QS_pos.ne'
    unfold pPow
    positivity
  · revert F
    change X.Theta _ ka wL wF T ≤ _
    have hnn := nnW_eq B hinj EX hF
    refine sup_le (sup_le ?_ ?_) ?_
    · refine (sc_mul_le (sc_pow_le (emb_WWc_le X _ wL) T) (emb_Thc_le X _ wF)).trans
        (sc_le_of_dvd ⟨(zOwnP D p wF : 𝓞 B.KO), ?_⟩ (le_sup_left.trans le_sup_left))
      simp only [scalOfP, sigRec, hnn, pPow]
      push_cast
      ring
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hT
      refine (sc_mul_le (sc_pow_le (emb_WWc_le X _ wL) _) (emb_Thc_le X _ _)).trans
        (sc_le_of_dvd ⟨(zOwnP D p (X.wF0 wL wF) : 𝓞 B.KO) *
          ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 B.KO) ^ (D.R.f * D.R.r * (WeightFamilies.dimY D j * wL.n)), ?_⟩
          (le_sup_right.trans le_sup_left))
      have e : (X.wF0 wL wF).n = wF.n + WeightFamilies.dimY D j * wL.n := rfl
      simp only [scalOfP, sigRec, hnn, pPow, e, Nat.add_sub_cancel_left]
      unfold WeightAlgebra.PJ.wF0
      push_cast
      ring
    · refine (emb_Thc_le X _ ka).trans
        (sc_le_of_dvd ⟨(zOwnP D p ka : 𝓞 B.KO) *
          ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 B.KO) ^ (D.R.f * D.R.r * (T * wL.n)), ?_⟩ le_sup_right)
      simp only [scalOfP, sigRec, hnn, pPow, hn]
      push_cast
      ring

end GlobalTheory.ScaledSpan
end

