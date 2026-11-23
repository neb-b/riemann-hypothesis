module

public import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharpolySmulOfProd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0625
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0586
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0623
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0636
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0935
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0204
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0637
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0635
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0630
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0686
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0100
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0750
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
public import ReciprocityTheory.GaloisValuations.ArithOfA
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralMulConjEqOfLintegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmallIdealNeBot
section
namespace GlobalTheory.SmallPrimeIdeal

open NumberField

theorem norm_le_one_of_isIntegral {K : Type} [NormedField K] [IsUltrametricDist K] {y : K}
    (hy : IsIntegral ℤ y) : ‖y‖ ≤ 1 := by
  obtain ⟨p, hp, hpy⟩ := hy
  by_contra hlt
  rw [not_le] at hlt

  have heq : y ^ p.natDegree + ∑ i ∈ Finset.range p.natDegree, (p.coeff i : K) * y ^ i = 0 := by
    rw [hp.as_sum] at hpy
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X_pow] at hpy
    simp only [algebraMap_int_eq, eq_intCast] at hpy
    exact hpy
  rcases Nat.eq_zero_or_pos p.natDegree with h0 | hpos
  · rw [h0] at heq
    simp at heq
  obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
    (Finset.nonempty_range_iff.mpr hpos.ne') (fun i => (p.coeff i : K) * y ^ i)
  have hnorm : ‖y‖ ^ p.natDegree = ‖∑ i ∈ Finset.range p.natDegree, (p.coeff i : K) * y ^ i‖ := by
    rw [← norm_pow, eq_neg_of_add_eq_zero_left heq, norm_neg]
  have hterm : ‖(p.coeff i : K) * y ^ i‖ < ‖y‖ ^ p.natDegree := by
    rw [norm_mul, norm_pow]
    calc ‖(p.coeff i : K)‖ * ‖y‖ ^ i ≤ 1 * ‖y‖ ^ i :=
          mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_intCast_le_one K _) (by positivity)
      _ = ‖y‖ ^ i := one_mul _
      _ < ‖y‖ ^ p.natDegree := pow_lt_pow_right₀ hlt (Finset.mem_range.mp hi)
  linarith

theorem norm_int_le_one {L K : Type} [Field L] [NormedField K] [IsUltrametricDist K]
    (a : L →+* K) (x : 𝓞 L) : ‖a (x : L)‖ ≤ 1 := by

  exact norm_le_one_of_isIntegral ((NumberField.RingOfIntegers.isIntegral_coe x).map a.toIntAlgHom)

def smallIdeal {L K : Type} [Field L] [NormedField K] [IsUltrametricDist K]
    (a : L →+* K) : Ideal (𝓞 L) where
  carrier := {x | ‖a (x : L)‖ < 1}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    have h : ‖a (x : L) + a (y : L)‖ ≤ max ‖a (x : L)‖ ‖a (y : L)‖ :=
      IsUltrametricDist.norm_add_le_max _ _
    have e : a ((x + y : 𝓞 L) : L) = a (x : L) + a (y : L) := by simp
    change ‖a ((x + y : 𝓞 L) : L)‖ < 1
    rw [e]
    exact lt_of_le_of_lt h (max_lt hx hy)
  smul_mem' := by
    intro c x hx
    have e : a ((c • x : 𝓞 L) : L) = a (c : L) * a (x : L) := by simp
    change ‖a ((c • x : 𝓞 L) : L)‖ < 1
    rw [e, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right (norm_int_le_one a c) (norm_nonneg _) hx

theorem mem_smallIdeal {L K : Type} [Field L] [NormedField K] [IsUltrametricDist K]
    (a : L →+* K) (x : 𝓞 L) : x ∈ smallIdeal a ↔ ‖a (x : L)‖ < 1 := by
  exact Iff.rfl

theorem norm_eq_one {L K : Type} [Field L] [NormedField K] [IsUltrametricDist K]
    (a : L →+* K) (x : 𝓞 L) (h : ¬ ‖a (x : L)‖ < 1) : ‖a (x : L)‖ = 1 := by
  exact le_antisymm (norm_int_le_one a x) (not_lt.mp h)

theorem smallIdeal_isPrime {L K : Type} [Field L] [NormedField K] [IsUltrametricDist K]
    (a : L →+* K) : (smallIdeal a).IsPrime := by
  refine ⟨?_, ?_⟩
  ·
    rw [Ideal.ne_top_iff_one, mem_smallIdeal]
    simp
  · intro x y hxy
    rw [mem_smallIdeal] at hxy
    rw [mem_smallIdeal, mem_smallIdeal]
    by_contra hc
    push Not at hc
    obtain ⟨hx, hy⟩ := hc
    have e : a ((x * y : 𝓞 L) : L) = a (x : L) * a (y : L) := by simp
    rw [e, norm_mul, norm_eq_one a x (not_lt.mpr hx), norm_eq_one a y (not_lt.mpr hy)] at hxy
    norm_num at hxy

theorem exists_local_dvd {L : Type} [Field L] [NumberField L] (P : Ideal (𝓞 L)) [P.IsPrime]
    (hP : P ≠ ⊥) (u v : 𝓞 L) :
    ∃ r s : 𝓞 L, s ∉ P ∧ (u * r = v * s ∨ v * r = u * s) := by

  let Rp := Localization.AtPrime P
  have : IsDiscreteValuationRing Rp :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 L) hP Rp
  have hinj : Function.Injective (algebraMap (𝓞 L) Rp) :=
    IsLocalization.injective Rp P.primeCompl_le_nonZeroDivisors
  rcases ValuationRing.dvd_total (algebraMap (𝓞 L) Rp u) (algebraMap (𝓞 L) Rp v) with ⟨c, hc⟩ | ⟨c, hc⟩
  · obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl c
    refine ⟨r, s, s.2, Or.inl (hinj ?_)⟩
    rw [map_mul, map_mul, hc, mul_assoc, IsLocalization.mk'_spec]
  · obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl c
    refine ⟨r, s, s.2, Or.inr (hinj ?_)⟩
    rw [map_mul, map_mul, hc, mul_assoc, IsLocalization.mk'_spec]

theorem smallIdeal_ne_bot {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact l.Prime]
    (a : L →+* PadicAlgCl l) : smallIdeal a ≠ ⊥ := by

  intro hbot
  have hl : ((l : 𝓞 L)) ∈ smallIdeal a := by
    rw [mem_smallIdeal]
    have e : a ((l : 𝓞 L) : L) = (l : PadicAlgCl l) := by simp
    have hext := PadicAlgCl.norm_extends (p := l) (l : ℚ_[l])
    rw [map_natCast] at hext
    rw [e, hext, Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  rw [hbot, Ideal.mem_bot] at hl
  have h0 : ((l : 𝓞 L) : L) = 0 := by rw [hl]; simp
  exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h0)

theorem le_one_of_le_one {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact l.Prime]
    (a b : L →+* PadicAlgCl l)
    (h : ∀ x : 𝓞 L, ‖a (x : L)‖ < 1 ↔ ‖b (x : L)‖ < 1) (x : L) (hx : ‖a x‖ ≤ 1) :
    ‖b x‖ ≤ 1 := by
  classical
  have hb : ∀ y : 𝓞 L, y ∈ smallIdeal a ↔ ‖b (y : L)‖ < 1 := fun y => (mem_smallIdeal a y).trans (h y)
  have := smallIdeal_isPrime a

  obtain ⟨u, w, hw, rfl⟩ := IsFractionRing.div_surjective (𝓞 L) x
  change ‖a ((u : L) / (w : L))‖ ≤ 1 at hx
  change ‖b ((u : L) / (w : L))‖ ≤ 1
  have hw0 : (w : L) ≠ 0 := by
    have := nonZeroDivisors.ne_zero hw
    exact_mod_cast this

  obtain ⟨r, s, hs, hrs⟩ := exists_local_dvd (smallIdeal a) (smallIdeal_ne_bot a) u w
  have hs0 : (s : L) ≠ 0 := by
    intro h0
    apply hs
    have : s = 0 := by exact_mod_cast h0
    rw [this]
    exact (smallIdeal a).zero_mem
  have hbs : ‖b (s : L)‖ = 1 := norm_eq_one b s (fun hlt => hs ((hb s).mpr hlt))
  have has : ‖a (s : L)‖ = 1 := norm_eq_one a s (fun hlt => hs ((mem_smallIdeal a s).mpr hlt))
  rcases hrs with h1 | h1
  ·
    have h1' : (u : L) * r = w * s := by exact_mod_cast congrArg (fun z : 𝓞 L => (z : L)) h1
    have hr0 : (r : L) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at h1'
      exact mul_ne_zero hw0 hs0 h1'.symm
    have e : (u : L) / w = s / r := by
      rw [div_eq_div_iff hw0 hr0]
      linear_combination h1'
    rw [e] at hx ⊢
    rw [map_div₀, norm_div, has] at hx
    have hpos : 0 < ‖a (r : L)‖ := norm_pos_iff.mpr ((map_ne_zero a).mpr hr0)
    have har : ¬ ‖a (r : L)‖ < 1 := by
      intro hlt
      rw [div_le_iff₀ hpos] at hx
      linarith
    have hbr : ‖b (r : L)‖ = 1 := norm_eq_one b r (fun hlt => har ((h r).mpr hlt))
    rw [map_div₀, norm_div, hbs, hbr, div_one]
  ·
    have h1' : (w : L) * r = u * s := by exact_mod_cast congrArg (fun z : 𝓞 L => (z : L)) h1
    have e : (u : L) / w = r / s := by
      rw [div_eq_div_iff hw0 hs0]
      linear_combination -h1'
    rw [e, map_div₀, norm_div, hbs, div_one]
    exact norm_int_le_one b r

theorem norm_le_one_iff {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact (Nat.Prime l)]
    (a b : L →+* Formalism.ConjugateSelfDual.Qbar l)
    (h : ∀ x : 𝓞 L, ‖a (x : L)‖ < (1 : ℝ) ↔ ‖b (x : L)‖ < (1 : ℝ)) (x : L) :
    ‖a x‖ ≤ (1 : ℝ) ↔ ‖b x‖ ≤ (1 : ℝ) := by
  exact ⟨le_one_of_le_one a b h x, le_one_of_le_one b a (fun y => (h y).symm) x⟩

end GlobalTheory.SmallPrimeIdeal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehShapeIffOfDiscreteSpectrum
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DefiniteBC GlobalTheory.BcSpeh GlobalTheory.LFun
  GlobalTheory.PRep Formalism.UG

namespace GlobalTheory.BcSpehCompare

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Linear

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {w : HeightOneSpectrum (𝓞 E)}

omit [_root_.NumberField.IsTotallyComplex E] in
theorem isCompact_KGL : IsCompact (KGL w (n := a) : Set (GL (Fin a) (w.adicCompletion E))) :=
  IntPtsUnitary.isCompact_GLint _
    (isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers E w))

theorem injective_of_irred {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ G V} (hσ : σ.IsIrreducible) {τ : G → W → W} (h0 : ∀ g, τ g 0 = 0) {f : V →ₗ[ℂ] W} (hf0 : f ≠ 0)
    (hf : ∀ g v, f (σ g v) = τ g (f v)) : Function.Injective f := by
  rcases ((GlobalTheory.CuspRep.isIrreducible_iff _).1 hσ).2 (LinearMap.ker f) (fun g v hv => by
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hf, hv, h0]) with h | h
  · exact LinearMap.ker_eq_bot.1 h
  · exact absurd (LinearMap.ker_eq_top.1 h) hf0

theorem hasSat_iff {P : CuspSub E a} {σ : LocIrr w a} (h : P.IsLocComp w σ) (B : Multiset ℂˣ) :
    (CG.mk P).HasSat w B ↔ HasSatGL w σ.ρ B := by
  rw [CG.hasSat_mk]
  obtain ⟨f, h0, hf⟩ := h
  have hi := injective_of_irred σ.irred (τ := fun g => P.locRep w g) (fun _ => map_zero _) h0 hf
  have hfix : ∀ v ∈ fixed σ.ρ (KGL w (n := a)), f v ∈ fixed (P.locRep w) (KGL w (n := a)) := fun v hv =>
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => by rw [← hf, GlobalTheory.LGrp.mem_fixed.1 hv k hk]
  have hne : ∀ v, v ≠ 0 → f v ≠ 0 := fun v => (map_ne_zero_iff f hi).2
  constructor
  · intro hB
    refine ⟨?_, fun v hv hv0 => (hB.2 _ (hfix v hv) (hne v hv0)).of_map f hf hi⟩
    obtain ⟨φ, hφ, hφ0⟩ := (Submodule.ne_bot_iff _).1 hB.1
    have h1 : LinearMap.range f ⊓ fixed (P.locRep w) (KGL w (n := a)) ≠ ⊥ := fun e =>
      h0 (LinearMap.range_eq_bot.1 (LocEx.eq_bot_of_fixed P w isCompact_KGL hφ0 hφ _
        (by rintro g _ ⟨v, rfl⟩; exact ⟨_, hf g v⟩) e))
    obtain ⟨_, ⟨⟨v, rfl⟩, hv⟩, hv0⟩ := (Submodule.ne_bot_iff _).1 h1
    exact (Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 fun k hk => hi (by
      rw [hf, GlobalTheory.LGrp.mem_fixed.1 hv k hk]), fun e => hv0 (by rw [e, map_zero])⟩
  · intro hB
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hB.1
    refine ⟨(Submodule.ne_bot_iff _).2 ⟨f v, hfix v hv, hne v hv0⟩, fun x hx hx0 => ⟨hx0, hx, hB.card, fun ϖ hϖ j hj => ?_⟩⟩
    have htop : LocUniq.isoPart σ.ρ (P.locRep w) = ⊤ := by
      have hm := Submodule.map_injective_of_injective P.V.injective_subtype
      rcases P.irred ((LocUniq.isoPart σ.ρ (P.locRep w)).map P.V.subtype) (Submodule.map_subtype_le _ _) (by
        rintro o _ ⟨x, hx, rfl⟩
        exact ⟨_, LocUniq.isoPart_op P w σ.ρ o hx, rfl⟩) with h1 | h1
      · have h3 : f v ∈ LocUniq.isoPart σ.ρ (P.locRep w) :=
          Submodule.mem_iSup_of_mem (⟨f, fun g => LinearMap.ext (hf g)⟩ : σ.ρ.IntertwiningMap (P.locRep w)) ⟨v, rfl⟩
        rw [hm (h1.trans (Submodule.map_bot _).symm)] at h3
        exact absurd h3 (hne v hv0)
      · exact hm (h1.trans (Submodule.map_subtype_top _).symm)
    have hc := Final.GLintComm E w a
    have hT := Tj_mem_hecke (n := a) hϖ j
    let e := LocGL.idem (P.isSmooth_locRep w) (isCompact_KGL (w := w) (a := a))
    have key : ∀ y ∈ LocUniq.isoPart σ.ρ (P.locRep w),
        heckeVec (P.locRep w) (KGL w (n := a)) (Tj ℂ a (Ov E w) ϖ j) (e y) = satEig (qV E w) a B j • e y := fun y hy => by
      refine Submodule.iSup_induction _ (motive := fun y =>
        heckeVec (P.locRep w) (KGL w (n := a)) (Tj ℂ a (Ov E w) ϖ j) (e y) = satEig (qV E w) a B j • e y) hy ?_ ?_ ?_
      · rintro g _ ⟨u, rfl⟩
        have h1 : e (g.toLinearMap u) = g.toLinearMap (LocGL.idem σ.smooth isCompact_KGL u) :=
          (LocGL.map_idem σ.smooth _ _ g u).symm
        rw [h1, ← map_heckeVec hc hT g.toLinearMap fun k y => LinearMap.congr_fun (g.isIntertwining' k) y, ← map_smul]
        congr 1
        by_cases hu : LocGL.idem σ.smooth (isCompact_KGL (w := w) (a := a)) u = 0
        · simp [hu, heckeVec]
        · exact (hB.2 _ (LocGL.idem_mem _ _ u) hu).2.2.2 ϖ hϖ j hj
      · simp [heckeVec]
      · intro y z hy hz
        rw [map_add (f := _), smul_add, ← hy, ← hz]
        refine Eq.trans (finsum_congr fun _ => ?_)
          (finsum_add_distrib (finite_heckeVec hc hT _ (e y)) (finite_heckeVec hc hT _ (e z)))
        simp only [map_add (f := _), smul_add]
    have h2 := key x (htop ▸ Submodule.mem_top)
    rwa [show e x = x from LocGL.idem_of_mem _ _ hx] at h2

end Linear

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n c a : ℕ} {w : HeightOneSpectrum (𝓞 E)}

theorem not_isSplitAt {s : w.adicCompletion E →+* w.adicCompletion E}
    (hs : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x))
    (hv : ∀ x, Valued.v (s x) = Valued.v x) : ¬ IsSplitAt w := by
  rintro ⟨u, hu, e⟩
  have hw : ∀ k : E, w.valuation E (IsCMField.complexConj E k) = w.valuation E k := fun k => by
    have h1 : Valued.v (algebraMap E (w.adicCompletion E) k) = w.valuation E k :=
      w.valuedAdicCompletion_eq_valuation' k
    have h2 : Valued.v (algebraMap E (w.adicCompletion E) (IsCMField.complexConj E k)) =
        w.valuation E (IsCMField.complexConj E k) := w.valuedAdicCompletion_eq_valuation' _
    rw [← h1, ← h2, ← hs, hv]
  have := w.isPrime
  refine hu (HeightOneSpectrum.ext (u.isMaximal.eq_of_le w.isPrime.ne_top
    (GlobalTheory.FixedPrime.le_of_under_le w.asIdeal (fun x hx => ?_) _ (congrArg HeightOneSpectrum.asIdeal e).le)))
  rw [← w.valuation_lt_one_iff_mem (K := E)] at hx ⊢
  exact (hw x).symm.trans_lt hx

theorem isUnramU_of_hasSatAt {π : Submodule ℂ (UA E n → ℂ)} {s : w.adicCompletion E →+* w.adicCompletion E}
    (hs : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x))
    (hval : ∀ x, Valued.v (s x) = Valued.v x)
    {ϖ : w.adicCompletion E} {q : ℕ} {α : Fin (n / 2) → ℂˣ} (h : HasSatAt π w s ϖ q α) : IsUnramU π w := by
  obtain ⟨b, hb, hJ, p, hp, σ, ⟨hσ, f, h0, h1, h2⟩, hS⟩ := h
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hS.1
  obtain ⟨ι, -, hι, -⟩ := _root_.GlobalTheory.UnitaryBC.exists_locUnitary_embedding E n w s hs hval (not_isSplitAt hs hval)
  have hsurj : Function.Surjective p := fun g => by
    have hg : cT s g.1.val * antiJ _ n * g.1.val = antiJ _ n := g.2
    have hm : b * g.1 * b⁻¹ ∈ UJ s (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
      change cT s (b.val * g.1.val * (b⁻¹).val) * 1 * (b.val * g.1.val * (b⁻¹).val) = 1
      calc _ = cT s (b⁻¹).val * (cT s g.1.val * (cT s b.val * b.val) * g.1.val) * (b⁻¹).val := by
            simp only [cT_mul, Matrix.mul_assoc, Matrix.mul_one]
        _ = cT s (b.val * (b⁻¹).val) * (b.val * (b⁻¹).val) := by
            rw [hJ, hg, ← hJ]; simp only [cT_mul, Matrix.mul_assoc]
        _ = 1 := by rw [Units.mul_inv, cT_one, Matrix.mul_one]
    refine ⟨⟨_, (hι ⟨_, hm⟩).1⟩, Subtype.ext ?_⟩
    rw [hp, (hι _).2]
    group
  have hi : Function.Injective f := by
    choose t ht using hsurj
    exact injective_of_irred hσ (τ := fun g => RU E n (t g)) (fun _ => map_zero _) h0 fun g u => by
      rw [← h2, ht]
  refine ⟨f v, h1 v, (map_ne_zero_iff f hi).2 hv0, fun x hx hk => ?_⟩
  rw [← h2 ⟨x, hx⟩ v, GlobalTheory.LGrp.mem_fixed.1 hv _ ⟨(p _).2, ?_⟩]
  change (p ⟨x, hx⟩).val ∈ KGL w (n := n)
  rw [hp]
  exact mul_mem (mul_mem (inv_mem hb) hk) hb

theorem exists_hasSatAt
    (hE : ∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal)
    {π : Submodule ℂ (UA E n → ℂ)} (hπ : IsAutRepU π) (hw : ¬ IsSplitAt w) (hu : IsUnramU π w) :
    ∃ (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E) (q : ℕ) (α : Fin (n / 2) → ℂˣ),
      (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) ∧ IsUnramInv ϖ s q ∧
        HasSatAt π w s ϖ q α := by
  obtain ⟨s, ϖ, q, h1, h2⟩ := GlobalTheory.InertPlaceConj.exists_conj_isUnramInv E w (hE w) hw
  obtain ⟨α, h3⟩ := GlobalTheory.T.exists_satakeParameter_definiteUnitary_inertPlace E n w s ϖ q h1 h2 (GlobalTheory.T.finiteDimensional_definiteUnitary_levelForms E n (GlobalTheory.T.exists_finset_definiteUnitary_doubleCosets E n))
    (_root_.GlobalTheory.UnitaryBC.exists_locUnitary_embedding E n w s h1 h2.2.1 hw) π hπ hu
  exact ⟨s, ϖ, q, α, h1, h2, h3⟩

theorem isNormalised_of_isCsd {P : CuspSub E a} (h : P.IsCsd) : GlobalTheory.DiscSpec.IsNormalised P := by
  intro φ hφ t g
  obtain ⟨ω, hω⟩ := Central.exists_hasCentral E a P
  have h1 := CsdUnitary.dchi_theta hω h fun _ => (t : ℂ)
  have h2 : dchi ω (fun _ => (t : ℂ)) = 0 := by
    rw [show star (fun _ => (t : ℂ) : Cinf E) = fun _ => (t : ℂ) from funext fun _ => Complex.conj_ofReal t,
      map_neg] at h1
    linear_combination -h1 / 2
  have h3 := chiInf_expU ω fun _ => (t : ℂ)
  rw [h2, Complex.exp_zero] at h3
  have h4 := hω.apply hφ (infId E (expU fun _ => (t : ℂ))) g
  rw [show ((ω.1 (infId E (expU fun _ => (t : ℂ))) : ℂˣ) : ℂ) = 1 from h3, one_mul] at h4
  rw [← h4]
  exact congrArg (fun x => φ.1 (x * g)) (cornerGL_scalar (sInf E) _)

end CM

end GlobalTheory.BcSpehCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransferEqOfIsOpenKer
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.ArtinTransfer

open scoped Pointwise
open UpperTheory.V.Base (galOf galEmb galEmbTop range_galEmb galEmb_mem)
open Formalism.L2.Host (IsUnitAt IsUnifAt aboveF)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap finiteCompletionMap infiniteAdeleMap)

section Group

variable {Γ B : Type} [Group Γ] [CommGroup B] {H : Subgroup Γ} [H.FiniteIndex] (φ : H →* B)

end Group

section Places

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω] [Algebra L Ω]


variable [Algebra K L] [IsScalarTower K L Ω]

end Places

section Ideles

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable {K} in
theorem loc_same (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) : (localIdele K v x).val.2 v = x := by
  classical
  exact Pi.mulSingle_eq_same v _

variable {K} in
theorem loc_ne {v w : HeightOneSpectrum (𝓞 K)} (h : w ≠ v) (x : (v.adicCompletion K)ˣ) :
    (localIdele K v x).val.2 w = 1 := by
  classical
  exact Pi.mulSingle_eq_of_ne h _

theorem ideleMap_apply (a : Ideles K) (w : HeightOneSpectrum (𝓞 L)) :
    (ideleMap K L a).val.2 w = finiteCompletionMap K L w (a.val.2 (w.under (𝓞 K))) := rfl

end Ideles

section Artin

variable {K L Ω B : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω] [Algebra L Ω]
  [CommGroup B]

variable [Algebra K L]


variable [IsScalarTower K L Ω] [IsAlgClosure K Ω] [IsAlgClosure L Ω]

end Artin

end GlobalTheory.ArtinTransfer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldMirabolic
section
noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric GlobalTheory.MirTower
open scoped ENNReal NNReal ComplexConjugate

namespace GlobalTheory.MirTower

theorem unfold_mirabolic : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) [MeasurableSpace (GA E a)] [BorelSpace (GA E a)] (μ : Measure (GA E a)) [μ.IsHaarMeasure] (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ (𝓕 𝓕₀ : Set (GA E a)), IsFundamentalDomain (ratMirU E a (a - 1)) 𝓕 μ → IsFundamentalDomain (ratMirU E a 0) 𝓕₀ μ → ∀ (w : GA E a → ℝ≥0), Measurable w → (∀ γ ∈ mirU E a (a - 1), ∀ g, w (ratGL E a γ * g) = w g) → (∀ (k : ℕ) (y : UnipotentBlockColumnIndex a k k → Ad E) (g : GA E a), w (blkU y * g) = w g) → (∀ f, Good ψ (a - 1) f → ∫⁻ g in 𝓕, ‖f g‖ₑ ^ 2 * w g ∂μ = ∫⁻ g in 𝓕₀, ‖whit ψ (a - 1) f g‖ₑ ^ 2 * w g ∂μ) ∧ ∀ f f', Good ψ (a - 1) f → Good ψ (a - 1) f' → ∫⁻ g in 𝓕, ‖f g‖ₑ ^ 2 * w g ∂μ ≠ ⊤ → ∫⁻ g in 𝓕, ‖f' g‖ₑ ^ 2 * w g ∂μ ≠ ⊤ → IntegrableOn (fun g => f g * conj (f' g) * (w g : ℝ)) 𝓕 μ ∧ IntegrableOn (fun g => whit ψ (a - 1) f g * conj (whit ψ (a - 1) f' g) * (w g : ℝ)) 𝓕₀ μ ∧ ∫ g in 𝓕, f g * conj (f' g) * (w g : ℝ) ∂μ = ∫ g in 𝓕₀, whit ψ (a - 1) f g * conj (whit ψ (a - 1) f' g) * (w g : ℝ) ∂μ := by
  intro E _ _ a _ _ μ _ ψ hψ 𝓕 𝓕₀ h𝓕 h𝓕₀ w hw hwΓ hwU

  have hm : a - 1 < a ∨ a - 1 = 0 := by omega

  have : SecondCountableTopology (GA E a) := secondCountable_GA

  have : LocallyCompactSpace (Ad E) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  have : LocallyCompactSpace (Matrix (Fin a) (Fin a) (Ad E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin a → Ad E))
  have : LocallyCompactSpace (Matrix (Fin a) (Fin a) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  have : LocallyCompactSpace (GA E a) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  have : SFinite μ := inferInstance
  refine ⟨fun f hf => ?_, fun f f' hf hf' h1 h2 => ?_⟩
  · exact lintegral_tower μ hψ hm h𝓕 h𝓕₀ (fun g => (w g : ℝ≥0∞)) (by fun_prop)
      (fun γ hγ g => by simp only [hwΓ γ hγ g]) (fun k _ y g => by simp only [hwU k y g]) hf
  · exact integral_tower μ hψ hm h𝓕 h𝓕₀ w hw hwΓ (fun k _ y g => hwU k y g) hf hf' h1 h2

end GlobalTheory.MirTower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupAtPlaceDenseInDecompositionGroupStatement
section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilGroupAtPlace_dense_in_decompositionGroup : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), ∀ d ∈ Dec (F := E) A, ∀ y : Ω, ∃ τ ∈ Weil h, τ y = d y := by
  first | exact @GlobalTheory.WeilDeligne.exists_weil_apply_eq | exact GlobalTheory.WeilDeligne.exists_weil_apply_eq | (intros; apply GlobalTheory.WeilDeligne.exists_weil_apply_eq <;> assumption)
end

