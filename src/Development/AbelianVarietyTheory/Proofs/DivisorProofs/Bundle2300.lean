module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0804
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1979
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2062
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmple
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2193
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2183
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesAlgHomKillHighOrder
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

theorem mvPowerSeries_algHom_kill_high_order :
    ∀ (k : Type) [CommRing k] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra k A],
      ∀ φ : MvPowerSeries σ k →ₐ[k] A, (∀ i, IsNilpotent (φ (X i))) →
        ∃ N : ℕ, ∀ f : MvPowerSeries σ k,
          (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → φ f = 0 := by
  intro k _ σ _ A _ _ φ hφ
  classical
  haveI := Fintype.ofFinite σ
  choose m hm using hφ
  set M := Finset.univ.sup m with hMdef
  have hM : ∀ i, φ (X i) ^ M = 0 := fun i =>
    pow_eq_zero_of_le (Finset.le_sup (Finset.mem_univ i)) (hm i)
  refine ⟨Fintype.card σ * M + 1, fun f hf => ?_⟩

  let fi : σ → MvPowerSeries σ k := fun i α =>
    if h : ∃ j, M ≤ α j then (if h.choose = i then coeff α f else 0) else 0
  have hcoeff : ∀ i α, coeff α (fi i) =
      if h : ∃ j, M ≤ α j then (if h.choose = i then coeff α f else 0) else 0 :=
    fun i α => rfl
  have hsum : f = ∑ i, fi i := by
    ext α
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [hcoeff]
    by_cases h : ∃ j, M ≤ α j
    · simp only [dif_pos h]
      rw [Finset.sum_ite_eq]
      simp
    · simp only [dif_neg h, Finset.sum_const_zero]
      apply hf
      push_neg at h
      rw [Finsupp.degree_eq_sum]
      calc ∑ i, α i ≤ ∑ _i : σ, M := Finset.sum_le_sum fun i _ => (h i).le
        _ = Fintype.card σ * M := by simp
        _ < Fintype.card σ * M + 1 := Nat.lt_succ_self _
  have hdvd : ∀ i, (X i : MvPowerSeries σ k) ^ M ∣ fi i := by
    intro i
    rw [MvPowerSeries.X_pow_dvd_iff]
    intro α hα
    rw [hcoeff]
    split_ifs with h h'
    · exact absurd (h'.symm ▸ h.choose_spec) (not_le.mpr hα)
    · rfl
    · rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  obtain ⟨g, hg⟩ := hdvd i
  rw [hg, map_mul, map_pow, hM i, zero_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatMulIntegralMemCmLatticePrimeTo
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

namespace GlobalTheory.HilbFam.LatDen

theorem nat_mul_integral_mem_lattice : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) (c : Ideal (OF E)) (y : (Af E)ˣ) (R : ℕ), l.Prime → OneOver l y → 0 < R → (R : OF E) ∈ c → ∃ M : ℕ, ¬ l ∣ M ∧ ∀ x : E, IsIntegral ℤ x → ((M * R : ℕ) : E) * x ∈ lattice c y := by
  intro E _ _ l c y R hl hy hR hRc
  obtain ⟨M, hM, hMz⟩ := GlobalTheory.HilbFam.AdeleDen.exists_den_prime_to E l ((y⁻¹ : (Af E)ˣ) : Af E) hl (fun w hw => by
    have h1 : ((y⁻¹ : (Af E)ˣ) : Af E) w * (y : Af E) w = 1 := by
      have h := congrArg (fun a : Af E => a w) (Units.inv_mul y)
      exact h
    rw [hy w hw, mul_one] at h1
    rw [h1, map_one])
  refine ⟨M, hM, fun x hx => ?_⟩
  show algebraMap E (Af E) (((M * R : ℕ) : E) * x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c
  refine GlobalTheory.CMVal.LatEnt.mem_hatO_of_sub hR hRc (zero_mem _) fun P => ?_
  have e : (algebraMap E (Af E) (((M * R : ℕ) : E) * x) * ((y⁻¹ : (Af E)ˣ) : Af E)) P - (0 : Af E) P =
      (R : P.adicCompletion E) * (algebraMap E (P.adicCompletion E) x *
        (algebraMap E (Af E) (M : E) * ((y⁻¹ : (Af E)ˣ) : Af E)) P) := by
    rw [show (0 : Af E) P = 0 from rfl, sub_zero,
      show (algebraMap E (Af E) (M : E) * ((y⁻¹ : (Af E)ˣ) : Af E)) P =
        algebraMap E (P.adicCompletion E) (M : E) * ((y⁻¹ : (Af E)ˣ) : Af E) P from rfl]
    show algebraMap E (P.adicCompletion E) (((M * R : ℕ) : E) * x) * ((y⁻¹ : (Af E)ˣ) : Af E) P = _
    rw [map_mul, map_natCast, map_natCast]
    push_cast
    ring
  have hx1 : Valued.v (algebraMap E (P.adicCompletion E) x) ≤ 1 := by
    have h2 : Valued.v (algebraMap E (P.adicCompletion E) x) = P.valuation E x := by
      rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P]
      rfl
    rw [h2]
    have : x = algebraMap (𝓞 E) E ⟨x, hx⟩ := rfl
    rw [this]
    exact P.valuation_le_one _
  rw [e, map_mul, GlobalTheory.CMVal.LatEnt.radN, map_mul]
  exact mul_le_of_le_one_right' (mul_le_one' hx1 (hMz P))

end GlobalTheory.HilbFam.LatDen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefIntersectionNumberNonnegSubscheme
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
open GlobalTheory.Cartier
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FibreNef

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a : Y ⟶ X) (b : Z ⟶ Y) :
    LBIso (L.pull (b ≫ a)) ((L.pull a).pull b) :=
  LBIso.symm (LBIso.chartPull (chartPullLinComb L a (fun _ : PUnit => b)
      (fun _ => b ≫ a) (fun _ => 1) (𝟙 _) fun _ => (Category.id_comp _).symm)
      (chartPullId _) (PolBaseChange.lbIso_refl (LB.isLB_pull hL _)))

theorem isProjOver_fibre {k : Type} [CommRing k] [Module.Finite ℤ k] {X : Scheme.{0}} {p : X ⟶ Sp k}
    (hp : IsProjOver p) (l : ℕ) [Fact l.Prime] {Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i]
    [Algebra (ZMod l) Γ(Z, ⊤)] : IsProjOver (strHom (ZMod l) (X := Z)) := by
  obtain ⟨N, e, he, -⟩ := hp
  have hb : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have P₀ := GlobalTheory.ProjSpace.isPullback_baseChange N (Int.castRingHom k)
  have hf : IsFinite (GlobalTheory.ProjSpace.baseChange N (Int.castRingHom k)) :=
    MorphismProperty.of_isPullback P₀.flip hb
  have hZ : IsProjOver ((i ≫ e ≫ GlobalTheory.ProjSpace.baseChange N (Int.castRingHom k)) ≫ PSpace.str ℤ N) :=
    GlobalTheory.isProjOver_comp_of_isFinite _ ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩
  obtain ⟨M, φ, hφ, -⟩ := hZ
  have P := GlobalTheory.ProjSpace.isPullback_baseChange M (Int.castRingHom (ZMod l))
  have hc : IsClosedImmersion (spMap (Int.castRingHom (ZMod l))) :=
    IsClosedImmersion.spec_of_surjective _ (ZMod.ringHom_surjective _)
  have hcb : IsClosedImmersion (GlobalTheory.ProjSpace.baseChange M (Int.castRingHom (ZMod l))) :=
    MorphismProperty.of_isPullback P.flip hc
  let ψ := P.lift φ (strHom (ZMod l) Z) (specZIsTerminal.hom_ext _ _)
  have hψ : ψ ≫ PSpace.str (ZMod l) M = strHom (ZMod l) Z := P.lift_snd _ _ _
  have hψ' : ψ ≫ GlobalTheory.ProjSpace.baseChange M (Int.castRingHom (ZMod l)) = φ := P.lift_fst _ _ _
  have : IsClosedImmersion (ψ ≫ GlobalTheory.ProjSpace.baseChange M (Int.castRingHom (ZMod l))) := by
    rw [hψ']; exact hφ
  exact ⟨M, ψ, IsClosedImmersion.of_comp_isClosedImmersion ψ
    (GlobalTheory.ProjSpace.baseChange M (Int.castRingHom (ZMod l))), hψ⟩

theorem isNef_pull_of_nefOver {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (l : ℕ)
    [Fact l.Prime] {Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] [Algebra (ZMod l) Γ(Z, ⊤)]
    (L : HermLB p) (hL : NefOver L l) : IsNef (ZMod l) (L.B.pull i) := by
  have hLi := LB.isLB_pull L.isLB i
  refine isNef_iff_isClosedImmersion.2 ⟨hLi, fun C c hc hC hd _ => ?_⟩
  letI := algebraΓAlong (ZMod l) c
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have h := hL C (c ≫ i) (ZMod l) hd
  rw [interNumOn_eq_interNum_pull (fun r => rfl) (fun j => by fin_cases j; exact hLi)]
  rw [topSelfIntersection] at h
  refine h.trans_eq (interNum_congr_lbIso _ _ (fun _ => LB.isLB_pull L.isLB _)
    (fun j => by fin_cases j; exact LB.isLB_pull hLi c) fun j => ?_)
  fin_cases j
  exact lbIso_pull_comp L.isLB i c

end GlobalTheory.FibreNef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefShiftOfGeneratedAtCharZeroPoints
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefOfGen

theorem card_pos_of_isAlgPt {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}
    (hX : IsArithVar p D) {x : X} (hx : IsAlgPt x) : (0 : ℝ) < Nat.card (X.residueField x →+* ℂ) := by
  obtain ⟨hc, hd⟩ := hx
  obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint x
  have hr : Set.range i = closure {i (genericPoint Z)} := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h₁
    exact h₁.def.symm
  rw [topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hr] at hd
  have hbij : Function.Bijective (i.residueFieldMap (genericPoint Z)).hom := by
    refine ⟨RingHom.injective _, fun u => ?_⟩
    obtain ⟨u, rfl⟩ := Z.residue_surjective _ u
    obtain ⟨u, rfl⟩ := i.stalkMap_surjective _ u
    exact ⟨X.residue _ u, ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap i _) u⟩
  have hc' : CharZero (Z.residueField (genericPoint Z)) := (RingHom.charZero_iff hbij.1).1 hc
  have hcΓ : CharZero Γ(Z, ⊤) := (Z.Γevaluation (genericPoint Z)).hom.charZero
  have hZ : IsArithVar (i ≫ p) 0 := hX.of_isClosedImmersion i hcΓ hd
  have := GlobalTheory.SmallSecHeight.numberField hZ hc'
  rw [GlobalTheory.HtSelfInter.card_ringHom_eq]
  exact_mod_cast Nat.card_pos

theorem nef_of_gen : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (m N : ℕ) (s : Fin N → (M.pow m).B.Sec), 1 ≤ m → (∀ x : X, CharZero (X.residueField x) → ∃ i, x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s i)) → M.SemiPos D → NefFib M → ∃ t : ℝ, 0 ≤ t ∧ (M.shift (fun _ => t) fun _ => rfl).IsNef D := by
  intro hA k _ X _ p D hX M m N s hm hs hsp hf
  have hc : ∀ i, ∃ c : ℝ, s i ∈ ((M.shift (fun _ => -c) fun _ => rfl).pow m).smallSec :=
    fun i => GlobalTheory.AmpleHtLow.small_of_shift k X p D hX M m hm (s i)
  choose c hc using hc
  obtain ⟨h, H⟩ := (hA.arExists k X p D hX).1 M
  refine ⟨-(-(∑ i, |c i|)), ?_, GlobalTheory.HtSelfInter.isNef_shift hX hsp hf fun x hx => ?_⟩
  · rw [neg_neg]
    exact Finset.sum_nonneg fun j _ => abs_nonneg (c j)
  obtain ⟨i, hi⟩ := hs x hx.1
  have hN := card_pos_of_isAlgPt hX hx
  have hb : IsPtHt M x (h x / Nat.card (X.residueField x →+* ℂ)) :=
    ⟨h, H, (div_mul_cancel₀ _ hN.ne').symm⟩
  refine ⟨_, hb, ?_⟩
  have h1 := GlobalTheory.SmallSecHeight.le_ptHt k X p D hX M m (c i) _ x (s i) hm (hc i) hi hx hb
  have h2 : -(∑ j, |c j|) ≤ c i :=
    (neg_le_neg (Finset.single_le_sum (fun j _ => abs_nonneg (c j)) (Finset.mem_univ i))).trans (neg_abs_le _)
  exact h2.trans h1

end GlobalTheory.NefOfGen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NoetherianSubringPrimeContractionOrDvr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring

noncomputable section

namespace GlobalTheory.PrimeReach

theorem prime_contraction_or_dvr : ∀ (R : Type) [CommRing R] (R₁ : Subring R) [IsNoetherianRing R₁] (p : PrimeSpectrum R₁), p ∈ Set.range (PrimeSpectrum.comap R₁.subtype) ∨ ∃ (Q : PrimeSpectrum R) (k : Type) (_ : Field k) (i : R₁ →+* k) (j : k →+* Q.asIdeal.ResidueField) (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (ρ : R₁ →+* V) (e : k →+* FractionRing V), j.comp i = (algebraMap R Q.asIdeal.ResidueField).comp R₁.subtype ∧ e.comp i = (algebraMap V (FractionRing V)).comp ρ ∧ p ∈ Set.range (PrimeSpectrum.comap ρ) := by
  intro R _ R₁ _ p
  by_cases hp : p ∈ Set.range (PrimeSpectrum.comap R₁.subtype)
  · exact Or.inl hp
  right
  haveI := p.isPrime
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R₁)) (J := p.asIdeal) bot_le
  obtain ⟨P, hP, hPq⟩ :=
    Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective (f := R₁.subtype) Subtype.val_injective q hq
  let Q : PrimeSpectrum R := ⟨P, hP⟩
  haveI hqpr : q.IsPrime := hq.1.1
  let f₀ : R₁ →+* Q.asIdeal.ResidueField := (algebraMap R Q.asIdeal.ResidueField).comp R₁.subtype
  have hker : RingHom.ker f₀ = q := by
    rw [← hPq]
    ext x
    simp only [f₀, RingHom.mem_ker, RingHom.comp_apply, Ideal.mem_comap]
    exact (Ideal.algebraMap_residueField_eq_zero).trans Iff.rfl
  let A := R₁ ⧸ q
  let g₀ : A →+* Q.asIdeal.ResidueField := Ideal.Quotient.lift q f₀ (fun a ha => by rw [← RingHom.mem_ker, hker]; exact ha)
  have hg₀ : Function.Injective g₀ := by
    rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, Ideal.Quotient.lift_mk, ← RingHom.mem_ker, hker] at hx
    exact (Submodule.mem_bot _).2 (Ideal.Quotient.eq_zero_iff_mem.2 hx)
  let k := FractionRing A
  let i : R₁ →+* k := (algebraMap A k).comp (Ideal.Quotient.mk q)
  let j : k →+* Q.asIdeal.ResidueField := IsFractionRing.lift hg₀
  have hji : j.comp i = f₀ := by
    ext x
    simp only [i, j, RingHom.comp_apply, IsFractionRing.lift_algebraMap]
    rfl
  let p' : Ideal A := p.asIdeal.map (Ideal.Quotient.mk q)
  haveI hp' : p'.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hqp)
  have hcp' : p'.comap (Ideal.Quotient.mk q) = p.asIdeal := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.2 hqp
  let O := Localization.AtPrime p'
  haveI : IsDomain O := IsLocalization.isDomain_localization p'.primeCompl_le_nonZeroDivisors
  have hOinj : Function.Injective (algebraMap A O) := IsLocalization.injective O p'.primeCompl_le_nonZeroDivisors
  have hcm : (IsLocalRing.maximalIdeal O).comap (algebraMap A O) = p' := Localization.AtPrime.under_maximalIdeal
  have hnf : ¬ IsField O := by
    intro hF
    apply hp
    have hm : IsLocalRing.maximalIdeal O = ⊥ := by
      letI := hF.toField
      exact IsLocalRing.maximalIdeal_eq_bot
    have h1 : p' = ⊥ := by
      rw [← hcm, hm, ← RingHom.ker_eq_comap_bot,
        (RingHom.injective_iff_ker_eq_bot _).1 hOinj]
    refine ⟨Q, PrimeSpectrum.ext ?_⟩
    show P.comap R₁.subtype = p.asIdeal
    rw [hPq, ← hcp', h1, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  obtain ⟨V, _, _, _, ρ₀, hρinj, hρloc⟩ := GlobalTheory.KTrivSpread.exists_dvr O hnf
  let ρ : R₁ →+* V := ρ₀.comp ((algebraMap A O).comp (Ideal.Quotient.mk q))
  let g' : A →+* FractionRing V := (algebraMap V (FractionRing V)).comp (ρ₀.comp (algebraMap A O))
  have hg' : Function.Injective g' := (IsFractionRing.injective V (FractionRing V)).comp (hρinj.comp hOinj)
  let e : k →+* FractionRing V := IsFractionRing.lift hg'
  refine ⟨Q, k, inferInstance, i, j, V, inferInstance, inferInstance, inferInstance, ρ, e, hji, ?_, ?_⟩
  · ext x
    simp only [e, i, ρ, RingHom.comp_apply, IsFractionRing.lift_algebraMap]
    rfl
  · have hmV : (IsLocalRing.maximalIdeal V).comap ρ₀ = IsLocalRing.maximalIdeal O := by
      refine le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal V).ne_top)) ?_
      intro x hx
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact (IsLocalRing.mem_maximalIdeal x).1 hx (isUnit_of_map_unit ρ₀ x hu)
    refine ⟨⟨IsLocalRing.maximalIdeal V, inferInstance⟩, PrimeSpectrum.ext ?_⟩
    show (IsLocalRing.maximalIdeal V).comap ρ = p.asIdeal
    rw [show ρ = (ρ₀.comp (algebraMap A O)).comp (Ideal.Quotient.mk q) from rfl, ← Ideal.comap_comap,
      ← Ideal.comap_comap, hmV, hcm, hcp']

end GlobalTheory.PrimeReach
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegCompOfInjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PullDegCompGen

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem exists_isPullDeg_of_valW {i : R →+* R'} (D : DegPre R) (D' : DegPre R')
    {W : (Sp R).Opens} (ψW : PsiOn D W) (g : (TK R').left ⟶ (TW W).left) (hg : g ≫ W.ι = jK R' ≫ specOf i)
    {Φ : D'.P.A.left ⟶ D.P.A.left} (gp : IsGrpPullback D'.P.A D.P.A (spMap i) Φ)
    (w : LB.Iso D'.P.L (D.P.L.pull Φ)) (hw : PGen w)
    (hr : PMaps w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap i))
    (xe : D'.X ≃+ D.X) (hc : ∀ x, (D'.c x).left ≫ Φ = spMap i ≫ (D.c (xe x)).left)
    (hψ : ∀ (x : D'.X) (z : (TK R').left) J J', Good D.P.L z J → Good D'.P.L z J' →
      val (ψW.psi (xe x)) g z J = (om w z J J' (D'.xK x))⁻¹ * val (D'.psi x) (𝟙 _) z J') :
    ∃ hD : IsPullDeg i D D', proj hD = Φ := by
  obtain ⟨e, e_hom, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf i))
  subst he
  have hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = specOf i ≫ eSec D.P.A :=
    (cubeMapOf gp).e_comm
  have hx : ∀ x, g ≫ (toUnit (TW W) ≫ D.c (xe x)).left =
      D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) := fun x => by
    show g ≫ W.ι ≫ (D.c (xe x)).left = (jK R' ≫ (D'.c x).left) ≫ _
    rw [Category.assoc, hc, ← Category.assoc, hg, Category.assoc]
  choose b hb vb using fun x => exists_gen D.P.isLB (K' := PUnit)
    (φ' := fun _ => D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i)) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (hx x))
    (LB.pullGen D.P.L _ _ (ψW.psi (xe x)) g) (DVR.pullGen_isGen _ _ _ _ (ψW.psi_gen _) g)
  choose psi hpsi vpsi using fun x => DegPull.exists_down_val hw D.P.isLB D'.P.isLB (K := PUnit)
    (φ' := fun _ => D'.xK x) (ε := fun _ => -1) (fun _ => rfl) (b x) (hb x)
  have eψ : ∀ x, psi x = D'.psi x := fun x => TorusExt.gen_ext_val D'.P.isLB (hpsi x) (D'.psi_gen x) fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
    have v := vpsi x _ (𝟙 _) y _ _ (hJ.mem _ (𝟙 _)) (hJ'.mem _ (𝟙 _))
    have u := hψ x y J J' hJ hJ'
    have v₁ : val (b x) (𝟙 _) y J = val (ψW.psi (xe x)) g y J :=
      (vb x _ _ y J hJ).trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]))
    have v₂ : val (b x) (𝟙 _) y J = (om w y J J' (D'.xK x))⁻¹ * val (psi x) (𝟙 _) y J' := by
      refine v.trans (congrArg₂ (· * ·) ?_ rfl)
      rw [pw, Fintype.prod_unique, zpow_neg_one]
      simp only [om, Category.id_comp]
    exact mul_left_cancel (v₂.symm.trans (v₁.trans u))
  refine ⟨⟨e, e_hom, w, (isGen_iff w).2 hw, hE, ?_, xe, hc, W, ψW, g, hg, fun x => ⟨b x, fun jN jL => ?_,
      corr_of_val D.P.isLB fun y J hJ => vb x _ _ y J hJ⟩⟩, rfl⟩
  · exact (maps_iff w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf i) _
      (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf i) hE D.P.L) (fun _ => rfl)).2 hr
  · rw [← eψ]
    refine unit_ext fun y hy => ?_
    have v := vpsi x _ (𝟙 _) y jN (fun _ => jL) (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy)
    refine (gm_res _ y _ hy _).trans (v.trans (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_
      (gm_res _ y _ hy _)))))
    rw [pw, Fintype.prod_unique]
    exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull (𝟙 _) _ y _ hy _))

theorem nonempty_isPullDeg_comp {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    [CommRing R''] [IsDomain R''] {i : R →+* R'} {j : R' →+* R''} (hj : Function.Injective j)
    {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p : IsPullDeg i D D') (q : IsPullDeg j D' D'') :
    Nonempty (IsPullDeg (j.comp i) D D'') := by
  have sc : spMap j ≫ spMap i = spMap (j.comp i) := (spMap_comp i j).symm
  have gp : IsGrpPullback D''.P.A D.P.A (spMap (j.comp i)) (proj q ≫ proj p) :=
    ((pull_grp q).comp (pull_grp p)).congr sc rfl
  have g₁ := (isGen_iff _).1 p.w_gen
  have g₂ := (isGen_iff _).1 q.w_gen
  obtain ⟨w, T⟩ := Geo.Tor.exists_comp D'.P.isLB p.w q.w g₁ g₂ D.P.isLB D''.P.isLB
  have hr := T.pmaps_comp D'.P.isLB (fun _ => q.he) (FieldPull.pmaps_rig p) (FieldPull.pmaps_rig q)
  rw [sc] at hr
  have hc : ∀ x, (D''.c x).left ≫ proj q ≫ proj p = spMap (j.comp i) ≫ (D.c ((q.xe.trans p.xe) x)).left := fun x =>
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ proj p) (q.c_pr x)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (p.c_pr _)).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) sc)))))
  have sj : jK R'' ≫ spMap j = genMap hj ≫ jK R' := (Category.id_comp _).symm.trans (fracMap_sq hj)
  have hg : (genMap hj ≫ p.g) ≫ p.W.ι = jK R'' ≫ specOf (j.comp i) := by
    rw [Category.assoc, p.g_comm, ← Category.assoc, ← sj, Category.assoc]
    exact congrArg (jK R'' ≫ ·) sc
  obtain ⟨r, -⟩ := exists_isPullDeg_of_valW D D'' p.psiW (genMap hj ≫ p.g) hg gp w
    (T.pgen_comp D'.P.isLB g₁ g₂) hr (q.xe.trans p.xe) hc (fun x z J J'' hJ hJ'' => by
      obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB z
      have v₁ := PsiEvenPull.psi_pull p (q.xe x) (genMap hj) z hJ hJ'
      have v₂ := psi_val q _ _ (fracMap_sq hj) hJ' hJ'' x
      have hx : D''.xK x ≫ proj q = genMap hj ≫ D'.xK (q.xe x) := by
        show (jK R'' ≫ (D''.c x).left) ≫ proj q = genMap hj ≫ jK R' ≫ (D'.c (q.xe x)).left
        rw [Category.assoc, q.c_pr, ← Category.assoc, ← Category.assoc, ← sj]
      have t : om w z J J'' (D''.xK x) = om p.w z J J' (D''.xK x ≫ proj q) * om q.w z J' J'' (D''.xK x) :=
        (congrArg (fun u => Geo.Tor.gw w (D''.xK x) z (J u) (J'' (D''.xK x)))
          (Category.assoc (D''.xK x) (proj q) (proj p)).symm).trans
          (T _ _ z _ _ _ (hJ ((D''.xK x ≫ proj q) ≫ proj p)) (hJ' (D''.xK x ≫ proj q)) (hJ'' _))
      change _ = (om p.w z J J' (genMap hj ≫ D'.xK (q.xe x)))⁻¹ * val (D'.psi (q.xe x)) (genMap hj) z J' at v₁
      rw [v₂, Category.id_comp, ← hx, ← _root_.mul_assoc, ← mul_inv, ← t] at v₁
      exact v₁)
  exact ⟨r⟩

end GlobalTheory.PullDegCompGen

namespace GlobalTheory.Mum

theorem nonempty_isPullDeg_comp_of_injective : ∀ (R R' R'' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [CommRing R''] [IsDomain R''] (φ : R →+* R') (φ' : R' →+* R'') (D : DegPre R) (D' : DegPre R') (D'' : DegPre R''), Function.Injective φ' → Nonempty (IsPullDeg φ D D') → Nonempty (IsPullDeg φ' D' D'') → Nonempty (IsPullDeg (φ'.comp φ) D D'') := by
  intro R R' R'' _ _ _ _ _ _ φ φ' D D' D'' hj ⟨p⟩ ⟨q⟩
  exact GlobalTheory.PullDegCompGen.nonempty_isPullDeg_comp hj p q

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiInverseIsogenyPairBaseChangeGrpPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiInverseIsogenyPair_baseChange_grpPullback : ∀ (T Y : Scheme.{0}) (t : T ⟶ Y) (A B : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (k : ℕ) (ψ : A ⟶ B) (ψ' : B ⟶ A) (A₁ : Over T) [GrpObj A₁] [IsCommMonObj A₁] (φ : A₁.left ⟶ A.left), IsAbelianScheme B → IsQuasiInv k ψ ψ' → IsGrpPullback A₁ A t φ → ∃ (B₁ : Over T) (_ : GrpObj B₁) (_ : IsCommMonObj B₁) (θ : B₁.left ⟶ B.left) (ψ₁ : A₁ ⟶ B₁) (ψ₁' : B₁ ⟶ A₁), IsAbelianScheme B₁ ∧ IsGrpPullback B₁ B t θ ∧ IsQuasiInv k ψ₁ ψ₁' ∧ φ ≫ ψ.left = ψ₁.left ≫ θ ∧ θ ≫ ψ'.left = ψ₁'.left ≫ φ := by
  first | (exact @GlobalTheory.UPel.HT.ES.pullQuasiInv) | (exact GlobalTheory.UPel.HT.ES.pullQuasiInv) | (intros; apply GlobalTheory.UPel.HT.ES.pullQuasiInv  <;> assumption)
end

