module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1314
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0586
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1300
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZarhinDualPolarisation.FlatFiniteFibres.FlatOfFibresFinite
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0741
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0747
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0745
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0744
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0743
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0746
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0090

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgEqZeroOfInfiniteRange
section
noncomputable section

open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F.MT
open scoped Classical

namespace GlobalTheory.CompanionTheory.MatchLinear

theorem index_rStab_ne_zero {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    (u : H → ℂ) (hu : IsLocallyConstant u) : (rStab u).index ≠ 0 := by
  have hd : IsLocallyConstant fun p : H × H => u (p.1 * p.2) - u p.1 :=
    (hu.comp_continuous (continuous_fst.mul continuous_snd)).sub (hu.comp_continuous continuous_fst)
  obtain ⟨A, B, -, hB, hA, h1, hAB⟩ := generalized_tube_lemma (isCompact_univ (X := H)) (isCompact_singleton (x := (1 : H)))
    (hd.isOpen_fiber 0) (fun p hp => by
      obtain ⟨-, h⟩ := hp
      have : p.2 = 1 := h
      simp [this])
  have hsub : B ⊆ (rStab u : Set H) := fun k hk x =>
    sub_eq_zero.1 (hAB (show (x, k) ∈ A ×ˢ B from ⟨hA (Set.mem_univ x), hk⟩))
  have hopen : IsOpen (rStab u : Set H) :=
    Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hB.mem_nhds (h1 rfl)) hsub)
  haveI := Subgroup.quotient_finite_of_isOpen (rStab u) hopen
  exact Subgroup.index_ne_zero_of_finite

theorem avg_lin {H : Type} [Group H] (S : Subgroup H) (hS : S.index ≠ 0) {J : Type} [Fintype J] (a : J → ℂ)
    (u : J → H → ℂ) (hu : ∀ j, S ≤ rStab (u j)) :
    avg (fun h => ∑ j, a j * u j h) = ∑ j, a j * avg (u j) := by
  have hsum : S ≤ rStab (fun h => ∑ j, a j * u j h) := fun k hk => show ∀ x, _ from fun x =>
    Finset.sum_congr rfl fun j _ => by rw [(hu j hk : ∀ x, u j (x * k) = u j x) x]
  haveI : S.FiniteIndex := ⟨hS⟩
  haveI : Finite (H ⧸ S) := Subgroup.finite_quotient_of_finiteIndex
  letI : Fintype (H ⧸ S) := Fintype.ofFinite _
  rw [avg_eq_of_le_rStab _ _ S hsum hS, finsum_eq_sum_of_fintype, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [avg_eq_of_le_rStab _ _ S (hu j) hS, finsum_eq_sum_of_fintype, ← Finset.mul_sum]
  ring

theorem twOrb_lin {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G) (hθ : Continuous θ)
    (K : Subgroup G) (hK : IsCompact (K : Set G)) (y : G) {J : Type} [Fintype J] (a : J → ℂ) (g : J → G → ℂ)
    (hg : ∀ j, IsLocallyConstant (g j))
    (hfin : ∀ j, {q : DoubleCoset.Quotient (twCent θ y : Set G) (K : Set G) |
      ∃ k ∈ K, g j ((Quotient.out q * k)⁻¹ * y * θ (Quotient.out q * k)) ≠ 0}.Finite) :
    twOrb θ K y (fun z => ∑ j, a j * g j z) = ∑ j, a j * twOrb θ K y (g j) := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hsupp : ∀ j, (Function.support fun q : DoubleCoset.Quotient (twCent θ y : Set G) (K : Set G) =>
      (((twCent θ y ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex (cptPart (twCent θ y)) : ℕ) : ℂ) *
        avg fun k : K => g j ((Quotient.out q * k)⁻¹ * y * θ (Quotient.out q * k))).Finite := by
    intro j
    refine (hfin j).subset fun q hq => ?_
    by_contra hno
    simp only [Set.mem_setOf_eq, not_exists, not_and, ne_eq, not_not] at hno
    apply hq
    have h0 : (fun k : K => g j ((Quotient.out q * k)⁻¹ * y * θ (Quotient.out q * k))) = fun _ => 0 :=
      funext fun k => hno k k.2
    have ha : avg (fun k : K => g j ((Quotient.out q * k)⁻¹ * y * θ (Quotient.out q * k))) = 0 := by
      rw [h0]; simp [avg]
    simp only [ha, mul_zero]
  unfold twOrb
  have hterm : ∀ q : DoubleCoset.Quotient (twCent θ y : Set G) (K : Set G),
      (((twCent θ y ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex (cptPart (twCent θ y)) : ℕ) : ℂ) *
        (avg fun k : K => ∑ j, a j * g j ((Quotient.out q * k)⁻¹ * y * θ (Quotient.out q * k))) =
      ∑ j, a j * ((((twCent θ y ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex
        (cptPart (twCent θ y)) : ℕ) : ℂ) *
        avg fun k : K => g j ((Quotient.out q * k)⁻¹ * y * θ (Quotient.out q * k))) := by
    intro q
    have hc : Continuous fun k : K => (Quotient.out q * (k : G))⁻¹ * y * θ (Quotient.out q * (k : G)) := by
      have h1 : Continuous fun k : K => Quotient.out q * (k : G) := continuous_const.mul continuous_subtype_val
      exact (h1.inv.mul continuous_const).mul (hθ.comp h1)
    have hi : ∀ j, (rStab fun k : K => g j ((Quotient.out q * k)⁻¹ * y * θ (Quotient.out q * k))).index ≠ 0 :=
      fun j => index_rStab_ne_zero _ ((hg j).comp_continuous hc)
    rw [avg_lin (⨅ j, rStab fun k : K => g j ((Quotient.out q * k)⁻¹ * y * θ (Quotient.out q * k)))
      (Subgroup.index_iInf_ne_zero hi) a
      (fun j (k : K) => g j ((Quotient.out q * k)⁻¹ * y * θ (Quotient.out q * k))) (fun j => iInf_le _ j),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [finsum_congr hterm, finsum_sum_comm _ _ fun j _ => ?_]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_finsum]
  · exact (hsupp j).subset (Function.support_const_smul_subset (a j) _ |>.trans subset_rfl)

theorem clSum_lin {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (S : Set G) (wt : G → ℂ)
    (hS : {c : TwCl θ | c.rep ∈ S}.Finite) {J : Type} [Fintype J] (a : J → ℂ) (g : J → G → ℂ)
    (h : ∀ y ∈ S, twOrb θ K y (fun z => ∑ j, a j * g j z) = ∑ j, a j * twOrb θ K y (g j)) :
    clSum θ K S wt (fun z => ∑ j, a j * g j z) = ∑ j, a j * clSum θ K S wt (g j) := by
  have hsupp : ∀ j, (Function.support fun c : TwCl θ => if c.rep ∈ S then wt c.rep * twOrb θ K c.rep (g j) else 0).Finite :=
    fun j => hS.subset fun c hc => by
      by_contra hn
      exact hc (if_neg hn)
  unfold clSum
  have hterm : ∀ c : TwCl θ, (if c.rep ∈ S then wt c.rep * twOrb θ K c.rep (fun z => ∑ j, a j * g j z) else 0) =
      ∑ j, a j * (if c.rep ∈ S then wt c.rep * twOrb θ K c.rep (g j) else 0) := by
    intro c
    by_cases hc : c.rep ∈ S
    · simp only [if_pos hc, h _ hc, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    · simp only [if_neg hc, mul_zero, Finset.sum_const_zero]
  rw [finsum_congr hterm, finsum_sum_comm _ _ fun j _ => ?_]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_finsum]
  · exact (hsupp j).subset (Function.support_const_smul_subset (a j) _ |>.trans subset_rfl)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem charpoly_nrmL_twConj (hU : Unr E) (n : ℕ) (w : Pl E) (x g : GLw n w) :
    (nrmL n w (g⁻¹ * x * thL n w g)).val.charpoly = (nrmL n w x).val.charpoly := by
  rw [GlobalTheory.CompanionTheory.TwistOrbit.nrmL_twConj' hU, Units.val_mul, Units.val_mul, Matrix.coe_units_inv,
    Matrix.charpoly_units_conj']

theorem finite_dc_unitary (hU : Unr E) (n : ℕ) (w : Pl E) (y : UL n w) (hy : y.1.val.charpoly.Separable)
    (f : UL n w → ℂ) (hf : HasCompactSupport f) :
    {q : DoubleCoset.Quotient (twCent (MonoidHom.id (UL n w)) y : Set (UL n w)) (KL n w : Set (UL n w)) |
      ∃ k ∈ KL n w, f ((Quotient.out q * k)⁻¹ * y * MonoidHom.id (UL n w) (Quotient.out q * k)) ≠ 0}.Finite := by
  obtain ⟨hKo, hKc⟩ := GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w
  obtain ⟨D, hD, hP⟩ := GlobalTheory.OrbitU.orbit_cpt_U E hU n w y hy _ hf.isCompact
  refine GlobalTheory.CompanionTheory.TwistOrbit.finite_of_subset_mul' _ _ hKo
    ((fun p : UL n w × UL n w => p.1 * p.2⁻¹) '' (D ×ˢ (KL n w : Set (UL n w))))
    ((hD.prod hKc).image (by fun_prop)) (fun x => ∃ k ∈ KL n w,
      f ((x * k)⁻¹ * y * MonoidHom.id (UL n w) (x * k)) ≠ 0) ?_
  rintro x ⟨k, hk, hne⟩
  obtain ⟨t, ht, d, hd, e⟩ := hP (x * k) (subset_tsupport f hne)
  exact ⟨t, ht, d * k⁻¹, ⟨(d, k), ⟨hd, hk⟩, rfl⟩, by rw [← mul_assoc, ← e, mul_inv_cancel_right]⟩

theorem finite_dc_pair (hU : Unr E) (a b : ℕ) (w : Pl E) (y : GLw a w × GLw b w)
    (h₁ : (nrmL a w y.1).val.charpoly.Separable) (h₂ : (nrmL b w y.2).val.charpoly.Separable)
    (f : GLw a w × GLw b w → ℂ) (hf : HasCompactSupport f) :
    {q : DoubleCoset.Quotient (twCent ((thL a w).prodMap (thL b w)) y : Set (GLw a w × GLw b w))
        (((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)) : Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)) |
      ∃ k ∈ (GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)), f ((Quotient.out q * k)⁻¹ * y *
        (thL a w).prodMap (thL b w) (Quotient.out q * k)) ≠ 0}.Finite := by
  obtain ⟨D, hD, hP⟩ := GlobalTheory.CompanionTheory.TwistOrbit.proper_pair hU a b w y h₁ h₂ _ hf.isCompact
  obtain ⟨hKo, hKc⟩ := GlobalTheory.BCT.StTw2Add.isOpen_isCompact_KK (E := E) a b w
  refine GlobalTheory.CompanionTheory.TwistOrbit.finite_of_subset_mul' _ _ hKo
    ((fun p : (GLw a w × GLw b w) × (GLw a w × GLw b w) => p.1 * p.2⁻¹) '' (D ×ˢ _))
    ((hD.prod hKc).image (by fun_prop)) (fun x => ∃ k ∈ (GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)),
      f ((x * k)⁻¹ * y * (thL a w).prodMap (thL b w) (x * k)) ≠ 0) ?_
  rintro x ⟨k, hk, hne⟩
  obtain ⟨t, ht, d, hd, e⟩ := hP (x * k) (subset_tsupport f hne)
  exact ⟨t, ht, d * k⁻¹, ⟨(d, k), ⟨hd, hk⟩, rfl⟩, by rw [← mul_assoc, ← e, mul_inv_cancel_right]⟩

theorem matchLin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n a b : ℕ) (w : Pl E)
    (μ : (w.adicCompletion E)ˣ →* ℂˣ) (J : Type) [Fintype J] (c : J → ℂ) (f : J → UL n w → ℂ)
    (φ : J → GLw a w × GLw b w → ℂ),
    (∀ j, IsLocallyConstant (f j) ∧ HasCompactSupport (f j) ∧ IsLocallyConstant (φ j) ∧ HasCompactSupport (φ j)) →
    (∀ j, Match n a b w μ (f j) (φ j)) → Match n a b w μ (fun γ => ∑ j, c j * f j γ) (fun y => ∑ j, c j * φ j y) := by
  intro E _ _ _ hU n a b w μ J _ c f φ hreg hM Q₁ Q₂ m₁ m₂ d₁ d₂ hsep c₁ c₂
  have hs₁ : Q₁.Separable := hsep.of_mul_left
  have hs₂ : Q₂.Separable := hsep.of_mul_right
  have e₁ : stTw2 a b w Q₁ Q₂ (fun y => ∑ j, c j * φ j y) = ∑ j, c j * stTw2 a b w Q₁ Q₂ (φ j) := by
    unfold stTw2
    refine clSum_lin _ _ _ _ ?_ c φ ?_
    · exact GlobalTheory.BCT.StTw2Add.finite_prod _ _ (fun x => (nrmL a w x).val.charpoly = Q₁)
        (fun x => (nrmL b w x).val.charpoly = Q₂)
        (fun x g => by simp only [charpoly_nrmL_twConj hU])
        (fun x g => by simp only [charpoly_nrmL_twConj hU])
        (GlobalTheory.BCT.ClsFin.classes_finite E hU a w Q₁ hs₁).1 (GlobalTheory.BCT.ClsFin.classes_finite E hU b w Q₂ hs₂).1
    · rintro y ⟨hy₁, hy₂⟩
      have hθ : Continuous ((thL a w).prodMap (thL b w)) :=
        ((GlobalTheory.BCT.thL_continuous_involutive E hU a w).1.comp continuous_fst).prodMk
          ((GlobalTheory.BCT.thL_continuous_involutive E hU b w).1.comp continuous_snd)
      exact twOrb_lin _ hθ _ (GlobalTheory.BCT.StTw2Add.isOpen_isCompact_KK a b w).2 y c φ (fun j => (hreg j).2.2.1)
        fun j => finite_dc_pair hU a b w y (hy₁ ▸ hs₁) (hy₂ ▸ hs₂) (φ j) (hreg j).2.2.2
  have e₂ : kapOrb n w Q₁ Q₂ (fun γ => ∑ j, c j * f j γ) = ∑ j, c j * kapOrb n w Q₁ Q₂ (f j) := by
    unfold kapOrb
    refine clSum_lin _ _ _ _ (GlobalTheory.BCT.ClsFin.classes_finite E hU n w (Q₁ * Q₂) hsep).2 c f ?_
    intro y hy
    exact twOrb_lin _ continuous_id _ (GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w).2 y c f (fun j => (hreg j).1)
      fun j => finite_dc_unitary hU n w y (by rw [show y.1.val.charpoly = Q₁ * Q₂ from hy]; exact hsep) (f j) (hreg j).2.1
  rw [e₁, e₂, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hM j Q₁ Q₂ m₁ m₂ d₁ d₂ hsep c₁ c₂]
  ring

end GlobalTheory.CompanionTheory.MatchLinear
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EpiOfFiniteFlat
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.CompanionTheory.Dblock

theorem epiOfFF : PositivityTheory.Tls2.Zar3.Ch1.EpiOfFF := by
  intro R _ A B A' l hf hs hq g₁ g₂ h
  have : EffectiveEpi l.left := inferInstance
  have : Epi l.left := inferInstance
  apply Over.OverMorphism.ext
  rw [← cancel_epi l.left]
  simpa using congrArg (fun k => k.left) h

end GlobalTheory.CompanionTheory.Dblock
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorThroughFiniteFlat
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Chart (sp)

namespace GlobalTheory.CompanionTheory.FlatFactor

theorem ext_of_affine_points {R : Type} [CommRing R] {W X : Over (Sp R)} (u v : W ⟶ X)
    (h : ∀ (S : Type) [CommRing S] [Algebra R S] (t : sp (R₀ := R) S ⟶ W), t ≫ u = t ≫ v) : u = v := by
  have key : ∀ (B : CommRingCat.{0}) (j₀ : Spec B ⟶ W.left), j₀ ≫ u.left = j₀ ≫ v.left := by
    intro B j₀
    letI : Algebra R B := (Spec.preimage (j₀ ≫ W.hom)).hom.toAlgebra
    let j : sp (R₀ := R) B ⟶ W := Over.homMk j₀ (Spec.map_preimage (j₀ ≫ W.hom)).symm
    exact congrArg CommaMorphism.left (h B j)
  apply Over.OverMorphism.ext
  exact Scheme.Cover.hom_ext W.left.affineCover _ _ fun i => key _ _

theorem comp_eq_of_comp_eq {R : Type} [CommRing R] {A B A' : Over (Sp R)} [GrpObj A] [GrpObj B] [GrpObj A']
    (l : A ⟶ B) (f : A ⟶ A') [IsMonHom l] [IsMonHom f]
    (hk : ∀ (S : Type) [CommRing S] [Algebra R S] (z : sp (R₀ := R) S ⟶ A), z ≫ l = 1 → z ≫ f = 1)
    {W : Over (Sp R)} (a b : W ⟶ A) (h : a ≫ l = b ≫ l) : a ≫ f = b ≫ f := by
  refine ext_of_affine_points _ _ fun S _ _ t => ?_
  have h1 : ((t ≫ a) / (t ≫ b)) ≫ l = 1 := by
    rw [GrpObj.div_comp, Category.assoc, Category.assoc, h, div_self']
  have h2 := hk S _ h1
  rw [GrpObj.div_comp, div_eq_one] at h2
  simpa using h2

theorem factorThroughFF : PositivityTheory.Tls2.Zar3.Ch1.FactorThroughFF := by
  intro R _ A B A' _ _ _ l f hl hf hfl hsl hql hk
  have hc : ∀ {Z : Scheme.{0}} (g g' : Z ⟶ A.left), g ≫ l.left = g' ≫ l.left →
      g ≫ f.left = g' ≫ f.left := by
    intro Z g g' h
    have hw : g' ≫ A.hom = g ≫ A.hom := by
      rw [← Over.w l, ← Category.assoc, ← h, Category.assoc]
    have := comp_eq_of_comp_eq l f hk (W := Over.mk (g ≫ A.hom))
      (Over.homMk g rfl) (Over.homMk g' hw) (Over.OverMorphism.ext h)
    exact congrArg CommaMorphism.left this
  have hfac := EffectiveEpi.fac l.left f.left hc
  let g : B ⟶ A' := Over.homMk (EffectiveEpi.desc l.left f.left hc) (by
    rw [← cancel_epi l.left, ← Category.assoc, hfac, Over.w, Over.w])
  have hg : l ≫ g = f := Over.OverMorphism.ext hfac
  refine ⟨g, ⟨?_, ?_⟩, hg⟩
  · rw [← IsMonHom.one_hom l, Category.assoc, hg, IsMonHom.one_hom]
  · have := GlobalTheory.FlatQuotient.epi_tensorHom l l
    rw [← cancel_epi (l ⊗ₘ l), ← IsMonHom.mul_hom_assoc, hg, tensorHom_comp_tensorHom_assoc, hg,
      IsMonHom.mul_hom]

end GlobalTheory.CompanionTheory.FlatFactor
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FewEquationsStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

namespace GlobalTheory.CompanionTheory.FewEq

theorem fewEq : FewEqSt := by
  have gen := GlobalTheory.T.cocycle_units_trivialize_modulo_ideal
  have data := _root_.GlobalTheory.CompanionTheory.FewEq.exists_local_of_triv
  have mingens := _root_.GlobalTheory.CompanionTheory.FewEq.exists_minimal_generators
  have flat := _root_.GlobalTheory.CompanionTheory.FewEq.minimal_generators_flat_independent
  have dep := _root_.GlobalTheory.CompanionTheory.FewEq.depSt
  have fibre := _root_.GlobalTheory.CompanionTheory.FewEq.FibreRed.dep_fibre
  have cocycle := _root_.GlobalTheory.CompanionTheory.FewEq.Cochain.exists_cochain
  have finish := _root_.GlobalTheory.CompanionTheory.FewEq.exists_correction
  intro R _ _ _ X s n hsm hpr hF M hM I hI hJ
  have hIm : I ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal hI
  obtain ⟨r, t, ht, hmin⟩ := mingens R I
  have hsep : X.IsSeparated := by
    have : IsSeparated (s ≫ terminal.from (Sp R)) := inferInstance
    rw [Subsingleton.elim (s ≫ terminal.from (Sp R)) (terminal.from X)] at this
    exact ⟨this⟩
  haveI : Flat s := inferInstance

  let A := {q : M.ι × X.Opens // IsAffineOpen q.2 ∧ q.2 ≤ M.U q.1}
  let V : A → X.Opens := fun a => a.1.2
  let j : A → M.ι := fun a => a.1.1
  have hj : ∀ a, V a ≤ M.U (j a) := fun a => a.2.2
  have hA : ∀ a, IsAffineOpen (V a) := fun a => a.2.1
  have hAA : ∀ a b, IsAffineOpen (V a ⊓ V b) := fun a b => (hA a).inf (hA b)
  have hAAA : ∀ a b d, IsAffineOpen (V a ⊓ V b ⊓ V d) := fun a b d => (hAA a b).inf (hA d)
  have hV : ⨆ a, V a = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨i, hi⟩ := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.exists_chart M hM x
    obtain ⟨W, hW, hxW, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hi
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(i, W), hW, hle⟩, hxW⟩
  have hsq : I * I ≤ IsLocalRing.maximalIdeal R * I := Ideal.mul_mono_left hIm
  suffices hrn : r ≤ n by
    refine ⟨fun i => if h : i.1 < r then t ⟨i.1, h⟩ else 0, le_antisymm ?_ ?_⟩
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      by_cases h : i.1 < r
      · simp only [h, dif_pos]
        rw [← ht]
        exact Ideal.subset_span ⟨_, rfl⟩
      · simp only [h, dif_neg, not_false_eq_true]
        exact zero_mem _
    · rw [← ht, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      refine Ideal.subset_span ⟨⟨i.1, i.2.trans_le hrn⟩, ?_⟩
      simp
  by_contra hrn
  obtain ⟨u, z, hz, hc⟩ := data R X s I M hM A V j hj hA hAA ((hJ I).2 le_rfl)

  let w : ∀ a, Γ(X, V a) := fun a => z a * (2 - u a * z a)
  have hw : ∀ a, u a * w a - 1 ∈ ext s (IsLocalRing.maximalIdeal R * I) (V a) := fun a => by
    have h2 : (u a * z a - 1) * (u a * z a - 1) ∈ ext s (IsLocalRing.maximalIdeal R * I) (V a) := by
      refine Ideal.map_mono hsq ?_
      rw [Ideal.map_mul]
      exact Ideal.mul_mem_mul (hz a) (hz a)
    have : u a * w a - 1 = -((u a * z a - 1) * (u a * z a - 1)) := by simp only [w]; ring
    rw [this]
    exact neg_mem h2
  obtain ⟨b, hb1, hb2⟩ := cocycle R X s _ I r t ht hIm M hM A V j hj u w hw hc
  have hb3 : ∀ i a c d, rs X (le₁₂ V a c d) (b i a c) + rs X (le₂₃ V a c d) (b i c d) -
        rs X (le₁₃ V a c d) (b i a d) ∈ ext s (IsLocalRing.maximalIdeal R) (V a ⊓ V c ⊓ V d) := fun i a c d =>
    flat R _ _ (GlobalTheory.SmallExtLift.cst_flat s (hAAA a c d)) r t I ht hmin _ (hb1 a c d) i
  obtain ⟨e, β, ⟨l, hl⟩, he⟩ := fibre dep R X s inferInstance n r (not_le.1 hrn) hF A V hV hA b hb3
  obtain ⟨J, y, z', hIJ, hy1, hy2⟩ := finish R X s I r t ht hIm hmin M A V j hj u w b e β l hw hb2 hl he
  exact hIJ ((hJ J).1 (gen R X s J M hM A V j hj hV y z' hy1 hy2))

end GlobalTheory.CompanionTheory.FewEq
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteOfFiniteFibres
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.AbFibre

theorem isPullback_baseChange {S T : Scheme.{0}} (s : T ⟶ S) {X Y : Over S} (f : X ⟶ Y) :
    IsPullback ((Over.pullback s).map f).left (pullback.fst X.hom s) (pullback.fst Y.hom s) f.left := by
  have h1 : ((Over.pullback s).map f).left ≫ pullback.snd Y.hom s = pullback.snd X.hom s := by
    simp only [Over.pullback_map_left]
    exact pullback.lift_snd _ _ _
  have h2 : ((Over.pullback s).map f).left ≫ pullback.fst Y.hom s = pullback.fst X.hom s ≫ f.left := by
    simp only [Over.pullback_map_left]
    exact pullback.lift_fst _ _ _
  have hX : f.left ≫ Y.hom = X.hom := Over.w f
  refine IsPullback.of_right ?_ h2 (IsPullback.of_hasPullback Y.hom s).flip
  rw [h1, hX]
  exact (IsPullback.of_hasPullback X.hom s).flip

theorem exists_geometric_point {S : Scheme.{0}} (Y : Over S) (y : Y.left) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (s : Spec (.of Ω) ⟶ S) (w : ↥(pullback Y.hom s)),
      pullback.fst Y.hom s w = y := by
  let Ω := AlgebraicClosure (Y.left.residueField y)
  let g : Spec (.of Ω) ⟶ Y.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.left.residueField y) Ω)) ≫ Y.left.fromSpecResidueField y
  let L : Spec (.of Ω) ⟶ pullback Y.hom (g ≫ Y.hom) := pullback.lift g (𝟙 _) (by simp)
  let pt : ↥(Spec (.of Ω)) := IsLocalRing.closedPoint Ω
  refine ⟨Ω, inferInstance, inferInstance, g ≫ Y.hom, L pt, ?_⟩
  change (L ≫ pullback.fst Y.hom (g ≫ Y.hom)) pt = y
  rw [pullback.lift_fst]
  exact Scheme.fromSpecResidueField_apply y _

theorem finiteOfFibres : PositivityTheory.Tls2.Zar3.Ch1.FiniteOfFibres := by
  intro R _ A B _ _ l hA hB _ hfib
  haveI := hA
  haveI := hB
  have hcomp : l.left ≫ B.hom = A.hom := Over.w l
  haveI : IsProper A.hom := IsAbelianScheme.proper (A := A)
  haveI : IsProper B.hom := IsAbelianScheme.proper (A := B)
  haveI : IsProper (l.left ≫ B.hom) := by rw [hcomp]; infer_instance
  haveI : IsProper l.left := IsProper.of_comp l.left B.hom
  have lift : ∀ {T : Scheme.{0}} (s : T ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) (x : ↥A.left)
      (w : ↥(pullback B.hom s)), pullback.fst B.hom s w = l.left x →
      ∃ v, ((Over.pullback s).map l).left v = w ∧ pullback.fst A.hom s v = x := by
    intro T s x w hxw
    have h := isPullback_baseChange s l
    obtain ⟨z, hz1, hz2⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := pullback.fst B.hom s) (g := l.left) w x hxw
    refine ⟨h.isoPullback.inv z, ?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst, hz1]
    · rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_snd, hz2]
  have hfin : ∀ y : ↥B.left, (l.left ⁻¹' {y}).Finite := by
    intro y
    obtain ⟨Ω, _, _, s, w, hw⟩ := exists_geometric_point B y
    have hF : IsFinite ((Over.pullback s).map l).left := (hfib Ω s).1
    refine ((Scheme.Hom.finite_preimage_singleton ((Over.pullback s).map l).left w).image
      (pullback.fst A.hom s)).subset ?_
    intro x hx
    have hx' : l.left x = y := hx
    obtain ⟨v, hv1, hv2⟩ := lift s x w (by rw [hw, hx'])
    exact ⟨v, hv1, hv2⟩
  have hsurj : Surjective l.left := by
    refine ⟨fun y => ?_⟩
    obtain ⟨Ω, _, _, s, w, hw⟩ := exists_geometric_point B y
    have hS : Surjective ((Over.pullback s).map l).left := (hfib Ω s).2
    obtain ⟨v, hv⟩ := hS.surj w
    refine ⟨pullback.fst A.hom s v, ?_⟩
    have hsq := (isPullback_baseChange s l).w
    rw [← Scheme.Hom.comp_apply, ← hsq, Scheme.Hom.comp_apply, hv, hw]
  haveI : LocallyQuasiFinite l.left := LocallyQuasiFinite.of_finite_preimage_singleton l.left hfin
  exact ⟨IsFinite.of_isProper_of_locallyQuasiFinite l.left, hsurj⟩

end GlobalTheory.CompanionTheory.AbFibre
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatOfFibresFinite
section
namespace GlobalTheory.CompanionTheory.FlatFib

theorem flatOfFibresFinite : PositivityTheory.Tls2.Zar3.Ch1.FlatOfFibresFinite := by
  intro R _ X Y f h1 h0 h2 h3 H
  exact GlobalTheory.flat_of_isFinite_of_finitePresentation_of_flat_geometric_fibres _ X Y f h1 h0 h2 h3 H

end GlobalTheory.CompanionTheory.FlatFib
end

