module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0595
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0006
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0263
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0294
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0436
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
public import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0002
public import Formalism.QuotientMetricDivisors.FinalW
public import Formalism.QuotientMetricDivisors.SixthReductionExplicit
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDegreeGapBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0715
public import Formalism.PieriBlockIdeals.StatementE
public import Formalism.PieriBlockIdeals.Bundle0007
public import Formalism.PieriBlockIdeals.PieriColumnMinors.RecursionInclusionExceptional
public import Formalism.PieriBlockIdeals.PieriColumnMinors.LargeParameterEstimates
public import Formalism.PieriBlockIdeals.PieriColumnMinors.CorollaryOfParamsSevenLinkageAlt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSectionsGroupScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniq

noncomputable section

namespace GlobalTheory.HomFixIndep

theorem eq_zero_of_locally {X : Scheme.{0}} {U : X.Opens} (s : Γ(X, U))
    (h : ∀ x ∈ U, ∃ (W : X.Opens) (hW : W ≤ U), x ∈ W ∧ (X.presheaf.map (homOfLE hW).op).hom s = 0) :
    s = 0 := by
  refine TopCat.Presheaf.section_ext X.sheaf U s 0 fun x hx => ?_
  obtain ⟨W, hW, hxW, h0⟩ := h x hx
  have e1 := X.presheaf.germ_res_apply (homOfLE hW) x hxW s
  change (X.presheaf.germ U x hx).hom s = (X.presheaf.germ U x hx).hom 0
  rw [← e1, h0, map_zero, map_zero]

theorem appLE_eq {X Y : Scheme.{0}} {f₁ f₂ : X ⟶ Y} (h : f₁ = f₂) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f₁ ⁻¹ᵁ U) (a : Γ(Y, U)) :
    (f₁.appLE U V e).hom a = (f₂.appLE U V (h ▸ e)).hom a := by
  subst h; rfl

theorem res_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) (V W : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (h : W ≤ V)
    (a : Γ(Y, U)) :
    (X.presheaf.map (homOfLE h).op).hom ((f.appLE U V e).hom a) = (f.appLE U W (h.trans e)).hom a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem appLE_appLE {X Y Z : Scheme.{0}} (g : X ⟶ Y) (f : Y ⟶ Z) (U : Z.Opens) (V : Y.Opens) (W : X.Opens)
    (e₁ : V ≤ f ⁻¹ᵁ U) (e₂ : W ≤ g ⁻¹ᵁ V) (a : Γ(Z, U)) :
    (g.appLE V W e₂).hom ((f.appLE U V e₁).hom a) =
      ((g ≫ f).appLE U W (fun _ hx => e₁ (e₂ hx))).hom a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

end GlobalTheory.HomFixIndep


open GlobalTheory.HomFixIndep in
theorem GlobalTheory.HomFixIndep.pulled_basis_indep : ∀ (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left) (k mA : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))), IsBCBasis A L k bA → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' : Over (Sp R)) [GrpObj A'] (φA' : A'.left ⟶ A.left) (ψA : A'.left ⟶ (topS Rg ⊗ A).left), IsGrpPullback A' A t φA' → ψA ≫ (snd (topS Rg) A).left = φA' → ∀ (d : Fin mA → Γ(Sp R, ⊤)), (∀ (j : Fin 1 → L.ι) (x : A'.left), x ∈ LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j → ∃ (W : A'.left.Opens) (hW : W ≤ LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j), x ∈ W ∧ ∑ i, (A'.hom.appLE ⊤ W (by simp)).hom (d i) * (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) j) W (hW.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ j))).hom ((bA i).f j) = 0) → d = 0 := by
  intro Rg _ A _ L k mA bA hB R _ t A' _ φA' ψA hT hψ d hloc
  let t'' : Spec (CommRingCat.of R) ⟶ (topS Rg).left :=
    IsOpenImmersion.lift (⊤ : (Sp Rg).Opens).ι t (by rw [Scheme.Opens.range_ι]; exact fun _ _ => trivial)
  have ht'' : (baseAt t'').hom = t := by simp [t'', baseAt, topS, overRes, baseOver]
  set T := baseAt t'' with hTdef
  have hw : (snd T A).left ≫ A.hom = (fst T A).left ≫ t := by
    rw [← ht'', Over.w (snd T A), Over.w (fst T A)]
  let g : (T ⊗ A).left ⟶ A'.left := hT.1.lift (snd T A).left (fst T A).left hw
  have hg1 : g ≫ φA' = (snd T A).left := hT.1.lift_fst _ _ _
  have hg2 : g ≫ A'.hom = (fst T A).left := hT.1.lift_snd _ _ _
  have hgψ : g ≫ ψA = (homAt t'' ▷ A).left := by
    apply psi_unique
    rw [Category.assoc, hψ, hg1, ← Over.comp_left, whiskerRight_snd]
  let b' : Fin mA → LB.Sec (LPow A L (k : ℤ) T) := fun i =>
    ReciprocityTheory.ChartRestriction.G.PullbackSections.pullSecLP A L (k : ℤ) (homAt t'' ▷ A) (whiskerRight_snd (homAt t'') A) (bA i)
  obtain ⟨hli, -⟩ := hB R t'' b' (fun i => ReciprocityTheory.ChartRestriction.G.PullbackSections.isPullSec_pullSecLP A L (k : ℤ) _ _ (bA i))
  rw [Fintype.linearIndependent_iff] at hli
  funext i
  refine hli d ?_ i
  apply Subtype.ext
  funext j
  have hD : (LPow A L (k : ℤ) T).U j ≤ g ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j := by
    intro y hy
    have e : g ≫ ψA ≫ (snd (topS Rg) A).left = (snd T A).left := by
      rw [← Category.assoc, hgψ, ← Over.comp_left, whiskerRight_snd]
    have h1 : (g ≫ ψA ≫ (snd (topS Rg) A).left).base y ∈ (L.U (j 0) : Set A.left) := by
      rw [e]; exact Set.mem_iInter.1 hy 0
    exact Set.mem_iInter.2 fun i => by rw [Subsingleton.elim i 0]; exact h1
  have hF : (∑ i, (A'.hom.appLE ⊤ (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j) (by simp)).hom (d i) *
      (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) j)
        (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j)
        (GlobalTheory.HomFixMat.wchart_comp_le L _ _ j)).hom ((bA i).f j)) = 0 := by
    refine eq_zero_of_locally _ fun x hx => ?_
    obtain ⟨W, hW, hxW, h0⟩ := hloc j x hx
    refine ⟨W, hW, hxW, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine (Finset.sum_congr rfl fun i _ => ?_).trans h0
    rw [map_mul]
    exact congrArg₂ (· * ·) (res_appLE _ _ _ _ _ _ _) (res_appLE _ _ _ _ _ _ _)
  calc (∑ i, d i • SecM.ofSec A (b' i)).val j
      = ∑ i, ((fst T A).left.appLE ⊤ ((LPow A L (k : ℤ) T).U j) (by simp)).hom (d i) *
          ((homAt t'' ▷ A).left.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) j)
            ((LPow A L (k : ℤ) T).U j) (chart_le_res A L _ (whiskerRight_snd (homAt t'') A) _ j)).hom ((bA i).f j) := by
        rw [Submodule.coe_sum, Finset.sum_apply]
        rfl
    _ = (g.appLE _ _ hD).hom (∑ i, (A'.hom.appLE ⊤ (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j) (by simp)).hom (d i) *
      (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) j)
        (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j)
        (GlobalTheory.HomFixMat.wchart_comp_le L _ _ j)).hom ((bA i).f j)) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul]
        exact congrArg₂ (· * ·) (((appLE_appLE _ _ _ _ _ _ _ _).trans (appLE_eq hg2 _ _ _ _)).symm)
          (((appLE_appLE _ _ _ _ _ _ _ _).trans (appLE_eq hgψ _ _ _ _)).symm)
    _ = _ := by rw [hF, map_zero]; rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOnePrescribedReAtIdempotent
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory

theorem quat_norm_one_re_at_idem : ∀ (R : Type) [CommRing R] (a b ε p q : R), ε * ε = ε → IsUnit a → IsUnit b →
    IsUnit (2 : R) → ε * (b - (p ^ 2 - a * q ^ 2)) = 0 → ∀ t : R, ∃ h : ℍ[R, a, b], nrm h = 1 ∧ ε * h.re = ε * t := by
  intro R _ a b ε p q hε ha hb h2 hE t
  obtain ⟨c, hc⟩ := ((h2.mul ha).mul hb)
  have hu : 2 * a * b * ((c⁻¹ : Rˣ) : R) = 1 := by
    rw [← hc]; simp
  set u : R := ((c⁻¹ : Rˣ) : R) with hu_def
  set l : R := (t ^ 2 - a - 1) * u with hl
  refine ⟨⟨ε * t + (1 - ε), ε * (l * b + 1), ε * (l * a * q), ε * (l * p)⟩, ?_, ?_⟩
  · simp only [nrm]
    linear_combination ((t - 1) ^ 2 + (-a * (l * b + 1) ^ 2 - b * (l * a * q) ^ 2 + a * b * (l * p) ^ 2)) * hε
      - ε * (t ^ 2 - a - 1) * hu - l ^ 2 * a * b * hE
  · show ε * (ε * t + (1 - ε)) = ε * t
    linear_combination (t - 1) * hε

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOneTraceOpenAdeles
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory.QSA

theorem traceOpen_field (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K]
    (h2 : (2 : K) ≠ 0) (hnb : (𝓝[≠] (0 : K)).NeBot) (hsq : SqOpen K) (a b : K) (ha : a ≠ 0) : TraceOpen K a b := by
  intro g hg W hW
  obtain ⟨g', hg'1, hg're, hW'⟩ := _root_.GlobalTheory.QSA.exists_nrm_one_re_sq_ne_one K h2 hnb a b ha g hg W hW
  have hu : IsUnit (1 - g'.re ^ 2) := IsUnit.mk0 _ (sub_ne_zero.2 (Ne.symm hg're))
  obtain ⟨O, hO, hmem, hO'⟩ := _root_.GlobalTheory.traceOpen_near_of_isUnit K a b hsq g' hg'1 hu W hW'
  exact ⟨O, hO, ⟨_, hmem⟩, hO'⟩

theorem traceOpen_inf (F : Type) [Field F] [NumberField F] (a b : F) (ha : a ≠ 0) :
    TraceOpen (InfiniteAdeleRing F) (algebraMap F (InfiniteAdeleRing F) a) (algebraMap F (InfiniteAdeleRing F) b) := by
  refine _root_.GlobalTheory.QSA.traceOpen_pi (InfinitePlace F) (fun w => w.Completion) _ _ (fun w => ?_)
  have h2 : (2 : w.Completion) ≠ 0 := by
    have := (map_ne_zero (algebraMap F w.Completion)).2 (two_ne_zero : (2 : F) ≠ 0)
    rwa [map_ofNat] at this
  exact traceOpen_field _ h2 (_root_.GlobalTheory.QSA.infinitePlace_completion_nhdsNE_neBot F w) (_root_.GlobalTheory.sqOpen_of_two_ne_zero _ h2) _ _ ((map_ne_zero (algebraMap F w.Completion)).2 ha)

theorem traceOpen_fin (F : Type) [Field F] [NumberField F] (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    TraceOpen (FiniteAdeleRing (𝓞 F) F) (algebraMap F (FiniteAdeleRing (𝓞 F) F) a)
      (algebraMap F (FiniteAdeleRing (𝓞 F) F) b) := by
  refine GlobalTheory.T.quaternionNormOneTraceOpen_finiteAdeleRing F a b (fun v => ?_) (_root_.GlobalTheory.QSA.IntRep.exists_nrm_eq_one_re_eq F a b ha hb)
  have h2 : (2 : v.adicCompletion F) ≠ 0 := by
    have := (map_ne_zero (algebraMap F (v.adicCompletion F))).2 (two_ne_zero : (2 : F) ≠ 0)
    rwa [map_ofNat] at this
  exact traceOpen_field _ h2 (_root_.GlobalTheory.QSA.sqOpen_and_nhdsNE_zero_neBot_adicCompletion F v).2 (_root_.GlobalTheory.QSA.sqOpen_and_nhdsNE_zero_neBot_adicCompletion F v).1 _ _ ((map_ne_zero (algebraMap F _)).2 ha)

theorem traceOpen_adele : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ g : DA F a b, nrm g = 1 → ∀ W : Set (DA F a b), W ∈ 𝓝 g → ∃ O : Set (AF F), IsOpen O ∧ O.Nonempty ∧ ∀ t ∈ O, ∃ u ∈ W, nrm u = 1 ∧ u.re = t := by
  intro F _ _ a b ha hb g hg W hW
  have H : TraceOpen (AF F) (algebraMap F (AF F) a) (algebraMap F (AF F) b) :=
    _root_.GlobalTheory.QSA.traceOpen_prod _ _ _ _ _ _ (traceOpen_inf F a b ha) (traceOpen_fin F a b ha hb)
  exact H g hg W hW
end GlobalTheory.QSA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamifiedTau1NeRamifiedTau2
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

noncomputable section

namespace GlobalTheory.RamifiedLoss

open Formalism.MainNotions.G GlobalTheory.HCEntries GlobalTheory.FockDegreeGap

variable {D : D7} {L : SizeData₂ D}

theorem ramifiedTau1_ne_ramifiedTau2 {φ : Formalism.HC.Frame} (t t' : φ.A) : φ.tau1 t ≠ φ.tau2 t' := by
  intro h
  have h1 := congrArg (fun g : φ.GG => g.1.1) h
  simp only [Formalism.HC.Frame.tau1, Formalism.HC.Frame.tau2] at h1
  exact absurd h1 (by decide)

theorem eTau_false (D : D7) (t : HH D) :
    (D.eTau (tauPl D (false, t)) : D.R.GG) = D.R.tau1 t := by
  unfold tauPl
  rw [Equiv.apply_symm_apply]
  rfl

theorem eTau_true (D : D7) (t : HH D) :
    (D.eTau (tauPl D (true, t)) : D.R.GG) = D.R.tau2 t := by
  unfold tauPl
  rw [Equiv.apply_symm_apply]
  rfl

theorem false_not_thick (D : D7) (t : HH D) :
    (D.eTau (tauPl D (false, t)) : D.R.GG) ∉ D.host.thickPlaces := by
  rw [eTau_false]
  intro h
  obtain ⟨s, -, hs⟩ := Finset.mem_image.1 h
  exact ramifiedTau1_ne_ramifiedTau2 _ _ hs.symm

theorem true_not_top (D : D7) (t : HH D) :
    (D.eTau (tauPl D (true, t)) : D.R.GG) ∉ D.host.topPlaces := by
  rw [eTau_true]
  intro h
  obtain ⟨s, -, hs⟩ := Finset.mem_image.1 h
  exact ramifiedTau1_ne_ramifiedTau2 _ _ hs

theorem false_not_top {t : HH D} (ht : t ∉ D.host.TT) :
    (D.eTau (tauPl D (false, t)) : D.R.GG) ∉ D.host.topPlaces := by
  rw [eTau_false]
  intro h
  obtain ⟨s, hs, he⟩ := Finset.mem_image.1 h
  have hst : s = t := D.R.iota_bijective.1 (congrArg Prod.snd he)
  exact ht (hst ▸ hs)

theorem k_b'_le (h : SizeLstar L) : (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b := by
  have hk := one_le_k D
  have ht := one_le_letterBlockLength D
  have hn := one_le_n D
  have hL := one_le_scL L
  have hb := one_le_b L
  have hS := L.Sc_pos
  have he := L.etaSz_pos
  have hm0 : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
  have hmt : (D.R.m : ℝ) ≤ D.R.t := by
    have : D.R.m ≤ D.R.t := by have := D.R.three_m_lt_t; omega
    exact_mod_cast this
  have h0 : 0 ≤ szlStar L := by unfold szlStar; positivity
  have h1 : (D.R.k : ℝ) * szlStar L ≤ L.sc.b := by
    unfold szlStar
    rw [← mul_div_assoc, div_le_iff₀ (by positivity), ← mul_assoc, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    have e2 : L.Sc + D.R.t + L.sc.L ≤ (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + L.sc.L) :=
      le_mul_of_one_le_left (by positivity) (one_le_pow₀ hn)
    have e1 : (D.R.k : ℝ) * D.R.m ≤ (D.R.k : ℝ) * ((D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + L.sc.L)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have e3 : 0 ≤ (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * L.sc.L ^ 2 := by positivity
    linarith
  have h2 : 0 ≤ L.sc.b / szlStar L := div_nonneg (by linarith) h0
  have h3 : L.sc.b' ≤ szlStar L := by linarith [h.1]
  exact (mul_le_mul_of_nonneg_left h3 (by linarith)).trans h1

theorem small_le (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) :
    L.etaSz ≤ L.sc.w'' D.R.n ∧ (D.R.k : ℝ) * D.R.N D.R.m ≤ L.sc.w'' D.R.n ∧
      L.sc.w'' D.R.n ≤ L.sc.b' / 2 := by
  have hb' := b'_pos L
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have he : L.etaSz ≤ L.sc.w'' D.R.n :=
    (le_mul_of_one_le_left L.etaSz_pos.le (one_le_mul_of_one_le_of_one_le hm (by linarith))).trans P.mteta
  refine ⟨he, ?_, ?_⟩
  · have h1 := P.h0_ge.2.2.2.2.1
    have h2 : LevelStarExponents.h0 L ≤ L.etaSz := div_le_self L.etaSz_pos.le hm
    obtain ⟨r1, r2⟩ := ranks_le D
    have hN : (1 : ℝ) ≤ D.R.N D.R.m := by linarith
    have h3 : (D.R.k : ℝ) * D.R.N D.R.m ≤ (D.R.N D.R.m : ℝ) ^ 2 := by nlinarith
    have h4 : (D.R.N D.R.m : ℝ) ^ 2 ≤ (D.R.N D.R.m : ℝ) ^ 3 := pow_le_pow_right₀ hN (by norm_num)
    have h5 : (0 : ℝ) ≤ (D.R.N D.R.m : ℝ) ^ 3 := by positivity
    linarith
  · unfold Scale.w''
    refine div_le_div_of_nonneg_left hb'.le (by norm_num) ?_
    nlinarith [one_le_n D]

theorem wj_false_le (h : SizesAt L) (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (t : HH D) : wj D j (tauPl D (false, t)) ≤ 9 / 4 * L.sc.b' := by
  obtain ⟨-, -, -, -, -, -, -, -, hLa, hR, hB, -⟩ := h
  obtain ⟨e1, -, e3⟩ := small_le P hx
  have hb' := b'_pos L
  by_cases ht : t ∈ D.host.TT
  · have a2 := (L.win_top j h1 h2 _ ⟨t, ht⟩ (eTau_false D t)).2
    have a4 := bT_le hLa hR hB ⟨t, ht⟩
    have a6 : L.sc.b' / L.sc.x ≤ L.sc.b' / 2 := div_le_div_of_nonneg_left hb'.le (by norm_num) hx
    linarith
  · have a2 := (L.win_thin j h1 h2 _ ⟨(D.eTau _).2, false_not_top ht, false_not_thick D t⟩).2
    linarith

theorem wj_true_le (h : SizesAt L) (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (t : HH D) : wj D j (tauPl D (true, t)) ≤ L.sc.b + L.etaSz + 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hS, -⟩ := h
  obtain ⟨e1, -, e3⟩ := small_le P hx
  have hb' := b'_pos L
  have hbb : L.sc.b' ≤ L.sc.b := by linarith [b'_Sc_le hS, L.Sc_pos]
  by_cases hc : (D.eTau (tauPl D (true, t)) : D.R.GG) ∈ D.host.thickPlaces
  · exact (L.win_thick j h1 h2 _ hc).2
  · have a2 := (L.win_thin j h1 h2 _ ⟨(D.eTau _).2, true_not_top D t, hc⟩).2
    linarith

theorem ctD_nonneg (u : D.what₂.Word) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) (t : HH D) : 0 ≤ ctD D u j t := by
  obtain ⟨j1, j2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hk := D.R.m_add_three_le_k
  have hp : ∀ τ, ∀ r ∈ Finset.range (D.R.N (i + 1 - 1)), 0 ≤ nuRow D u (i + 1) τ r :=
    fun τ r hr => (RowWeightLemmas.nuRow_pos D u i j2 τ r (Finset.mem_range.1 hr)).le
  have m0 : 0 ∈ Finset.range (D.R.N (i + 1 - 1)) := Finset.mem_range.2 (by unfold Ranks.N; omega)
  have m1 : 1 ∈ Finset.range (D.R.N (i + 1 - 1)) := Finset.mem_range.2 (by unfold Ranks.N; omega)
  have a1 := Finset.single_le_sum (hp (tauPl D (false, t))) m0
  have a2 := hp (tauPl D (false, t)) 0 m0
  have a3 := hp (tauPl D (false, t)) 1 m1
  have a4 := hp (tauPl D (true, t)) 0 m0
  unfold ctD nuAbs
  split_ifs <;> linarith

theorem ctD_le (h : SizesAt L) (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) (u : D.what₂.Word) (j : ℕ)
    (hj : j ∈ SizeData₂.lifts D) (t : HH D) :
    ctD D u j t ≤ (if t ∈ D.host.TT then 2 * L.sc.b else 0) + 4 * (D.R.k : ℝ) * L.sc.b' := by
  obtain ⟨j1, j2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  obtain ⟨e1, e2, e3⟩ := small_le P hx
  have e4 := P.kS_le
  have e5 := P.mteta
  have hb' := b'_pos L
  have hb := one_le_b L
  have hS := L.Sc_pos
  have hN : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
  have e6 : L.Sc ≤ L.sc.w'' D.R.n := by nlinarith
  have e7 : (D.R.N D.R.m : ℝ) ≤ L.sc.w'' D.R.n := by nlinarith
  have w0 := (wj_bounds h hx (i + 1) j1 j2 (tauPl D (false, t))).1
  have w1 := wj_false_le h P hx (i + 1) j1 j2 t
  have w2 := wj_true_le h P hx (i + 1) j1 j2 t
  have w3 : (D.R.k : ℝ) * wj D (i + 1) (tauPl D (false, t)) ≤ D.R.k * (9 / 4 * L.sc.b') :=
    mul_le_mul_of_nonneg_left w1 (by linarith)
  have w4 : 5 * L.sc.b' ≤ D.R.k * L.sc.b' := mul_le_mul_of_nonneg_right hk' hb'.le
  have a := (abs_le.1 (nuAbs_place P u i j2 _ w0)).2
  unfold ctD
  by_cases ht : t ∈ D.host.TT
  · simp only [if_pos ht]
    rw [topWt_top L (t := ⟨t, ht⟩) (eTau_false D t)] at a
    have b1 := (head_row u i j2 (tauPl D (false, t)) 0 (by omega)).2
    rw [D.hcW_first u _ (by omega), (L.top_u _ ⟨t, ht⟩ (by omega) (eTau_false D t)).1] at b1
    have b2 := (head_row u i j2 (tauPl D (false, t)) 1 (by omega)).1
    have b3 := (L.cloud_u u (tauPl D (false, t)) ⟨1, by omega⟩ le_rfl (by show 1 + 1 < D.R.k; omega)).2
    have b4 := (head_row u i j2 (tauPl D (true, t)) 0 (by omega)).1
    rw [D.hcW_first u _ (by omega)] at b4
    have b5 := P.cloud_place_bound (tauPl D (true, t)) (by omega) (true_not_top D t)
    have b6 := (L.cloud_v (tauPl D (true, t)) ⟨0, by omega⟩).2
    push_cast at b5
    linarith
  · simp only [if_neg ht]
    rw [topWt_off L (false_not_top ht)] at a
    linarith

theorem card_HH (D : D7) : (Fintype.card (HH D) : ℝ) = D.R.n := by
  have : Fintype.card (HH D) = D.R.n := D.R.card_A
  exact_mod_cast this

theorem f_eq (D : D7) : (D.R.f : ℝ) = 2 * D.R.n := by
  unfold Ranks.f
  push_cast
  ring

theorem sum_ctD_le (h : SizesAt L) (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) (j : ℕ) (hj : j ∈ SizeData₂.lifts D)
    (u : D.what₂.Word) :
    ∑ t : HH D, ctD D u j t ≤ 2 * (D.host.TT.card : ℝ) * L.sc.b + 2 * (D.R.f : ℝ) * D.R.k * L.sc.b' := by
  refine (Finset.sum_le_sum fun t _ => ctD_le h P hx u j hj t).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul, card_HH, f_eq]
  ring

theorem FRamD_bounds (h : SizesAt L) (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) :
    -((D.R.f : ℝ) * D.R.k * L.sc.b') ≤ FRamD D j ∧ FRamD D j ≤ 0 := by
  obtain ⟨j1, j2⟩ := Finset.mem_Icc.1 hj
  have hk := one_le_k D
  have hn := one_le_n D
  have hb' := b'_pos L
  have h0 : 0 ≤ ∑ t : HH D, min (wPl D j (false, t)) (wPl D j (true, t)) :=
    Finset.sum_nonneg fun t _ => le_min (wj_bounds h hx j j1 j2 _).1 (wj_bounds h hx j j1 j2 _).1
  have h1 : ∑ t : HH D, min (wPl D j (false, t)) (wPl D j (true, t)) ≤ D.R.n * (9 / 4 * L.sc.b') := by
    refine (Finset.sum_le_card_nsmul _ _ _ fun t _ =>
      (min_le_left _ _).trans (wj_false_le h P hx j j1 j2 t)).trans (le_of_eq ?_)
    rw [Finset.card_univ, nsmul_eq_mul, card_HH]
  have h2 : ((D.R.k : ℝ) - 1) / 2 * ∑ t : HH D, min (wPl D j (false, t)) (wPl D j (true, t)) ≤
      D.R.k / 2 * (D.R.n * (9 / 4 * L.sc.b')) := mul_le_mul (by linarith) h1 h0 (by linarith)
  have h3 : 0 ≤ (D.R.n : ℝ) * D.R.k * L.sc.b' := by positivity
  unfold FRamD
  rw [f_eq]
  exact ⟨by linarith, mul_nonpos_of_nonpos_of_nonneg (by linarith) h0⟩

theorem abs_EatD_le (h : SizesAt L) (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) :
    |EatD D j| ≤ (D.host.TT.card : ℝ) * L.sc.b + (D.R.f : ℝ) * D.R.k * L.sc.b' := by
  obtain ⟨a1, a2⟩ := FRamD_bounds h P hx j hj
  have a3 := Finset.sup'_le (⟨D.u₀, Finset.mem_univ _⟩ : (Finset.univ : Finset D.what₂.Word).Nonempty)
    (fun u : D.what₂.Word => ∑ t : HH D, ctD D u j t) fun u _ => sum_ctD_le h P hx j hj u
  have a4 := (Finset.sum_nonneg fun t _ => ctD_nonneg D.u₀ j hj t).trans
    (Finset.le_sup' (fun u : D.what₂.Word => ∑ t : HH D, ctD D u j t) (Finset.mem_univ D.u₀))
  have a5 : 0 ≤ (D.host.TT.card : ℝ) * L.sc.b := mul_nonneg (Nat.cast_nonneg _) (by linarith [one_le_b L])
  unfold EatD
  rw [abs_le]
  constructor <;> linarith

end GlobalTheory.RamifiedLoss

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumExponentLogLeOfCut
section
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

namespace GlobalTheory

theorem sum_exponent_log_le_of_cut :
    Formalism.CohomologicalDescent.E.ExCut → ∀ (P : Par) (X' A : ℝ), P.Hyp → P.Large → LargeParameterEstimates.Rows P X' A → LargeParameterEstimates.Big P.L P.x X' A →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P → Fintype.card ι = P.f → W.Sp.card ≤ 5 →
    ∀ T : ℕ, W.T2.card ≤ T → ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime) →
    ∑ l ∈ Q, (W.Jrec7 P l : ℝ) * Real.log (l : ℝ) ≤
      30 * (T : ℝ) * (P.m : ℝ) * P.b * P.L ^ 2 + 2 * (P.m : ℝ) * P.b := by
  intro hC P X' A hH hL hR hB ι _ _ W hW hcard hSp T hT Q hQ
  have hs := Formalism.CohomologicalDescent.E.recursion_sum_exceptional (Formalism.CohomologicalDescent.E.exIntervalLt_of_exCut hC) hC Formalism.CohomologicalDescent.Top.prime_count_bound_rs
    P hH hL ι W hW hcard hSp Q hQ
  have hTf : W.T2.card ≤ P.f := by rw [← hcard]; exact Finset.card_le_univ _
  have ht := LargeParameterEstimates.tail_bound_holds P X' A _ hH hR hB hTf
  have F := LargeParameterEstimates.large_parameter_facts_of_hyp hH hR hB
  have hb : 0 ≤ P.b := F.b_pos.le
  have hm : (0 : ℝ) ≤ (P.m : ℝ) * P.b * P.L ^ 2 := by positivity
  have hTT : (W.T2.card : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have key : 30 * (W.T2.card : ℝ) * (P.m : ℝ) * P.b * P.L ^ 2 ≤ 30 * (T : ℝ) * (P.m : ℝ) * P.b * P.L ^ 2 := by
    nlinarith
  linarith

end GlobalTheory
end

