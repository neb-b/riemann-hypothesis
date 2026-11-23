module

public import Mathlib
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0004
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0101
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0103
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0105
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0091
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0087
public import ReciprocityTheory.GroupCohomology.FinGen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0104
public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0094
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0106
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerVanishesOfRadicalSums

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousExpGAndToMInv
section
namespace GlobalTheory.CompanionTheory.ExpOneParam

theorem continuous_expG_and_toM_inv :
    ∀ (n : ℕ) (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.inG ε Z →
      Continuous (fun t : ℝ => Formalism.REAL.expG ε Z t) ∧
        ∀ t : ℝ, Formalism.REAL.toM (Formalism.REAL.expG ε Z t)⁻¹ = NormedSpace.exp (-((t : ℂ) • Z)) := by
  intro n ε Z hZ
  obtain ⟨h0, hadd, hcont, -⟩ := Formalism.REAL.group_exponential_facts n ε Z hZ
  refine ⟨hcont, fun t => ?_⟩
  have hinv : (Formalism.REAL.expG ε Z t)⁻¹ = Formalism.REAL.expG ε Z (-t) := by
    refine inv_eq_of_mul_eq_one_left ?_
    rw [← hadd, neg_add_cancel, h0]
  rw [hinv, Formalism.REAL.toM_expG ε Z (-t) hZ, Complex.ofReal_neg, neg_smul]

end GlobalTheory.CompanionTheory.ExpOneParam
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DvMemOf
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeCech

universe w

variable {R : Type} [CommRing R]

structure DFil (K : DCx.{w} R) where
  L : ℤ → ∀ p q, Submodule R (K.X p q)
  mem_h : ∀ r p q x, x ∈ L r p q → K.dh p q x ∈ L r (p + 1) q
  mem_v : ∀ r p q x, x ∈ L r p q → K.dv p q x ∈ L r p (q + 1)
  anti : ∀ {r r' : ℤ}, r ≤ r' → ∀ p q, L r' p q ≤ L r p q

def DFil.Ex {K : DCx.{w} R} (F : DFil K) (r : ℤ) (p : ℕ) : ℕ → Prop
  | 0 => ∀ x ∈ F.L r p 0, K.dv p 0 x ∈ F.L (r + 1) p 1 → x ∈ F.L (r + 1) p 0
  | q + 1 => ∀ x ∈ F.L r p (q + 1), K.dv p (q + 1) x ∈ F.L (r + 1) p (q + 2) →
      ∃ v ∈ F.L r p q, x - K.dv p q v ∈ F.L (r + 1) p (q + 1)

variable {K : DCx.{w} R} (F : DFil K)

theorem sgl_mem {r : ℤ} {p q : ℕ} {x : K.X p q} (hx : x ∈ F.L r p q) (a b : ℕ) : K.sgl p q x a b ∈ F.L r a b := by
  by_cases h : a = p ∧ b = q
  · obtain ⟨rfl, rfl⟩ := h
    rwa [K.sgl_self]
  · rw [K.sgl_ne x (by omega)]
    exact zero_mem _

theorem dv_mem_of {r : ℤ} {e q : ℕ} (y : ∀ p q, K.X p q) (h1 : K.D y e (q + 1) ∈ F.L r e (q + 1))
    (h2 : ∀ e', e = e' + 1 → y e' (q + 1) ∈ F.L r e' (q + 1)) : K.dv e q (y e q) ∈ F.L r e (q + 1) := by
  have h3 : K.Dh y e (q + 1) ∈ F.L r e (q + 1) := by
    cases e with
    | zero => exact zero_mem _
    | succ e => exact F.mem_h _ _ _ _ (h2 e rfl)
  rw [K.D_apply] at h1
  have h4 : (-1 : ℤ) ^ e • K.dv e q (y e q) ∈ F.L r e (q + 1) := (Submodule.add_mem_iff_right _ h3).1 h1
  rcases neg_one_pow_eq_or ℤ e with h | h <;> rw [h] at h4 <;> simpa using h4

theorem kill (r : ℤ) (m : ℕ) (y : ∀ p q, K.X p q) (hy : y ∈ K.T (m + 1)) (hyL : ∀ p q, y p q ∈ F.L r p q) :
    ∀ e : ℕ, (∀ p q, p < e → K.D y p q ∈ F.L (r + 1) p q) → (∀ p q, p < e → p + q = m + 1 → F.Ex r p q) →
      ∃ w ∈ K.T m, (∀ p q, e ≤ p → w p q = 0) ∧ (∀ p q, (y - K.D w) p q ∈ F.L r p q) ∧
        ∀ p q, p < e → (y - K.D w) p q ∈ F.L (r + 1) p q := by
  intro e
  induction e with
  | zero =>
    intro _ _
    refine ⟨0, zero_mem _, fun _ _ _ => rfl, fun p q => ?_, fun p q h => absurd h (by omega)⟩
    simpa using hyL p q
  | succ e ih =>
    intro hD hE
    obtain ⟨w, hwT, hw0, hwL, hwL'⟩ := ih (fun p q hp => hD p q (by omega)) (fun p q hp => hE p q (by omega))
    have hyT : y - K.D w ∈ K.T (m + 1) := sub_mem hy (K.D_mem m w hwT)
    have hDy : K.D (y - K.D w) = K.D y := by rw [map_sub, K.DD, sub_zero]
    generalize hy' : y - K.D w = y' at hyT hDy hwL hwL'
    by_cases he : e ≤ m + 1
    · obtain ⟨q, hq⟩ : ∃ q, e + q = m + 1 := ⟨m + 1 - e, by omega⟩
      have hx : K.dv e q (y' e q) ∈ F.L (r + 1) e (q + 1) :=
        dv_mem_of F y' (by rw [hDy]; exact hD e (q + 1) (by omega)) (fun e' h => hwL' e' (q + 1) (by omega))
      have hEx := hE e q (by omega) hq
      cases q with
      | zero =>
        have hx0 : y' e 0 ∈ F.L (r + 1) e 0 := hEx _ (hwL e 0) hx
        refine ⟨w, hwT, fun p q h => hw0 p q (by omega), by rw [hy']; exact hwL, fun p q hp => ?_⟩
        rw [hy']
        rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | rfl
        · exact hwL' p q hp
        · by_cases hq0 : q = 0
          · subst hq0; exact hx0
          · rw [hyT p q (by omega)]; exact zero_mem _
      | succ q =>
        obtain ⟨v, hv, hxv⟩ := hEx _ (hwL e (q + 1)) hx
        have hDu : K.D ((-1 : ℤ) ^ e • K.sgl e q v) =
            (-1 : ℤ) ^ e • K.sgl (e + 1) q (K.dh e q v) + K.sgl e (q + 1) (K.dv e q v) := by
          rw [map_zsmul, K.D_sgl, smul_add, smul_smul, ← pow_add, ← two_mul, pow_mul]
          simp
        have hval : ∀ p q', (y - K.D (w + (-1 : ℤ) ^ e • K.sgl e q v)) p q' =
            y' p q' - (-1 : ℤ) ^ e • K.sgl (e + 1) q (K.dh e q v) p q' - K.sgl e (q + 1) (K.dv e q v) p q' := by
          intro p q'
          rw [map_add (f := _), hDu, ← sub_sub, hy']
          simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
          abel
        refine ⟨w + (-1 : ℤ) ^ e • K.sgl e q v, add_mem hwT (?_), fun p q' h => ?_, fun p q' => ?_, fun p q' hp => ?_⟩
        · refine (K.T m).smul_of_tower_mem _ ?_
          intro a b hab
          exact K.sgl_ne v (by omega)
        · simp only [Pi.add_apply, Pi.smul_apply]
          rw [hw0 p q' (by omega), K.sgl_ne v (Or.inl (by omega))]
          simp
        · rw [hval]
          exact sub_mem (sub_mem (hwL p q') ((F.L r p q').smul_of_tower_mem _ (sgl_mem F (F.mem_h _ _ _ _ hv) p q')))
            (sgl_mem F (F.mem_v _ _ _ _ hv) p q')
        · rw [hval]
          rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | rfl
          · rw [K.sgl_ne _ (Or.inl (by omega)), K.sgl_ne _ (Or.inl (by omega))]
            simpa using hwL' p q' hp
          · rw [K.sgl_ne _ (Or.inl (by omega))]
            by_cases hq0 : q' = q + 1
            · subst hq0
              rw [K.sgl_self]
              simpa using hxv
            · rw [K.sgl_ne _ (Or.inr hq0), hyT p q' (by omega)]
              simp
    · refine ⟨w, hwT, fun p q h => hw0 p q (by omega), by rw [hy']; exact hwL, fun p q hp => ?_⟩
      rw [hy']
      rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | rfl
      · exact hwL' p q hp
      · rw [hyT p q (by omega)]; exact zero_mem _

theorem stair_up (n : ℕ) (hTop : ∀ p q, F.L 0 p q = ⊤) (hV : ∀ p q, n + 1 < p → Subsingleton (K.X p q))
    (hE : ∀ (r : ℕ) p q, q ≠ r → F.Ex (r : ℤ) p q) (P : K.X (n + 1) (n + 1)) (hP : P ∈ F.L ((n : ℤ) + 1) (n + 1) (n + 1))
    (y0 : ∀ p q, K.X p q) (hy0 : y0 ∈ K.T (2 * n + 1)) (hD : K.D y0 = K.sgl (n + 1) (n + 1) P) (r : ℕ) (hr : r ≤ n) :
    ∃ y ∈ K.T (2 * n + 1), K.D y = K.sgl (n + 1) (n + 1) P ∧ ∀ p q, y p q ∈ F.L (r : ℤ) p q := by
  induction r with
  | zero =>
    refine ⟨y0, hy0, hD, fun p q => ?_⟩
    rw [Nat.cast_zero, hTop]
    trivial
  | succ r ih =>
    obtain ⟨y, hyT, hDy, hyL⟩ := ih (by omega)
    have hPr : P ∈ F.L ((r : ℤ) + 1) (n + 1) (n + 1) := F.anti (by omega) _ _ hP
    obtain ⟨w, hwT, -, hwL, hwL'⟩ := kill F (r : ℤ) (2 * n) y hyT hyL (n + 2)
      (fun p q _ => by rw [hDy]; exact sgl_mem F hPr p q)
      (fun p q hp hq => hE r p q (by omega))
    refine ⟨y - K.D w, sub_mem hyT (K.D_mem _ w hwT), by rw [map_sub, K.DD, sub_zero, hDy], fun p q => ?_⟩
    rw [Nat.cast_succ]
    by_cases hp : p < n + 2
    · exact hwL' p q hp
    · have := hV p q (by omega)
      rw [Subsingleton.elim ((y - K.D w) p q) 0]
      exact zero_mem _

theorem stair (n : ℕ) (hTop : ∀ p q, F.L 0 p q = ⊤) (hV : ∀ p q, n + 1 < p → Subsingleton (K.X p q))
    (hE : ∀ (r : ℕ) p q, q ≠ r → F.Ex (r : ℤ) p q) (P : K.X (n + 1) (n + 1)) (hP : P ∈ F.L ((n : ℤ) + 1) (n + 1) (n + 1))
    (y0 : ∀ p q, K.X p q) (hy0 : y0 ∈ K.T (2 * n + 1)) (hD : K.D y0 = K.sgl (n + 1) (n + 1) P) :
    ∃ (ω : K.X n (n + 1)) (f : K.X (n + 1) n), ω ∈ F.L ((n : ℤ) + 1) n (n + 1) ∧
      K.dv n (n + 1) ω ∈ F.L ((n : ℤ) + 1 + 1) n (n + 2) ∧ f ∈ F.L (n : ℤ) (n + 1) n ∧
      P = K.dh n (n + 1) ω + (-1 : ℤ) ^ (n + 1) • K.dv (n + 1) n f := by
  obtain ⟨y, hyT, hDy, hyL⟩ := stair_up F n hTop hV hE P hP y0 hy0 hD n le_rfl

  obtain ⟨w, hwT, -, hwL, hwL'⟩ := kill F (n : ℤ) (2 * n) y hyT hyL (n + 1)
    (fun p q _ => by rw [hDy]; exact sgl_mem F hP p q) (fun p q hp hq => hE n p q (by omega))
  have hy1T : y - K.D w ∈ K.T (2 * n + 1) := sub_mem hyT (K.D_mem _ w hwT)
  have hDy1 : K.D (y - K.D w) = K.sgl (n + 1) (n + 1) P := by rw [map_sub, K.DD, sub_zero, hDy]
  generalize y - K.D w = y1 at hy1T hDy1 hwL hwL'

  have htT : y1 - K.sgl (n + 1) n (y1 (n + 1) n) ∈ K.T (2 * n + 1) :=
    sub_mem hy1T fun a b hab => K.sgl_ne _ (by omega)
  have hDt : K.D (y1 - K.sgl (n + 1) n (y1 (n + 1) n)) =
      K.sgl (n + 1) (n + 1) (P - (-1 : ℤ) ^ (n + 1) • K.dv (n + 1) n (y1 (n + 1) n)) := by
    have := hV (n + 2) n (by omega)
    rw [map_sub, K.D_sgl, hDy1, Subsingleton.elim (K.dh (n + 1) n (y1 (n + 1) n)) 0, map_zero, zero_add, map_sub, map_zsmul]
  have htL : ∀ p q, (y1 - K.sgl (n + 1) n (y1 (n + 1) n)) p q ∈ F.L ((n : ℤ) + 1) p q := by
    intro p q
    rw [Pi.sub_apply, Pi.sub_apply]
    by_cases hp : p < n + 1
    · rw [K.sgl_ne _ (Or.inl (by omega)), sub_zero]
      exact hwL' p q hp
    · by_cases hp' : p = n + 1
      · subst hp'
        by_cases hq : q = n
        · subst hq
          rw [K.sgl_self, sub_self]
          exact zero_mem _
        · rw [K.sgl_ne _ (Or.inr hq), hy1T _ _ (by omega), sub_zero]
          exact zero_mem _
      · have := hV p q (by omega)
        rw [Subsingleton.elim (y1 p q - K.sgl (n + 1) n (y1 (n + 1) n) p q) 0]
        exact zero_mem _
  have ecast : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; rfl
  obtain ⟨w2, hw2T, hw20, hw2L, hw2L'⟩ := kill F ((n : ℤ) + 1) (2 * n) _ htT htL n
    (fun p q hp => by
      rw [hDt, K.sgl_ne _ (Or.inl (by omega))]
      exact zero_mem _)
    (fun p q hp hq => by
      have := hE (n + 1) p q (by omega)
      rwa [ecast] at this)
  have hDt' : K.D ((y1 - K.sgl (n + 1) n (y1 (n + 1) n)) - K.D w2) =
      K.sgl (n + 1) (n + 1) (P - (-1 : ℤ) ^ (n + 1) • K.dv (n + 1) n (y1 (n + 1) n)) := by
    rw [map_sub, K.DD, sub_zero, hDt]
  have ht0 : ((y1 - K.sgl (n + 1) n (y1 (n + 1) n)) - K.D w2) (n + 1) n = 0 := by
    have h1 : K.D w2 (n + 1) n = 0 := by
      rw [K.D_apply]
      have h2 : K.Dv w2 (n + 1) n = 0 := by
        cases n with
        | zero => rfl
        | succ n =>
          show K.dv (n + 1 + 1) n (w2 (n + 1 + 1) n) = 0
          rw [hw20 _ _ (by omega), map_zero]
      have h3 : K.Dh w2 (n + 1) n = 0 := by
        show K.dh n n (w2 n n) = 0
        rw [hw20 _ _ le_rfl, map_zero]
      rw [h2, h3]; simp
    show (y1 (n + 1) n - K.sgl (n + 1) n (y1 (n + 1) n) (n + 1) n) - K.D w2 (n + 1) n = 0
    rw [h1, K.sgl_self]
    simp
  generalize (y1 - K.sgl (n + 1) n (y1 (n + 1) n)) - K.D w2 = t at hDt' ht0 hw2L hw2L'
  refine ⟨t n (n + 1), y1 (n + 1) n, hw2L _ _, ?_, hwL _ _, ?_⟩
  · refine dv_mem_of F t ?_ (fun e' h => hw2L' e' _ (by omega))
    rw [hDt', K.sgl_ne _ (Or.inl (by omega))]
    exact zero_mem _
  · have h := congrFun (congrFun hDt' (n + 1)) (n + 1)
    rw [K.sgl_self, K.D_apply] at h
    have h2 : K.Dv t (n + 1) (n + 1) = 0 := by
      show K.dv (n + 1) n (t (n + 1) n) = 0
      rw [ht0, map_zero]
    rw [h2, smul_zero, add_zero] at h
    have h3 : K.Dh t (n + 1) (n + 1) = K.dh n (n + 1) (t n (n + 1)) := rfl
    rw [← h3, h]
    abel

end GlobalTheory.CompanionTheory.ConeCech
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ElementsBijectiveOfBijectiveAppStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elements_bijective_of_bijective_app : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {E' E : C ⥤ Type t} (p : E' ⟶ E) (F : C ⥤ ModuleCat.{w} R), (∀ T, Function.Bijective (p.app T)) → ∀ n, Function.Bijective ((elMor p F).hom.f n) := by
  first | exact @GlobalTheory.CompanionTheory.Cech.elMor_bijective_of_bijective | exact GlobalTheory.CompanionTheory.Cech.elMor_bijective_of_bijective | (intros; apply GlobalTheory.CompanionTheory.Cech.elMor_bijective_of_bijective <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InitialObjectAugmentedResolutionStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.initial_object_augmented_resolution : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R) (T₀ : C) (h : Limits.IsInitial T₀), (cx F).ResUpTo 1 (aug F fun T => (F.map (h.to T)).hom) := by
  first | exact @GlobalTheory.CompanionTheory.InitialCoh.resUpTo_one | exact GlobalTheory.CompanionTheory.InitialCoh.resUpTo_one | (intros; apply GlobalTheory.CompanionTheory.InitialCoh.resUpTo_one <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHaarMeasureSingleton
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
noncomputable section

namespace GlobalTheory.CompanionTheory.Mass.MeanV

theorem isStdV_measure_singleton_zero : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (lam : Measure (Fv F v)), IsStdV v lam → lam {0} = 0 := by
  intro F _ _ v lam hstd
  obtain ⟨hH, h1⟩ := hstd
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : CharZero (Fv F v) :=
    charZero_of_injective_algebraMap (algebraMap F (Fv F v)).injective
  have hs : ∀ x : Fv F v, lam {x} = lam {0} := by
    intro x
    rw [← measure_preimage_add lam x ({x} : Set (Fv F v))]
    congr 1
    ext y
    simp
  by_contra h0
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_mul_gt h0 ENNReal.one_ne_top
  have hcard : ((Finset.range N).image (fun n : ℕ => (n : Fv F v))).card = N := by
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  have hsum : lam (((Finset.range N).image (fun n : ℕ => (n : Fv F v)) : Finset (Fv F v)) : Set (Fv F v))
      = N * lam {0} := by
    rw [← sum_measure_singleton, Finset.sum_congr rfl (fun x _ => hs x), Finset.sum_const, hcard,
      nsmul_eq_mul]
  have hsub : (((Finset.range N).image (fun n : ℕ => (n : Fv F v)) : Finset (Fv F v)) : Set (Fv F v))
      ⊆ (v.adicCompletionIntegers F : Set (Fv F v)) := by
    intro x hx
    simp only [Finset.coe_image, Set.mem_image] at hx
    obtain ⟨n, -, rfl⟩ := hx
    exact natCast_mem (v.adicCompletionIntegers F) n
  have hle := measure_mono (μ := lam) hsub
  rw [hsum, h1] at hle
  exact absurd hN (not_lt.2 hle)

end GlobalTheory.CompanionTheory.Mass.MeanV

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleFiniteLimitOfLseq
section
open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw

namespace GlobalTheory.CompanionTheory.TowerLim

theorem module_finite_lim : ∀ (W : Type) [CommRing W] (l : ℕ) [IsAdicComplete (Ideal.span {(l : W)}) W]
    (S S' : Sys.{1} W) (_ : LSeq l S S'), IsFiniteLength W (S.M 1) → Module.Finite W S.lim := by
  intro W _ l _ S S' L h1
  have hfl := _root_.GlobalTheory.CompanionTheory.TowerLen.isFiniteLength_level W l S S' L h1
  have hart : ∀ n, IsArtinian W (S.M n) := fun n =>
    (isFiniteLength_iff_isNoetherian_isArtinian.1 (hfl n)).2
  have hinj := _root_.GlobalTheory.CompanionTheory.Tower.lim_eq_pow_smul W l S S' L hart

  have hvan : ∀ n, (Ideal.span {(l : W)} ^ n • (⊤ : Submodule W S.lim)) ≤ LinearMap.ker (pr S n) := by
    intro n
    refine Submodule.smul_le.2 fun r hr m _ => ?_
    rw [Ideal.span_singleton_pow] at hr
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [LinearMap.mem_ker, map_smul, mul_smul]
    rw [L.kill n, smul_zero]
  have hH : IsHausdorff (Ideal.span {(l : W)}) S.lim := by
    refine ⟨fun x hx => Subtype.ext (funext fun n => ?_)⟩
    have hm : x ∈ (Ideal.span {(l : W)} ^ n • (⊤ : Submodule W S.lim)) := by
      simpa [SModEq.zero] using hx n
    exact hvan n hm
  have hmem1 : ∀ x : S.lim, pr S 1 x = 0 → x ∈ Ideal.span {(l : W)} • (⊤ : Submodule W S.lim) := by
    intro x hx
    obtain ⟨y, hy⟩ := hinj 1 x hx
    rw [hy, pow_one]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial
  have hle : Ideal.span {(l : W)} • (⊤ : Submodule W S.lim) ≤ LinearMap.ker (pr S 1) := by
    simpa using hvan 1
  let q := (Ideal.span {(l : W)} • (⊤ : Submodule W S.lim)).liftQ (pr S 1) hle
  have hq : Function.Injective q := by
    refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
    induction z using Submodule.Quotient.induction_on with
    | H x =>
      rw [Submodule.Quotient.mk_eq_zero]
      exact hmem1 x hz
  have : IsNoetherian W (S.M 1) := (isFiniteLength_iff_isNoetherian_isArtinian.1 h1).1
  have : Module.Finite W (S.lim ⧸ Ideal.span {(l : W)} • (⊤ : Submodule W S.lim)) :=
    Module.Finite.of_injective q hq
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := W)
    (M := S.lim ⧸ Ideal.span {(l : W)} • (⊤ : Submodule W S.lim))
  choose s' hs' using fun i => Submodule.Quotient.mk_surjective _ (s i)
  have : IsPrecomplete (Ideal.span {(l : W)}) (Fin r → W) := ReciprocityTheory.Coh.isPrecomplete_pi _
  have hsurj : Function.Surjective ((Ideal.span {(l : W)} • (⊤ : Submodule W S.lim)).mkQ ∘ₗ
      Fintype.linearCombination W s') := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hs, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨Pi.single i 1, by simp [hs']⟩
  exact Module.Finite.of_surjective _ (surjective_of_mkQ_comp_surjective hsurj)

end GlobalTheory.CompanionTheory.TowerLim
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PatternSetCardColumnStepStatement
section
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pattern_set_card_column_step : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ), j < d →
    (patSet (K := K) (colGe d j)).ncard =
      Fintype.card K ^ j * (patSet (K := K) (colGe d (j + 1))).ncard := by
  intro K _ _ _ d j hj
  classical
  have card_colGe (k : ℕ) :
      (patSet (K := K) (colGe d k)).ncard =
        Fintype.card K ^ Nat.card {p : Fin d × Fin d // colGe d k p.1 p.2} := by
    let A (f : {p : Fin d × Fin d // colGe d k p.1 p.2} → K) : Matrix (Fin d) (Fin d) K :=
      fun i l => if i = l then 1 else if h : colGe d k i l then f ⟨(i, l), h⟩ else 0
    have hunit (f) : IsUnit (A f).det := by
      have htri : (A f).IsUpperTriangular := by
        intro i l h
        change l < i at h
        have hnot : ¬ colGe d k i l := fun hcol => (not_lt_of_gt h) hcol.1
        simp [A, ne_of_gt h, hnot]
      rw [Matrix.det_of_isUpperTriangular htri]
      simp [A]
    let e : patSet (K := K) (colGe d k) ≃ ({p : Fin d × Fin d // colGe d k p.1 p.2} → K) :=
      { toFun := fun u p => (u.val : Matrix (Fin d) (Fin d) K) p.1.1 p.1.2
        invFun := fun f => ⟨Matrix.nonsingInvUnit (A f) (hunit f), by
          intro i l
          change (i = l → A f i l = 1) ∧ (i ≠ l → ¬ colGe d k i l → A f i l = 0)
          exact ⟨fun h => by simp [A, h], fun h hcol => by simp [A, h, hcol]⟩⟩
        left_inv := fun u => by
          apply Subtype.ext
          apply Units.ext
          ext i l
          change A (fun p => (u.val : Matrix (Fin d) (Fin d) K) p.1.1 p.1.2) i l =
            (u.val : Matrix (Fin d) (Fin d) K) i l
          have hu := u.property i l
          by_cases hil : i = l
          · simpa only [A, ite_eq_left hil] using (hu.1 hil).symm
          · by_cases hcol : colGe d k i l
            · simp [A, hil, hcol]
            · simp [A, hil, hcol, hu.2 hil hcol]
        right_inv := fun f => by
          funext p
          change A f p.1.1 p.1.2 = f p
          have hil : p.1.1 ≠ p.1.2 := ne_of_lt p.2.1
          simp [A, hil, p.2] }
    rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card (α := K)]
  rw [card_colGe j, card_colGe (j + 1), natCard_colGe d j hj, pow_add]
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexLatticeEqHaarDetStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_lattice_eq_haar_det : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (g : GL (Fin n) k) (A₀ A : AddSubgroup (Fin n → k)), IsCompact (A : Set (Fin n → k)) → IsOpen (A₀ : Set (Fin n → k)) → A₀ ≤ A → A₀ ≤ A.comap (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k)).toAddMonoidHom → ((A₀.relIndex A : ℕ) : ℝ) = (MeasureTheory.distribHaarChar k (Matrix.GeneralLinearGroup.det g) : ℝ) * ((A₀.relIndex (A.comap (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k)).toAddMonoidHom) : ℕ) : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.IndexDet.relIndex_eq_distribHaarChar_det_mul | exact GlobalTheory.CompanionTheory.IndexDet.relIndex_eq_distribHaarChar_det_mul | (intros; apply GlobalTheory.CompanionTheory.IndexDet.relIndex_eq_distribHaarChar_det_mul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerColumnRecursionStatement
section
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_column_recursion : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (ψ₀ : AddChar K ℂ) (χ : GL (Fin d) K → ℂ), j < d →
    (patSet (K := K) (colGe d j)).ncard = Fintype.card K ^ j * (patSet (K := K) (colGe d (j + 1))).ncard →
    (∀ x : Fin j → K, (∑ r : Fin j → K, (ψ₀ (∑ i, r i * x i))⁻¹) = if x = 0 then (Fintype.card K : ℂ) ^ j else 0) →
    wh (colGe d (j + 1)) (colGeE K d (j + 1)) ψ₀ χ = ∑ r : Fin j → K, wh (colGe d j) (colGeR K d j r) ψ₀ χ := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.ColStep.Fourier.wh_colGe_succ_eq_sum | exact GlobalTheory.CompanionTheory.TyFin.ColStep.Fourier.wh_colGe_succ_eq_sum | (intros; apply GlobalTheory.CompanionTheory.TyFin.ColStep.Fourier.wh_colGe_succ_eq_sum <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerVanishesOfRadicalSumsStatement
section
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_vanishes_of_radical_sums : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (ψ₀ : AddChar K ℂ) (χ : GL (Fin d) K → ℂ),
    (∀ u : GL (Fin d) K, (open Classical in ∑ v : GL (Fin d) K,
      if v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j) then χ (u * v) else 0) = 0) →
    wh (colGe d j) (colGeR K d j 0) ψ₀ χ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.ColStep.Avg.wh_zero_row' | exact GlobalTheory.CompanionTheory.TyFin.ColStep.Avg.wh_zero_row' | (intros; apply GlobalTheory.CompanionTheory.TyFin.ColStep.Avg.wh_zero_row' <;> assumption)
end

