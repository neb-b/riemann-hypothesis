module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.TwistSubEqMatrixSubst
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.GenericMatrixEvaluationDet
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0012
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0011
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0013
public import Lemmata.GeneralBFactLeftAltForm.MQ
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.IsotypicProjectionCommutesOperators

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.BinomialStableContainsComponents
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def genericMatrixRootWeights (R : Type*) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) (GLCoord R n) :=
  (genMat R n).map fun x => algebraMap _ (GLCoord R n) x

def genericMatrixInverse (R : Type*) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) (GLCoord R n) :=
  ((genMat R n).adjugate).map fun x =>
    IsLocalization.Away.invSelf (genMat R n).det * algebraMap _ (GLCoord R n) x

def coefficientMap (R : Type*) [CommRing R] (n : ℕ) : R →+* GLCoord R n :=
  (algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n)).comp MvPolynomial.C

def genericTranslate {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι)
    (G : MvPolynomial (ι × Fin n) R) : MvPolynomial (ι × Fin n) (GLCoord R n) :=
  matrixSubst LL S (coefficientMap R n) (genericMatrixInverse R n) (genericMatrixRootWeights R n) G


open Classical in
def weightComponent {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (nu : Fin n → ℤ) (F : MvPolynomial (ι × Fin n) R) : MvPolynomial (ι × Fin n) R :=
  ∑ m ∈ F.support.filter (fun m => wtS LL S m = nu), monomial m (F.coeff m)

def TorusActsThroughWeight : Prop :=
  ∀ (R B : Type) [CommRing R] [CommRing B] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι)
    (φ : R →+* B) (D : Fin n → Bˣ) (m : ι × Fin n →₀ ℕ) (c : R),
      matrixSubst LL S φ (Matrix.diagonal fun a => ((D a : Bˣ) : B)) (Matrix.diagonal fun a => (((D a)⁻¹ : Bˣ) : B))
        (monomial m c) = monomial m (φ c * ((∏ a, D a ^ (wtS LL S m a) : Bˣ) : B))

def BinomialStableContainsComponents : Prop :=
  ∀ (R : Type) [CommRing R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι)
    (W : Submodule R (MvPolynomial (ι × Fin n) R)), (∀ a k, ∀ x ∈ W, binomPol R LL S a k x ∈ W) →
    ∀ x ∈ W, ∀ nu, weightComponent LL S nu x ∈ W

def TwistExponentsAreWeightEntries : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι) (j : Fin n)
    (G : MvPolynomial (ι × Fin n) R),
      sDegs LL S j G = (genericTranslate LL S G).support.image (fun m => wtS LL S m j)

def GenericMonomialsSpecialise : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι)
    (k1 : Type) [CommRing k1] (φ : R →+* k1) (g0 g0inv : Matrix (Fin n) (Fin n) k1), g0 * g0inv = 1 →
    ∀ G : MvPolynomial (ι × Fin n) R, (matrixSubst LL S φ g0inv g0 G).support ⊆ (genericTranslate LL S G).support

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.CrRootMem
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ}

def cr_Pos (n : ℕ) : AddSubmonoid (Fin n → ℤ) :=
  AddSubmonoid.closure {β | ∃ a b : Fin n, a < b ∧ β = rootW a b}

def cr_h (ν : Fin n → ℤ) : ℤ := ∑ a : Fin n, ∑ b : Fin n, if a < b then ν a - ν b else 0

def cr_c (ν : Fin n → ℤ) : ℤ := ∑ a, ν a ^ 2 + cr_h ν

theorem cr_ht_add (x y : Fin n → ℤ) : weightHeight' (x + y) = weightHeight' x + weightHeight' y := by
  simp only [weightHeight', Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

theorem cr_ht_zero : weightHeight' (0 : Fin n → ℤ) = 0 := by simp [weightHeight']

theorem cr_ht_root (a b : Fin n) (h : a < b) : 0 < weightHeight' (rootW a b) := by
  have := v2rep_ht_root (0 : Fin n → ℤ) a b h
  rwa [zero_add, cr_ht_zero] at this

theorem cr_h_eq (ν : Fin n → ℤ) : cr_h ν = ∑ a : Fin n, ((n : ℤ) - 1 - 2 * (a.val : ℤ)) * ν a := by
  classical
  have h1 : ∀ a : Fin n, (∑ b : Fin n, if a < b then ν a else 0) = ((n : ℤ) - 1 - (a.val : ℤ)) * ν a := by
    intro a
    rw [← Finset.sum_filter, Finset.sum_const]
    have : (Finset.univ.filter fun b : Fin n => a < b) = Finset.Ioi a := by ext b; simp
    rw [this, Fin.card_Ioi, nsmul_eq_mul]
    have ha := a.isLt
    congr 1
    omega
  have h2 : ∀ b : Fin n, (∑ a : Fin n, if a < b then ν b else 0) = (b.val : ℤ) * ν b := by
    intro b
    rw [← Finset.sum_filter, Finset.sum_const]
    have : (Finset.univ.filter fun a : Fin n => a < b) = Finset.Iio b := by ext a; simp
    rw [this, Fin.card_Iio, nsmul_eq_mul]
  have h3 : cr_h ν = (∑ a : Fin n, ∑ b : Fin n, if a < b then ν a else 0) -
      ∑ a : Fin n, ∑ b : Fin n, if a < b then ν b else 0 := by
    rw [cr_h, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp
  rw [h3, Finset.sum_comm (f := fun a b : Fin n => if a < b then ν b else 0), Finset.sum_congr rfl fun a _ => h1 a,
    Finset.sum_congr rfl fun b _ => h2 b, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem cr_h_ht (ν : Fin n → ℤ) : cr_h ν = ((n : ℤ) - 1) * ∑ a, ν a + 2 * weightHeight' ν := by
  rw [cr_h_eq, weightHeight', Finset.mul_sum, mul_neg, Finset.mul_sum, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem cr_Pos_sum {β : Fin n → ℤ} (h : β ∈ cr_Pos n) : ∑ a, β a = 0 := by
  classical
  induction h using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨a, b, _, rfl⟩ := hx
    simp [rootW, Finset.sum_sub_distrib]
  | zero => simp
  | add x y _ _ hx hy => simp [Finset.sum_add_distrib, hx, hy]

theorem cr_Pos_ht {β : Fin n → ℤ} (h : β ∈ cr_Pos n) : 0 ≤ weightHeight' β := by
  induction h using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨a, b, hab, rfl⟩ := hx
    exact (cr_ht_root a b hab).le
  | zero => rw [cr_ht_zero]
  | add x y _ _ hx hy => rw [cr_ht_add]; omega

theorem cr_Pos_pair {ν β : Fin n → ℤ} (hν : Dominant ν) (h : β ∈ cr_Pos n) : 0 ≤ ∑ a, ν a * β a := by
  classical
  induction h using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨a, b, hab, rfl⟩ := hx
    have : ∑ c, ν c * rootW a b c = ν a - ν b := by
      simp [rootW, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]
    rw [this]
    have := hν hab.le
    omega
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    omega

theorem cr_root_mem (a b : Fin n) (h : a < b) : rootW a b ∈ cr_Pos n :=
  AddSubmonoid.subset_closure ⟨a, b, h, rfl⟩

theorem cr_c_lt {lam mu : Fin n → ℤ} (hl : Dominant lam) (hm : Dominant mu) (h : lam - mu ∈ cr_Pos n)
    (hpos : 0 < weightHeight' (lam - mu)) : cr_c mu < cr_c lam := by
  have h1 := cr_Pos_pair hl h
  have h2 := cr_Pos_pair hm h
  have h3 := cr_Pos_sum h
  have e1 : cr_h lam - cr_h mu = 2 * weightHeight' (lam - mu) := by
    have hh : cr_h (lam - mu) = 2 * weightHeight' (lam - mu) := by rw [cr_h_ht, h3]; ring
    rw [← hh, cr_h_eq, cr_h_eq, cr_h_eq, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.sub_apply]
    ring
  have e2 : ∑ a, lam a ^ 2 - ∑ a, mu a ^ 2 = ∑ a, lam a * (lam - mu) a + ∑ a, mu a * (lam - mu) a := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.sub_apply]
    ring
  unfold cr_c
  omega

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.DegreeZeroWeightsBounded
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def casimirConjugation (E : GLOps n K V) (c : Fin n) (s : Finset (Fin n)) : Module.End K (Module.End K V) :=
  ∑ i ∈ s, (LinearMap.mulLeft K (E c i)).comp (LinearMap.mulRight K (E i c))

def casimirPower (E : GLOps n K V) (c : Fin n) (s : Finset (Fin n)) (q : ℕ) : Module.End K V :=
  ((casimirConjugation E c s) ^ q) 1

def casimirPowerScaled (E : GLOps n K V) (c : Fin n) (s : Finset (Fin n)) (b q : ℕ) : Module.End K V :=
  ((b.factorial : K) / (((q + b).factorial : K) * (q.factorial : K))) • casimirPower E c s q

def extremalProjector (E : GLOps n K V) (c : Fin n) (L : ℕ) : Module.End K V :=
  ∑ q ∈ range (L + 1), ((-1 : K) ^ q) • casimirPowerScaled E c (Finset.Iio c) c.val q

def DegreeZeroWeightsBounded (E : GLOps n K V) (L : ℕ) : Prop :=
  ∀ ν : Fin n → ℤ, (∑ a, ν a = 0) → weightSp E ν ≠ ⊥ → ∀ a, |ν a| ≤ (L : ℤ)

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.DividedPowerPadicValuationBound
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem choose_factorial_identity (α β f : ℕ) (h : f ≤ β) :
    β.choose f * ((β - f).factorial * (α + f).factorial) = (α + f).choose f * (β.factorial * α.factorial) := by
  have h1 := Nat.choose_mul_factorial_mul_factorial h
  have h2 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left f α)
  rw [Nat.add_sub_cancel] at h2
  apply Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos f)
  calc f.factorial * (β.choose f * ((β - f).factorial * (α + f).factorial))
      = (β.choose f * f.factorial * (β - f).factorial) * (α + f).factorial := by ring
    _ = β.factorial * (α + f).factorial := by rw [h1]
    _ = β.factorial * ((α + f).choose f * f.factorial * α.factorial) := by rw [h2]
    _ = f.factorial * ((α + f).choose f * (β.factorial * α.factorial)) := by ring

theorem product_two_coordinates_swap {n : ℕ} (g g' : Fin n → ℕ) (a b : Fin n) (hab : a ≠ b)
    (h : ∀ c, c ≠ a → c ≠ b → g' c = g c) :
    (∏ c, g' c) * (g a * g b) = (∏ c, g c) * (g' a * g' b) := by
  classical
  have hs : ∀ f : Fin n → ℕ, ∏ c, f c = f a * f b * ∏ c ∈ (univ.erase a).erase b, f c := by
    intro f
    rw [← Finset.mul_prod_erase univ f (mem_univ a),
      ← Finset.mul_prod_erase (univ.erase a) f (mem_erase.2 ⟨hab.symm, mem_univ b⟩)]
    ring
  have hrest : ∏ c ∈ (univ.erase a).erase b, g' c = ∏ c ∈ (univ.erase a).erase b, g c :=
    prod_congr rfl fun c hc => h c (ne_of_mem_erase (mem_of_mem_erase hc)) (ne_of_mem_erase hc)
  rw [hs g', hs g, hrest]
  ring

theorem sum_single_apply_section {ι : Type} {n : ℕ} (g : ι → ι × Fin n) (hg : ∀ l, (g l).1 = l) (f : ι →₀ ℕ)
    (v : ι × Fin n) [Decidable (v = g v.1)] :
    (∑ l ∈ f.support, Finsupp.single (g l) (f l)) v = if v = g v.1 then f v.1 else 0 := by
  classical
  rw [Finsupp.finsetSum_apply]
  have key : ∀ l, g l = v → l = v.1 ∧ v = g v.1 := by
    rintro l rfl
    exact ⟨(hg l).symm, by rw [hg l]⟩
  split_ifs with hv
  · rw [Finset.sum_eq_single v.1]
    · rw [← hv, Finsupp.single_eq_same]
    · intro l _ hl
      rw [Finsupp.single_apply, if_neg]
      exact fun h => hl (key l h).1
    · intro hnot
      simp only [Finsupp.mem_support_iff, not_not] at hnot
      simp [hnot]
  · refine Finset.sum_eq_zero fun l _ => ?_
    rw [Finsupp.single_apply, if_neg]
    exact fun h => hv (key l h).2

theorem exponent_factorial_eq_prod {ι : Type} [Fintype ι] {n : ℕ} (m : ι × Fin n →₀ ℕ) :
    expFact m = ∏ l : ι, ∏ c : Fin n, (m (l, c)).factorial := by
  classical
  unfold expFact
  rw [Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero), Fintype.prod_prod_type]

theorem exponent_factorial_ne_zero {σ : Type} (m : σ →₀ ℕ) : expFact m ≠ 0 := by
  unfold expFact Finsupp.prod
  exact Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _

theorem divided_power_padic_valuation_bound {ι : Type} [Fintype ι] {n : ℕ} (p : ℕ) [Fact p.Prime] (src dst : ι → ι × Fin n)
    (hs : ∀ l, (src l).1 = l) (hd : ∀ l, (dst l).1 = l) (hne : ∀ l, src l ≠ dst l)
    (m : ι × Fin n →₀ ℕ) (f : ι →₀ ℕ) (zf : ι → ℤ) (hz : ∀ l, (zf l).natAbs = (m (src l)).choose (f l)) :
    (∏ l ∈ f.support, zf l) = 0 ∨ padicValNat p (expFact m) ≤ 2 * padicValInt p (∏ l ∈ f.support, zf l) +
      padicValNat p (expFact ((m - ∑ l ∈ f.support, Finsupp.single (src l) (f l)) +
        ∑ l ∈ f.support, Finsupp.single (dst l) (f l))) := by
  classical
  by_cases hall : ∀ l ∈ f.support, f l ≤ m (src l)
  swap
  ·
    left
    push_neg at hall
    obtain ⟨l, hl, hlt⟩ := hall
    apply Finset.prod_eq_zero hl
    have := hz l
    rw [Nat.choose_eq_zero_of_lt hlt] at this
    exact Int.natAbs_eq_zero.1 this
  have hall' : ∀ l, f l ≤ m (src l) := fun l => by
    by_cases hl : l ∈ f.support
    · exact hall l hl
    · simp only [Finsupp.mem_support_iff, not_not] at hl
      rw [hl]
      exact Nat.zero_le _
  right
  have hm' : ∀ x : ι × Fin n, ((m - ∑ l ∈ f.support, Finsupp.single (src l) (f l)) +
      ∑ l ∈ f.support, Finsupp.single (dst l) (f l)) x =
      (m x - (if x = src x.1 then f x.1 else 0)) + (if x = dst x.1 then f x.1 else 0) := by
    intro x
    rw [Finsupp.add_apply, Finsupp.tsub_apply, sum_single_apply_section src hs f x, sum_single_apply_section dst hd f x]
  set m' : ι × Fin n →₀ ℕ := (m - ∑ l ∈ f.support, Finsupp.single (src l) (f l)) +
      ∑ l ∈ f.support, Finsupp.single (dst l) (f l) with hm'def

  have hrow : ∀ l, (∏ c, (m (l, c)).factorial) * (m (dst l) + f l).choose (f l) =
      (∏ c, (m' (l, c)).factorial) * (m (src l)).choose (f l) := by
    intro l
    obtain ⟨a, ha⟩ : ∃ a, src l = (l, a) := ⟨(src l).2, Prod.ext (hs l) rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, dst l = (l, b) := ⟨(dst l).2, Prod.ext (hd l) rfl⟩
    have hab : a ≠ b := fun h => hne l (by rw [ha, hb, h])
    have hma : m' (l, a) = m (l, a) - f l := by
      rw [hm']; simp [ha, hb, hab]
    have hmb : m' (l, b) = m (l, b) + f l := by
      rw [hm']; simp [ha, hb, hab, Ne.symm hab]
    have hmc : ∀ c, c ≠ a → c ≠ b → m' (l, c) = m (l, c) := by
      intro c hca hcb
      rw [hm']; simp [ha, hb, hca, hcb]
    have hF : f l ≤ m (l, a) := ha ▸ hall' l
    have h2 := product_two_coordinates_swap (fun c => (m (l, c)).factorial) (fun c => (m' (l, c)).factorial) a b hab
      (fun c hca hcb => by simp only [hmc c hca hcb])
    beta_reduce at h2
    rw [hma, hmb] at h2
    have h3 := choose_factorial_identity (m (l, b)) (m (l, a)) (f l) hF
    rw [ha, hb]
    apply Nat.eq_of_mul_eq_mul_right
      (Nat.mul_pos (Nat.factorial_pos (m (l, a))) (Nat.factorial_pos (m (l, b))))
    calc (∏ c, (m (l, c)).factorial) * (m (l, b) + f l).choose (f l) *
          ((m (l, a)).factorial * (m (l, b)).factorial)
        = (∏ c, (m (l, c)).factorial) * ((m (l, b) + f l).choose (f l) *
          ((m (l, a)).factorial * (m (l, b)).factorial)) := by ring
      _ = (∏ c, (m (l, c)).factorial) * ((m (l, a)).choose (f l) *
          ((m (l, a) - f l).factorial * (m (l, b) + f l).factorial)) := by rw [h3]
      _ = (m (l, a)).choose (f l) * ((∏ c, (m (l, c)).factorial) *
          ((m (l, a) - f l).factorial * (m (l, b) + f l).factorial)) := by ring
      _ = (m (l, a)).choose (f l) * ((∏ c, (m' (l, c)).factorial) *
          ((m (l, a)).factorial * (m (l, b)).factorial)) := by rw [h2]
      _ = (∏ c, (m' (l, c)).factorial) * (m (l, a)).choose (f l) *
          ((m (l, a)).factorial * (m (l, b)).factorial) := by ring
  have htot : expFact m * ∏ l, (m (dst l) + f l).choose (f l) =
      expFact m' * ∏ l, (m (src l)).choose (f l) := by
    rw [exponent_factorial_eq_prod m, exponent_factorial_eq_prod m', ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun l _ => hrow l
  have hY : (∏ l ∈ f.support, zf l).natAbs = ∏ l, (m (src l)).choose (f l) := by
    have hnat : (∏ l ∈ f.support, zf l).natAbs = ∏ l ∈ f.support, (zf l).natAbs := by
      first
        | exact map_prod Int.natAbsHom zf f.support
        | simpa using map_prod Int.natAbsHom zf f.support
    rw [hnat, Finset.prod_congr rfl (fun l _ => hz l)]
    refine Finset.prod_subset (Finset.subset_univ _) fun l _ hl => ?_
    simp only [Finsupp.mem_support_iff, not_not] at hl
    rw [hl, Nat.choose_zero_right]
  have hX0 : ∏ l, (m (dst l) + f l).choose (f l) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun l _ => (Nat.choose_pos (Nat.le_add_left _ _)).ne'
  have hY0 : ∏ l, (m (src l)).choose (f l) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun l _ => (Nat.choose_pos (hall' l)).ne'
  have hv := congrArg (padicValNat p) htot
  rw [(show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (exponent_factorial_ne_zero m) hX0, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (exponent_factorial_ne_zero m') hY0] at hv
  rw [show padicValInt p (∏ l ∈ f.support, zf l) =
    padicValNat p (∏ l ∈ f.support, zf l).natAbs from by
      rw [padicValInt, Nat.padicValNat_def], hY]
  omega

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.ExistsClearDenominators
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section lat
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {W : Type} [AddCommGroup W] [Module (KK O) W] [Module O W] [IsScalarTower O (KK O) W]

theorem exists_clear_denominators_alt (M : Submodule O W) (y : W) (hy : y ∈ MQ (K := KK O) M) : ∃ a : O, a ≠ 0 ∧ a • y ∈ M := by
  apply Bl.general_b_fact_left_alt_form.goal1
  exact hy

def latticeInter (M : Submodule O W) (L : Submodule (KK O) W) : Submodule O L :=
  M.comap (L.subtype.restrictScalars O)

theorem latticeInter_isLattice (M : Submodule O W) (hfg : M.FG) (hMQ : MQ (K := KK O) M = ⊤) (L : Submodule (KK O) W) :
    Submodule.IsFullLattice (KK O) (latticeInter M L) := by
  refine { toIsLattice := Submodule.IsLattice.of_fg (KK O) ?_, span_eq_top := ?_ }
  · have hN : IsNoetherian O M := isNoetherian_of_fg_of_noetherian M hfg
    refine Submodule.fg_of_fg_map_injective (L.subtype.restrictScalars O) (fun x y h => Subtype.ext h) ?_
    refine (isNoetherian_submodule.1 hN) _ ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  · apply top_unique
    intro x _
    obtain ⟨a, ha, hax⟩ := exists_clear_denominators_alt M (x : W) (by rw [hMQ]; trivial)
    have ha' : algebraMap O (KK O) a ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).2 ha
    have hx : a • x ∈ latticeInter M L := hax
    have hspan := (Submodule.span (KK O) (latticeInter M L : Set L)).smul_mem
      (algebraMap O (KK O) a)⁻¹ (Submodule.subset_span hx)
    rwa [← algebraMap_smul (KK O) a x, inv_smul_smul₀ ha'] at hspan
end lat

theorem lattice_adapted_basis_exists : LatticeAdaptedBasisExists := by
  intro O _ _ _ W _ _ _ _ _ M hfg hMQ L
  have := latticeInter_isLattice M hfg hMQ L
  have := Submodule.IsLattice.finite (KK O) (latticeInter M L)
  have := Submodule.IsLattice.free (KK O) (latticeInter M L)
  let bO := Module.finBasis O (latticeInter M L)
  refine ⟨_, bO.extendOfIsFullLattice (KK O), fun i => ?_, fun x hx i => ?_⟩
  · rw [Module.Basis.extendOfIsFullLattice_apply]
    exact (bO i).2
  · obtain ⟨c, hc⟩ : ∃ c : Fin _ → O, x = ∑ j, (algebraMap O (KK O) (c j)) • (bO.extendOfIsFullLattice (KK O)) j := by
      refine ⟨fun j => bO.repr ⟨x, hx⟩ j, ?_⟩
      have h2 := congrArg (fun z : latticeInter M L => (z : L)) (bO.sum_repr ⟨x, hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at h2
      refine h2.symm.trans (Finset.sum_congr rfl fun j _ => ?_)
      rw [Module.Basis.extendOfIsFullLattice_apply, algebraMap_smul]
    refine ⟨c i, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hc, map_sum]
    simp only [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.GeneratedWeightLemmaOfFormulas
section
namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem generated_weight_lemma_of_formulas (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (hV1 : ValuationsAdditive D) (hDP : DividedPowerFormulaCharZero) (hBin : BinomialFormulaCharZero) :
    ShaLengthVersionTwo D :=
  generated_weight_lemma_char_zero D hV1 (stable_subspace_complete_reducibility D h2) highest_weight_module_bounds polynomial_operators_gl_relations monomials_are_weight_vectors polynomial_locally_finite hDP hBin

end Formalism.MainNotions.G.GLWeightTheory
end

