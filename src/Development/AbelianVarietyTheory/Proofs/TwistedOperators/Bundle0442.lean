module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFinWeil
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0675
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivariantOfWave
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEigenSysOfHeckeLin
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InertPlaceHomLatticeComponentsScaledIntegral
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0249

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfLat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU

namespace GlobalTheory.SplitIdx

variable {D : D7}

def intMat (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (m n : ℕ) :
    AddSubgroup (Matrix (Fin m) (Fin n) (v.adicCompletion F)) where
  carrier := {y | ∀ i j, y i j ∈ v.adicCompletionIntegers F}
  add_mem' hx hy i j := add_mem (hx i j) (hy i j)
  zero_mem' _ _ := zero_mem _
  neg_mem' hx i j := neg_mem (hx i j)

def mulL {K : Type} [CommRing K] {m n : ℕ} (P : Matrix (Fin m) (Fin m) K) :
    Matrix (Fin m) (Fin n) K →+ Matrix (Fin m) (Fin n) K :=
  AddMonoidHom.mk' (fun y => P * y) (Matrix.mul_add P)

def halfLat (S T : HSp D) (e : AE D) : AddSubgroup (WO S T) :=
  (latO S T (frameLat S) (frameLat T) fun _ => True) ⊓ GlobalTheory.PlaceModel.half S T e

def actL (S T : HSp D) (h : GA D T) : WO S T →+ WO S T :=
  AddMonoidHom.mk' (actO S T 1 h) fun x y => by simp only [actO, Matrix.mul_add, Matrix.add_mul]

end GlobalTheory.SplitIdx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfLatticeCharSumDetectsNsmulMultiple
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory.CharSumHalf

open GlobalTheory.Core.Rk.ThetaOf GlobalTheory.DownLift.GenQuot


set_option synthInstance.maxHeartbeats 100000 in
theorem charSum_detects_multiple : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (e : AE D) (k : ℕ) (R : Finset (WO S T)), 0 < k → (∀ u ∈ Λ, IsHalf e u → ∀ y ∈ Λ, IsHalf (cA D e) y → ψ (symplO S T u y) = 1) → (∀ x : WO S T, IsHalf e x → (∀ y ∈ Λ, IsHalf (cA D e) y → ψ (symplO S T x y) = 1) → x ∈ Λ) → (∀ y ∈ R, IsHalf (cA D e) y ∧ k • y ∈ Λ) → (∀ y : WO S T, IsHalf (cA D e) y → k • y ∈ Λ → ∃! r, r ∈ R ∧ y - r ∈ Λ) → ∀ t ∈ Λ, IsHalf e t → ((∃ u ∈ Λ, IsHalf e u ∧ t = k • u) → ∑ r ∈ R, ψ (symplO S T t r) = R.card) ∧ ((¬ ∃ u ∈ Λ, IsHalf e u ∧ t = k • u) → ∑ r ∈ R, ψ (symplO S T t r) = 0) := by
  intro D ψ S T Λ e k R hk hpair hann hR hU t htΛ hte
  classical
  have half_sub : ∀ {c : AE D} {x y : WO S T}, IsHalf c x → IsHalf c y → IsHalf c (x - y) :=
    fun hx hy i j => by simp only [Matrix.sub_apply, mul_sub, hx i j, hy i j]
  have half_add : ∀ {c : AE D} {x y : WO S T}, IsHalf c x → IsHalf c y → IsHalf c (x + y) :=
    fun hx hy i j => by simp only [Matrix.add_apply, mul_add, hx i j, hy i j]
  have half_nsmul : ∀ {c : AE D} {x : WO S T} (n : ℕ), IsHalf c x → IsHalf c (n • x) :=
    fun n hx i j => by rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hx i j]
  have half_smul : ∀ {c : AE D} {x : WO S T} (a : AE D), IsHalf c x → IsHalf c (a • x) :=
    fun a hx i j => by simp only [Matrix.smul_apply, smul_eq_mul]; rw [mul_left_comm, hx i j]
  have pair_add : ∀ x y y' : WO S T,
      ψ (symplO S T x (y + y')) = ψ (symplO S T x y) * ψ (symplO S T x y') := by
    intro x y y'; rw [symplO_add_right, AddChar.map_add_eq_mul]
  constructor
  · rintro ⟨u, huΛ, hue, rfl⟩
    have h1 : ∀ r ∈ R, ψ (symplO S T (k • u) r) = 1 := fun r hr => by
      rw [symplO_nsmul_swap]
      exact hpair u huΛ hue _ (hR r hr).2 (half_nsmul k (hR r hr).1)
    rw [Finset.sum_congr rfl h1]; simp
  · intro hnot
    have hex : ∃ r₀ ∈ R, ψ (symplO S T t r₀) ≠ 1 := by
      by_contra hall
      push_neg at hall
      apply hnot
      set a : AE D := algebraMap D.host.F (AE D) ((k : D.host.F)⁻¹) with ha
      have hka : k • a = 1 := by
        rw [ha, ← map_nsmul, nsmul_eq_mul, mul_inv_cancel₀ (by exact_mod_cast hk.ne'), map_one]
      have hkx : ∀ x : WO S T, k • (a • x) = x := fun x => by
        rw [← smul_assoc, hka, one_smul]
      refine ⟨a • t, ?_, half_smul a hte, (hkx t).symm⟩
      apply hann _ (half_smul a hte)
      intro y hyΛ hyc
      obtain ⟨r, ⟨hrR, hdiff⟩, -⟩ := hU (a • y) (half_smul a hyc) (by rw [hkx]; exact hyΛ)
      have hsw : symplO S T (a • t) y = symplO S T t (a • y) := by
        conv_lhs => rw [← hkx y]
        rw [← symplO_nsmul_swap, hkx]
      rw [hsw, show a • y = (a • y - r) + r by abel, pair_add, hall r hrR, mul_one]
      exact hpair t htΛ hte _ hdiff (half_sub (half_smul a hyc) (hR r hrR).1)
    obtain ⟨r₀, hr₀R, hr₀⟩ := hex
    obtain ⟨rep, rep_spec⟩ : ∃ rep : WO S T → WO S T,
        ∀ y, IsHalf (cA D e) y → k • y ∈ Λ → rep y ∈ R ∧ y - rep y ∈ Λ := by
      refine ⟨fun y => if h : IsHalf (cA D e) y ∧ k • y ∈ Λ then (hU y h.1 h.2).exists.choose else 0, ?_⟩
      intro y h1 h2
      dsimp only
      rw [dite_eq_left (And.intro h1 h2)]
      exact (hU y h1 h2).exists.choose_spec
    have rep_eq : ∀ y r, IsHalf (cA D e) y → k • y ∈ Λ → r ∈ R → y - r ∈ Λ → rep y = r :=
      fun y r h1 h2 hr hd => (hU y h1 h2).unique (rep_spec y h1 h2) ⟨hr, hd⟩
    have hadd : ∀ r ∈ R, ∀ s ∈ R, IsHalf (cA D e) (r + s) ∧ k • (r + s) ∈ Λ := fun r hr s hs =>
      ⟨half_add (hR r hr).1 (hR s hs).1, by rw [nsmul_add]; exact Λ.add_mem (hR r hr).2 (hR s hs).2⟩
    have hsub : ∀ r ∈ R, ∀ s ∈ R, IsHalf (cA D e) (r - s) ∧ k • (r - s) ∈ Λ := fun r hr s hs =>
      ⟨half_sub (hR r hr).1 (hR s hs).1, by rw [nsmul_sub]; exact Λ.sub_mem (hR r hr).2 (hR s hs).2⟩
    have key : ∑ r ∈ R, ψ (symplO S T t r₀) * ψ (symplO S T t r) = ∑ r ∈ R, ψ (symplO S T t r) := by
      apply Finset.sum_nbij' (fun r => rep (r + r₀)) (fun r => rep (r - r₀))
      · intro r hr; exact (rep_spec _ (hadd r hr r₀ hr₀R).1 (hadd r hr r₀ hr₀R).2).1
      · intro r hr; exact (rep_spec _ (hsub r hr r₀ hr₀R).1 (hsub r hr r₀ hr₀R).2).1
      · intro r hr
        obtain ⟨h1, h2⟩ := rep_spec _ (hadd r hr r₀ hr₀R).1 (hadd r hr r₀ hr₀R).2
        have hs := hsub _ h1 r₀ hr₀R
        refine rep_eq _ r hs.1 hs.2 hr ?_
        have : rep (r + r₀) - r₀ - r = -((r + r₀) - rep (r + r₀)) := by abel
        rw [this]; exact Λ.neg_mem h2
      · intro r hr
        obtain ⟨h1, h2⟩ := rep_spec _ (hsub r hr r₀ hr₀R).1 (hsub r hr r₀ hr₀R).2
        have hs := hadd _ h1 r₀ hr₀R
        refine rep_eq _ r hs.1 hs.2 hr ?_
        have : rep (r - r₀) + r₀ - r = -((r - r₀) - rep (r - r₀)) := by abel
        rw [this]; exact Λ.neg_mem h2
      · intro r hr
        obtain ⟨h1, h2⟩ := rep_spec _ (hadd r hr r₀ hr₀R).1 (hadd r hr r₀ hr₀R).2
        have hrep : rep (r + r₀) = (r + r₀) + -((r + r₀) - rep (r + r₀)) := by abel
        have hhalf : IsHalf (cA D e) (-((r + r₀) - rep (r + r₀))) := by
          have := half_sub (hadd r hr r₀ hr₀R).1 (hR _ h1).1
          intro i j; simp only [Matrix.neg_apply, mul_neg, this i j]
        show _ = ψ (symplO S T t (rep (r + r₀)))
        rw [hrep, pair_add, pair_add, hpair t htΛ hte _ (Λ.neg_mem h2) hhalf, mul_one, mul_comm]
    rw [← Finset.mul_sum] at key
    have h0 : (ψ (symplO S T t r₀) - 1) * ∑ r ∈ R, ψ (symplO S T t r) = 0 := by
      rw [sub_mul, key, one_mul, sub_self]
    exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hr₀)

end GlobalTheory.CharSumHalf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx GlobalTheory.Chain NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.StepVac

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum

variable {D : D7}

theorem toEAf_surjective (z : EAf D) : ∃ w : AE D, toEAf D w = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | tmul b α => exact ⟨pairA D.host.F 0 α ⊗ₜ[D.host.F] b, rfl⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, RingHom.map_add _ _ _⟩

theorem map_sum_mem {R R' ι : Type} [CommRing R] [CommRing R'] (f : R →+* R') (A : Subring R') (p : ι → R) (s : Finset ι)
    (h : ∀ i ∈ s, f (p i) ∈ A) : f (∑ i ∈ s, p i) ∈ A := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]; exact sum_mem h

theorem res_ite {R κ : Type} [CommRing R] [CommRing κ] (A : Subring R) (f : A →+* κ) {c z : R} (hc : c ∈ A) (hz : z ∈ A)
    (h1 : f ⟨c, hc⟩ = 1) (p : Prop) [Decidable p] (h : z = if p then c else 0) : f ⟨z, hz⟩ = if p then 1 else 0 := by
  split_ifs at h ⊢
  · subst h; exact h1
  · subst h; exact f.map_zero

theorem res_idemSum {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) :
    ∃ h : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ∀ PP ∈ P, resS D.host.F PP ⟨toEAf D e, h⟩ = 1 := by
  have hee := idemSum_mul_self he
  obtain ⟨⟨es, hes, hs⟩, hc⟩ := he
  choose hi h1 using fun PP hP => GlobalTheory.IdemRes.resS_idem_eq_one D (es PP) PP (hes PP hP)
  have h : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [hs]; exact map_sum_mem (toEAf D) _ es P hi
  refine ⟨h, fun PP hP => ?_⟩
  have hcross := cross_eq_zero (R := AE D) isUnit_natCast (cA D) es P (fun i hi => (hes i hi).1.1) (hs ▸ hc)
  have hm : e * es PP = es PP := by
    rw [hs, Finset.sum_mul, Finset.sum_eq_single PP (fun j hj hji =>
      idemAt_mul (hes j hj) (hes PP hP) (hcross j hj PP hP) (hcross PP hP j hj) hji.symm) (fun h => absurd hP h)]
    exact (hes PP hP).1.1
  have : (⟨toEAf D e, h⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨toEAf D (es PP), hi PP hP⟩ =
      ⟨toEAf D (es PP), hi PP hP⟩ := Subtype.ext ((RingHom.map_mul _ _ _).symm.trans (congrArg _ hm))
  have h2 := congrArg (resS D.host.F PP) this
  rwa [RingHom.map_mul, h1 PP hP, mul_one] at h2

def rectOne (κ : Type) [Zero κ] [One κ] (b a : ℕ) : Matrix (Fin b) (Fin a) κ := fun i j => if i.val = j.val then 1 else 0

theorem lowZero_rectOne (κ : Type) [Zero κ] [One κ] (b a k : ℕ) : LowZero k (rectOne κ b a) :=
  fun i j hi hj => if_neg (by omega)

theorem topL_rectOne (κ : Type) [Zero κ] [One κ] {b a k : ℕ} (ha : k ≤ a) (hb : k ≤ b) : topL k (rectOne κ b a) = 1 := by
  ext i j
  rw [topL, dif_pos ⟨by omega, by omega⟩, rectOne, Matrix.one_apply]
  simp only [Fin.ext_iff]

theorem frame_cancel {A : Type} [CommRing A] {a b : ℕ} (βS : GL (Fin a) A) (βT : GL (Fin b) A) (c : A)
    (I : Matrix (Fin b) (Fin a) A) : (βT⁻¹).val * (c • (βT.val * I * (βS⁻¹).val)) * βS.val = c • I := by
  rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul,
    Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

theorem exists_point (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) {e : AE D}
    {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) : ∃ x : WO S T, IsHalf e x ∧ IsIntM (frMapO S T βS βT x) ∧
      ∀ PP ∈ P, redM PP (frMapO S T βS βT x) = rectOne _ _ _ := by
  obtain ⟨h, h1⟩ := res_idemSum he
  choose s hs using toEAf_surjective (D := D)
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin T.rank) (Fin S.rank) (EAf D), ∀ c : EAf D,
      HMul.hMul (HMul.hMul (βT⁻¹).val (c • M)) βS.val = c • rectOne (EAf D) T.rank S.rank := ⟨_, fun c => frame_cancel βS βT c _⟩
  let x : WO S T := fun i j => e * s (M i j)
  have hx : frMapO S T βS βT x = toEAf D e • rectOne (EAf D) T.rank S.rank := by
    rw [← hM]
    unfold frMapO
    congr 2
    ext i j
    exact (RingHom.map_mul _ _ _).trans (congrArg _ (hs _))
  have hx' : ∀ i j, frMapO S T βS βT x i j = if i.val = j.val then toEAf D e else 0 := fun i j => by
    rw [hx, Matrix.smul_apply, rectOne, smul_eq_mul, mul_ite, mul_one, mul_zero]
  have hi : IsIntM (frMapO S T βS βT x) := fun i j => by
    rw [hx']
    split_ifs
    exacts [h, zero_mem _]
  refine ⟨x, fun i j => by rw [← mul_assoc, idemSum_mul_self he], hi, fun PP hP => ?_⟩
  ext i j
  exact (dif_pos (hi i j)).trans (res_ite _ (resS D.host.F PP) h (hi i j) (h1 PP hP) _ (hx' i j))

theorem omegaG_rectOne {a b : ℕ} (hab : a ≤ b) (L : LevDat D.host.E ℂ a) (χj : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) :
    omegaG L χj (fun PP => rectOne (kP PP) b a) ≠ 0 := by
  unfold omegaG
  rw [dif_pos]
  · refine mul_ne_zero (mul_ne_zero (Units.ne_zero _) ?_) ?_
    · exact Finset.prod_ne_zero_iff.2 fun _ _ => Finset.prod_ne_zero_iff.2 fun _ _ => Units.ne_zero _
    · exact Finset.prod_ne_zero_iff.2 fun _ _ => inv_ne_zero (Units.ne_zero _)
  · refine ⟨fun PP _ => lowZero_rectOne _ _ _ _, fun _ => 1, fun PP => (topL_rectOne _ le_rfl hab).symm,
      fun PP => Subgroup.one_mem _, ?_⟩
    convert L.P.H.one_mem using 1
    funext PP
    exact blockDiagonalExtendByOnePrimeField_one _ _

theorem omegaQ_rectOne {a b r : ℕ} (ha : r ≤ a) (hb : r ≤ b) (Q : Finset (Pl D.host.E))
    (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ) : omegaQ Q r ξ k (fun PP => rectOne (kP PP) b a) ≠ 0 := by
  unfold omegaQ
  rw [dif_pos]
  · exact Finset.prod_ne_zero_iff.2 fun _ _ => zpow_ne_zero _ (Units.ne_zero _)
  · intro PP _
    refine ⟨lowZero_rectOne _ _ _ _, ?_⟩
    rw [topL_rectOne _ ha hb, Matrix.det_one]
    exact isUnit_one

theorem stepVec_vac {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)} {LS : LevDat D.host.E ℂ S.rank}
    {χj ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {Q : Finset (Pl D.host.E)} {f₀ f : WO S T → ℂ}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (hr : S.rank ≤ T.rank)
    (h : IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ f₀ f) :
    IsThetaFunO ψ S T f ∧ f ≠ 0 ∧ ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f := by
  classical
  obtain ⟨hf, e, he, ⟨Tm, hTm⟩, hall⟩ := h
  have hinf := infPart_idemSum he
  obtain ⟨K, hK, hC⟩ := exists_nsmul_of_frMapO
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS)
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT) βS βT
  obtain ⟨h1, h2⟩ := placeModel_span_ne hf.1 hS hT (idemSum_mul_self he) he.2 hinf hTm
    (isSBHalf_of_red e _ (frMapO S T βS βT) (frMapO_add βS βT) (exists_den_frMapO hS.1.fg hT.1.fg βS βT)
      ⟨K, hK, fun t ht => hC t (infPart_of_half hinf ht)⟩ _
      (fun y => omegaG LS χj y * omegaQ Q LS.r ξ 1 y) fun y y' h => by
        rw [omegaG_congr LS χj y y' fun PP hP => h PP (Finset.mem_union_left _ hP),
          omegaQ_congr Q LS.r ξ 1 y y' fun PP hP => h PP (Finset.mem_union_right _ hP)])
  rw [← hall Tm hTm] at h1 h2
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 h1
  refine ⟨?_, h2 ?_ fun hz => ?_, fun τ => ?_⟩
  · rw [← hc]
    exact GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hf.1.1 f₀ hf.2.theta _ c.support Subtype.val c fun i _ => i.2
  · rintro rfl
    obtain ⟨⟨p, hp⟩, h2⟩ := hf.2.norm
    have := h2 p hp
    simp [nrm2] at this
  · obtain ⟨x, a1, a2, a3⟩ := exists_point S T βS βT he
    have := congrFun hz x
    rw [if_pos ⟨a1, a2⟩, omegaG_congr LS χj _ (fun PP => rectOne (kP PP) _ _) fun PP hP =>
      a3 PP (Finset.mem_union_left _ hP), omegaQ_congr Q LS.r ξ 1 _ (fun PP => rectOne (kP PP) _ _) fun PP hP =>
      a3 PP (Finset.mem_union_right _ hP)] at this
    exact mul_ne_zero (omegaG_rectOne hr LS χj) (omegaQ_rectOne LS.hr (LS.hr.trans hr) Q ξ 1) this
  · rw [← hc]
    exact GlobalTheory.FockTranslate.isFockVacAt_sum D ψ θ S T hf.1.1 hf.2.inf f₀ hf.2.theta τ _ (hf.2.fock τ) _ c.support
      Subtype.val c fun i _ => i.2

theorem hasInfExp_mul {χ η : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {a b : ℚ} (hχ : HasInfExp D χ τ a)
    (hη : HasInfExp D η τ b) : HasInfExp D (χ * η) τ (a + b) := by
  obtain ⟨n, hn, h0, h1⟩ := hχ
  obtain ⟨m, hm, -, h2⟩ := hη
  refine ⟨n + m, by push_cast; rw [hn, hm]; ring, h0, fun θ hθ x hx hx' => ?_⟩
  have hu : θ τ (infPart D (x : AE D)) ≠ 0 := ((x.isUnit.map (infPart D)).map (θ τ)).ne_zero
  rw [MonoidHom.mul_apply, Circle.coe_mul, h1 θ hθ x hx hx', h2 θ hθ x hx hx',
    zpow_add₀ (div_ne_zero hu (by exact_mod_cast norm_ne_zero_iff.2 hu))]

theorem hasInfExp_inv {χ : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {a : ℚ} (hχ : HasInfExp D χ τ a) :
    HasInfExp D χ⁻¹ τ (-a) := by
  obtain ⟨n, hn, h0, h1⟩ := hχ
  refine ⟨-n, by push_cast; rw [hn]; ring, h0, fun θ hθ x hx hx' => ?_⟩
  rw [MonoidHom.inv_apply, Circle.coe_inv, h1 θ hθ x hx hx', zpow_neg]

theorem hasInfExp_of_order {θ : InfFam D} (hθ : IsInfFam θ) {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E}
    (h : ChrEq c χ) {n : ℕ} (hn : 0 < n) (ho : χ.OrderDvd n) (τ : D.what₂.Tau) : HasInfExp D c τ 0 := by
  have key := GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite D (c ^ n)
    ⟨h.1.1.pow n, fun x => by rw [MonoidHom.pow_apply, h.1.2 x, one_pow]⟩
    (GlobalTheory.CharOrderFin.char_pow_eq_one_of_orderDvd D c χ h n ho)
  refine ⟨0, by simp, ⟨θ, hθ⟩, fun θ _ x hx _ => ?_⟩
  obtain ⟨y, rfl⟩ := GlobalTheory.IdeleDiv.exists_pow_eq_of_finPart_eq_one D n hn x hx
  rw [zpow_zero, map_pow, show c y ^ n = 1 from key y, Circle.coe_one]

theorem hasInfQ_tau {χ : Formalism.L2.Host.HChar D.host.E} {a : D.R.Psi → ℚ}
    (h : χ.HasInfQ (Formalism.L2.Host.embPsi D.host) a) : χ.HasInfQ (tauE D) fun τ => a (D.eTau τ) := by
  obtain ⟨n, hn, h⟩ := h
  exact ⟨fun τ => n (D.eTau τ), fun τ => hn _, fun k => (h k).trans (D.eTau.prod_comp _).symm⟩

theorem chrStep_exp {T : Type} {L : LevCh D T} {μ0 : T} (hL : L.Is μ0) {θ : InfFam D} (hθ : IsInfFam θ) (t : T)
    (k : Fin D.R.m) (τ : D.what₂.Tau) :
    HasInfExp D (Lift.chrStep (L.mu t) L.eta ((k : ℕ) + 1)).1 τ (expS D k τ) ∧
      HasInfExp D (Lift.chrStep (L.mu t) L.eta ((k : ℕ) + 1)).2 τ (expT D k τ) := by
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  have h1 : HasInfExp D (L.mu t ((k : ℕ) + 1)) τ (-(D.hc τ).e k) := by
    have := hasInfExp_mul (GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hL.mu0 k) (hasInfQ_tau (L.C.isMu0 k).inf) τ)
      (hasInfExp_of_order hθ (hL.xi t) hn ho τ)
    rwa [add_zero, Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at this
  have h2 : HasInfExp D L.eta τ (1 / 2) :=
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hL.eta (hasInfQ_tau (a := fun _ => 1 / 2) ⟨_, fun _ => by norm_num, L.C.isEta.inf⟩) τ
  have h3 := hasInfExp_mul h1 (hasInfExp_inv h2)
  unfold Lift.chrStep expS expT
  by_cases hk : Even (k : ℕ)
  · rw [if_pos hk.add_one, if_pos hk, if_pos hk, sub_zero, sub_eq_add_neg]
    exact ⟨h3, h1⟩
  · rw [if_neg (by rwa [Nat.odd_add_one, Nat.not_odd_iff_even]), if_neg hk, if_neg hk, sub_zero, sub_eq_add_neg]
    exact ⟨h1, h3⟩

theorem rank_Yc {j : ℕ} (hj : j ≤ D.R.m) : (Yc D j).rank = D.R.r + j * D.R.t := by
  rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left hj]; rfl

theorem stepsOK : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → IsInfFam R.θ → R.chain_ωY → R.chain_ωX → R.chain_vY → R.chain_vX → StepsOK R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL hθ hωY hωX hvY hvX
  refine ⟨fun t k hk => ⟨⟨_, _, hωY t k hk, chrStep_exp hL hθ t k⟩, ?_⟩, fun t k hk => ⟨⟨_, _, hωX t, fun τ => ?_⟩, ?_⟩⟩
  · obtain ⟨a, b, c⟩ := stepVec_vac (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βY k k.2)) (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βY _ hk))
      (by rw [rank_Yc k.2.le, rank_Yc hk.le]; nlinarith) (hvY t k hk)
    exact ⟨a, b, c⟩
  · have := chrStep_exp hL hθ t k τ
    rwa [show (k : ℕ) + 1 = D.R.m by have := k.2; omega] at this
  · obtain ⟨a, b, c⟩ := stepVec_vac (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βY (D.R.m - 1) (hk ▸ k.2)))
      (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hL.βX) (by
        rw [rank_Yc (Nat.sub_le _ _), D.sp.X'_rank]
        exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) _) (hvX t)
    exact ⟨a, b, c⟩

end GlobalTheory.Chain.StepVac

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IndexMovedHomLatticeInertPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

theorem GlobalTheory.InertHomIdx.idx_moved_inert : ∀ (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → ∀ c ϖ e, IsUnramInv ϖ c (qV D.host.F v) → IsInertChart D.sp.cm.sig T.gram (frameLat T) h c e → ∀ (d : Fin T.rank → ℤ) (t : GU c T.rank), t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KU c T.rank, ∀ k₂ ∈ KU c T.rank, GlobalTheory.FinWeil.idx (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)) ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).map (GlobalTheory.FinWeilO.rhoF S T (1, embV T v (e.symm (k₁ * t * k₂))))) = qV D.host.E w ^ (S.rank * (∑ i, max (d i) 0).toNat) := by
  intro D S T v w h hw c ϖ e hU he d t ht k₁ hk₁ k₂ hk₂
  obtain ⟨-, ⟨a, ha, -, hea⟩, -⟩ := he
  have hg : (locMat D.sp.cm.sig T.gram h (e.symm (k₁ * t * k₂))).1 =
      a.1 * (k₁ * t * k₂).1.1 * (a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 := by
    have h1 := hea (e.symm (k₁ * t * k₂))
    rw [MulEquiv.apply_symm_apply] at h1
    rw [h1]
    simp only [Units.val_mul, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [_root_.GlobalTheory.InertHomIdx.idx_latF_moved D S T v w h hw]
  obtain ⟨c₀, b, hc₀, hX⟩ := _root_.GlobalTheory.InertHomLattice.mem_map_latF_iff D S T v w h hw a ha
  set M := (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).toAddSubgroup.map (GlobalTheory.InertHomIdx.matW S T w) with hM
  clear_value M
  let τ : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E) →+ Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E) :=
    { toFun := fun X => c₀ • ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 * X * b.1)
      map_zero' := by simp
      map_add' := fun X Y => by simp [Matrix.mul_add, Matrix.add_mul, smul_add] }
  have hτ : Function.Injective τ := by
    intro X Y hXY
    have h1 : c₀ • ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 * X * b.1) = c₀ • ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 * Y * b.1) := hXY
    have h2 := congrArg (fun Z => c₀⁻¹ • (a.1 * Z * (b⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E)).1)) h1
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hc₀, one_smul] at h2
    simpa [← Matrix.mul_assoc, Matrix.mul_assoc _ _ (b⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E)).1] using h2
  have h1 : M.map τ = GlobalTheory.InertHomIdx.intMat (w.adicCompletion D.host.E) T.rank S.rank := by
    ext Y
    constructor
    · rintro ⟨X, hX', rfl⟩
      exact (hX X).1 hX'
    · intro hY
      refine ⟨c₀⁻¹ • (a.1 * Y * (b⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E)).1), (hX _).2 ?_, ?_⟩
      · show c₀ • ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 * (c₀⁻¹ • (a.1 * Y * (b⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E)).1)) * b.1) ∈ _
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hc₀, one_smul, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
        rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
        exact hY
      · show c₀ • ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 * (c₀⁻¹ • (a.1 * Y * (b⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E)).1)) * b.1) = Y
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hc₀, one_smul, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
        rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have h2 : (M.map (GlobalTheory.InertHomIdx.lmul (locMat D.sp.cm.sig T.gram h (e.symm (k₁ * t * k₂))).1)).map τ =
      (GlobalTheory.InertHomIdx.intMat (w.adicCompletion D.host.E) T.rank S.rank).map (GlobalTheory.InertHomIdx.lmul (k₁ * t * k₂).1.1) := by
    have hcomm : τ.comp (GlobalTheory.InertHomIdx.lmul (locMat D.sp.cm.sig T.gram h (e.symm (k₁ * t * k₂))).1) =
        (GlobalTheory.InertHomIdx.lmul (k₁ * t * k₂).1.1).comp τ := by
      refine AddMonoidHom.ext fun X => ?_
      show c₀ • ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 * ((locMat D.sp.cm.sig T.gram h (e.symm (k₁ * t * k₂))).1 * X) * b.1) = (k₁ * t * k₂).1.1 * (c₀ • ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 * X * b.1))
      rw [hg, Matrix.mul_smul]
      congr 1
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1) a.1, Units.inv_mul, Matrix.one_mul]
    rw [← h1, AddSubgroup.map_map, AddSubgroup.map_map, hcomm]
  rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hτ, h2, h1,
    _root_.GlobalTheory.LatIdx.relIndex_intMat_translate ϖ c _ hU T.rank S.rank d t ht k₁ hk₁ k₂ hk₂]
  congr 1
  show (Ideal.absNorm v.asIdeal) ^ 2 = Ideal.absNorm w.asIdeal
  rw [GlobalTheory.LFun.InertChart.absNorm_eq (Algebra.IsQuadraticExtension.finrank_eq_two _ _) hw]

end
end

