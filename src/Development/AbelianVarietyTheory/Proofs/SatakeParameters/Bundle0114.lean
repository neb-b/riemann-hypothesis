module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoordLattice
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyPadicIntRingHomOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0823
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHyperspecialIffGIntOfSuppAtSplit
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitHecke.Stab

open GlobalTheory.AdelicLatMove (mt_mul mt_one gram_mul_inv)

theorem isInt_mulVec {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K] {n : ℕ}
    {M : Matrix (Fin n) (Fin n) K} {x : Fin n → K} (hM : IntM O M) (hx : ∀ i, IsInt O (x i)) (i : Fin n) :
    IsInt O ((M *ᵥ x) i) :=
  isInt_iff.2 (show ∑ k, M i k * x k ∈ _ from
    sum_mem fun k _ => mul_mem (isInt_iff.1 (hM i k)) (isInt_iff.1 (hx k)))

theorem isInt_vecMul {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K] {n : ℕ}
    {M : Matrix (Fin n) (Fin n) K} {x : Fin n → K} (hM : IntM O M) (hx : ∀ i, IsInt O (x i)) (i : Fin n) :
    IsInt O ((x ᵥ* M) i) :=
  isInt_iff.2 (show ∑ k, x k * M k i ∈ _ from
    sum_mem fun k _ => mul_mem (isInt_iff.1 (hx k)) (isInt_iff.1 (hM k i)))

theorem map_mulVec' {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (y : Fin n → R) : (fun i => f ((M *ᵥ y) i)) = M.map f *ᵥ fun i => f (y i) :=
  funext fun i => RingHom.map_mulVec f M y i

theorem dual_move {R K : Type} [CommRing R] [Field K] (c : R →+* R) (π : R →+* K) {n : ℕ}
    (G M N : Matrix (Fin n) (Fin n) R) (β : GL (Fin n) K) (h : G * N = (M.map c)ᵀ * G) (y : Fin n → R) :
    (fun i => π (c ((M *ᵥ y) i))) ᵥ* (G.map π * β.1) =
      ((fun i => π (c (y i))) ᵥ* (G.map π * β.1)) ᵥ* ((β⁻¹).1 * N.map π * β.1) := by
  have hG : G.map π * N.map π = (M.map (π.comp c))ᵀ * G.map π := by
    rw [← Matrix.map_mul, h, Matrix.map_mul]
    rfl
  have hc := map_mulVec' (π.comp c) M y
  simp only [RingHom.comp_apply] at hc
  rw [Matrix.vecMul_vecMul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ β.1,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one, hG, Matrix.mul_assoc,
    ← Matrix.vecMul_mulVec, hc]

theorem split_move {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ} (a b : R)
    (M : Matrix (Fin n) (Fin n) R) (h : ∀ i j, (a + b) * (M - 1) i j = (M - 1) i j) (y : Fin n → R) :
    (M.map f *ᵥ fun i => f (y i)) = ((fun i => f (a * (M *ᵥ y) i)) + fun i => f (b * (M *ᵥ y) i)) +
      (((fun i => f (y i)) - fun i => f (a * y i)) - fun i => f (b * y i)) := by
  have h1 : (a + b) • (M - 1) = M - 1 := Matrix.ext fun i j => h i j
  have h3 : (a + b) • (M *ᵥ y - y) = M *ᵥ y - y := by
    have := congrArg (· *ᵥ y) h1
    simpa only [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec] using this
  rw [← map_mulVec']
  funext i
  have h4 : (a + b) * ((M *ᵥ y) i - y i) = (M *ᵥ y) i - y i := congrFun h3 i
  simp only [Pi.add_apply, Pi.sub_apply, ← map_add (f := _), ← map_sub]
  congr 1
  linear_combination -h4

variable {D : D7}

theorem finPart_surj (z : Af D.host.F ⊗[D.host.F] D.host.E) : ∃ a : AE D, finPart D a = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | tmul α x => exact ⟨pairA D.host.F 0 α ⊗ₜ[D.host.F] x, rfl⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, RingHom.map_add _ _ _⟩

theorem idem_mul_mem (V : HSp D) {a : AE D} (ha : a * a = a) {y : Fin V.rank → AE D}
    (hy : (fun i => finPart D (y i)) ∈ LamHat V) : (fun i => finPart D (a * y i)) ∈ LamHat V := by
  let Λ := GlobalTheory.PlaceModel.latFrame V
  have hs : ∀ b ∈ intAE D, ∀ z ∈ latHat D.host.F D.host.E
      (Λ : Set (Fin V.rank → D.host.E)),
      (fun i => b * z i) ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) := by
    intro b hb z hz
    change z ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) at hz
    change _ ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E))
    induction hb using AddSubgroup.closure_induction with
    | mem b hb =>
      obtain ⟨s, hs, o, rfl⟩ := hb
      induction hz using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨t, ht, x, hx, rfl⟩ := hz
        refine AddSubgroup.subset_closure ⟨s * t, fun v => mul_mem (hs v) (ht v), o • x,
          Λ.smul_mem o hx, ?_⟩
        funext i
        rw [Algebra.TensorProduct.tmul_mul_tmul]
        rfl
      | zero =>
        simp only [Pi.zero_apply, mul_zero]
        exact zero_mem _
      | add u w _ _ hu hw =>
        simp only [Pi.add_apply, mul_add]
        exact add_mem hu hw
      | neg u _ hu =>
        simp only [Pi.neg_apply, mul_neg]
        exact neg_mem hu
    | zero =>
      simp only [zero_mul]
      exact zero_mem _
    | add u w _ _ hu hw =>
      simp only [add_mul]
      exact add_mem hu hw
    | neg u _ hu =>
      simp only [neg_mul]
      exact neg_mem hu
  have h := hs (finPart D a)
    (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha]))
    (fun i => finPart D (y i)) (by rw [GlobalTheory.PlaceModel.coe_latFrame]; exact hy)
  rw [GlobalTheory.PlaceModel.coe_latFrame] at h
  simpa only [RingHom.map_mul] using h

theorem finMat_eq (V : HSp D) (g : GA D V) : finMat D.sp.cm.sig V.gram g = (mt V g).map (finPart D) := rfl

theorem suppAt_inv {e : AE D} {V : HSp D} {g : GA D V} (hg : SuppAt e V g) : SuppAt e V g⁻¹ := by
  have h : (e + cA D e) • (mt V g - 1) = mt V g - 1 := Matrix.ext fun i j => hg i j
  have h1 : mt V g⁻¹ - 1 = -((mt V g - 1) * mt V g⁻¹) := by
    rw [Matrix.sub_mul, ← mt_mul, mul_inv_cancel, mt_one, Matrix.one_mul, neg_sub]
  have h2 : (e + cA D e) • (mt V g⁻¹ - 1) = mt V g⁻¹ - 1 := by
    rw [h1, smul_neg, ← Matrix.smul_mul, h]
  exact fun i j => congrFun (congrFun h2 i) j

theorem mem_GfC {e : AE D} (he : IsSplitIdem D e) {V : HSp D} {g : GA D V} (hg : SuppAt e V g) : g ∈ GfC V := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h : infPart D ((mt V g - 1) i j) = 0 := by
    rw [← hg i j, RingHom.map_mul, RingHom.map_add (f := _), GlobalTheory.SplitScalar.infPart_splitIdem he,
      GlobalTheory.SplitScalar.infPart_splitIdem (GlobalTheory.SplitScalar.isSplitIdem_conj he), add_zero, zero_mul]
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero] at h
  show infPart D (mt V g i j) = (1 : Matrix _ _ _) i j
  rw [h, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · rw [RingHom.map_one]
  · rw [RingHom.map_zero]

variable {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v} {V : HSp D}
  {β : GL (Fin V.rank) (Fv D.host.F v)}

theorem intM_of_stable (hπ : Chart e v π) (hβ : Frame V e π β) {g : GA D V}
    (h : ∀ y ∈ LamHat V, finMat D.sp.cm.sig V.gram g *ᵥ y ∈ LamHat V) : IntM (Ov D v) (rho V π β g).1 := by
  intro i j
  choose y hy using fun k => hπ.1 (β.1 k j)
  have hcol : (fun k => π (y k)) = β.1 *ᵥ Pi.single j 1 := by
    funext k
    rw [hy, Matrix.mulVec_single_one]
    rfl
  have h1 := (hβ y).2 fun k => by
    rw [hcol, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mulVec_single_one]
    exact intM_one k j
  have h2 := h _ h1
  rw [finMat_eq, ← map_mulVec'] at h2
  have h3 : mt V g *ᵥ (fun k => e * y k) = fun k => e * (mt V g *ᵥ y) k := Matrix.mulVec_smul _ e y
  rw [h3] at h2
  have h4 := (hβ _).1 h2 i
  rw [map_mulVec', hcol, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h4
  rw [rho_val]
  exact h4

theorem stable_of_intM (he : IsSplitIdem D e) (hβ : Frame V e π β)
    (hd : ∀ y : Fin V.rank → AE D, (fun i => finPart D (cA D e * y i)) ∈ LamHat V ↔ ∀ j, IsInt (Ov D v)
      (((fun i => π (cA D (y i))) ᵥ* ((V.gram.map fun a => π (incA D a)) * β.1)) j))
    {g : GA D V} (hg : SuppAt e V g) (h1 : IntM (Ov D v) (rho V π β g).1) (h2 : IntM (Ov D v) (rho V π β g⁻¹).1)
    (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) (hz : z ∈ LamHat V) :
    finMat D.sp.cm.sig V.gram g *ᵥ z ∈ LamHat V := by
  choose y hy using fun k => finPart_surj (z k)
  obtain rfl : z = fun k => finPart D (y k) := funext fun k => (hy k).symm
  have he' := GlobalTheory.SplitScalar.isSplitIdem_conj he
  have a1 := idem_mul_mem V he.1 hz
  have a2 := idem_mul_mem V he'.1 hz
  have b1 : (fun i => finPart D (e * (mt V g *ᵥ y) i)) ∈ LamHat V := by
    refine (hβ _).2 fun i => ?_
    have := isInt_mulVec h1 ((hβ y).1 a1) i
    rwa [rho_val, Matrix.mulVec_mulVec, Matrix.mul_assoc _ β.1, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.mul_one, ← Matrix.mulVec_mulVec, ← map_mulVec'] at this
  have b2 : (fun i => finPart D (cA D e * (mt V g *ᵥ y) i)) ∈ LamHat V := by
    refine (hd _).2 fun i => ?_
    have := isInt_vecMul h2 ((hd y).1 a2) i
    rw [rho_val] at this
    exact (congrFun (dual_move (cA D) π (V.gram.map (incA D)) _ _ β (gram_mul_inv V g) y) i).symm ▸ this
  rw [finMat_eq, split_move (finPart D) e (cA D e) (mt V g) hg y]
  exact add_mem (add_mem b1 b2) (sub_mem (sub_mem hz a1) a2)

theorem finMat_mul_inv (g : GA D V) (y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    finMat D.sp.cm.sig V.gram g *ᵥ (finMat D.sp.cm.sig V.gram g⁻¹ *ᵥ y) = y := by
  rw [finMat_eq, finMat_eq, Matrix.mulVec_mulVec, ← Matrix.map_mul, ← mt_mul, mul_inv_cancel, mt_one,
    Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _), Matrix.one_mulVec]

theorem mem_KsphC_iff_gInt : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ (V : HSp D) (β : GL (Fin V.rank) (Fv D.host.F v)), Frame V e π β → ∀ g : GA D V, SuppAt e V g → (g ∈ KsphC V ∅ ↔ GInt (Ov D v) (rho V π β g)) := by
  intro D e v π he hπ V β hβ g hg
  have hd := _root_.GlobalTheory.SplitDualLat.conj_mem_lamHat_iff e v π he hπ V β hβ
  unfold GInt
  rw [← map_inv]
  constructor
  · rintro ⟨-, h, -⟩
    exact ⟨intM_of_stable hπ hβ fun y hy => (h y).1 hy,
      intM_of_stable hπ hβ fun y hy => (h _).2 (by rw [finMat_mul_inv]; exact hy)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨mem_GfC he hg, fun y => ⟨stable_of_intM he hβ hd hg h1 h2 y, fun hy => ?_⟩,
      fun w hw => absurd hw (Finset.notMem_empty w)⟩
    have h3 := stable_of_intM he hβ hd (suppAt_inv hg) h2 (by rw [inv_inv]; exact h1) _ hy
    have h4 := finMat_mul_inv g⁻¹ y
    rw [inv_inv] at h4
    rwa [h4] at h3

end GlobalTheory.SplitHecke.Stab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemRangeWittAlgClosureOfBoundedRingHom
section
open Filter Topology

noncomputable section

namespace GlobalTheory.TeichImage

variable {p : ℕ} [hp : Fact p.Prime]

theorem coprime_pow_sub_one {n : ℕ} (hn : 0 < n) : Nat.Coprime (p ^ n - 1) p := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out]
  intro h
  have h1 : p ∣ p ^ n := dvd_pow_self p hn.ne'
  have h2 : 1 ≤ p ^ n := Nat.one_le_pow _ _ hp.out.pos
  have h3 : p ∣ p ^ n - (p ^ n - 1) := Nat.dvd_sub h1 h
  rw [show p ^ n - (p ^ n - 1) = 1 by omega] at h3
  exact hp.out.one_lt.ne' (Nat.dvd_one.1 h3)

theorem mem_range_of_pow_eq {n : ℕ} (hn : 0 < n) {τ : ℂ_[p]} (hτ : τ ^ (p ^ n) = τ) :
    τ ∈ Set.range (Formalism.L2.G.Pend.wToC p) := by
  by_cases h0 : τ = 0
  · exact ⟨0, by rw [h0, map_zero]⟩
  have hq : 2 ≤ p ^ n := le_trans hp.out.two_le (Nat.le_self_pow hn.ne' p)
  have h1 : τ ^ (p ^ n - 1) = 1 := by
    have : τ ^ (p ^ n - 1) * τ = 1 * τ := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega), hτ, one_mul]
    exact mul_right_cancel₀ h0 this
  exact Formalism.L2.G.Pend.root_mem_range p (by omega) (coprime_pow_sub_one hn) h1

theorem exists_lim {n : ℕ} (hn : 0 < n) (a : ℂ_[p])
    (ha : ∀ M : ℕ, ‖a ^ ((p ^ n) ^ (M + 1)) - a ^ ((p ^ n) ^ M)‖ ≤ ((p : ℝ)⁻¹) ^ (M + 1)) :
    ∃ τ ∈ Set.range (Formalism.L2.G.Pend.wToC p), ∀ N : ℕ, ‖a ^ ((p ^ n) ^ N) - τ‖ ≤ ((p : ℝ)⁻¹) ^ (N + 1) := by
  set r : ℝ := (p : ℝ)⁻¹ with hr
  have hr0 : 0 ≤ r := Formalism.L2.G.Pend.r_nonneg p
  have hr1 : r < 1 := Formalism.L2.G.Pend.r_lt_one p
  set u : ℕ → ℂ_[p] := fun M => a ^ ((p ^ n) ^ M) with hu
  have hcau : CauchySeq u := by
    refine cauchySeq_of_le_geometric r r hr1 fun m => ?_
    rw [dist_eq_norm, norm_sub_rev, ← pow_succ']
    exact ha m
  obtain ⟨τ, hτ⟩ := cauchySeq_tendsto_of_complete hcau
  have hball : ∀ N M : ℕ, N ≤ M → ‖u M - u N‖ ≤ r ^ (N + 1) := by
    intro N M hNM
    induction M, hNM using Nat.le_induction with
    | base => rw [sub_self, norm_zero]; exact pow_nonneg hr0 _
    | succ M hNM ih =>
      have : u (M + 1) - u N = (u (M + 1) - u M) + (u M - u N) := by ring
      rw [this]
      refine Formalism.L2.G.Pend.nadd p ((ha M).trans ?_) ih
      exact pow_le_pow_of_le_one hr0 hr1.le (by omega)
  have hlim : ∀ N : ℕ, ‖u N - τ‖ ≤ r ^ (N + 1) := by
    intro N
    have hmem : τ ∈ Metric.closedBall (u N) (r ^ (N + 1)) :=
      Metric.isClosed_closedBall.mem_of_tendsto hτ
        (eventually_atTop.2 ⟨N, fun M hM => by rw [Metric.mem_closedBall, dist_eq_norm]; exact hball N M hM⟩)
    rw [Metric.mem_closedBall, dist_eq_norm] at hmem
    rw [norm_sub_rev]; exact hmem
  have hsucc : ∀ M, u (M + 1) = u M ^ (p ^ n) := by
    intro M
    show a ^ ((p ^ n) ^ (M + 1)) = (a ^ ((p ^ n) ^ M)) ^ (p ^ n)
    rw [← pow_mul a ((p ^ n) ^ M) (p ^ n), ← pow_succ]
  have h1 : Tendsto (fun M => u (M + 1)) atTop (𝓝 τ) := hτ.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun M => u (M + 1)) atTop (𝓝 (τ ^ (p ^ n))) := by
    simp only [hsucc]; exact hτ.pow _
  have hfix : τ ^ (p ^ n) = τ := tendsto_nhds_unique h2 h1
  exact ⟨τ, mem_range_of_pow_eq hn hfix, hlim⟩

section Ring

variable {W : Type} [CommRing W] {n : ℕ}

theorem dvd_pow_iter (hW : ∀ x : W, (p : W) ∣ x ^ (p ^ n) - x) (N : ℕ) (x : W) :
    (p : W) ∣ x ^ ((p ^ n) ^ N) - x := by
  induction N with
  | zero => rw [pow_zero, pow_one, sub_self]; exact dvd_zero _
  | succ N ih =>
    have e : x ^ ((p ^ n) ^ (N + 1)) = (x ^ ((p ^ n) ^ N)) ^ (p ^ n) := by
      rw [← pow_mul x ((p ^ n) ^ N) (p ^ n), ← pow_succ]
    rw [e, show (x ^ ((p ^ n) ^ N)) ^ (p ^ n) - x =
      ((x ^ ((p ^ n) ^ N)) ^ (p ^ n) - x ^ ((p ^ n) ^ N)) + (x ^ ((p ^ n) ^ N) - x) by ring]
    exact dvd_add (hW _) ih

theorem dvd_pow_iter_succ (hn : 0 < n) (hW : ∀ x : W, (p : W) ∣ x ^ (p ^ n) - x) (M : ℕ) (x : W) :
    (p : W) ^ (M + 1) ∣ x ^ ((p ^ n) ^ (M + 1)) - x ^ ((p ^ n) ^ M) := by
  have h := dvd_sub_pow_of_dvd_sub (hW x) (n * M)
  have e1 : (x ^ (p ^ n)) ^ (p ^ (n * M)) = x ^ ((p ^ n) ^ (M + 1)) := by
    rw [← pow_mul, pow_succ, ← pow_mul, mul_comm]
  have e2 : x ^ (p ^ (n * M)) = x ^ ((p ^ n) ^ M) := by rw [← pow_mul]
  rw [e1, e2] at h
  exact (pow_dvd_pow _ (by have := Nat.le_mul_of_pos_left M hn; omega)).trans h

theorem norm_map_pow_mul (φ : W →+* ℂ_[p]) (hφ : ∀ x, ‖φ x‖ ≤ 1) (k : ℕ) (c : W) :
    ‖φ ((p : W) ^ k * c)‖ ≤ ((p : ℝ)⁻¹) ^ k := by
  rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow, Formalism.L2.G.Pend.norm_p_C]
  exact mul_le_of_le_one_right (pow_nonneg (Formalism.L2.G.Pend.r_nonneg p) k) (hφ c)

end Ring

end GlobalTheory.TeichImage

namespace GlobalTheory

theorem mem_range_wToC_of_pow_congr : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (W : Type) [CommRing W], 0 < n →
    (∀ x : W, (p : W) ∣ x ^ (p ^ n) - x) → IsAdicComplete (Ideal.span {(p : W)}) W →
    ∀ φ : W →+* ℂ_[p], (∀ x, ‖φ x‖ ≤ 1) → ∀ x, φ x ∈ Set.range (Formalism.L2.G.Pend.wToC p) := by
  intro p _ n W _ hn hW _ φ hφ x
  have hr0 : 0 ≤ ((p : ℝ)⁻¹) := Formalism.L2.G.Pend.r_nonneg p
  have key : ∀ k : ℕ, ∀ x : W, ∃ w, ‖φ x - Formalism.L2.G.Pend.wToC p w‖ ≤ ((p : ℝ)⁻¹) ^ k := by
    intro k
    induction k with
    | zero => intro x; exact ⟨0, by rw [map_zero, sub_zero, pow_zero]; exact hφ x⟩
    | succ k ih =>
      intro x
      obtain ⟨τ, ⟨wτ, hwτ⟩, hτ⟩ := TeichImage.exists_lim hn (φ x) (fun M => by
        obtain ⟨c, hc⟩ := TeichImage.dvd_pow_iter_succ hn hW M x
        rw [← map_pow, ← map_pow, ← map_sub, hc]
        exact TeichImage.norm_map_pow_mul φ hφ (M + 1) c)
      obtain ⟨c, hc⟩ := TeichImage.dvd_pow_iter hW k x
      obtain ⟨w₁, hw₁⟩ := ih (-c)
      refine ⟨wτ + (p : Formalism.L2.G.Pend.WW p) * w₁, ?_⟩
      have hx : x = x ^ ((p ^ n) ^ k) + (p : W) * (-c) := by linear_combination -hc
      have e : φ x - Formalism.L2.G.Pend.wToC p (wτ + (p : Formalism.L2.G.Pend.WW p) * w₁) =
          (φ x ^ ((p ^ n) ^ k) - τ) + (p : ℂ_[p]) * (φ (-c) - Formalism.L2.G.Pend.wToC p w₁) := by
        conv_lhs => rw [hx]
        rw [map_add (f := _), map_add (f := _), map_mul, map_mul, map_pow, map_natCast, map_natCast, hwτ]
        ring
      rw [e]
      refine Formalism.L2.G.Pend.nadd p ((hτ k)) ?_
      rw [norm_mul, Formalism.L2.G.Pend.norm_p_C, pow_succ']
      exact mul_le_mul_of_nonneg_left hw₁ hr0
  apply Formalism.L2.G.Pend.mem_range_of_closure p
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (Formalism.L2.G.Pend.r_lt_one p)
  obtain ⟨w, hw⟩ := key N x
  exact ⟨_, ⟨w, rfl⟩, by rw [dist_eq_norm]; exact lt_of_le_of_lt hw hN⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NonemptyCoefficientFieldEmbeddingPadicComplex
section
open IsLocalRing

namespace GlobalTheory

theorem nonempty_cEmb_of_pos_nV : ∀ (p : ℕ) [Fact p.Prime] (G : Formalism.MainNotions.G.GAtP p), 0 < G.P.nV →
    Nonempty (Formalism.L2.G.Pend.CEmb G) := by
  intro p _ G hV
  let v : Fin G.P.nV := ⟨0, hV⟩
  have S := G.P.setting v
  haveI := S.frac_alt
  haveI := S.frac_O
  haveI : IsAdicComplete (maximalIdeal G.O) G.O := S.complete_O

  haveI hW0 : CharZero (G.P.W v) := by
    obtain ⟨l, hl⟩ := CharP.exists (G.P.W v)
    rcases CharP.char_is_prime_or_zero (G.P.W v) l with hlp | hl0
    · exfalso
      by_cases hlpe : l = p
      · subst hlpe
        exact S.p_unif.ne_zero (CharP.cast_eq_zero _ l)
      · have hcop : Nat.Coprime p l := (Nat.coprime_primes (Fact.out) hlp).2 (Ne.symm hlpe)
        have h := Nat.gcd_eq_gcd_ab p l
        rw [hcop] at h
        have h' := congrArg (fun z : ℤ => (z : G.P.W v)) h
        simp only [Nat.cast_one, Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast,
          CharP.cast_eq_zero, zero_mul, add_zero] at h'
        exact S.p_unif.not_isUnit (IsUnit.of_mul_eq_one _ h'.symm)
    · subst hl0
      exact CharP.charP_to_charZero _
  haveI : CharZero (G.P.Qq v) :=
    (RingHom.charZero_iff (IsFractionRing.injective (G.P.W v) (G.P.Qq v))).1 hW0
  haveI : CharZero G.Kf := (RingHom.charZero_iff (G.P.ι v).injective).1 inferInstance

  letI : Algebra (G.P.W v) G.O := (G.P.j v).toAlgebra
  haveI : Module.Finite (G.P.W v) G.O := S.finite
  have hcomap : (maximalIdeal G.O).comap (algebraMap (G.P.W v) G.O) = Ideal.span {(p : G.P.W v)} := by
    have hmax : ((maximalIdeal G.O).comap (algebraMap (G.P.W v) G.O)).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := G.P.W v) _
    rw [IsLocalRing.eq_maximalIdeal hmax, S.p_unif.maximalIdeal_eq]
  have hpO : (p : G.O) ∈ maximalIdeal G.O := by
    have : (p : G.P.W v) ∈ (maximalIdeal G.O).comap (algebraMap (G.P.W v) G.O) :=
      hcomap ▸ Ideal.subset_span rfl
    simpa using this

  haveI : Finite (ResidueField (G.P.W v)) := by
    have h := S.res_card
    rw [← S.p_unif.maximalIdeal_eq] at h
    exact Nat.finite_of_card_ne_zero (h ▸ pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  haveI : Finite (ResidueField G.O) := by
    haveI : Module.Finite (G.P.W v) (ResidueField G.O) := inferInstance
    haveI : Algebra.IsIntegral (G.P.W v) (ResidueField G.O) := inferInstance
    exact Module.finite_of_finite (ResidueField (G.P.W v))

  obtain ⟨p', hp', K₀, e, e₀, hfd, he⟩ := exists_ringEquiv_integralClosure_padicInt G.O G.Kf
  have hpp : p' = p := by
    have h1 : e₀ (p : G.O) ∈ maximalIdeal (integralClosure ℤ_[p'] K₀) := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact (mem_maximalIdeal _).1 hpO (by simpa using hu.map e₀.symm)
    rw [mem_maximalIdeal_integralClosure_iff, map_natCast] at h1
    have h2 : (((p : integralClosure ℤ_[p'] K₀) : K₀) : PadicAlgCl p') =
        algebraMap ℚ_[p'] (PadicAlgCl p') p := by simp
    rw [h2, PadicAlgCl.norm_extends, Padic.norm_natCast_lt_one_iff] at h1
    exact (Nat.prime_dvd_prime_iff_eq hp'.out Fact.out).1 h1
  subst hpp

  refine ⟨⟨(algebraMap (PadicAlgCl p') ℂ_[p']).comp (K₀.val.toRingHom.comp e.toRingHom), fun x => ?_⟩⟩
  have hx : ((e (algebraMap G.O G.Kf x) : K₀) : PadicAlgCl p') = (((e₀ x : integralClosure ℤ_[p'] K₀) : K₀) : PadicAlgCl p') := by
    rw [he x]
  simp only [RingHom.comp_apply]
  show ‖algebraMap (PadicAlgCl p') ℂ_[p'] ((e (algebraMap G.O G.Kf x) : K₀) : PadicAlgCl p')‖ ≤ 1
  rw [hx, ← PadicComplex.coe_eq, PadicComplex.norm_extends]
  exact (mem_integralClosure_padicInt_iff K₀ _).1 (e₀ x).2
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PowerOfAbelianSchemeProjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

namespace GlobalTheory.KS

theorem isProjOver_pow : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R),
    IsProjOver s → ∀ (A : Over X) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB →
    Out.RelAmple A L → ∀ k : ℕ, IsProjOver ((GlobalTheory.KS.pow A k).hom ≫ s) := by
  intro R _ _ X s hs A _ _ hA L hL hamp k
  obtain ⟨hsp, H, hH⟩ := (GlobalTheory.isProjOver_iff_isProper_and_exists_isAmpleLB s).1 hs
  have p := Out.powIsPowGrp A k
  have hrel : Out.RelAmple (Out.powObj A k) (Out.boxLB L p.pr) :=
    GlobalTheory.relAmple_boxLB X (Out.powObj A k) A k p L hL hamp
  obtain ⟨-, N, hN⟩ := GlobalTheory.RelAmpleQProj.isProper_and_exists_isAmpleLB (Out.powObj A k)
    (LB.isLB_linComb hL _ _) hrel hH
  let e : GlobalTheory.KS.pow A k ≅ Out.powObj A k :=
    IsLimit.conePointUniqueUpToIso (limit.isLimit _) (Out.powIsLimit A k)
  have hpA : IsProper A.hom := hA.proper
  have : IsProper (GlobalTheory.KS.pow A k).hom := GlobalTheory.KS.Leray.isProper_pow_hom A hpA k
  have : IsIso e.hom.left := ((Over.forget X).mapIso e).isIso_hom
  have := hsp
  exact (hN.pull_of_isAffineHom e.hom.left).isProjOver _

end GlobalTheory.KS
end

