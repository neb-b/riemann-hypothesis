module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.DualLattices.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import ReciprocityTheory.DualLattices.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermEvRegaugedSecondLawFamily
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0005
public import ReciprocityTheory.DualLattices.UnramifiedCokernelLowerBoundOf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.JacobianMulTangentChartMatrixIntertwines
section
set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem nv_lin {R S : Type} [CommRing R] [CommRing S] (s : R →+* S) {n d : ℕ} (f : PS R n d)
    (hf : MvPowerSeries.constantCoeff f = 0) (a : Fin n → Fin d → S)
    (h : ∀ i j i' j', a i j * a i' j' = 0) :
    nv s f a = ∑ i, ∑ j, s (MvPowerSeries.coeff (Finsupp.single (i, j) 1) f) * a i j := by
  have ha : ∀ i j, IsNilpotent (a i j) := fun i j => ⟨2, by rw [pow_two, h]⟩
  rw [(nv_calculus R S s n d a ha).2.2.2.2.2 h f, hf, map_zero, zero_add, Fintype.sum_prod_type]

private theorem chart_add {R₀ : Type} [CommRing R₀] {B : BX R₀} {O : LAlg R₀} {g : ℕ} {F : FGLaw (O : Type) g}
    {Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R} (hY : BXChart B O F.F Y)
    (R : LAlg R₀) (s : LHom O R) (e : (R : Type)) (he : e * e = 0) (v w : Fin g → (R : Type)) :
    Y R s (fun k => v k * e) + Y R s (fun k => w k * e) = Y R s (fun k => (v k + w k) * e) := by
  have hn : ∀ x : (R : Type), IsNilpotent (x * e) := fun x =>
    ⟨2, by rw [mul_pow, pow_two e, he, mul_zero]⟩
  have hl : ∀ v w : Fin g → (R : Type), Y R s (fun k => v k * e) + Y R s (fun k => w k * e) =
      Y R s (fun k => (∑ j, s.1 (MvPowerSeries.coeff (Finsupp.single (0, j) 1) (F.F k)) * v j +
        ∑ j, s.1 (MvPowerSeries.coeff (Finsupp.single (1, j) 1) (F.F k)) * w j) * e) := by
    intro v w
    rw [hY.law R s _ _ (fun _ => hn _) (fun _ => hn _)]
    congr 1
    funext k
    rw [nv_lin _ _ (F.const k)]
    · simp [Fin.sum_univ_two, add_mul, Finset.sum_mul, _root_.mul_assoc]
    · have hx : ∀ x y : (R : Type), x * e * (y * e) = 0 := fun x y => by
        rw [_root_.mul_mul_mul_comm, he, mul_zero]
      intro i j i' j'
      fin_cases i <;> fin_cases i' <;> exact hx _ _
  have h0 : Y R s (fun k => (0 : Fin g → (R : Type)) k * e) = 0 := by
    simp only [Pi.zero_apply, zero_mul]
    exact hY.zero R s
  have h1 := hl v 0
  have h2 := hl 0 w
  rw [h0, add_zero] at h1
  rw [h0, zero_add] at h2
  have h1' := hY.inj R s _ _ (fun _ => hn _) (fun _ => hn _) h1
  have h2' := hY.inj R s _ _ (fun _ => hn _) (fun _ => hn _) h2
  rw [hl]
  congr 1
  funext k
  have e1 := congrFun h1' k
  have e2 := congrFun h2' k
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, zero_add] at e1 e2
  rw [add_mul, add_mul, e1, e2]

private theorem chart_sum {R₀ : Type} [CommRing R₀] {B : BX R₀} {O : LAlg R₀} {g : ℕ} {F : FGLaw (O : Type) g}
    {Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R} (hY : BXChart B O F.F Y)
    (R : LAlg R₀) (s : LHom O R) (e : (R : Type)) (he : e * e = 0) {κ : Type} (t : Finset κ)
    (v : κ → Fin g → (R : Type)) :
    ∑ i ∈ t, Y R s (fun k => v i k * e) = Y R s (fun k => (∑ i ∈ t, v i k) * e) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, zero_mul]
    exact (hY.zero R s).symm
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, ih, chart_add hY R s e he]
    simp only [Finset.sum_insert ha]

theorem lin_mul_tanMat : ∀ (R₀ : Type) [CommRing R₀] (B : BX R₀) (O : LAlg R₀) (g : ℕ) (F : FGLaw (O : Type) g) (Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R), BXChart B O F.F Y → ∀ (gb : Module.Basis (Fin g) R₀ B.gg) (S : Matrix (Fin g) (Fin g) (O : Type)), TanMat B O Y gb S → ∀ (A : OEnd B O) (α : Fin g → PS (O : Type) 1 g) (ρ : Matrix (Fin g) (Fin g) (O : Type)), (∀ j, MvPowerSeries.constantCoeff (α j) = 0) → (∀ (R : LAlg R₀) (s : LHom O R) (a : Fin g → (R : Type)), (∀ i, IsNilpotent (a i)) → A.f s (Y R s a) = Y R s (fun j => nv s.1.toRingHom (α j) ![a])) → (∀ {R S : LAlg R₀} (s : LHom O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g) (i : π.ker) (m : Fin g → π.ker), (∀ k, (m k : (R : Type)) = s.1 (ρ k l) * i) → A.f s (B.tg π hπ (gb l ⊗ₜ[R₀] i)) = B.tg π hπ (∑ k, gb k ⊗ₜ[R₀] m k)) → lin α * S = S * ρ := by
  intro R₀ _ B O g F Y hY gb S hS A α ρ hα hA hρ
  let Dp : DualPair O := DualNum.dualPair O
  have hπ : Dp.π.SqZero := Dp.π.sqZero_of_span Dp.η (fun r => ⟨Dp.σ.1 r, Dp.sect r⟩) Dp.ker_eq Dp.η_sq
  have hn : ∀ x : (Dp.D : Type), IsNilpotent (x * Dp.η) := fun x =>
    ⟨2, by rw [mul_pow, pow_two Dp.η, Dp.η_sq, mul_zero]⟩
  have hη : Dp.η ∈ Dp.π.ker := by simpa using Dp.ση_mem 1
  ext j l
  have h := hρ Dp.σ Dp.π hπ l ⟨Dp.η, hη⟩ (fun k => ⟨Dp.σ.1 (ρ k l) * Dp.η, Dp.ση_mem _⟩) (fun _ => rfl)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, hS _ _ Dp.σ, hA _ _ _ (fun _ => hn _)] at h
  simp only [hS _ _ Dp.σ, ← _root_.mul_assoc] at h
  rw [chart_sum hY _ _ _ Dp.η_sq] at h
  have hv : (fun j => nv Dp.σ.1.toRingHom (α j) ![fun k => Dp.σ.1 (S k l) * Dp.η]) =
      fun j => Dp.σ.1 ((lin α * S) j l) * Dp.η := by
    funext j
    rw [nv_lin _ _ (hα j)]
    · simp [Matrix.mul_apply, lin, Finset.sum_mul, _root_.mul_assoc]
    · intro i j i' j'
      fin_cases i; fin_cases i'
      show Dp.σ.1 _ * Dp.η * (Dp.σ.1 _ * Dp.η) = 0
      rw [_root_.mul_mul_mul_comm, Dp.η_sq, mul_zero]
  rw [hv] at h
  have h2 := congrFun (hY.inj _ _ _ _ (fun _ => hn _) (fun _ => hn _) h) j
  rw [← sub_eq_zero]
  apply Dp.free
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, sub_mul, h2, Matrix.mul_apply, map_sum]
  simp only [map_mul, sub_self]

end GlobalTheory.ChF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LinMulFAndCompAndSpanLeAndMemPow
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChF

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory.Regauge

variable {R : Type} [CommRing R] {d : ℕ}

private theorem gp_mulF (F : FGLaw R d) (N : ℕ) : GP (mulF F.F N) :=
  FormalMul.constantCoeff_mulF F.F F.const N

private theorem nsum_add (F : FGLaw R d) (a b : ℕ) :
    mulF F.F (a + b) = addOf F.F (mulF F.F a) (mulF F.F b) := by
  induction b with
  | zero => exact (addOf_zero F (gp_mulF F a)).symm
  | succ b ih =>
    change addOf F.F (mulF F.F (a + b)) (pt R d 0) = addOf F.F _ (addOf F.F (mulF F.F b) (pt R d 0))
    rw [ih, addOf_assoc F (gp_mulF F a) (gp_mulF F b) (gp_pt 0)]

private theorem nsum_mul (F : FGLaw R d) (N M : ℕ) :
    mulF F.F (N * M) = comp1 (mulF F.F N) (mulF F.F M) := by
  have hV := single_point_zero_constant (gp_mulF F M)
  induction N with
  | zero =>
    rw [Nat.zero_mul]
    exact (evP_zero _ hV).symm
  | succ N ih =>
    rw [Nat.succ_mul, nsum_add, ih]
    change _ = evP ![mulF F.F M] (addOf F.F (mulF F.F N) (pt R d 0))
    rw [evP_addOf _ hV _ _ _ (gp_mulF F N) (gp_pt 0), evP_pt _ hV]
    rfl

private theorem ev_mem_pow {m n : ℕ} {a : Fin m → Pt R n d} (ha : ∀ j, GP (a j))
    {K : Ideal (PS R n d)} (hK : ∀ j i, a j i ∈ K) {N : ℕ} {f : PS R m d}
    (hf : f ∈ germIdeal (Fin m × Fin d) R ^ N) : ev a f ∈ K ^ N := by
  have h : (germIdeal (Fin m × Fin d) R ^ N).map (substAlgHom (R := R) (gt_hasSubst a ha)) ≤ K ^ N := by
    rw [Ideal.map_pow, germIdeal_eq_span]
    refine Ideal.pow_right_mono ?_ N
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
    rw [substAlgHom_X]
    exact hK _ _
  have := h (Ideal.mem_map_of_mem _ hf)
  rwa [substAlgHom_apply] at this

private theorem mem_sq_iff {σ : Type} [Finite σ] {g : MvPowerSeries σ R} :
    g ∈ germIdeal σ R ^ 2 ↔ constantCoeff g = 0 ∧ ∀ s, coeff (Finsupp.single s 1) g = 0 := by
  rw [mem_germIdeal_pow_iff]
  constructor
  · intro h
    exact ⟨by simpa using h 0 (by simp), fun s => h _ (by simp)⟩
  · rintro ⟨h0, h1⟩ e he
    rcases (by omega : e.degree = 0 ∨ e.degree = 1) with h | h
    · obtain rfl := (Finsupp.degree_eq_zero_iff e).1 h
      simpa using h0
    · obtain ⟨s, rfl⟩ : e ∈ Set.range (fun s : σ => Finsupp.single s 1) := by
        rw [Finsupp.range_single_one]; exact h
      exact h1 s

private theorem coeff_single_X' {σ : Type} [DecidableEq σ] (s t : σ) :
    coeff (Finsupp.single s 1) (X t : MvPowerSeries σ R) = if s = t then 1 else 0 := by
  rw [coeff_X]
  simp [Finsupp.single_left_inj]

private theorem sub_lin_mem {σ : Type} [Fintype σ] {g : MvPowerSeries σ R} (hg : constantCoeff g = 0) :
    g - ∑ s, coeff (Finsupp.single s 1) g • X s ∈ germIdeal σ R ^ 2 := by
  classical
  refine mem_sq_iff.2 ⟨by simp [hg], fun s => ?_⟩
  simp [coeff_single_X']

private theorem ev_sub_lin_mem {m n : ℕ} {a : Fin m → Pt R n d} (ha : ∀ j, GP (a j))
    {f : PS R m d} (hf : constantCoeff f = 0) :
    ev a f - ∑ s : Fin m × Fin d, coeff (Finsupp.single s 1) f • a s.1 s.2 ∈
      germIdeal (Fin n × Fin d) R ^ 2 := by
  have h := ev_mem_pow ha (K := germIdeal (Fin n × Fin d) R) (fun j i => ha j i) (sub_lin_mem hf)
  unfold ev at h ⊢
  rw [← substAlgHom_apply (gt_hasSubst a ha)] at h ⊢
  set_option synthInstance.maxHeartbeats 100000 in
    simpa only [map_sub, map_sum, map_smul, substAlgHom_X] using h

private theorem coeff_law (F : FGLaw R d) (i : Fin d) (l : Fin 2) (j : Fin d) :
    coeff (Finsupp.single (l, j) 1) (F.F i) = if j = i then 1 else 0 := by
  have hp : GP (pt R (n := 1) d 0) := gp_pt 0
  fin_cases l
  · have h := (mem_sq_iff.1 (ev_sub_lin_mem (pair_points_zero_constant hp gp_zero₂) (F.const i))).2 (0, j)
    have e : ev ![pt R (n := 1) d 0, 0] (F.F i) = X (0, i) := congrFun (addOf_zero F hp) i
    rw [e] at h
    simp [Fintype.sum_prod_type, pt, coeff_single_X', sub_eq_zero] at h
    simpa using h.symm
  · have h := (mem_sq_iff.1 (ev_sub_lin_mem (pair_points_zero_constant gp_zero₂ hp) (F.const i))).2 (0, j)
    rw [F.unit i] at h
    simp [Fintype.sum_prod_type, pt, coeff_single_X', sub_eq_zero] at h
    simpa using h.symm

private theorem nsum_sub_mem (F : FGLaw R d) (N : ℕ) (i : Fin d) :
    mulF F.F N i - (N : R) • X (0, i) ∈ germIdeal (Fin 1 × Fin d) R ^ 2 := by
  induction N with
  | zero => simp [mulF]
  | succ N ih =>
    have h := ev_sub_lin_mem (pair_points_zero_constant (gp_mulF F N) (gp_pt 0)) (F.const i)
    simp only [Fintype.sum_prod_type, coeff_law, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    convert add_mem h ih using 1
    change ev ![mulF F.F N, pt R d 0] (F.F i) - _ = _
    simp only [pt, Nat.cast_succ, add_smul, one_smul]
    abel

private theorem lin_nsum (F : FGLaw R d) (N : ℕ) :
    lin (mulF F.F N) = (N : R) • (1 : Matrix (Fin d) (Fin d) R) := by
  ext i j
  have h := (mem_sq_iff.1 (nsum_sub_mem F N i)).2 (0, j)
  rw [map_sub, sub_eq_zero, map_smul, coeff_single_X'] at h
  simp [lin, h, Matrix.one_apply, eq_comm]

private theorem span_nsum_le (F : FGLaw R d) (N M : ℕ) :
    Ideal.span (Set.range (mulF F.F (N * M))) ≤ Ideal.span (Set.range (mulF F.F M)) := by
  rw [Ideal.span_le, nsum_mul]
  rintro _ ⟨j, rfl⟩
  have := ev_mem_pow (single_point_zero_constant (gp_mulF F M)) (K := Ideal.span (Set.range (mulF F.F M))) (N := 1)
    (f := mulF F.F N j) (fun l i => by fin_cases l; exact Ideal.subset_span ⟨i, rfl⟩)
    (by rw [pow_one]; exact gp_mulF F N j)
  rwa [pow_one] at this

private theorem nsum_pow_mem (F : FGLaw R d) (p k : ℕ) (j : Fin d) :
    mulF F.F (p ^ k) j ∈ ((Ideal.span {(p : R)}).map (C : R →+* PS R 1 d) ⊔
      Ideal.span (Set.range (X : Fin 1 × Fin d → PS R 1 d))) ^ (k + 1) := by
  set J := (Ideal.span {(p : R)}).map (C : R →+* PS R 1 d) ⊔
      Ideal.span (Set.range (X : Fin 1 × Fin d → PS R 1 d)) with hJ
  induction k generalizing j with
  | zero =>
    rw [zero_add, pow_one, hJ, ← germIdeal_eq_span]
    exact Ideal.mem_sup_right (gp_mulF F _ j)
  | succ k ih =>
    have hV := single_point_zero_constant (gp_mulF F (p ^ k))
    have h := ev_mem_pow hV (K := J ^ (k + 1)) (fun l i => by fin_cases l; exact ih i)
      (nsum_sub_mem F p j)
    rw [← pow_mul, gt_ev_sub _ hV, smul_eq_C_mul, gt_ev_mul _ hV, gt_ev_X _ hV] at h
    have h1 := Ideal.pow_le_pow_right (show k + 1 + 1 ≤ (k + 1) * 2 by omega) h
    have hC : ev ![mulF F.F (p ^ k)] (C (p : R) : PS R 1 d) = C (p : R) := subst_C _
    have h2 : C (p : R) * mulF F.F (p ^ k) j ∈ J ^ (k + 1 + 1) := by
      rw [pow_succ' J (k + 1)]
      exact Ideal.mul_mem_mul (Ideal.mem_sup_left (Ideal.mem_map_of_mem _
        (Ideal.subset_span rfl))) (ih j)
    rw [hC] at h1
    have h3 := add_mem h1 h2
    rw [pow_succ' p k, nsum_mul]
    simpa [comp1] using h3

end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF

theorem lin_mulF_and_comp_and_span_le_and_mem_pow : ∀ (R : Type) [CommRing R] (d : ℕ) (F : FGLaw R d), (∀ N : ℕ, lin (mulF F.F N) = (N : R) • (1 : Matrix (Fin d) (Fin d) R)) ∧ (∀ N M : ℕ, mulF F.F (N * M) = comp1 (mulF F.F N) (mulF F.F M)) ∧ (∀ N M : ℕ, Ideal.span (Set.range (mulF F.F (N * M))) ≤ Ideal.span (Set.range (mulF F.F M))) ∧ ∀ (p k : ℕ) (j : Fin d), mulF F.F (p ^ k) j ∈ ((Ideal.span {(p : R)}).map (MvPowerSeries.C : R →+* PS R 1 d) ⊔ Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin d → PS R 1 d))) ^ (k + 1) :=
  fun _ _ _ F => ⟨lin_nsum F, nsum_mul F, span_nsum_le F, nsum_pow_mem F⟩

end GlobalTheory.ChF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LinearDataHodgeTateInclusion
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private lemma smul_mem_span_of_split {O κ : Type} [CommRing O] [Fintype κ] [DecidableEq κ] {g d r m : ℕ}
    (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O) (Ht : Matrix (Fin g) κ O)
    (s : Fin m → Fin d → O) (cp : O) (hex : SplitEx A B)
    (hB : ∀ i, ∃ k, s k = Bᵀ *ᵥ (fun l => Ht l i)) (hT : ∀ i, ∃ k, Aᵀ *ᵥ s k = Pi.single i 1)
    (hsurj : ∀ f : Fin g → O, ∃ t, Ht *ᵥ t = cp • f) (f : Fin d → O) :
    cp • f ∈ Submodule.span O (Set.range s) := by
  obtain ⟨-, A', B', -, -, h1⟩ := hex
  choose k hk using hT
  set u : Fin d → O := ∑ i, (Aᵀ *ᵥ f) i • s (k i) with hu
  have huS : u ∈ Submodule.span O (Set.range s) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k i, rfl⟩)
  have hAu : Aᵀ *ᵥ u = Aᵀ *ᵥ f := by
    rw [hu, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hk]
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h0 : Aᵀ *ᵥ (f - u) = 0 := by rw [Matrix.mulVec_sub, hAu, sub_self]
  have h2 : A'ᵀ * Aᵀ + Bᵀ * B'ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, ← Matrix.transpose_add, h1, Matrix.transpose_one]
  have h3 : f - u = Bᵀ *ᵥ (B'ᵀ *ᵥ (f - u)) := by
    have := congrArg (fun M => M *ᵥ (f - u)) h2
    simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero, zero_add,
      Matrix.one_mulVec] at this
    exact this.symm
  obtain ⟨t, ht⟩ := hsurj (B'ᵀ *ᵥ (f - u))
  have h4 : cp • (f - u) = Bᵀ *ᵥ (Ht *ᵥ t) := by rw [ht, Matrix.mulVec_smul, ← h3]
  have h5 : Ht *ᵥ t = ∑ i, t i • (fun l => Ht l i) := by
    ext l
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have h6 : cp • (f - u) ∈ Submodule.span O (Set.range s) := by
    rw [h4, h5, Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Matrix.mulVec_smul]
    obtain ⟨j, hj⟩ := hB i
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj⟩)
  have h7 : cp • f = cp • (f - u) + cp • u := by rw [← smul_add, sub_add_cancel]
  rw [h7]
  exact Submodule.add_mem _ h6 (Submodule.smul_mem _ _ huS)

theorem linDat_hodgeTate_inclusion : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (d r m : ℕ) (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O) (ρG : OE →+* Matrix (Fin d) (Fin d) O) (N : OE →+* Matrix (Fin r) (Fin r) ℤ) (s : Fin m → Fin d → O), LinDat H A B ρG N s → ∀ c : O, v (algebraMap O C c) ^ (p - 1) ≤ v (algebraMap O C (p : O)) → ∀ f : Fin d → O, c • f ∈ Submodule.span O (Set.range s) := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ OE _ _ _ _ _ _ cp hS g H d r m A B ρG N s hL c hc f
  have := htd_domain hS
  obtain ⟨hEt, hdiag, hdet⟩ := htd_E H
  have hsurj := ht_cp_surj H.Ht H.Bt _ cp hEt hdiag hdet (htd_cp_ne hS) H.form_eq_alt
  have hle : v (algebraMap O C c) ≤ v (algebraMap O C cp) := by
    rw [← hS.cp_val] at hc
    exact le_of_pow_le_pow_left₀ (by have := (Fact.out : p.Prime).two_le; omega) zero_le hc
  obtain ⟨e, rfl⟩ := hv.dvd_of_le hle
  rw [mul_comm, mul_smul]
  exact Submodule.smul_mem _ _
    (smul_mem_span_of_split A B H.Ht s cp hL.exact hL.fromB hL.fromT hsurj f)

end GlobalTheory.ChF
end
end

