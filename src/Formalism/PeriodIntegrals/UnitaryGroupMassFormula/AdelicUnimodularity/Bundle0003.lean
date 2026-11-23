module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.ExistsNatVec
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularIndex.PairwiseDisjointCosets

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.ConstructionB
section
noncomputable section

namespace PI.WAU.B

open Formalism.MainNotions.S MeasureTheory NumberField IsDedekindDomain Formalism.UG Matrix PI.WAU.B
open scoped TensorProduct

theorem cover_of {G : Type} [Group G] (K : Set G) (P : G → Prop) {C : Type} [Countable C]
    (f : G → C) (hf : ∀ x y, P x → P y → f x = f y → y⁻¹ * x ∈ K) :
    ∃ s : Set G, s.Countable ∧ ∀ x, P x → ∃ y ∈ s, y⁻¹ * x ∈ K := by
  classical
  refine ⟨Set.range fun c : {c : C // ∃ x, P x ∧ f x = c} => c.2.choose, Set.countable_range _,
    fun x hx => ?_⟩
  let c : {c : C // ∃ x, P x ∧ f x = c} := ⟨f x, x, hx, rfl⟩
  obtain ⟨hP, hfc⟩ := c.2.choose_spec
  exact ⟨c.2.choose, ⟨c, rfl⟩, hf x _ hx hP hfc.symm⟩

theorem nsmul_cancel {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {N : ℕ}
    (hN : 0 < N) {v w : V} (h : N • v = N • w) : v = w := by
  have h' : (N : K) • v = (N : K) • w := by
    rw [Nat.cast_smul_eq_nsmul K, Nat.cast_smul_eq_nsmul K]
    exact h
  exact smul_right_injective V (Nat.cast_ne_zero.mpr hN.ne') h'

section

variable (I : AutInst) {k : ℕ} (m : Fin k → Fin I.n → I.E)

theorem fmat_inv_mul (y : I.Gf) : I.fmat y⁻¹ * I.fmat y = 1 := by
  rw [show I.fmat y⁻¹ * I.fmat y = I.fmat (y⁻¹ * y) from rfl, inv_mul_cancel]
  rfl

theorem fmat_mul_inv (y : I.Gf) : I.fmat y * I.fmat y⁻¹ = 1 := by
  rw [show I.fmat y * I.fmat y⁻¹ = I.fmat (y * y⁻¹) from rfl, mul_inv_cancel]
  rfl

def PN (N : ℕ) (x : I.Gf) : Prop :=
  0 < N ∧ ∀ j, N • (I.fmat x *ᵥ ivec (F := I.F) (m j)) ∈ I.Lf ∧
    N • (I.fmat x⁻¹ *ᵥ ivec (F := I.F) (m j)) ∈ I.Lf

def fN (N : ℕ) (x : I.Gf) : Fin k → Fin k → Bad I.F (N * N) → I.F := by
  classical
  exact fun j => if h : N • (I.fmat x *ᵥ ivec (F := I.F) (m j)) ∈ Tset (F := I.F) m then
    fun i => cls (N * N) (h.choose i) else fun _ _ => 0

theorem half (hm : ∀ i, m i ∈ I.L) (hgen : ∀ l ∈ I.L, ∃ z : Fin k → ℤ, l = ∑ i, z i • m i)
    {N : ℕ} {x y : I.Gf} (hx : PN I m N x) (hy : PN I m N y) (he : fN I m N x = fN I m N y)
    (j : Fin k) : (I.fmat y⁻¹ * I.fmat x) *ᵥ ivec (F := I.F) (m j) ∈ I.Lf := by
  classical
  obtain ⟨hN, hxj⟩ := hx
  obtain ⟨_, hyj⟩ := hy
  have hTx : N • (I.fmat x *ᵥ ivec (F := I.F) (m j)) ∈ Tset (F := I.F) m :=
    lam_sub_alt hm hgen (hxj j).1
  have hTy : N • (I.fmat y *ᵥ ivec (F := I.F) (m j)) ∈ Tset (F := I.F) m :=
    lam_sub_alt hm hgen (hyj j).1
  have hej := congrFun he j
  simp only [fN, dif_pos hTx, dif_pos hTy] at hej
  obtain ⟨haI, haE⟩ := hTx.choose_spec
  obtain ⟨ha'I, ha'E⟩ := hTy.choose_spec

  have hb : ∀ i, ∃ b : Af I.F, (∀ v, b v ∈ v.adicCompletionIntegers I.F) ∧
      hTx.choose i - hTy.choose i = ((N * N : ℕ) : Af I.F) * b := fun i =>
    cls_eq (Nat.mul_pos hN hN) (haI i) (ha'I i) (congrFun hej i)
  choose b hbI hbE using hb
  set w : Fin I.n → I.E ⊗[I.F] Af I.F := ∑ i, incA I.F I.E (b i) • ivec (F := I.F) (m i) with hwdef
  have hw : w ∈ I.Lf :=
    Submodule.sum_mem _ fun i _ => smulO_mem (incA_mem (hbI i)) (ivec_mem (hm i))
  have hdiff : N • (I.fmat x *ᵥ ivec (F := I.F) (m j) - I.fmat y *ᵥ ivec (F := I.F) (m j)) =
      N • (N • w) := by
    rw [smul_sub, haE, ha'E, ← Finset.sum_sub_distrib, hwdef, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sub_smul, ← map_sub, hbE i, map_mul, map_natCast, mul_smul, Nat.cast_smul_eq_nsmul,
      smul_smul]
  have hd : I.fmat x *ᵥ ivec (F := I.F) (m j) - I.fmat y *ᵥ ivec (F := I.F) (m j) = N • w :=
    nsmul_cancel (K := I.F) hN hdiff
  have hxu : I.fmat x *ᵥ ivec (F := I.F) (m j) = I.fmat y *ᵥ ivec (F := I.F) (m j) + N • w := by
    rw [← hd]
    abel
  rw [← Matrix.mulVec_mulVec, hxu, Matrix.mulVec_add, Matrix.mulVec_mulVec, fmat_inv_mul I y,
    Matrix.one_mulVec]
  refine Submodule.add_mem _ (ivec_mem (hm j)) ?_
  have hP : ∀ i, (N • I.fmat y⁻¹) *ᵥ ivec (F := I.F) (m i) ∈ I.Lf := fun i => by
    rw [Matrix.smul_mulVec]
    exact (hyj i).2
  have h2 := mulVec_lam hm hgen (N • I.fmat y⁻¹) hP hw
  rwa [Matrix.smul_mulVec, ← Matrix.mulVec_smul] at h2

theorem step (hm : ∀ i, m i ∈ I.L) (hgen : ∀ l ∈ I.L, ∃ z : Fin k → ℤ, l = ∑ i, z i • m i)
    {N : ℕ} {x y : I.Gf} (hx : PN I m N x) (hy : PN I m N y) (he : fN I m N x = fN I m N y) :
    y⁻¹ * x ∈ I.Kset := by
  show ∀ w, w ∈ I.Lf ↔
    (((y⁻¹ * x : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix _ _ _) *ᵥ w ∈ I.Lf
  have hco : (((y⁻¹ * x : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix _ _ _) =
      I.fmat y⁻¹ * I.fmat x := rfl
  intro w
  rw [hco]
  constructor
  · intro hw
    exact mulVec_lam hm hgen _ (half I m hm hgen hx hy he) hw
  · intro hw
    have h2 := mulVec_lam hm hgen _ (half I m hm hgen hy hx he.symm) hw
    have h1 : I.fmat x⁻¹ * I.fmat y * (I.fmat y⁻¹ * I.fmat x) = 1 := by
      rw [mul_assoc, ← mul_assoc (I.fmat y), fmat_mul_inv, one_mul, fmat_inv_mul]
    rwa [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] at h2

theorem exists_PN (x : I.Gf) : ∃ N, PN I m N x := by
  classical
  have hA : ∀ j, ∃ N : ℕ, 0 < N ∧ N • (I.fmat x *ᵥ ivec (F := I.F) (m j)) ∈ I.Lf :=
    fun j => exists_nat_vec I.L_span _
  have hB : ∀ j, ∃ N : ℕ, 0 < N ∧ N • (I.fmat x⁻¹ *ᵥ ivec (F := I.F) (m j)) ∈ I.Lf :=
    fun j => exists_nat_vec I.L_span _
  choose A hA0 hA using hA
  choose B hB0 hB using hB
  refine ⟨(∏ j, A j) * ∏ j, B j, ?_, fun j => ⟨?_, ?_⟩⟩
  · exact Nat.mul_pos (Finset.prod_pos fun j _ => hA0 j) (Finset.prod_pos fun j _ => hB0 j)
  · obtain ⟨M, hM⟩ := Finset.dvd_prod_of_mem A (Finset.mem_univ j)
    rw [hM, mul_assoc]
    exact nsmul_lam (hA j) _
  · obtain ⟨M, hM⟩ := Finset.dvd_prod_of_mem B (Finset.mem_univ j)
    rw [hM, show (∏ j, A j) * (B j * M) = B j * (M * ∏ j, A j) by ring]
    exact nsmul_lam (hB j) _

end

end PI.WAU.B

namespace PI.WAU

open PI.WAU.B

theorem compact_countable : KCountable := by
  intro I
  obtain ⟨k, m, hm, hgen⟩ := exists_gen I.L (Module.Finite.iff_fg.mpr I.L_fg)
  have hcov : ∀ N : ℕ, ∃ s : Set I.Gf, s.Countable ∧
      ∀ x, PN I m N x → ∃ y ∈ s, y⁻¹ * x ∈ I.Kset := by
    intro N
    haveI : Countable (Bad I.F (N * N) → I.F) := countable_cls (N * N)
    exact cover_of I.Kset (PN I m N) (fN I m N) fun x y hx hy he => step I m hm hgen hx hy he
  choose s hs hsK using hcov
  refine ⟨⋃ N, s N, Set.countable_iUnion hs, fun x => ?_⟩
  obtain ⟨N, hN⟩ := exists_PN I m x
  obtain ⟨y, hy, hyK⟩ := hsK N x hN
  exact ⟨y, Set.mem_iUnion.mpr ⟨N, hy⟩, hyK⟩

end PI.WAU
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.ConstructionD
section
noncomputable section

namespace PI.WAU

open Formalism.MainNotions.S MeasureTheory Matrix Pointwise

theorem kg_one_eq (I : AutInst) : I.Kg 1 = I.Kset := by
  ext x
  refine ⟨fun h => h.1, fun h => ⟨h, fun y hy => ⟨(I.fmat x - 1) *ᵥ y, ?_, by simp⟩⟩⟩
  have h' : ∀ y, y ∈ I.Lf ↔ I.fmat x *ᵥ y ∈ I.Lf := h
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  exact I.Lf.sub_mem ((h' y).1 hy) hy

theorem kset_open (I : AutInst) : IsOpen I.Kset := by
  rw [← kg_one_eq]
  exact I.topf_open 1 le_rfl

theorem ksub_coe (I : AutInst) : ((Ksub I : Subgroup I.Gf) : Set I.Gf) = I.Kset := rfl

theorem sigmaFinite_of_K (I : AutInst) (μ : Measure I.Gf) (hμ : μ.IsHaarMeasure)
    (hKc : IsCompact I.Kset) (hQ : ∃ s : Set I.Gf, s.Countable ∧ ∀ x : I.Gf, ∃ y ∈ s, y⁻¹ * x ∈ I.Kset) :
    SigmaFinite μ := by
  haveI := hμ
  obtain ⟨s, hs, hcov⟩ := hQ
  refine Measure.sigmaFinite_of_countable (S := (fun y => (fun x => y * x) '' I.Kset) '' s)
    (hs.image _) ?_ ?_
  · rintro _ ⟨y, -, rfl⟩
    show μ ((fun x => y * x) '' I.Kset) < ⊤
    rw [Set.image_mul_left, measure_preimage_mul]
    exact hKc.measure_lt_top
  · rw [Set.sUnion_image, Set.eq_univ_iff_forall]
    intro x
    obtain ⟨y, hy, hyx⟩ := hcov x
    exact Set.mem_biUnion hy ⟨y⁻¹ * x, hyx, mul_inv_cancel_left y x⟩

theorem adUnimod_of (hA : KgSubgroup) (hC : KCompact) (hQ : KCountable) (hI : IndexEq) :
    PI.AdUnimod := by
  intro I μ hμ
  haveI := sigmaFinite_of_K I μ hμ (hC I) (hQ I)
  choose U hU using fun n : ℕ => hA I (n + 1) (by omega)
  refine PI.UnimodIdxWork.unimodIdx_main I.Gf μ hμ U (fun n => ?_) (fun V hV => ?_) (Ksub I) ?_ ?_ (hI I)
  · rw [hU n]
    exact I.topf_open (n + 1) (by omega)
  · obtain ⟨g, hg1, hgV⟩ := I.topf_basis V hV
    refine ⟨g - 1, ?_⟩
    rw [hU (g - 1), show g - 1 + 1 = g by omega]
    exact hgV
  · rw [ksub_coe]
    exact kset_open I
  · rw [ksub_coe]
    exact hC I

end PI.WAU
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.LamAfLeOhatL
section
noncomputable section

namespace PI.WAU

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Formalism.MainNotions.S
open scoped TensorProduct

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def ohatL (L : Submodule (𝓞 E) (Fin n → E)) : AddSubgroup (Fin n → E ⊗[F] Af F) :=
  AddSubgroup.closure {y | ∃ c ∈ Ohat F, ∃ l ∈ L, y = ((1 : E) ⊗ₜ[F] c) • fun i => Formalism.UG.inclE (F := F) (Af F) (l i)}

theorem smul_ohatL (L : Submodule (𝓞 E) (Fin n → E)) {a : E ⊗[F] Af F} (ha : a ∈ IntAf F E) :
    ∀ y ∈ ohatL (F := F) L, a • y ∈ ohatL (F := F) L := by
  let T : Subring (E ⊗[F] Af F) :=
    { carrier := {a | ∀ y ∈ ohatL (F := F) L, a • y ∈ ohatL (F := F) L}
      mul_mem' := fun {a c} ha hc y hy => by rw [mul_smul]; exact ha _ (hc y hy)
      one_mem' := fun y hy => by rw [one_smul]; exact hy
      add_mem' := fun {a c} ha hc y hy => by rw [add_smul]; exact add_mem (ha y hy) (hc y hy)
      zero_mem' := fun y _ => by rw [zero_smul]; exact zero_mem _
      neg_mem' := fun {a} ha y hy => by rw [neg_smul]; exact neg_mem (ha y hy) }
  have hle : IntAf F E ≤ T := by
    apply Subring.closure_le.mpr
    rintro a (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨c', hc'⟩, rfl⟩)
    · obtain ⟨o, rfl⟩ := hx
      refine fun y hy => ?_
      unfold ohatL at hy
      induction hy using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨c, hc, l, hl, rfl⟩ := hz
        apply AddSubgroup.subset_closure
        refine ⟨c, hc, o • l, L.smul_mem o hl, ?_⟩
        funext i
        show (algebraMap (𝓞 E) E o ⊗ₜ[F] (1 : Af F)) * (((1 : E) ⊗ₜ[F] c) * ((l i) ⊗ₜ[F] (1 : Af F))) =
          ((1 : E) ⊗ₜ[F] c) * (((o • l) i) ⊗ₜ[F] (1 : Af F))
        rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          Algebra.TensorProduct.tmul_mul_tmul, Pi.smul_apply, Algebra.smul_def]
        simp only [one_mul, mul_one]
      | zero => rw [smul_zero]; exact zero_mem _
      | add u w _ _ hu hw => rw [smul_add]; exact add_mem hu hw
      | neg u _ hu => rw [smul_neg]; exact neg_mem hu
    · refine fun y hy => ?_
      unfold ohatL at hy
      induction hy using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨c, hc, l, hl, rfl⟩ := hz
        apply AddSubgroup.subset_closure
        refine ⟨c' * c, ohat_mul hc' hc, l, hl, ?_⟩
        rw [smul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      | zero => rw [smul_zero]; exact zero_mem _
      | add u w _ _ hu hw => rw [smul_add]; exact add_mem hu hw
      | neg u _ hu => rw [smul_neg]; exact neg_mem hu
  exact hle ha

theorem lamAf_le_ohatL (L : Submodule (𝓞 E) (Fin n → E)) {y : Fin n → E ⊗[F] Af F}
    (hy : y ∈ lamAf (F := F) L) : y ∈ ohatL (F := F) L := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, rfl⟩ := hx
    apply AddSubgroup.subset_closure
    refine ⟨1, ohat_one, (l : Fin n → E), l.2, ?_⟩
    rw [← Algebra.TensorProduct.one_def, one_smul]
  | zero => exact zero_mem _
  | add x z _ _ hx hz => exact add_mem hx hz
  | smul a x _ hx => exact smul_ohatL L a.2 x hx

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem intC_zero {b : Module.Basis ι F E} : IntC b (0 : E ⊗[F] Af F) := by
  intro k
  simp only [map_zero, Pi.zero_apply]
  exact ohat_zero

theorem intC_neg {b : Module.Basis ι F E} {x : E ⊗[F] Af F} (hx : IntC b x) : IntC b (-x) := by
  intro k
  simp only [map_neg, Pi.neg_apply]
  exact ohat_neg (hx k)

theorem exists_upper (b : Module.Basis ι F E) (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) :
    ∃ D : ℕ, 0 < D ∧ ∀ y ∈ lamAf (F := F) L, ∀ j, IntC b (D • y j) := by
  obtain ⟨T, hT⟩ := (hfg.restrictScalars (R := ℤ))
  obtain ⟨D, hD, hDint⟩ := exists_den_fin (fun x : T × Fin n × ι =>
    b.repr ((x.1 : Fin n → E) x.2.1) x.2.2)
  have hQ : ∀ l ∈ L, ∀ j k, IntF ((D : F) * b.repr (l j) k) := by
    intro l hl
    have hl' : l ∈ Submodule.span ℤ (T : Set (Fin n → E)) := by rw [hT]; exact hl
    clear hl
    induction hl' using Submodule.span_induction with
    | mem x hx => intro j k; exact hDint ⟨⟨x, hx⟩, j, k⟩
    | zero =>
      intro j k
      unfold IntF
      simp only [Pi.zero_apply, map_zero, Finsupp.coe_zero, mul_zero]
      exact ohat_zero
    | add x z _ _ hx hz =>
      intro j k
      have h1 := hx j k
      have h2 := hz j k
      unfold IntF at h1 h2 ⊢
      rw [Pi.add_apply, map_add (f := _), Finsupp.add_apply, mul_add, map_add (f := _)]
      exact ohat_add h1 h2
    | smul a x _ hx =>
      intro j k
      have h1 := hx j k
      unfold IntF at h1 ⊢
      rw [Pi.smul_apply, map_zsmul, Finsupp.smul_apply, mul_smul_comm, map_zsmul]
      exact ohat_zsmul h1 a
  refine ⟨D, hD, fun y hy j => ?_⟩
  have hy' := lamAf_le_ohatL L hy
  clear hy
  unfold ohatL at hy'
  induction hy' using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c, hc, l, hl, rfl⟩ := hz
    intro k
    rw [map_nsmul, Pi.smul_apply]
    have ew : ((((1 : E) ⊗ₜ[F] c) • fun i => Formalism.UG.inclE (F := F) (Af F) (l i)) j) =
        (l j) ⊗ₜ[F] c := by
      simp [Formalism.UG.inclE, Algebra.TensorProduct.tmul_mul_tmul]
    rw [ew]
    simp only [coord, TensorProduct.lift.tmul, LinearMap.mk₂_apply]
    rw [← Nat.cast_smul_eq_nsmul F, smul_smul, Algebra.smul_def]
    exact ohat_mul (hQ l hl j k) hc
  | zero => rw [Pi.zero_apply, smul_zero]; exact intC_zero
  | add u w _ _ hu hw => rw [Pi.add_apply, smul_add]; exact intC_add hu hw
  | neg u _ hu => rw [Pi.neg_apply, smul_neg]; exact intC_neg hu

end PI.WAU
end
end

