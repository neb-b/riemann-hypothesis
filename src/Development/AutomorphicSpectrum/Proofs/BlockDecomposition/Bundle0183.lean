module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.LiftUnit
public import GroundTheory.GlobalFields.TateThesis.Bundle0008

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemOHOfMemIntAd
section
noncomputable section

open NumberField IsDedekindDomain Matrix Topology
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.EisCol

open PositivityTheory.RgEis PositivityTheory.RgEis.TF GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global.IdeleGroup

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem col_apply (i₀ : ι) (κ : GL ι 𝔸[k]) (j : ι) :
    TF.col i₀ κ j = ((κ⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) j i₀ := by
  unfold TF.col
  rw [Matrix.mulVec_single_one]
  rfl

def finPart : 𝔸[k] →+* FiniteAdeleRing (𝓞 k) k := RingHom.snd _ _

theorem mem_OH_of_mem_intAd {x : 𝔸[k]} (hx : x ∈ intAd k) : x.2 ∈ OH k := by
  rw [mem_integralFiniteAdeles]
  intro v
  have := (Subring.mem_iInf.1 hx) v
  exact this

theorem sum_norm_sq {g : GL ι 𝔸[k]} {w : InfinitePlace k}
    (hg : (g : Matrix ι ι 𝔸[k]).map ((adStd k).φ w) ∈ Matrix.unitaryGroup ι ℂ) (i₀ : ι) :
    ∑ j, ‖((g : Matrix ι ι 𝔸[k]) j i₀).1 w‖ ^ 2 = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1 hg) i₀) i₀
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  have h2 : ∀ j, (star ((g : Matrix ι ι 𝔸[k]).map ((adStd k).φ w))) i₀ j *
      ((g : Matrix ι ι 𝔸[k]).map ((adStd k).φ w)) j i₀ =
      ((‖((g : Matrix ι ι 𝔸[k]) j i₀).1 w‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    have e : ‖(adStd k).φ w ((g : Matrix ι ι 𝔸[k]) j i₀)‖ = ‖((g : Matrix ι ι 𝔸[k]) j i₀).1 w‖ :=
      (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _
    rw [← e, Matrix.star_apply, Matrix.map_apply, mul_comm, Complex.star_def, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
  simp only [h2] at h
  exact_mod_cast h

theorem stab_entry {p : GL ι 𝔸[k]} {i₀ : ι} (hp : p ∈ stab 𝔸[k] {i₀}) {j : ι} (hj : j ≠ i₀) :
    (p : Matrix ι ι 𝔸[k]) j i₀ = 0 ∧ ((p⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) j i₀ = 0 :=
  hp j hj i₀ rfl

theorem stab_mul_inv {p : GL ι 𝔸[k]} {i₀ : ι} (hp : p ∈ stab 𝔸[k] {i₀}) :
    (p : Matrix ι ι 𝔸[k]) i₀ i₀ * ((p⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) i₀ i₀ = 1 := by
  have h : ((p : Matrix ι ι 𝔸[k]) * ((p⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k])) i₀ i₀ = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
  rw [Matrix.mul_apply, Finset.sum_eq_single i₀] at h
  · exact h
  · intro j _ hj
    rw [(stab_entry hp hj).2, mul_zero]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

theorem bdet_single {R : Type} [CommRing R] {p : GL ι R} {i₀ : ι} (hu : IsUnit ((p : Matrix ι ι R) i₀ i₀)) :
    ((bdet {i₀} p : Rˣ) : R) = (p : Matrix ι ι R) i₀ i₀ := by
  have key : ∀ (i₁ : DecidableEq ({i₀} : Set ι)) (i₂ : Fintype ({i₀} : Set ι)),
      @Matrix.det _ i₁ i₂ R _ ((p : Matrix ι ι R).submatrix (Subtype.val : ({i₀} : Set ι) → ι) Subtype.val) =
        (p : Matrix ι ι R) i₀ i₀ := fun i₁ i₂ =>
    @Matrix.det_eq_elem_of_subsingleton _ i₁ i₂ R _ _ _ (⟨i₀, rfl⟩ : ({i₀} : Set ι))
  unfold bdet
  split_ifs with h
  · rw [IsUnit.unit_spec, key]
  · rw [key] at h
    exact absurd hu h

theorem bdet_val {p : GL ι 𝔸[k]} {i₀ : ι} (hp : p ∈ stab 𝔸[k] {i₀}) :
    ((bdet {i₀} p : 𝔸[k]ˣ) : 𝔸[k]) = (p : Matrix ι ι 𝔸[k]) i₀ i₀ :=
  bdet_single (IsUnit.of_mul_eq_one _ (stab_mul_inv hp))

theorem bdet_inv_val {p : GL ι 𝔸[k]} {i₀ : ι} (hp : p ∈ stab 𝔸[k] {i₀}) :
    (((bdet {i₀} p)⁻¹ : 𝔸[k]ˣ) : 𝔸[k]) = ((p⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) i₀ i₀ :=
  Units.inv_eq_of_mul_eq_one_right (by rw [bdet_val hp]; exact stab_mul_inv hp)

theorem col_mul {p : GL ι 𝔸[k]} {i₀ : ι} (hp : p ∈ stab 𝔸[k] {i₀}) (κ : GL ι 𝔸[k]) :
    TF.col i₀ (p * κ) = (((bdet {i₀} p)⁻¹ : 𝔸[k]ˣ) : 𝔸[k]) • TF.col i₀ κ := by
  have h : ((p⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ Pi.single i₀ 1 =
      ((((bdet {i₀} p)⁻¹ : 𝔸[k]ˣ) : 𝔸[k])) • (Pi.single i₀ 1 : ι → 𝔸[k]) := by
    ext1 j
    have e : (((p⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ Pi.single i₀ 1) j =
        ((p⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) j i₀ := by
      rw [Matrix.mulVec_single_one]
      rfl
    rw [e, bdet_inv_val hp, Pi.smul_apply]
    by_cases hj : j = i₀
    · subst hj
      rw [Pi.single_eq_same, smul_eq_mul, mul_one]
    · rw [(stab_entry hp hj).2, Pi.single_eq_of_ne hj, smul_zero]
  unfold TF.col
  rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul]

theorem col_continuous (i₀ : ι) : Continuous fun κ : GL ι 𝔸[k] => TF.col i₀ κ := by
  unfold TF.col
  exact (Units.continuous_coe_inv).matrix_mulVec continuous_const

theorem col_one (i₀ : ι) : TF.col (k := k) i₀ 1 = Pi.single i₀ 1 := by
  unfold TF.col
  rw [inv_one, Units.val_one, Matrix.one_mulVec]

theorem col_unitVec {κ : GL ι 𝔸[k]} (hκ : κ ∈ (adStd k).kGL ι) (i₀ : ι) :
    UnitVec (fun j => (TF.col i₀ κ j).1) := by
  intro w
  have h := sum_norm_sq ((((adStd k).kGL ι).inv_mem hκ).2 w) i₀
  refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h
  exact congrArg (fun x : 𝔸[k] => ‖x.1 w‖ ^ 2) (col_apply i₀ κ j)

theorem col_prim {κ : GL ι 𝔸[k]} (hκ : κ ∈ (adStd k).kGL ι) (i₀ : ι) :
    Prim fun j => (TF.col i₀ κ j).2 := by
  refine ⟨fun j => ?_, fun j => ((κ : Matrix ι ι 𝔸[k]) i₀ j).2, fun j => ?_, ?_⟩
  · exact Eq.mpr (congrArg (fun x : 𝔸[k] => x.2 ∈ OH k) (col_apply i₀ κ j))
      (mem_OH_of_mem_intAd (hκ.1 j i₀).2)
  · exact mem_OH_of_mem_intAd (hκ.1 i₀ j).1
  · have h : ((κ : Matrix ι ι 𝔸[k]) * ((κ⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k])) i₀ i₀ = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
    rw [Matrix.mul_apply] at h
    have h2 := congrArg (finPart (k := k)) h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_one] at h2
    refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h2
    rw [map_mul]
    exact congrArg (fun x : 𝔸[k] => finPart ((κ : Matrix ι ι 𝔸[k]) i₀ j) * finPart x) (col_apply i₀ κ j)

theorem bdet_split {p : GL ι 𝔸[k]} (hk : p ∈ (adStd k).kGL ι) {i₀ : ι} (hp : p ∈ stab 𝔸[k] {i₀}) :
    ∃ (a : (InfiniteAdeleRing k)ˣ) (u : (FiniteAdeleRing (𝓞 k) k)ˣ), bdet {i₀} p = ofInfinite a * ofFinite u ∧
      (∀ w, ‖(a : InfiniteAdeleRing k) w‖ = 1) ∧ u ∈ finiteIntegralUnits k := by
  refine ⟨toInfinite k (bdet {i₀} p), toFinite k (bdet {i₀} p), ?_, fun w => ?_, ?_⟩
  · rw [mul_comm, ofFinite_mul_ofInfinite]
  · have hv : ((toInfinite k (bdet {i₀} p) : (InfiniteAdeleRing k)ˣ) : InfiniteAdeleRing k) =
        ((p : Matrix ι ι 𝔸[k]) i₀ i₀).1 := by
      rw [← bdet_val hp]; rfl
    rw [hv]
    have h := sum_norm_sq (hk.2 w) i₀
    rw [Finset.sum_eq_single i₀ (fun j _ hj => by
      rw [(stab_entry hp hj).1]
      show ‖(0 : w.Completion)‖ ^ 2 = 0
      simp)
      (fun h' => absurd (Finset.mem_univ _) h')] at h
    have h0 : 0 ≤ ‖((p : Matrix ι ι 𝔸[k]) i₀ i₀).1 w‖ := norm_nonneg _
    nlinarith [h, h0, sq_nonneg (‖((p : Matrix ι ι 𝔸[k]) i₀ i₀).1 w‖ - 1)]
  · rw [mem_finiteIntegralUnits]
    intro v
    have h1 : ((toFinite k (bdet {i₀} p) : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) =
        ((p : Matrix ι ι 𝔸[k]) i₀ i₀).2 := by
      rw [← bdet_val hp]; rfl
    have h2 : (((toFinite k (bdet {i₀} p))⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) =
        (((p⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) i₀ i₀).2 := by
      rw [← bdet_inv_val hp, ← map_inv]; rfl
    rw [h1, h2]
    exact ⟨(mem_integralFiniteAdeles.1 (mem_OH_of_mem_intAd (hk.1 i₀ i₀).1)) v,
      (mem_integralFiniteAdeles.1 (mem_OH_of_mem_intAd (hk.1 i₀ i₀).2)) v⟩

theorem colLaw : ColLaw := by
  intro k _ _ ι _ _ i₀
  exact ⟨fun κ hκ => ⟨col_unitVec hκ i₀, col_prim hκ i₀⟩, col_continuous i₀, col_one i₀,
    fun p hk hp => ⟨col_mul hp, bdet_split hk hp⟩⟩

end GlobalTheory.CompanionTheory.EisCol
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemStabOfInvCol
section
noncomputable section

open NumberField IsDedekindDomain Matrix Topology
open scoped NumberField.AdeleRing Nat

namespace GlobalTheory.CompanionTheory.RgEisSupp

open PositivityTheory.RgEis PositivityTheory.RgEis.TF

theorem inM_of_dvd {k : Type} [Field k] [NumberField k] {M N : ℕ} (h : M ∣ N)
    {x : FiniteAdeleRing (𝓞 k) k} (hx : InM N x) : InM M x := by
  obtain ⟨c, rfl⟩ := h
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨(c : FiniteAdeleRing (𝓞 k) k) * y, (OH k).mul_mem (natCast_mem _ c) hy, ?_⟩
  push_cast
  ring

theorem col_apply {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]
    (i₀ : ι) (κ : GL ι 𝔸[k]) (r : ι) :
    TF.col i₀ κ r = ((κ⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) r i₀ := by
  rw [TF.col, Matrix.mulVec_single_one]
  rfl

theorem mem_stab_of_inv_col {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (g : GL ι R) (i₀ : ι) (h : ∀ j, j ≠ i₀ → ((g⁻¹ : GL ι R) : Matrix ι ι R) j i₀ = 0) :
    g ∈ stab R ({i₀} : Set ι) := by
  have key : ∀ r, (g : Matrix ι ι R) r i₀ * ((g⁻¹ : GL ι R) : Matrix ι ι R) i₀ i₀ = (1 : Matrix ι ι R) r i₀ := by
    intro r
    have e : ((g : Matrix ι ι R) * ((g⁻¹ : GL ι R) : Matrix ι ι R)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [← e, Matrix.mul_apply]
    exact (Finset.sum_eq_single (f := fun m => (g : Matrix ι ι R) r m * ((g⁻¹ : GL ι R) : Matrix ι ι R) m i₀) i₀
      (fun m _ hm => by simp only [h m hm, mul_zero]) (fun hi => absurd (Finset.mem_univ _) hi)).symm
  show ∀ r ∉ ({i₀} : Set ι), ∀ c ∈ ({i₀} : Set ι),
    (g : Matrix ι ι R) r c = 0 ∧ ((g⁻¹ : GL ι R) : Matrix ι ι R) r c = 0
  intro r hr c hc
  obtain rfl : c = i₀ := hc
  have hr' : r ≠ c := hr
  refine ⟨?_, h r hr'⟩
  have h0 := key r
  have h1 := key c
  rw [Matrix.one_apply_ne hr'] at h0
  rw [Matrix.one_apply_eq] at h1
  calc (g : Matrix ι ι R) r c
      = (g : Matrix ι ι R) r c * ((g : Matrix ι ι R) c c * ((g⁻¹ : GL ι R) : Matrix ι ι R) c c) := by rw [h1, mul_one]
    _ = ((g : Matrix ι ι R) r c * ((g⁻¹ : GL ι R) : Matrix ι ι R) c c) * (g : Matrix ι ι R) c c := by ring
    _ = 0 := by rw [h0, zero_mul]

theorem supp : ColLaw → InMTop → Supp := by
  intro hCol hTop k _ _ ι _ _ i₀ hK U hU M₀ hM₀
  obtain ⟨hmem, hcont, -, -⟩ := hCol k ι i₀
  obtain ⟨hclop, hzero⟩ := hTop k
  have : CompactSpace ((adStd k).kGL ι) := isCompact_iff_compactSpace.mp hK

  set O : Set ((adStd k).kGL ι) :=
    {κ | ∃ p : (adStd k).kGL ι, p.1 ∈ stab 𝔸[k] ({i₀} : Set ι) ∧ ∃ u ∈ interior U, κ = p * u} with hOdef
  have hO : IsOpen O := by
    have e : O = ⋃ p : {p : (adStd k).kGL ι // p.1 ∈ stab 𝔸[k] ({i₀} : Set ι)},
        (fun x => (p.1)⁻¹ * x) ⁻¹' interior U := by
      ext κ
      simp only [hOdef, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage]
      constructor
      · rintro ⟨p, hp, u, hu, rfl⟩
        exact ⟨⟨p, hp⟩, by simpa using hu⟩
      · rintro ⟨⟨p, hp⟩, h⟩
        exact ⟨p, hp, _, h, by simp⟩
    rw [e]
    exact isOpen_iUnion fun p => isOpen_interior.preimage (continuous_const.mul continuous_id)
  have hfc : Continuous fun κ : (adStd k).kGL ι => TF.col i₀ κ.1 := hcont.comp continuous_subtype_val

  set C : ℕ → Set ((adStd k).kGL ι) := fun n =>
    {κ | (∀ j, j ≠ i₀ → InM (n ! * M₀) (TF.col i₀ κ.1 j).2) ∧
      ∀ w, 1 - 1 / ((n : ℝ) + 1) ≤ ‖(TF.col i₀ κ.1 i₀).1 w‖ ^ 2} with hCdef
  have hne : ∀ n : ℕ, n ! * M₀ ≠ 0 := fun n => Nat.mul_ne_zero (Nat.factorial_ne_zero n) hM₀
  have hCcl : ∀ n, IsClosed (C n) := by
    intro n
    simp only [hCdef, Set.setOf_and, Set.setOf_forall]
    refine IsClosed.inter (isClosed_iInter fun j => isClosed_iInter fun _ => ?_) (isClosed_iInter fun w => ?_)
    · have c2 : Continuous fun κ : (adStd k).kGL ι => (TF.col i₀ κ.1 j).2 :=
        continuous_snd.comp ((continuous_apply j).comp hfc)
      exact (hclop _ (hne n)).2.preimage c2
    · have c1 : Continuous fun κ : (adStd k).kGL ι => ‖(TF.col i₀ κ.1 i₀).1 w‖ ^ 2 :=
        (((continuous_apply w).comp (continuous_fst.comp ((continuous_apply i₀).comp hfc))).norm).pow 2
      exact isClosed_le continuous_const c1
  have hanti : ∀ n, C (n + 1) ⊆ C n := by
    intro n κ hκ
    refine ⟨fun j hj => inM_of_dvd (Nat.mul_dvd_mul_right (Nat.factorial_dvd_factorial (Nat.le_succ n)) M₀) (hκ.1 j hj), fun w => ?_⟩
    refine le_trans ?_ (hκ.2 w)
    have : (1 : ℝ) / (((n + 1 : ℕ) : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      push_cast
      linarith
    linarith
  have hex : ∃ n, C n ⊆ O := by
    by_contra hno
    push_neg at hno
    obtain ⟨κ, hκ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (fun n => C n \ O) (fun n => Set.diff_subset_diff_left (hanti n))
      (fun n => Set.nonempty_of_not_subset (hno n)) ((hCcl 0).sdiff hO).isCompact
      (fun n => (hCcl n).sdiff hO)
    have hall : ∀ n, κ ∈ C n := fun n => (Set.mem_iInter.1 hκ n).1
    have hκO : κ ∉ O := (Set.mem_iInter.1 hκ 0).2
    have hfin : ∀ j, j ≠ i₀ → (TF.col i₀ κ.1 j).2 = 0 := fun j hj =>
      hzero _ fun M hM => inM_of_dvd
        ((Nat.dvd_factorial (Nat.pos_of_ne_zero hM) le_rfl).mul_right M₀) ((hall M).1 j hj)
    have hone : ∀ w, 1 ≤ ‖(TF.col i₀ κ.1 i₀).1 w‖ ^ 2 := by
      intro w
      refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      have := (hall n).2 w
      linarith
    have hinf : ∀ j, j ≠ i₀ → (TF.col i₀ κ.1 j).1 = 0 := by
      intro j hj
      funext w
      have hs := (hmem κ.1 κ.2).1 w
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)] at hs
      have hle : ‖(TF.col i₀ κ.1 j).1 w‖ ^ 2 ≤
          ∑ x ∈ Finset.univ.erase i₀, ‖(TF.col i₀ κ.1 x).1 w‖ ^ 2 :=
        Finset.single_le_sum (f := fun x => ‖(TF.col i₀ κ.1 x).1 w‖ ^ 2) (fun _ _ => by positivity)
          (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩)
      have h0 : ‖(TF.col i₀ κ.1 j).1 w‖ ^ 2 ≤ 0 := by
        have := hone w
        linarith
      have h1 : ‖(TF.col i₀ κ.1 j).1 w‖ = 0 := by
        have h2 := sq_nonneg ‖(TF.col i₀ κ.1 j).1 w‖
        exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm h0 h2)
      exact norm_eq_zero.1 h1
    have hst : κ.1 ∈ stab 𝔸[k] ({i₀} : Set ι) := by
      refine mem_stab_of_inv_col κ.1 i₀ fun j hj => ?_
      rw [← col_apply]
      exact Prod.ext (hinf j hj) (hfin j hj)
    exact hκO ⟨κ, hst, 1, mem_interior_iff_mem_nhds.2 hU, (mul_one κ).symm⟩
  obtain ⟨n, hn⟩ := hex
  refine ⟨n ! * M₀, 1 / ((n : ℝ) + 1), hne n, Dvd.intro_left _ rfl, by positivity, fun κ h1 h2 => ?_⟩
  obtain ⟨p, hp, u, hu, e⟩ := hn (show κ ∈ C n from ⟨h1, fun w => (h2 w).le⟩)
  exact ⟨p, hp, u, interior_subset hu, e⟩

end GlobalTheory.CompanionTheory.RgEisSupp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NatCastFiniteAdeleApply
section
noncomputable section

open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.IdeleGroup PositivityTheory.RgEis PositivityTheory.RgEis.TF
open WithZero Multiplicative

namespace GlobalTheory.CompanionTheory.EisTF

variable {k : Type} [Field k] [NumberField k]

theorem natCast_finiteAdele_apply (v : HeightOneSpectrum (𝓞 k)) (M : ℕ) :
    ((M : FiniteAdeleRing (𝓞 k) k) v) = (M : v.adicCompletion k) := by
  induction M with
  | zero => simp only [Nat.cast_zero]; rfl
  | succ m ih =>
    simp only [Nat.cast_succ]
    change ((m : FiniteAdeleRing (𝓞 k) k) v) + (1 : FiniteAdeleRing (𝓞 k) k) v = _
    rw [ih]
    rfl

theorem valued_natCast_le_one (v : HeightOneSpectrum (𝓞 k)) (M : ℕ) :
    Valued.v (M : v.adicCompletion k) ≤ 1 := by
  have : (M : v.adicCompletion k) ∈ v.adicCompletionIntegers k := natCast_mem _ M
  exact this

theorem valued_absNorm_lt_one (v : HeightOneSpectrum (𝓞 k)) :
    Valued.v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion k) < 1 := by
  have hv : ∀ x : k, Valued.v (algebraMap k (v.adicCompletion k) x) = v.valuation k x :=
    fun x => v.valuedAdicCompletion_eq_valuation' x
  have h : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 k) ∈ v.asIdeal := Ideal.absNorm_mem _
  have h2 := (v.valuation_lt_one_iff_mem (K := k) _).2 h
  have h3 : ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion k) =
      algebraMap k (v.adicCompletion k) (algebraMap (𝓞 k) k ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 k)) := by
    simp
  rw [h3, hv]
  exact h2

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ exp (-1 : ℤ) := by
  by_cases hx : x = 0
  · simp [hx]
  · obtain ⟨a, rfl⟩ : ∃ a : ℤ, x = exp a := ⟨log x, (exp_log hx).symm⟩
    rw [← exp_zero, exp_lt_exp] at h
    rw [exp_le_exp]
    omega

theorem valued_absNorm_pow_le (v : HeightOneSpectrum (𝓞 k)) (n : ℕ) :
    Valued.v (((Ideal.absNorm v.asIdeal ^ n : ℕ)) : v.adicCompletion k) ≤ exp (-(n : ℤ)) := by
  have h1 := le_exp_neg_one_of_lt_one (valued_absNorm_lt_one v)
  rw [Nat.cast_pow, map_pow]
  refine (pow_le_pow_left₀ zero_le' h1 n).trans (le_of_eq ?_)
  rw [← exp_nsmul]
  congr 1
  simp

theorem valued_prod_le (S : Finset (HeightOneSpectrum (𝓞 k))) (n : HeightOneSpectrum (𝓞 k) → ℕ)
    {v : HeightOneSpectrum (𝓞 k)} (hv : v ∈ S) :
    Valued.v (((∏ w ∈ S, Ideal.absNorm w.asIdeal ^ n w : ℕ)) : v.adicCompletion k) ≤ exp (-(n v : ℤ)) := by
  classical
  rw [← Finset.mul_prod_erase S _ hv, Nat.cast_mul, map_mul]
  calc _ ≤ Valued.v (((Ideal.absNorm v.asIdeal ^ n v : ℕ)) : v.adicCompletion k) * 1 :=
        mul_le_mul_right (valued_natCast_le_one v _) _
    _ ≤ exp (-(n v : ℤ)) := by rw [mul_one]; exact valued_absNorm_pow_le v (n v)

theorem condM : CondM := by
  intro k _ _ ω
  let χ : (FiniteAdeleRing (𝓞 k) k)ˣ →* Circle := ω.toIdele.comp ofFinite
  have hχ : Continuous χ := ω.continuous_toIdele.comp continuous_ofFinite
  obtain ⟨S, n, -, h0, hker⟩ := exists_finiteLevel_le_ker_circle χ hχ
  refine ⟨∏ v ∈ S, Ideal.absNorm v.asIdeal ^ n v, ?_, ?_⟩
  · refine Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ ?_
    exact fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  · rintro u hu ⟨y, hy, huy⟩
    have hmem : u ∈ finiteLevel n := by
      refine mem_finiteLevel.2 fun v => ?_
      have hz : finiteComponent v u ∈ unitsLevel (K := k) v 0 := by
        rw [unitsLevel_zero, Submonoid.mem_units_iff]
        exact (mem_finiteIntegralUnits k).1 hu v
      by_cases hv : v ∈ S
      · refine mem_unitsLevel.2 ⟨(mem_unitsLevel.1 hz).1, ?_⟩
        have hyv : Valued.v (y v) ≤ 1 := mem_integralFiniteAdeles.1 hy v
        have huv : ((u : FiniteAdeleRing (𝓞 k) k) v) - 1 =
            ((∏ w ∈ S, Ideal.absNorm w.asIdeal ^ n w : ℕ) : v.adicCompletion k) * y v := by
          have := congrArg (fun x : FiniteAdeleRing (𝓞 k) k => x v) huy
          rw [← natCast_finiteAdele_apply]
          exact this
        rw [coe_finiteComponent, huv, map_mul]
        calc _ ≤ Valued.v ((∏ w ∈ S, Ideal.absNorm w.asIdeal ^ n w : ℕ) : v.adicCompletion k) * 1 :=
              mul_le_mul_right hyv _
          _ ≤ _ := by rw [mul_one]; exact valued_prod_le S n hv
      · rw [h0 v hv]
        exact hz
    exact MonoidHom.mem_ker.1 (hker hmem)

end GlobalTheory.CompanionTheory.EisTF
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealComponentCoe
section
noncomputable section

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace GlobalTheory.CompanionTheory.RgEisSign

variable {k : Type} [Field k] [NumberField k]


open scoped Classical in
def even_im_hermitian_sub (ω : HeckeCharacter k) (w : {w : InfinitePlace k // w.IsReal}) : ℕ :=
  if ω.realComponent w.2 (-1) = 1 then 0 else 1

theorem realComponent_coe (ω : HeckeCharacter k) (h : IsOfFinOrder ω)
    (w : {w : InfinitePlace k // w.IsReal}) (x : ℝˣ) :
    (ω.realComponent w.2 x : ℂ) = if 0 < (x : ℝ) then (1 : ℂ) else (-1) ^ even_im_hermitian_sub ω w := by
  split_ifs with hx
  · rw [ω.realComponent_eq_one_of_isOfFinOrder h w.2 hx]; simp
  · have hneg : (x : ℝ) < 0 := lt_of_le_of_ne (not_lt.1 hx) x.ne_zero
    have hpos : 0 < ((-x : ℝˣ) : ℝ) := by simpa using hneg
    have hx' : x = (-1) * (-x) := by simp
    have hc : ω.realComponent w.2 (-1) * ω.realComponent w.2 (-1) = 1 := by
      rw [← map_mul]; simp
    rw [hx', map_mul, ω.realComponent_eq_one_of_isOfFinOrder h w.2 hpos, mul_one]
    unfold even_im_hermitian_sub
    split_ifs with h1
    · rw [h1]; simp
    · have h2 : ((ω.realComponent w.2 (-1) : Circle) : ℂ) * ((ω.realComponent w.2 (-1) : Circle) : ℂ) = 1 := by
        rw [← Circle.coe_mul, hc]; simp
      rcases mul_self_eq_one_iff.1 h2 with h3 | h3
      · exact absurd (Circle.ext (by simpa using h3)) h1
      · simpa using h3

theorem real_factor (ω : HeckeCharacter k) (h : IsOfFinOrder ω) (a : (InfiniteAdeleRing k)ˣ)
    (w : {w : InfinitePlace k // w.IsReal}) :
    (ω.infiniteComponent w.1 (infiniteComponent w.1 a) : ℂ) =
      if 0 < (homeomorphMixedSpace k (a : InfiniteAdeleRing k)).1 w then (1 : ℂ)
      else (-1) ^ even_im_hermitian_sub ω w := by
  have hs := realUnitsHom_surjective w.2 (infiniteComponent w.1 a)
  have hv : ((Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal w.2 : w.1.Completion →+* ℝ).toMonoidHom
      (infiniteComponent w.1 a) : ℝˣ) : ℝ) = (homeomorphMixedSpace k (a : InfiniteAdeleRing k)).1 w := rfl
  rw [← hs, ← hv]
  exact realComponent_coe ω h w _

theorem complex_factor (ω : HeckeCharacter k) (h : IsOfFinOrder ω) (a : (InfiniteAdeleRing k)ˣ)
    (w : {w : InfinitePlace k // w.IsComplex}) :
    (ω.infiniteComponent w.1 (infiniteComponent w.1 a) : ℂ) = 1 := by
  rw [← complexUnitsHom_surjective w.2 (infiniteComponent w.1 a)]
  have := ω.complexComponent_eq_one_of_isOfFinOrder h w.2
    (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex w.2 : w.1.Completion →+* ℂ).toMonoidHom
      (infiniteComponent w.1 a))
  exact congrArg (fun c : Circle => (c : ℂ)) this |>.trans (by simp)

theorem signChar : PositivityTheory.RgEis.TF.SignChar := by
  intro k _ _ ω h
  have hf : IsOfFinOrder ω :=
    isOfFinOrder_iff_pow_eq_one.2 ⟨2, by norm_num, by rw [pow_two]; exact h⟩
  refine ⟨even_im_hermitian_sub ω, fun a => ?_⟩
  rw [HeckeCharacter.toIdele_ofInfinite]
  have h1 : ((∏ w, ω.infiniteComponent w (infiniteComponent w a) : Circle) : ℂ) =
      ∏ w, (ω.infiniteComponent w (infiniteComponent w a) : ℂ) :=
    map_prod Circle.coeHom (fun w => ω.infiniteComponent w (infiniteComponent w a)) Finset.univ
  rw [h1, InfinitePlace.prod_eq_prod_mul_prod, Finset.prod_eq_one (fun w _ => complex_factor ω hf a w),
    mul_one]
  exact Finset.prod_congr rfl fun w _ => real_factor ω hf a w

end GlobalTheory.CompanionTheory.RgEisSign
end
end

