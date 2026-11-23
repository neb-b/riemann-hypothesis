module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle0005
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.MemColSpanIff
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.SegStartSpec
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.OddTops

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.IsLatticeMapSubIff
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

section Poly

variable {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)

theorem colAddGen_map {r n : ℕ} (l j : Fin n) (f : MvPolynomial (Fin r × Fin n) A) :
    colAddGen B l j (map φ f) = map φ (colAddGen A l j f) := by
  have h : (colAddGen B (r := r) l j).toRingHom.comp (map φ) = (map φ).comp (colAddGen A (r := r) l j).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [colAddGen]
    · intro x
      simp only [colAddGen, RingHom.comp_apply, map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
      split_ifs <;> simp
  exact RingHom.congr_fun h f

theorem rowAct_map' {r n : ℕ} (g : Matrix (Fin r) (Fin r) A) (f : MvPolynomial (Fin r × Fin n) A) :
    rowAct B (g.map φ) (map φ f) = map φ (rowAct A g f) := by
  have h : (rowAct B (n := n) (g.map φ)).toRingHom.comp (map φ) = (map φ).comp (rowAct A (n := n) g).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [rowAct]
    · intro x
      simp [rowAct]
  exact RingHom.congr_fun h f

theorem dualWeyl_map {r n : ℕ} {ν : Fin n → ℕ} {f : MvPolynomial (Fin r × Fin n) A} (hf : f ∈ dualWeyl A r n ν) :
    map φ f ∈ dualWeyl B r n ν := by
  unfold dualWeyl at *
  have h1 := (Submodule.mem_inf.1 hf).1
  have h2 := (Submodule.mem_inf.1 hf).2
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · rw [mem_weightedHomogeneousSubmodule] at h1 ⊢
    intro d hd
    rw [coeff_map] at hd
    exact h1 (fun h => hd (by rw [h, map_zero]))
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero,
      AlgHom.toLinearMap_apply] at h2 ⊢
    intro l j h
    rw [colAddGen_map, h2 l j h, map_rename]

theorem map_smul' {σ : Type*} (c : A) (f : MvPolynomial σ A) : map φ (c • f) = φ c • map φ f := by
  rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]

end Poly

structure Iso2 (R₁ F₁ R₂ F₂ : Type) [CommRing R₁] [Field F₁] [Algebra R₁ F₁] [CommRing R₂] [Field F₂]
    [Algebra R₂ F₂] where
  φR : R₁ ≃+* R₂
  φF : F₁ ≃+* F₂
  h : ∀ x, φF (algebraMap R₁ F₁ x) = algebraMap R₂ F₂ (φR x)

section Sub

variable {R₁ F₁ R₂ F₂ : Type} [CommRing R₁] [Field F₁] [Algebra R₁ F₁] [CommRing R₂] [Field F₂] [Algebra R₂ F₂]

def Iso2.symm (J : Iso2 R₁ F₁ R₂ F₂) : Iso2 R₂ F₂ R₁ F₁ where
  φR := J.φR.symm
  φF := J.φF.symm
  h x := by
    apply J.φF.injective
    rw [RingEquiv.apply_symm_apply, J.h, RingEquiv.apply_symm_apply]

variable (J : Iso2 R₁ F₁ R₂ F₂) {k : ℕ}

def mapSub (L : Submodule R₁ (Fin k → F₁)) : Submodule R₂ (Fin k → F₂) where
  carrier := {y | (fun i => J.φF.symm (y i)) ∈ L}
  add_mem' := by
    intro x y hx hy
    have : (fun i => J.φF.symm ((x + y) i)) = (fun i => J.φF.symm (x i)) + fun i => J.φF.symm (y i) := by
      funext i; simp
    show (fun i => J.φF.symm ((x + y) i)) ∈ L
    rw [this]; exact L.add_mem hx hy
  zero_mem' := by
    have : (fun i => J.φF.symm ((0 : Fin k → F₂) i)) = 0 := by funext i; simp
    show (fun i => J.φF.symm ((0 : Fin k → F₂) i)) ∈ L
    rw [this]; exact L.zero_mem
  smul_mem' := by
    intro c x hx
    have : (fun i => J.φF.symm ((c • x) i)) = J.φR.symm c • fun i => J.φF.symm (x i) := by
      funext i
      simp only [Pi.smul_apply, Algebra.smul_def, map_mul]
      rw [show J.φF.symm (algebraMap R₂ F₂ c) = algebraMap R₁ F₁ (J.φR.symm c) from J.symm.h c]
    show (fun i => J.φF.symm ((c • x) i)) ∈ L
    rw [this]; exact L.smul_mem _ hx

theorem mem_mapSub (L : Submodule R₁ (Fin k → F₁)) (y : Fin k → F₂) :
    y ∈ mapSub J L ↔ (fun i => J.φF.symm (y i)) ∈ L := Iff.rfl

theorem map_mem_mapSub (L : Submodule R₁ (Fin k → F₁)) (x : Fin k → F₁) :
    (fun i => J.φF (x i)) ∈ mapSub J L ↔ x ∈ L := by
  rw [mem_mapSub]
  simp

theorem mapSub_symm (L : Submodule R₁ (Fin k → F₁)) : mapSub J.symm (mapSub J L) = L := by
  ext x
  rw [mem_mapSub, mem_mapSub]
  simp [Iso2.symm]

theorem mapSub_symm' (L : Submodule R₂ (Fin k → F₂)) : mapSub J (mapSub J.symm L) = L := by
  ext x
  rw [mem_mapSub, mem_mapSub]
  simp [Iso2.symm]

theorem mapSub_mono {L L' : Submodule R₁ (Fin k → F₁)} (h : L ≤ L') : mapSub J L ≤ mapSub J L' :=
  fun _ hy => h hy

theorem mapSub_span (S : Set (Fin k → F₁)) :
    mapSub J (Submodule.span R₁ S) = Submodule.span R₂ ((fun x i => J.φF (x i)) '' S) := by
  apply le_antisymm
  · intro y hy
    have key : ∀ x ∈ Submodule.span R₁ S, (fun i => J.φF (x i)) ∈
        Submodule.span R₂ ((fun (x : Fin k → F₁) i => J.φF (x i)) '' S) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
      | zero =>
        have : (fun i => J.φF ((0 : Fin k → F₁) i)) = 0 := by funext i; simp
        rw [this]; exact Submodule.zero_mem _
      | add x y _ _ hx hy =>
        have : (fun i => J.φF ((x + y) i)) = (fun i => J.φF (x i)) + fun i => J.φF (y i) := by funext i; simp
        rw [this]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx =>
        have : (fun i => J.φF ((c • x) i)) = J.φR c • fun i => J.φF (x i) := by
          funext i
          simp only [Pi.smul_apply, Algebra.smul_def, map_mul, J.h]
        rw [this]; exact Submodule.smul_mem _ _ hx
    have := key _ hy
    simpa using this
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact (map_mem_mapSub J _ x).2 (Submodule.subset_span hx)

theorem mapSub_colSpan (g : Matrix (Fin k) (Fin k) F₁) :
    mapSub J (colSpan R₁ g) = colSpan R₂ (g.map J.φF) := by
  unfold colSpan
  rw [mapSub_span, ← Set.range_comp]
  rfl

theorem isLattice_mapSub {L : Submodule R₁ (Fin k → F₁)} (h : IsLattice R₁ L) : IsLattice R₂ (mapSub J L) := by
  obtain ⟨g, hg, rfl⟩ := h
  refine ⟨g.map J.φF, ?_, mapSub_colSpan J g⟩
  have : (g.map J.φF).det = J.φF g.det := by
    exact (RingHom.map_det (J.φF : F₁ →+* F₂) g).symm
  rw [this]
  exact hg.map J.φF

theorem isLattice_mapSub_iff (L : Submodule R₁ (Fin k → F₁)) : IsLattice R₁ L ↔ IsLattice R₂ (mapSub J L) :=
  ⟨isLattice_mapSub J, fun h => by have := isLattice_mapSub J.symm h; rwa [mapSub_symm] at this⟩

def mapSubEquiv : Submodule R₁ (Fin k → F₁) ≃ Submodule R₂ (Fin k → F₂) where
  toFun := mapSub J
  invFun := mapSub J.symm
  left_inv := mapSub_symm J
  right_inv := mapSub_symm' J

theorem isEdge_mapSub (p n' r : ℕ) {e : Edge R₁ F₁ k} (h : IsEdge p n' r e) :
    IsEdge p n' r (⟨mapSub J e.src, mapSub J e.tgt⟩ : Edge R₂ F₂ k) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨isLattice_mapSub J h1, isLattice_mapSub J h2, mapSub_mono J h3, ?_, ?_⟩
  · intro y hy
    have h6 := h4 _ hy
    have : (fun i => J.φF.symm (((p : R₂) • y) i)) = (p : R₁) • fun i => J.φF.symm (y i) := by
      funext i
      simp [Algebra.smul_def]
    show (fun i => J.φF.symm (((p : R₂) • y) i)) ∈ e.src
    rw [this]; exact h6
  · rw [← h5]
    let E : ↥(mapSub J e.tgt) ≃ ↥e.tgt :=
      { toFun := fun y => ⟨fun i => J.φF.symm (y.1 i), y.2⟩
        invFun := fun x => ⟨fun i => J.φF (x.1 i), (map_mem_mapSub J _ _).2 x.2⟩
        left_inv := fun y => Subtype.ext (by funext i; simp)
        right_inv := fun x => Subtype.ext (by funext i; simp) }
    refine Nat.card_congr (Quotient.congr E fun a b => ?_)
    rw [Submodule.quotientRel_def, Submodule.quotientRel_def, Submodule.mem_comap, Submodule.mem_comap]
    show (a.1 - b.1) ∈ mapSub J e.src ↔ ((E a).1 - (E b).1) ∈ e.src
    rw [mem_mapSub]
    have : (fun i => J.φF.symm ((a.1 - b.1) i)) = (E a).1 - (E b).1 := by
      funext i
      simp [E]
    rw [this]

end Sub

end Formalism.MainNotions.flipOneThree.Pf

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.MapMDetUnit
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.LatticeSystems

section Tr

variable {p n' : ℕ} (R : RS p n') {k : ℕ}

theorem mapM_det_unit (V : Matrix (Fin k) (Fin k) R.W) (hV : IsUnit V.det) :
    IsUnit (mapM (Qq := R.Qq) V).det := by
  show IsUnit ((algebraMap R.W R.Qq).mapMatrix V).det
  rw [← RingHom.map_det]
  exact hV.map _

theorem colSpan_mapM (V : Matrix (Fin k) (Fin k) R.W) (hV : IsUnit V.det) :
    colSpan R.W (mapM (Qq := R.Qq) V) = colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq) := by
  have h := colSpan_unimod (1 : Matrix (Fin k) (Fin k) R.Qq) V hV
  rwa [one_mul] at h

private theorem colSpan_map_mulVecLin_eq_colSpan_mul (M g : Matrix (Fin k) (Fin k) R.Qq) :
    (colSpan R.W g).map ((Matrix.mulVecLin M).restrictScalars R.W) = colSpan R.W (M * g) := by
  rw [colSpan, colSpan, Submodule.map_span, ← Set.range_comp]
  congr 1

private theorem isEdge_map_mulVecLin_of_isUnit_det (M : Matrix (Fin k) (Fin k) R.Qq) (hM : IsUnit M.det) (e : Edge R.W R.Qq k)
    (he : IsEdge p n' 1 e) :
    IsEdge p n' 1 (⟨e.src.map ((Matrix.mulVecLin M).restrictScalars R.W),
      e.tgt.map ((Matrix.mulVecLin M).restrictScalars R.W)⟩ : Edge R.W R.Qq k) := by
  obtain ⟨⟨g1, hg1, hs⟩, ⟨g2, hg2, ht⟩, hle, hpm, hcard⟩ := he
  set f := (Matrix.mulVecLin M).restrictScalars R.W with hfdef
  have hfinj : Function.Injective f := by
    have h := (Matrix.mulVec_injective_iff_isUnit (A := M)).2 ((Matrix.isUnit_iff_isUnit_det M).2 hM)
    exact h
  refine ⟨⟨M * g1, by rw [Matrix.det_mul]; exact hM.mul hg1, by rw [hs]; exact colSpan_map_mulVecLin_eq_colSpan_mul R M g1⟩,
    ⟨M * g2, by rw [Matrix.det_mul]; exact hM.mul hg2, by rw [ht]; exact colSpan_map_mulVecLin_eq_colSpan_mul R M g2⟩,
    Submodule.map_mono hle, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨(p : R.W) • y, hpm y hy, map_smul f _ y⟩
  · rw [← hcard]
    let e0 := Submodule.equivMapOfInjective f hfinj e.tgt
    have hPQ : (Submodule.comap e.tgt.subtype e.src).map (e0 : e.tgt →ₗ[R.W] _) =
        Submodule.comap (e.tgt.map f).subtype (e.src.map f) := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.1, hy, rfl⟩
      · intro hz
        obtain ⟨y, hys, hyz⟩ := hz
        refine ⟨⟨y, hle hys⟩, hys, Subtype.ext ?_⟩
        exact hyz
    exact (Nat.card_congr (Submodule.Quotient.equiv _ _ e0 hPQ).toEquiv).symm

private theorem natCast_p_ne_zero_Qq (j : Fin k) : (p : R.Qq) ≠ 0 := by
  intro h0
  obtain ⟨g, hg, hgeq⟩ := (baseEdge R j).1
  have hker : colSpan R.W (dj j (p : R.Qq)) ≤
      LinearMap.ker ((LinearMap.proj j : (Fin k → R.Qq) →ₗ[R.Qq] R.Qq).restrictScalars R.W) := by
    rw [colSpan, Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    simp [dj, Matrix.diagonal_apply, h0]
  obtain ⟨c, hc⟩ : ∃ c, g j c ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hg.ne_zero (Matrix.det_eq_zero_of_row_eq_zero j hall)
  have hmem : (fun i => g i c) ∈ colSpan R.W (dj j (p : R.Qq)) := by
    have hgeq' : colSpan R.W (dj j (p : R.Qq)) = colSpan R.W g := hgeq
    rw [hgeq']
    exact Submodule.subset_span ⟨c, rfl⟩
  have h1 := hker hmem
  simp at h1
  exact hc h1

theorem edgeT (V : Matrix (Fin k) (Fin k) R.W) (hV : IsUnit V.det) (j : Fin k) :
    IsEdge p n' 1 (⟨colSpan R.W (mapM V * dj j (p : R.Qq)), colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq)⟩ :
      Edge R.W R.Qq k) := by
  have h := isEdge_map_mulVecLin_of_isUnit_det R (mapM V) (mapM_det_unit R V hV) _ (baseEdge R j)
  simp only [colSpan_map_mulVecLin_eq_colSpan_mul, mul_one, colSpan_mapM R V hV] at h
  exact h

theorem edgeS (V : Matrix (Fin k) (Fin k) R.W) (hV : IsUnit V.det) (j : Fin k) :
    IsEdge p n' 1 (⟨colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq), colSpan R.W (mapM V * dj j (p : R.Qq)⁻¹)⟩ :
      Edge R.W R.Qq k) := by
  have hp := natCast_p_ne_zero_Qq R j
  have hdet : IsUnit (mapM V * dj j (p : R.Qq)⁻¹).det := by
    rw [Matrix.det_mul, dj_det]
    exact (mapM_det_unit R V hV).mul (isUnit_iff_ne_zero.2 (inv_ne_zero hp))
  have h := isEdge_map_mulVecLin_of_isUnit_det R _ hdet _ (baseEdge R j)
  simp only [colSpan_map_mulVecLin_eq_colSpan_mul, mul_one, mul_assoc, dj_mul, inv_mul_cancel₀ hp, dj_one,
    colSpan_mapM R V hV] at h
  exact h

theorem transport (L : Submodule R.W (Fin k → R.Qq)) (hL : IsLattice R.W L) {Ne : ℕ}
    (es : Fin Ne → Edge R.W R.Qq k) (hinj : Function.Injective es) (hes : ∀ i, IsEdge p n' 1 (es i)) :
    ∃ es' : Fin Ne → Edge R.W R.Qq k, Function.Injective es' ∧ (∀ i, IsEdge p n' 1 (es' i)) ∧
      (∀ i, (es i).tgt = colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq) → (es' i).tgt = L) ∧
      (∀ i, (es i).src = colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq) → (es' i).src = L) := by
  obtain ⟨g, hg, rfl⟩ := hL
  set f := (Matrix.mulVecLin g).restrictScalars R.W with hfdef
  have hfinj : Function.Injective f :=
    (Matrix.mulVec_injective_iff_isUnit (A := g)).2 ((Matrix.isUnit_iff_isUnit_det g).2 hg)
  refine ⟨fun i => ⟨(es i).src.map f, (es i).tgt.map f⟩, ?_, fun i => isEdge_map_mulVecLin_of_isUnit_det R g hg _ (hes i), ?_, ?_⟩
  · intro i i' h
    apply hinj
    have h1 : (es i).src.map f = (es i').src.map f := congrArg Edge.src h
    have h2 : (es i).tgt.map f = (es i').tgt.map f := congrArg Edge.tgt h
    have e1 := Submodule.map_injective_of_injective hfinj h1
    have e2 := Submodule.map_injective_of_injective hfinj h2
    cases hi : es i
    cases hi' : es i'
    rw [hi, hi'] at e1 e2
    simp only at e1 e2
    rw [e1, e2]
  · intro i hi
    show (es i).tgt.map f = _
    rw [hi, colSpan_map_mulVecLin_eq_colSpan_mul, mul_one]
  · intro i hi
    show (es i).src.map f = _
    rw [hi, colSpan_map_mulVecLin_eq_colSpan_mul, mul_one]

end Tr

end Formalism.MainNotions.flipOneThree.Pf

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.ThrLPOf
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem TLP_pos (K : Cst) : 0 < K.TLP := by
  unfold Cst.TLP
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 108) (le_trans (le_max_left _ _) (le_max_left _ _))

theorem thrLP_of (hO : RestOddTops) (K : Cst) (hK : K.Pos) : TransportedAlt K (FactsLP K) := by
  have hK' := hK
  unfold Cst.Pos at hK'
  have hCt : 0 < K.Ct := hK'.2.2.2.2.2.2.2.1
  refine ⟨K.TLP, 4 * K.Ct + 4, TLP_pos K, by linarith, ?_⟩
  intro CH hCH C hC X h
  have B := base_of K hK CH hCH X h
  have h' := h
  unfold Dat.Hyp HypI at h'
  obtain ⟨-, -, -, -, -, -, hm, -, hb, -, -, -, -, -, -, -, -, -, -, -, -, -, hcs, -⟩ := h'
  have hd := dle_of hK hCH h B
  have hp := B.hp25
  exact
    { cst := hcs
      bpos := hb
      ppos := by exact_mod_cast (show (0 : ℝ) < X.p by linarith)
      m2 := by omega
      D1nn := D1nn_of hK B
      four_depth_lt_conductor := four_depth_lt_conductor_of_bounds hd hcs
      dle := hd
      a8 := second_moment_of_columns hCH B
      eps := eps_of hCH B
      lowa := lowa_of B
      lowb := lowb_of h
      tle := fun aw bw hw => tle_of hO hK hC h B aw bw hw }

theorem thrLP (K : Cst) (hK : K.Pos) : TransportedAlt K (FactsLP K) := by
  exact thrLP_of restOddTops K hK

end Formalism.MainNotions.flipOneThree.Pf

end
end

