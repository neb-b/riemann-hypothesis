module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0296
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitLatticeUnimodularAndPrimitive
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsEqOfStabilizerConjugateLattices
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0017
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalHyperbolicFrameAnisotropicMemSpanTrans
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St
variable {D : D7}

theorem crd_sum_smul (X : HidaSetting D) {ι : Type} [Fintype ι] (c : ι → X.B.I.E) (v : ι → (VS D).V) :
    X.crd (∑ k, X.ιE (c k) • v k) = fun i => ∑ k, c k * X.crd (v k) i := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [HidaSetting.crd, crdOf, map_sum, Finset.sum_apply, map_mul]

theorem crd_injective (X : HidaSetting D) : Function.Injective X.crd := by
  intro v w h
  apply X.bas.repr.injective
  ext i
  have := congrFun h i
  simp only [HidaSetting.crd, crdOf] at this
  rw [X.ιE.symm.injective this]

theorem orth_mem_span_qFr : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V),
    WittX X u wt → ∀ y : (VS D).V, (∀ a, (VS D).hT (X.eX a) y = 0 ∧ (VS D).hT (X.fY a) y = 0) →
    (VS D).hT (X.zu u) y = 0 → ∃ d : Fin (D.R.N 0) → D.host.E, Fintype.linearCombination D.host.E (qFr wt) d = y := by
  intro D X u wt hw y hef hz
  classical
  obtain ⟨Q, Qi, G', hQQi, hQiQ, hq, he, hf, hzc, -, -⟩ := qFrame_basis_gram D X u wt hw
  have hcol : ∀ k i, Q i k = X.crd (famQ X u wt k) i := by
    rintro (j | a | a | ⟨⟩) i
    · simp [famQ, hq]
    · simp [famQ, he, HidaSetting.eR]
    · simp [famQ, hf, HidaSetting.fR]
    · simp [famQ, hzc, HidaSetting.zR]
  set c := Qi *ᵥ X.crd y with hc
  have hy : y = ∑ k, X.ιE (c k) • famQ X u wt k := by
    apply crd_injective X
    rw [crd_sum_smul]
    have : Q *ᵥ c = X.crd y := by rw [hc, Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]
    rw [← this]
    funext i
    simp only [Matrix.mulVec, dotProduct, hcol]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type] at hy
  simp only [famQ, Sum.elim_inl, Sum.elim_inr, Fintype.univ_unit, Finset.sum_singleton] at hy
  have hqe : ∀ j b, (VS D).hT (X.eX b) (qFr wt j) = 0 := fun j b =>
    hT_symm_zero (hT_qFr_rest X u wt hw j (Sum.inl b))
  have hqf : ∀ j b, (VS D).hT (X.fY b) (qFr wt j) = 0 := fun j b =>
    hT_symm_zero (hT_qFr_rest X u wt hw j (Sum.inr (Sum.inl b)))
  have hqz : ∀ j, (VS D).hT (X.zu u) (qFr wt j) = 0 := fun j =>
    hT_symm_zero (hT_qFr_rest X u wt hw j (Sum.inr (Sum.inr ())))

  have c2 : ∀ b, X.ιE (c (Sum.inr (Sum.inr (Sum.inl b)))) = 0 := by
    intro b
    have h := (hef b).1
    rw [hy] at h
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_add (f := _), map_sum, hqe, X.ee, X.ef, (X.zu_orth u b).1] using h
  have c1 : ∀ b, X.ιE (c (Sum.inr (Sum.inl b))) = 0 := by
    intro b
    have h := (hef b).2
    rw [hy] at h
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_add (f := _), map_sum, hqf, X.ff, hT_fe, (X.zu_orth u b).2] using h
  have c3 : X.ιE (c (Sum.inr (Sum.inr (Sum.inr ())))) = 0 := by
    have h := hz
    rw [hy] at h
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_add (f := _), map_sum, hqz, hT_ze, hT_zf] at h
    rw [h.resolve_right (hT_zz_ne X u), map_zero]
  refine ⟨fun j => X.ιE (c (Sum.inl j)), ?_⟩
  rw [hy, Fintype.linearCombination_apply]
  simp [c1, c2, c3]

end GlobalTheory.St
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairIsScalarInUnipotentRadicalDoubleCoset
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SnFam.CvScal

variable {D : D7}

lemma mem_orth_iff' {U : Submodule D.host.E (VS D).V} {y : (VS D).V} :
    y ∈ orth (VS D) U ↔ ∀ x ∈ U, (VS D).hT x y = 0 := by
  simp [orth, Submodule.mem_iInf]

lemma orth_anti {U U' : Submodule D.host.E (VS D).V} (h : U ≤ U') : orth (VS D) U' ≤ orth (VS D) U := by
  intro y hy
  rw [mem_orth_iff'] at hy ⊢
  exact fun x hx => hy x (h hx)

lemma z_mem_orth {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) : F.fl.z ∈ orth (VS D) (Xsp F) := by
  rw [mem_orth_iff']
  intro x hx
  have hx' : x ∈ Submodule.span D.host.E (Set.range F.fl.e) := hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem x h => obtain ⟨a, rfl⟩ := h; exact F.fl.z_orth a
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

lemma Xsp_le_Xplus {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) : Xsp F ≤ Xplus F := by
  show F.fl.X ≤ F.fl.X ⊔ _
  exact le_sup_left

lemma Xa_of_ge {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) {j : ℕ} (h : D.R.rS ≤ j) :
    Xflag F j = Xsp F := by
  show F.fl.Xa j = F.fl.X
  unfold FlagG.Xa FlagG.X
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_range]
  constructor
  · rintro ⟨i, -, rfl⟩; exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩; exact ⟨i, lt_of_lt_of_le i.2 h, rfl⟩

lemma nrat_mapsTo {T : D.host.E} {F : LFlag (D.sp.Y 0) D.R.rS T} {n} (hn : n ∈ NRat F) :
    ∀ x ∈ Xsp F, n x ∈ Xsp F := by
  intro x hx
  have h1 := hn.2.1 D.R.rS x (by rw [Xa_of_ge F (Nat.le_succ _)]; exact hx)
  rw [Xa_of_ge F le_rfl] at h1
  simpa using add_mem h1 hx

lemma map_eq_self {U : Submodule D.host.E (VS D).V} [FiniteDimensional D.host.E U]
    (f : (VS D).V ≃ₗ[D.host.E] (VS D).V) (h : ∀ x ∈ U, f x ∈ U) :
    U.map (f : (VS D).V →ₗ[D.host.E] (VS D).V) = U :=
  Submodule.eq_of_le_of_finrank_eq (by rintro _ ⟨x, hx, rfl⟩; exact h x hx) (LinearEquiv.finrank_map_eq f U)

lemma fd_Xsp {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) : FiniteDimensional D.host.E (Xsp F) :=
  FiniteDimensional.span_of_finite _ (Set.finite_range _)

lemma nrat_map {T : D.host.E} {F : LFlag (D.sp.Y 0) D.R.rS T} {n} (hn : n ∈ NRat F) :
    (Xsp F).map (n : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp F :=
  haveI := fd_Xsp F
  map_eq_self n (nrat_mapsTo hn)

lemma sgRel_iff {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')
    (y y' : (VS D).V) (al al' : D.host.E) :
    SgRel F F' y y' al al' ↔ y - y' - (al • F.zt + al' • F'.zt) ∈ Xsp F ⊔ Xsp F' := by
  rw [Submodule.mem_sup]
  unfold SgRel
  constructor
  · rintro ⟨x, hx, x', hx', h⟩; exact ⟨x, hx, x', hx', by rw [h]; abel⟩
  · rintro ⟨x, hx, x', hx', h⟩
    refine ⟨x, hx, x', hx', ?_⟩
    have : y - y' = x + x' + (al • F.zt + al' • F'.zt) := by rw [h]; abel
    rw [this]; abel

end GlobalTheory.SnFam.CvScal

namespace GlobalTheory.SnFam.CvScal
variable {D : D7}

theorem pair_scalar (D : D7) {T T' : D.host.E} (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F : LFlag (D.sp.Y 0) D.R.rS T)
    (F' F'' : LFlag (D.sp.Y 0) D.R.rS T') (_hΛ : Submodule.IsLattice D.host.E Λ) (hF : F.zt = F.fl.z)
    (hF' : F'.zt = F'.fl.z) (hF'' : F''.zt = F''.fl.z) (n) (hn : n ∈ NRat F) (m) (hm : m ∈ NRat F')
    (hfr : ∀ a, frame F'' a = (n * m) (frame F' a)) : IsScalar Λ F F' F'' (n * m) := by
  have hnm : ∀ v, (n * m) v = n (m v) := fun v => rfl
  have he : ∀ a, F''.fl.e a = n (m (F'.fl.e a)) := by
    intro a
    have := hfr (Fin.castSucc a)
    simpa [frame, FlagG.fvec, Fin.snoc_castSucc, hnm] using this
  have hz : F''.fl.z = n (m F'.fl.z) := by
    have := hfr (Fin.last _)
    simpa [frame, FlagG.fvec, Fin.snoc_last, hnm] using this

  have hX'' : Xsp F'' = (Xsp F').map (n : (VS D).V →ₗ[D.host.E] (VS D).V) := by
    have h1 : Xsp F'' = (Xsp F').map ((n : (VS D).V →ₗ[D.host.E] (VS D).V) ∘ₗ (m : (VS D).V →ₗ[D.host.E] (VS D).V)) := by
      show Submodule.span _ _ = Submodule.map _ (Submodule.span _ _)
      rw [Submodule.map_span, ← Set.range_comp]
      congr 2
      funext a
      exact he a
    rw [h1, Submodule.map_comp, nrat_map hm]
  have hsup : (Xsp F ⊔ Xsp F').map (n : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp F ⊔ Xsp F'' := by
    rw [Submodule.map_sup, nrat_map hn, hX'']
  have nX' : ∀ v ∈ Xsp F', n v ∈ Xsp F'' := fun v hv => hX'' ▸ Submodule.mem_map_of_mem hv
  intro y1 hy1 y2 _ y1' hy1' y2'' _ h12 h12' al al'
  rw [sgRel_iff, sgRel_iff, hF, hF', hF'']
  have oy1 : y1 ∈ orth (VS D) (Xsp F) := orth_anti (Xsp_le_Xplus F) hy1.2
  have oy1' : y1' ∈ orth (VS D) (Xsp F') := orth_anti (Xsp_le_Xplus F') hy1'.2
  have A : y2 - n y1 ∈ Xsp F := by
    have := add_mem h12 (hn.2.2 y1 oy1)
    rw [← neg_mem_iff]; convert this using 1; abel
  have B : y2'' - n y1' ∈ Xsp F'' := by
    have := add_mem h12' (nX' _ (hm.2.2 y1' oy1'))
    convert this using 1; rw [hnm, map_sub]; abel
  have C : F.fl.z - n F.fl.z ∈ Xsp F := by
    have := hn.2.2 _ (z_mem_orth F)
    rw [← neg_mem_iff]; convert this using 1; abel
  have Dd : F''.fl.z - n F'.fl.z ∈ Xsp F'' := by
    have := nX' _ (hm.2.2 _ (z_mem_orth F'))
    convert this using 1; rw [hz, map_sub]
  set d1 := y1 - y1' - (al • F.fl.z + al' • F'.fl.z) with hd1
  set d2 := y2 - y2'' - (al • F.fl.z + al' • F''.fl.z) with hd2
  have key : d2 = n d1 + ((y2 - n y1) - (y2'' - n y1') - al • (F.fl.z - n F.fl.z) - al' • (F''.fl.z - n F'.fl.z)) := by
    simp only [hd1, hd2, map_sub, map_add (f := _), map_smul, smul_sub]; abel
  have kmem : (y2 - n y1) - (y2'' - n y1') - al • (F.fl.z - n F.fl.z) - al' • (F''.fl.z - n F'.fl.z) ∈ Xsp F ⊔ Xsp F'' :=
    sub_mem (sub_mem (sub_mem (Submodule.mem_sup_left A) (Submodule.mem_sup_right B))
      (Submodule.smul_mem _ _ (Submodule.mem_sup_left C))) (Submodule.smul_mem _ _ (Submodule.mem_sup_right Dd))
  rw [key, Submodule.add_mem_iff_left _ kmem, ← hsup]
  constructor
  · intro h; exact Submodule.mem_map_of_mem h
  · rintro ⟨w, hw, hw'⟩
    have : w = d1 := n.injective hw'
    exact this ▸ hw

end GlobalTheory.SnFam.CvScal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ParameterSizeConstraints
section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeAsm

theorem pairsPar : ∀ (Ca Cg cb Cw cT CT C0 C' Cl : ℝ) (D : D7) (large₂ : SizeData₂ D), HostC →
    Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → 1 ≤ C' → 1 ≤ Cl → CT ≤ Ca →
    Module.finrank ℚ D.host.E = 2 * Formalism.HermitianLatticesTheory.fDeg D.host.E ∧ D.R.m = 2 * D.R.rS + 2 ∧ Cl ≤ (D.R.m : ℝ) ∧
    D.R.m ^ 4 ≤ Formalism.HermitianLatticesTheory.fDeg D.host.E ∧ D.R.m ^ 5 * Formalism.HermitianLatticesTheory.fDeg D.host.E ≤ D.R.k ∧
    Cl * ((D.R.m : ℝ) ^ 2 * Real.log large₂.sc.b) ≤ D.R.k ∧ Real.log (Formalism.HermitianLatticesTheory.fDeg D.host.E : ℝ) ≤ Real.sqrt D.R.rS ∧
    2 ≤ large₂.sc.b ∧ 1 ≤ Formalism.HermitianLatticesTheory.vInv D.host.E ∧ 2 * Formalism.HermitianLatticesTheory.vInv D.host.E ≤ large₂.sc.b ∧
    ((D.R.k : ℝ) * large₂.sc.b) ^ 8 ≤ (Formalism.MainNotions.S.Lat.gS D : ℝ) ∧
    ∀ u : D.what₂.Word, 1 ≤ Tu D u ∧ (Tu D u : ℝ) ≤ large₂.sc.b ^ (Ca * (D.R.m : ℝ)) := by
  intro Ca Cg cb Cw cT CT C0 C' Cl D large₂ hH hK hC' hCl hCa
  have hStd : Std D large₂ := ⟨C', Cl, Cg, cb, Cw, cT, CT, C0, hK⟩
  obtain ⟨_, _, hvI, hv1, hf, _, hfin, _, _, _, _, hg2, hT⟩ := hH D large₂ hStd
  obtain ⟨⟨hS0, _, _⟩, _⟩ := hK
  obtain ⟨_, h2, h3, _, h5, _, h7, _, _, _, h11, h12, _, _, _, _, _, _, _, _, _, _, h23, h24, h25⟩ := hS0
  have hL : 1 < large₂.sc.L := one_lt_scale_L D large₂
  have hb2 : 2 ≤ large₂.sc.b := two_le_scale_b D large₂
  have hlb : Real.log large₂.sc.b = large₂.sc.L := log_scale_eq_L D large₂
  refine ⟨by rw [hfin, hf], (two_rank_add_two_eq_m D).symm, h24, by rw [hf]; exact h3, ?_, by rw [hlb]; exact h7,
    by rw [hf]; exact h5, hb2, by rw [hvI]; exact hv1, ?_, ?_, ?_⟩
  · rw [hf]
    have hm : (0 : ℝ) ≤ (D.R.m : ℝ) ^ 5 * D.R.f := by positivity
    have : ((D.R.m ^ 5 * D.R.f : ℕ) : ℝ) ≤ D.R.k := by
      push_cast
      calc (D.R.m : ℝ) ^ 5 * D.R.f = 1 * ((D.R.m : ℝ) ^ 5 * D.R.f) * 1 := by ring
        _ ≤ C' * ((D.R.m : ℝ) ^ 5 * D.R.f) * large₂.sc.L := by gcongr <;> linarith
        _ = C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by ring
        _ ≤ D.R.k := h2
    exact_mod_cast this
  · rw [hvI]
    have hrd : 0 < D.host.rdE := pf_rd_pos D
    have hL0 : 0 < large₂.sc.L := by linarith
    have h1 : Real.log D.host.rdE ≤ large₂.sc.L := by
      refine h11.trans ?_
      rw [div_le_iff₀ h25]; nlinarith
    have h2v : 2 * D.host.v = D.host.rdE := by
      show 2 * (D.host.rdE / 2) = D.host.rdE; ring
    rw [h2v]
    calc D.host.rdE = Real.exp (Real.log D.host.rdE) := (Real.exp_log hrd).symm
      _ ≤ Real.exp large₂.sc.L := Real.exp_le_exp.2 h1
      _ = large₂.sc.b := by rw [← hlb, Real.exp_log (by linarith)]
  · have hg1 : 1 ≤ D.host.g 1 := by
      rcases Nat.eq_zero_or_pos (D.host.g 1) with h | h
      · have : Formalism.MainNotions.S.Lat.gS D = 0 := by simp [Formalism.MainNotions.S.Lat.gS, h]
        omega
      · exact h
    calc ((D.R.k : ℝ) * large₂.sc.b) ^ 8 ≤ (D.host.g 0 : ℝ) := h12
      _ = (D.host.g 0 : ℝ) * 1 := (mul_one _).symm
      _ ≤ (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) := by gcongr; exact_mod_cast hg1
      _ = (Formalism.MainNotions.S.Lat.gS D : ℝ) := by simp [Formalism.MainNotions.S.Lat.gS]
  · intro u
    refine ⟨(hT u).1.one_lt.le, ?_⟩
    have h := (h23 u).2
    calc (Tu D u : ℝ) = Tr D u := rfl
      _ ≤ large₂.sc.b ^ (CT * (D.R.m : ℝ)) := h
      _ ≤ large₂.sc.b ^ (Ca * (D.R.m : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by linarith)
        have : (0 : ℝ) ≤ D.R.m := by positivity
        nlinarith

end GlobalTheory.TypeAsm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PartsOfLat
section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowsOrb.Parts
open GlobalTheory.RowsOrb.Uniq

variable {D : D7} (X : HidaSetting D)

theorem lsS_le {r : ℕ} (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)
    (v : Fin r → (VS D).V) {y : (VS D).V} (hy : y ∈ latSpanS aa v) :
    y ∈ Submodule.span D.host.E (Set.range v) := by
  have hle : latSpanS aa v ≤ (Submodule.span D.host.E (Set.range v)).restrictScalars (𝓞 D.host.E) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, x, -, rfl⟩
    exact Submodule.smul_mem _ x (Submodule.subset_span ⟨a, rfl⟩)
  exact hle hy

theorem Xsp_eq (u : D.what₂.Word) : Xsp (lf D (X.Fu u)) = Submodule.span D.host.E (Set.range X.eX) := by
  show Submodule.span D.host.E (Set.range (X.Fu u).e) = _
  rw [X.Fu_e]

theorem XS_eq (u : D.what₂.Word) : XS D (X.Fu u) = latSpanS (fun a => aaD D a) X.eX := by
  simp only [XS, latSpanS, aaD, X.Fu_e]

theorem xlam_split (u : D.what₂.Word) (M : Submodule (𝓞 D.host.E) (VS D).V)
    (hM : ∀ x ∈ M, ∀ a, (VS D).hT (X.eX a) x = 0 ∧ (VS D).hT (X.fY a) x = 0) :
    XLam (latSpanS (fun a => aaD D a) X.eX ⊔ M ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) (lf D (X.Fu u)) =
      XS D (X.Fu u) := by
  rw [XS_eq]
  show _ ⊓ toO (VS D) (Xsp (lf D (X.Fu u))) = _
  rw [Xsp_eq]
  refine le_antisymm ?_ (le_inf (le_sup_left.trans le_sup_left) fun y hy => lsS_le _ _ hy)
  rintro y ⟨hyΛ, hyX⟩
  have hyX' : y ∈ Submodule.span D.host.E (Set.range X.eX) := hyX
  obtain ⟨y1, hy1, b, hb, rfl⟩ := Submodule.mem_sup.mp hyΛ
  obtain ⟨a, ha, m, hm, rfl⟩ := Submodule.mem_sup.mp hy1
  have haX := lsS_le _ _ ha
  have hbY := lsS_le _ _ hb

  have hb0 : b = 0 := by
    have hpair : ∀ c, (VS D).hT (X.eX c) b = 0 := by
      intro c
      have h1 := orth_span (fun d => X.ee c d) hyX'
      have h2 := orth_span (fun d => X.ee c d) haX
      rw [map_add (f := _), map_add (f := _), h2, (hM m hm c).1, zero_add, zero_add] at h1
      exact h1
    rw [coord X.ef hbY]
    simp [hpair]
  subst hb0
  rw [add_zero] at hyX' ⊢

  have hmX : m ∈ Submodule.span D.host.E (Set.range X.eX) := by
    have := Submodule.sub_mem _ hyX' haX
    rwa [add_sub_cancel_left] at this
  have hm0 : m = 0 := by
    rw [coord (dual_symm GlobalTheory.RowsOrb.Uniq.hh X.ef) hmX]
    simp [(hM m hm _).2]
  rw [hm0, add_zero]
  exact ha

theorem map_perp (L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X)) :
    ∀ x ∈ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)), ∀ a,
      (VS D).hT (X.eX a) x = 0 ∧ (VS D).hT (X.fY a) x = 0 := by
  intro x hx a
  obtain ⟨w, -, rfl⟩ := Submodule.mem_map.mp hx
  exact (GlobalTheory.RowsOrb.mem_Wb X (w : (VS D).V)).mp w.2 a

theorem lmap_eq (u : D.what₂.Word) (L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X)) :
    GlobalTheory.RowsOrb.Lmap X u (latSpanS (fun a => aaD D a) X.eX ⊔
      L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔
      latSpanS (fun a => (aaD D a)⁻¹) X.fY) = L := by
  ext w
  rw [lmap_char X u (latSpanS (fun a => aaD D a) X.eX ⊔
      L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔
      latSpanS (fun a => (aaD D a)⁻¹) X.fY) (fun a => aaD D a) (fun a => (aaD D a)⁻¹) X.ef (map_perp X L)
      rfl w]
  constructor
  · rintro ⟨l, hl, hP⟩
    obtain ⟨w', hw', rfl⟩ := Submodule.mem_map.mp hl
    have hfix : P (VS D).hT X.eX X.fY (w' : (VS D).V) = w' := by
      rw [P_apply]
      simp [((GlobalTheory.RowsOrb.mem_Wb X (w' : (VS D).V)).mp w'.2 _).2]
    have : w' = w := Subtype.ext (hfix.symm.trans hP)
    exact this ▸ hw'
  · intro hw
    refine ⟨(w : (VS D).V), Submodule.mem_map_of_mem hw, ?_⟩
    rw [P_apply]
    simp [((GlobalTheory.RowsOrb.mem_Wb X (w : (VS D).V)).mp w.2 _).2]

end GlobalTheory.RowsOrb.Parts


open GlobalTheory.RowsOrb.Parts in
theorem GlobalTheory.RowsOrb.parts_of_lat : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X)), XLam (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) (lf D (X.Fu u)) = XS D (X.Fu u) ∧ XLam (VS D).L0 (lf D (X.Fu u)) = XS D (X.Fu u) ∧ GlobalTheory.RowsOrb.Lmap X u (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) = L ∧ ∀ w : GlobalTheory.RowsOrb.Wb X, (w : (VS D).V) ∈ Lsub (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) (lf D (X.Fu u)) → w ∈ L := by
  intro D X u L
  refine ⟨xlam_split X u _ (map_perp X L), ?_, lmap_eq X u L, ?_⟩
  · rw [X.Lam_split]
    exact xlam_split X u X.Lb X.Lb_perp
  · intro w hw
    rw [Lsub, Submodule.mem_inf] at hw
    have hX : toO (VS D) (Xsp (lf D (X.Fu u))) =
        GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X := by
      rw [GlobalTheory.RowsOrb.Uniq.fixedFrameOfWord_isotropicSpan_eq, Xsp_eq]
    have hmem : w ∈ GlobalTheory.RowsOrb.Lmap X u (latSpanS (fun a => aaD D a) X.eX ⊔
        L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔
        latSpanS (fun a => (aaD D a)⁻¹) X.fY) :=
      (GlobalTheory.RowsOrb.mem_Lmap X u _ w).mpr ((sup_le_sup inf_le_left hX.le) hw.1)
    rwa [lmap_eq X u L] at hmem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryExtendByIdentityOnFixSet
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.St

theorem col_mul_eq_mulVec {A : Type} [CommRing A] {n ι κ : Type} [Fintype n] [Fintype ι]
    (M : Matrix n ι A) (B : Matrix ι κ A) (c : κ) :
    M *ᵥ (fun i => B i c) = fun i => (M * B) i c := by
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]

theorem rational_unitary_extend_by_identity : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∀ y₀ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) X.B.I.E, (y₀.map (starRingEnd X.B.I.E))ᵀ * (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm * y₀ = (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm → ∃ γ₀ : GL (Fin X.B.I.n) X.B.I.E, γ₀ ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J ∧ (∀ x ∈ fixSet X u, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ x = x) ∧ ∀ j, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd (qFr wt j) = ∑ i, y₀ i j • X.crd (qFr wt i) := by
  intro D X u wt hw y₀ hy
  obtain ⟨Q, Qi, G', hQQi, hQiQ, hq, he, hf, hz, hG', hblk⟩ := _root_.GlobalTheory.St.qFrame_basis_gram D X u wt hw
  have hU := (GlobalTheory.unitary_stabiliser_orthogonal_summand X.B.I.E (starRingEnd X.B.I.E) _ _ _ X.B.I.J
    ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm) G' Q Qi hQQi hQiQ hblk hG').1 y₀ hy
  set M := Q * Matrix.fromBlocks y₀ 0 0 (1 : Matrix (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) X.B.I.E) * Qi with hM
  have hJu : IsUnit X.B.I.J.det := isUnit_iff_ne_zero.2 X.B.I.J_det
  have hdet : IsUnit M.det := by
    refine Matrix.isUnit_det_of_left_inverse (B := X.B.I.J⁻¹ * ((M.map (starRingEnd X.B.I.E))ᵀ * X.B.I.J)) ?_
    rw [Matrix.mul_assoc, hU, Matrix.nonsing_inv_mul _ hJu]
  have hMu : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 hdet
  have hMQ : M * Q = Q * Matrix.fromBlocks y₀ 0 0 1 := by
    rw [hM, Matrix.mul_assoc, hQiQ, Matrix.mul_one]
    rfl
  refine ⟨hMu.unit, ?_, ?_, ?_⟩
  · show Formalism.UG.cT (starRingEnd X.B.I.E) (hMu.unit : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) * X.B.I.J * (hMu.unit : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = X.B.I.J
    rw [IsUnit.unit_spec]
    exact hU
  · intro x hx
    rw [IsUnit.unit_spec]
    have key : ∀ b, M *ᵥ (fun i => Q i (Sum.inr b)) = fun i => Q i (Sum.inr b) := by
      intro b
      rw [col_mul_eq_mulVec, hMQ]
      funext i
      erw [Matrix.mul_apply, Fintype.sum_sum_type]
      simp only [Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, zero_add, Matrix.one_apply, mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rcases hx with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hz'
    · have := key (Sum.inl a)
      have e : (fun i => Q i (Sum.inr (Sum.inl a))) = X.eR a := funext fun i => he a i
      rwa [e] at this
    · have := key (Sum.inr (Sum.inl a))
      have e : (fun i => Q i (Sum.inr (Sum.inr (Sum.inl a)))) = X.fR a := funext fun i => hf a i
      rwa [e] at this
    · rw [Set.mem_singleton_iff] at hz'
      subst hz'
      have := key (Sum.inr (Sum.inr ()))
      have e : (fun i => Q i (Sum.inr (Sum.inr (Sum.inr ())))) = X.zR u := funext fun i => hz i
      rwa [e] at this
  · intro j
    rw [IsUnit.unit_spec]
    have e : ∀ j, X.crd (qFr wt j) = fun i => Q i (Sum.inl j) := fun j => funext fun i => (hq j i).symm
    rw [e j, col_mul_eq_mulVec, hMQ]
    funext r
    simp only [e, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
    erw [Matrix.mul_apply, Fintype.sum_sum_type]
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end GlobalTheory.St
end
end

