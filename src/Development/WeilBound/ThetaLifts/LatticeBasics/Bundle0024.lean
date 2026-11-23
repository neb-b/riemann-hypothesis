module

public import Development.WeilBound.ThetaLifts.LatticeBasics.MemLam
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0010
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0013
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.PfDict
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0191
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0022
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0008
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDict

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.NearUnits
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.SplitFlip PositivityTheory.KCo PositivityTheory.ThK.SplitDict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace Bmp

theorem near_units {A : Type} [Monoid A] [TopologicalSpace A] {U : Set Aˣ} (hU : U ∈ 𝓝 (1 : Aˣ)) :
    ∀ᶠ p in 𝓝 ((1, 1) : A × A), ∀ g : Aˣ, g.1 = p.1 → (g⁻¹).1 = p.2 → g ∈ U := by
  rw [Units.isInducing_embedProduct.nhds_eq_comap] at hU
  obtain ⟨V, hV, h⟩ := hU
  have c : Continuous fun p : A × A => (p.1, MulOpposite.op p.2) := continuous_fst.prodMk (MulOpposite.continuous_op.comp continuous_snd)
  filter_upwards [c.continuousAt.preimage_mem_nhds (x := (1, 1)) hV] with p hp g h1 h2
  exact h (show (g.1, MulOpposite.op (g⁻¹).1) ∈ V by rw [h1, h2]; exact hp)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {t : E →ₐ[F] Fv F v} {sec : Fv F v × Fv F v → AE F E} {n d : ℕ}

theorem near_UA (h : PositivityTheory.KCo.IsSec σ t sec) {X : Spc F E n} (hu : IsUnit ((incM F X.J).map (piW t))) {U : Set (UA σ X.J)} (hU : U ∈ 𝓝 1) :
    ∀ᶠ p in 𝓝 ((1, 1) : Matrix (Fin n) (Fin n) (Fv F v) × Matrix (Fin n) (Fin n) (Fv F v)), ∀ g ∈ UAt σ X (evFin F v),
      (mat g).map (piW t) = p.1 → (mat g⁻¹).map (piW t) = p.2 → g ∈ U := by
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul _ _
  obtain ⟨U', h1, h2⟩ := (mem_nhds_subtype _ _ _).1 hU
  obtain ⟨A, hA⟩ := hu
  have cs : Continuous (sgl v : Fv F v → AF F) := (continuous_const.prodMk (continuous_singleFin v) : Continuous fun a => ((0 : Ainf F), singleFin v a))
  let S : Matrix (Fin n) (Fin n) (Fv F v) → Matrix (Fin n) (Fin n) (Fv F v) → Matrix (Fin n) (Fin n) (AE F E) := fun p q =>
    1 + of fun i j => sgl v ((p - 1) i j) • sec (1, 0) + sgl v (((A⁻¹).1 * qᵀ * A.1 - 1) i j) • sec (0, 1)
  have cS : Continuous fun p : _ × _ => S p.1 p.2 := continuous_const.add (continuous_matrix fun i j =>
    ((cs.comp ((continuous_fst.sub continuous_const).matrix_elem i j)).smul continuous_const).add
    ((cs.comp ((((continuous_const.matrix_mul continuous_snd.matrix_transpose).matrix_mul continuous_const).sub
      continuous_const).matrix_elem i j)).smul continuous_const))
  have S1 : S 1 1 = 1 := by ext i j; simp [S]
  have eS : ∀ g : UA σ X.J, At (evFin F v) (mat g - 1) → mat g = S ((mat g).map (piW t)) ((mat g⁻¹).map (piW t)) := fun g hg => by
    refine h.extM ?_ ?_ ?_
    · rw [← sub_sub]
      exact hg.kd_sub (kd_at_matrix.2 fun i j => (at_sgl_smul _ _).kd_add (at_sgl_smul _ _))
    · ext i j
      by_cases hij : i = j <;> simp [S, (h.smul _ _).1, h.fst, ev_sgl, hij, map_sub]
    · have e1 := h.unit_rel g
      have e2 : ((mat g⁻¹).map (piW t))ᵀ * ((mat g).map (piW t))ᵀ = 1 := by
        rw [← transpose_mul, ← Matrix.map_mul, show mat g * mat g⁻¹ = 1 from g.1.mul_inv, Matrix.map_one _ (map_zero _) (map_one _),
          transpose_one]
      have e3 : (mat g).map (piW (t.comp σ)) = (A⁻¹).1 * ((mat g⁻¹).map (piW t))ᵀ * A.1 := by
        rw [← hA] at e1
        conv_rhs => rw [← e1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ _ (_)ᵀ]
        erw [e2]
        rw [Matrix.mul_one, Units.inv_mul, Matrix.one_mul]
        rfl
      rw [e3]
      ext i j
      by_cases hij : i = j <;> simp [S, (h.smul _ _).2, h.snd, ev_sgl, hij, map_sub]
  have c2 := cS.prodMk (cS.comp continuous_swap)
  filter_upwards [(c2.tendsto' (1, 1) (1, 1) (by simp [S1])).eventually (near_units h1)] with p hp g hg e1 e2
  have hg' : At (evFin F v) (mat g⁻¹ - 1) := by
    rw [show mat g⁻¹ - 1 = -mat g⁻¹ * (mat g - 1) by
      rw [mul_sub, neg_mul, show mat g⁻¹ * mat g = 1 from g.1.inv_mul]; simp [neg_add_eq_sub]]
    exact At.kd_mul_left hg _
  refine h2 (hp g.1 ((eS g hg).trans (by rw [e1, e2])) ((eS g⁻¹ hg').trans (by rw [inv_inv, e1, e2]; rfl)))

theorem exists_level {P : Matrix (Fin n) (Fin n) (Fv F v) × Matrix (Fin n) (Fin n) (Fv F v) → Prop} (hP : ∀ᶠ p in 𝓝 (1, 1), P p) :
    ∃ a : v.adicCompletionIntegers F, a ≠ 0 ∧ a ∈ IsLocalRing.maximalIdeal _ ∧
      ∀ p q, p - 1 ∈ lam (Fv F v) a n n → q - 1 ∈ lam (Fv F v) a n n → P (p, q) := by
  have := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  have : CompactSpace (Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F)) := inferInstanceAs (CompactSpace (_ → _ → _))
  obtain ⟨w, w1, w0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (IsDiscreteValuationRing.not_a_field (v.adicCompletionIntegers F))
  have cm : Continuous fun α : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F) => α.map (algebraMap _ (Fv F v)) :=
    continuous_id.matrix_map continuous_subtype_val
  have h1 : ∀ᶠ a : Fv F v in 𝓝 0, ∀ y ∈ (Set.univ : Set (Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F) × Matrix _ _ _)),
      P (a • y.1.map (algebraMap _ _) + 1, a • y.2.map (algebraMap _ _) + 1) :=
    isCompact_univ.eventually_forall_of_forall_eventually fun y _ =>
      ((((continuous_fst.smul (cm.comp (continuous_fst.comp continuous_snd))).add continuous_const).prodMk
        ((continuous_fst.smul (cm.comp (continuous_snd.comp continuous_snd))).add continuous_const)).tendsto' (0, y) (1, 1)
        (by simp)).eventually hP
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((Valued.tendsto_zero_pow_of_v_lt_one (x := (w : Fv F v)) ((Valuation.mem_maximalIdeal_iff _ _).1 w1)).eventually h1)
  refine ⟨w ^ (N + 1), pow_ne_zero _ w0, Ideal.pow_mem_of_mem _ w1 _ N.succ_pos, fun p q ⟨α, hα⟩ ⟨β, hβ⟩ => ?_⟩
  exact (eq_add_of_sub_eq hα.symm) ▸ (eq_add_of_sub_eq hβ.symm) ▸ hN (N + 1) N.le_succ (α, β) trivial

theorem ind_mem {a : v.adicCompletionIntegers F} (ha : a ≠ 0) (Y₀ : Matrix (Fin n) (Fin d) (Fv F v)) :
    (fun Y => Set.indicator (lam (Fv F v) a n d : Set _) (fun _ => (1 : ℂ)) (Y - Y₀)) ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)) := by
  have := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  have : CompactSpace (Matrix (Fin n) (Fin d) (v.adicCompletionIntegers F)) := inferInstanceAs (CompactSpace (_ → _ → _))
  have ha' : (a : Fv F v) ≠ 0 := fun h => ha (Subtype.ext h)
  have op : IsOpen ((lam (Fv F v) a n d).toAddSubgroup : Set (Matrix (Fin n) (Fin d) (Fv F v))) := by
    have o : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
    have e : ∀ᶠ Y in 𝓝 (0 : Matrix (Fin n) (Fin d) (Fv F v)), ∀ i j, (a : Fv F v)⁻¹ * Y i j ∈ v.adicCompletionIntegers F :=
      eventually_all.2 fun i => eventually_all.2 fun j => by
        have c : Continuous fun Y : Matrix (Fin n) (Fin d) (Fv F v) => (a : Fv F v)⁻¹ * Y i j :=
          continuous_const.mul (continuous_id.matrix_elem i j)
        exact (c.tendsto' 0 0 (by simp)).eventually (o.mem_nhds (zero_mem _))
    refine AddSubgroup.isOpen_of_mem_nhds _ (g := 0) (e.mono fun Y hY => mem_lam.2 ⟨fun i j => ⟨_, hY i j⟩, ?_⟩)
    exact Matrix.ext fun i j => mul_inv_cancel_left₀ ha' _
  have hf := GlobalTheory.WeilM.HaarUniq.indicator_mem ⟨_, op⟩ (isCompact_range
    (f := fun α : Matrix (Fin n) (Fin d) (v.adicCompletionIntegers F) => (a : Fv F v) • α.map (algebraMap _ (Fv F v)))
    (continuous_matrix fun i j => continuous_const.mul (continuous_subtype_val.comp (continuous_id.matrix_elem i j))))
  exact ⟨hf.1.comp_continuous (Homeomorph.subRight Y₀).continuous, hf.2.comp_homeomorph (Homeomorph.subRight Y₀)⟩

end Bmp

open Bmp in
theorem bump : Bump := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp hnd v hv
  obtain ⟨t⟩ : Nonempty (E →ₐ[F] Fv F v) := ⟨B.τ ⟨v, hv⟩⟩
  obtain ⟨⟨ι, hι⟩, -, -, k⟩ := dictX F E σ n d B X W M om χX χW hp.base ⟨_, _, hp.herm⟩ ⟨_, _, hp.skew⟩ hp.weil v t
  obtain ⟨⟨sec, h⟩, hsm⟩ := section_statement F E σ hp.base.cm v t
  have hG := grams h hp.herm hp.skew
  have hopen : IsOpen (Euler.intGrp σ X v : Set (UA σ X.J)) := by
    first
    | exact Euler.isOpen_int (Euler.herm_full hp.herm) v
    | exact Euler.isOpen_int hp.herm.lat v
  have n1 := near_UA h hG.uA (hopen.mem_nhds (one_mem _))
  have hv1 : ∀ᶠ y in 𝓝 (1 : Fv F v), ValuativeRel.valuation (Fv F v) y = 1 := by
    simpa [Filter.Eventually] using (ValuativeRel.valuation (Fv F v)).locally_const (x := 1) (by simp)
  have n2 := near_units (A := Matrix (Fin n) (Fin n) (Fv F v))
    (U := {g | chrW χW t (gdet g) = 1 ∧ ValuativeRel.valuation (Fv F v) (gdet g : Fv F v) = 1})
    (Eventually.and ((GeneralLinearGroup.continuous_det.tendsto' 1 1 (map_one _)).eventually
      ((hsm χW hp.hW).2.mem_nhds (one_mem _)))
      (((Units.continuous_val.comp GeneralLinearGroup.continuous_det).tendsto' 1 1 (by simp)).eventually hv1))
  obtain ⟨a, a0, a1, ha⟩ := exists_level (((continuous_fst.matrix_transpose.prodMk continuous_snd.matrix_transpose).tendsto'
    (1, 1) (1, 1) (by simp)).eventually (n1.and n2))
  let y : Matrix (Fin n) (Fin d) (v.adicCompletionIntegers F) := (1 : Matrix (Fin d) (Fin d) _).submatrix (Fin.castLE hnd) id
  have hy : y * yᵀ = 1 := by
    rw [transpose_submatrix, transpose_one, ← submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.one_mul,
      submatrix_one _ (Fin.castLE_injective hnd)]
  obtain ⟨Y₀, hY₀⟩ : ∃ Y₀, Y₀ = y.map (algebraMap _ (Fv F v)) := ⟨_, rfl⟩
  obtain ⟨φ, hφ, e⟩ := hι.bij.2.2 (ind_mem a0 Y₀)
  have mult : ∀ u, At (evFin F v) u → u.map (piW (t.comp σ)) = 0 → ∀ c : ℂ, (∀ Y, Y - Y₀ ∈ lam (Fv F v) a n d →
      psiV B.ψ v (trace (Yᵀ * -u.map (piW t))) = c) → Acts (evFin F v) (M.co.rho B.ψ u) φ (c • φ) := fun u hu h0 c hc => by
    have ac := PositivityTheory.KCo.adjoint_statement.Heisenberg₂ F _ B.ψ v _ (hu.kd_map M.co.e.toLinearMap) φ
    have mem := schr_mem ((PositivityTheory.KCo.adjoint_statement.psi F _ hp.base.std).2 v).1 (locW v (M.co.e.toLinearMap u)) hφ
    rw [← hι.bij.2.1 mem ((SB _).smul_mem c hφ) (funext fun Y => ?_)]
    · exact ac
    obtain ⟨x, hx, hcx, -⟩ := exists_coord h hG (ofM Y, 0)
    have := hι.mult u hu h0 φ hφ _ mem ac x hx (coord_snd.1 (congrArg Prod.snd hcx))
    rw [co_eq h, symp_eq h hG hx, hcx, dotProduct_zero, sub_zero, toM_ofM] at this
    rw [this, map_smul, Pi.smul_apply, smul_eq_mul, e]
    by_cases hY : Y - Y₀ ∈ lam (Fv F v) a n d
    · rw [← hc Y hY, ← dot_ofM]; rfl
    · simp [Set.indicator_of_notMem hY]
  refine ⟨φ, hφ, fun h0 => ?_, fun g hg => ?_⟩
  · have := congrFun e Y₀
    simp [h0] at this
  let g₀ := GeneralLinearGroup.map (piW t) g.1
  rcases dich (O := v.adicCompletionIntegers F) (psiV B.ψ v) (fun x => ⟨fun H => ⟨⟨x, (hp.base.psiP v hv x).1 fun z hz => H ⟨z, hz⟩⟩, rfl⟩,
    fun ⟨o, ho⟩ z => (hp.base.psiP v hv x).2 (ho ▸ o.2) z z.2⟩) a0 a1 y _ hy (invT g₀)⁻¹ with ⟨h1, h2⟩ | ⟨l, h1, h2⟩
  · obtain ⟨b1, b2⟩ := ha _ _ h1 h2
    obtain ⟨b2, b3⟩ := b2 g₀ rfl rfl
    obtain ⟨φ₁, m1, ac, e1⟩ := (k ι hι).1 g hg g₀ rfl φ hφ
    have key : ∀ Y, g₀.1ᵀ * Y - Y₀ ∈ lam (Fv F v) a n d ↔ Y - Y₀ ∈ lam (Fv F v) a n d := fun Y => by
      refine ⟨fun H => ?_, fun H => hY₀ ▸ keep h1 y (hY₀ ▸ H)⟩
      have := keep h2 y (hY₀ ▸ H)
      rwa [show g₀.1ᵀ = ((invT g₀)⁻¹).1 from rfl, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, ← hY₀] at this
    have e2 : ι φ₁ = ι φ := e1.trans (funext fun Y => by
      clear b1 ha k n1 n2 mult
      rw [omB, b2, apow_of_valuation_eq_one b3, show gdet (1 : GL (Fin d) (Fv F v)) = 1 from map_one _, map_one, apow_one,
        Units.val_one, Units.val_one, Matrix.mul_one, one_mul, one_mul, one_mul, one_mul, e]
      by_cases hY : Y - Y₀ ∈ lam (Fv F v) a n d
      · exact (Set.indicator_of_mem ((key Y).2 hY) _).trans (Set.indicator_of_mem hY fun _ => (1 : ℂ)).symm
      · exact (Set.indicator_of_notMem (mt (key Y).1 hY) _).trans (Set.indicator_of_notMem hY fun _ => (1 : ℂ)).symm)
    rw [hι.bij.2.1 m1 hφ e2] at ac
    exact Or.inl ⟨b1 g hg rfl rfl, ac⟩
  · rw [← hY₀] at h2
    let u₀ : Matrix (Fin n) (Fin d) (Fv F v) := of fun i j => -l (single i j 1)
    have el : ∀ Y, trace (Yᵀ * -u₀) = l Y := fun Y => by
      conv_rhs => rw [matrix_eq_sum_single Y]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [← dot_ofM, dotProduct, ofM, Fintype.sum_prod_type, map_sum, u₀, Matrix.neg_apply, of_apply, neg_neg]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [← smul_eq_mul, ← map_smul]; simp
    refine Or.inr ⟨secM sec u₀ 0, psiV B.ψ v (l Y₀), psiV B.ψ v (l (g₀.1ᵀ * Y₀)), h.atM _ _, fun H => h2 ?_,
      mult _ (h.atM _ _) (h.sndM _ _) _ fun Y hY => ?_,
      mult _ ((h.atM _ _).kd_mul_left _) (by rw [Matrix.map_mul, h.sndM, Matrix.mul_zero]) _ fun Y hY => ?_⟩
    · refine mul_right_cancel₀ ((psiV B.ψ v).val_isUnit (l Y₀)).ne_zero ?_
      rw [← AddChar.map_add_eq_mul, ← map_add (f := _), sub_add_cancel, one_mul, H]
      rfl
    · rw [h.fstM, el, ← sub_add_cancel Y Y₀, map_add (f := _), AddChar.map_add_eq_mul, (h1 _ hY).1, one_mul]
    · rw [Matrix.map_mul, h.fstM, ← Matrix.mul_neg, ← Matrix.mul_assoc, ← transpose_transpose (Yᵀ * _), transpose_mul,
        transpose_transpose, el, ← sub_add_cancel Y Y₀, Matrix.mul_add, map_add, AddChar.map_add_eq_mul]
      exact (congrArg (· * _) (h1 _ hY).2).trans (one_mul _)

end GlobalTheory.ThK.Dbl

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.ThConstMatch
section
noncomputable section

namespace GlobalTheory.ThK.Dbl.TC

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem exists_ext {ι : Type} (M : ι → Type) [∀ v, AddCommGroup (M v)] [∀ v, Module ℂ (M v)] {S T : Finset ι} (h : S ⊆ T)
    (z : ∀ v, M v) : ∃ e : (PiTensorProduct ℂ fun v : S => M v) →ₗ[ℂ] PiTensorProduct ℂ fun v : T => M v,
      ∀ u : ∀ v, M v, (∀ v ∉ S, u v = z v) → e (PiTensorProduct.tprod ℂ fun v : S => u v) = PiTensorProduct.tprod ℂ fun v : T => u v := by
  let c : (∀ v : S, M v) → ∀ v : T, M v := fun x v => if hv : (v : ι) ∈ S then x ⟨v, hv⟩ else z v
  have key : ∀ [DecidableEq S] x (i : S) w, c (Function.update x i w) = Function.update (c x) ⟨i, h i.2⟩ w := fun x i w => by
    funext v
    by_cases hvi : v = ⟨i, h i.2⟩
    · subst hvi
      simp [c]
    · rw [Function.update_of_ne hvi]
      by_cases hv : (v : ι) ∈ S
      · simp only [c, dif_pos hv]
        exact Function.update_of_ne (fun e => hvi (Subtype.ext (by rw [← e]))) _ _
      · simp only [c, dif_neg hv]
  refine ⟨PiTensorProduct.lift
    { toFun := fun x => PiTensorProduct.tprod ℂ (c x)
      map_update_add' := fun x i y y' => by simp only [key]; exact (PiTensorProduct.tprod ℂ).map_update_add _ _ _ _
      map_update_smul' := fun x i a y => by simp only [key]; exact (PiTensorProduct.tprod ℂ).map_update_smul _ _ _ _ }, fun u hu => ?_⟩
  rw [PiTensorProduct.lift.tprod]
  refine congrArg (PiTensorProduct.tprod ℂ) (funext fun v => ?_)
  by_cases hv : (v : ι) ∈ S
  · simp only [c, dif_pos hv]
  · simp only [c, dif_neg hv, hu v hv]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d a a' : ℕ}
  {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
  {R : RealMaps F a a'} {Rf : FinMaps F a a'}


variable (B G R Rf) in
def On (T : Finset (Pl F)) (Φ : Fn F a (a + a')) (Φ' : Fn F a' (a + a')) : Prop :=
  ∃ (m m' : ℕ) (f : Fin m → SInf F _) (φ : Fin m → ∀ v : Pl F, (_ → Fv F v) → ℂ)
    (f' : Fin m' → SInf F _) (φ' : Fin m' → ∀ v : Pl F, (_ → Fv F v) → ℂ),
    (∀ i, f i ∈ G.M.Pol B.ψ B.emb ∧ (∀ v, φ i v ∈ SB _) ∧ ∀ v ∉ T, φ i v = G.M.vac v) ∧
    (∀ j, f' j ∈ G.M'.Pol B.ψ B.emb ∧ (∀ v, φ' j v ∈ SB _) ∧ ∀ v ∉ T, φ' j v = G.M'.vac v) ∧
    Φ = ∑ i, pure (f i) (φ i) ∧ Φ' = ∑ j, pure (f' j) (φ' j) ∧
    ∑ i, R.p (f i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p v (φ i v)) =
      ∑ j, R.p' (f' j) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p' v (φ' j v))

theorem On.mono (hm : IsMatched B G X om om' R Rf) {S T : Finset (Pl F)} (h0 : X.T ⊆ S) (h : S ⊆ T) {Φ Φ'}
    (H : On B G R Rf S Φ Φ') : On B G R Rf T Φ Φ' := by
  obtain ⟨m, m', f, φ, f', φ', h1, h2, e1, e2, e3⟩ := H
  obtain ⟨e, he⟩ := exists_ext Rf.Pi h fun v => Rf.p v (G.M.vac v)
  refine ⟨m, m', f, φ, f', φ', fun i => ⟨(h1 i).1, (h1 i).2.1, fun v hv => (h1 i).2.2 v fun k => hv (h k)⟩,
    fun i => ⟨(h2 i).1, (h2 i).2.1, fun v hv => (h2 i).2.2 v fun k => hv (h k)⟩, e1, e2, ?_⟩
  have := congrArg (e.lTensor R.Pi) e3
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.lTensor_tmul] at this
  refine (Finset.sum_congr rfl fun i _ => ?_).trans (this.trans (Finset.sum_congr rfl fun i _ => ?_))
  · rw [he (fun v => Rf.p v (φ i v)) fun v hv => by rw [(h1 i).2.2 v hv]]
  · rw [he (fun v => Rf.p' v (φ' i v)) fun v hv => by rw [(h2 i).2.2 v hv, (hm.fin.sph v fun k => hv (h0 k)).1]]

theorem pm_zero : PolMatch B G X R Rf 0 0 :=
  ⟨_, le_rfl, 0, 0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, by simp, by simp, by simp⟩

theorem pm_add (hm : IsMatched B G X om om' R Rf) {Φ Φ' Ψ Ψ'} (c : ℂ) (h1 : PolMatch B G X R Rf Φ Φ')
    (h2 : PolMatch B G X R Rf Ψ Ψ') : PolMatch B G X R Rf (c • Φ + Ψ) (c • Φ' + Ψ') := by
  obtain ⟨T₁, hT₁, H₁⟩ := h1
  obtain ⟨T₂, hT₂, H₂⟩ := h2
  obtain ⟨m, m', f, φ, f', φ', hf, hf', rfl, rfl, e1⟩ := On.mono hm hT₁ (Finset.subset_union_left (s₂ := T₂)) H₁
  obtain ⟨k, k', g, ψ, g', ψ', hg, hg', rfl, rfl, e2⟩ := On.mono hm hT₂ (Finset.subset_union_right (s₁ := T₁)) H₂
  refine ⟨T₁ ∪ T₂, hT₁.trans Finset.subset_union_left, m + k, m' + k', Fin.append (c • f) g, Fin.append φ ψ, Fin.append (c • f') g',
    Fin.append φ' ψ', fun i => ?_, fun i => ?_, funext fun x => ?_, funext fun x => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left, Pi.smul_apply]
      exact ⟨Submodule.smul_mem _ _ (hf i).1, (hf i).2⟩
    · simp only [Fin.append_right]
      exact hg i
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left, Pi.smul_apply]
      exact ⟨Submodule.smul_mem _ _ (hf' i).1, (hf' i).2⟩
    · simp only [Fin.append_right]
      exact hg' i
  · simp [Fin.sum_univ_add, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Finset.mul_sum, mul_assoc]
  · simp [Fin.sum_univ_add, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Finset.mul_sum, mul_assoc]
  · rw [Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Pi.smul_apply, map_smul, ← TensorProduct.smul_tmul']
    rw [← Finset.smul_sum, ← Finset.smul_sum, e1, e2]

theorem loc_op (hS : SplitModel) {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {o : Rep σ Y W} {χ χ' : Chr F E} {r s r' s' : ℕ}
    (p : IsPair B M χ χ' o r s r' s') {v : Pl F} (t : E →ₐ[F] Fv F v) {h : UA σ W.J} (hh : h ∈ UAt σ W (evFin F v)) :
    ∃ O : Module.End ℂ ((Fin n × Fin d → Fv F v) → ℂ), (∀ φ ∈ SB _, O φ ∈ SB _ ∧ Acts (evFin F v) (o (1, h)) φ (O φ)) ∧
      ∀ f (φ : ∀ u : Pl F, (Fin n × Fin d → Fv F u) → ℂ), (∀ u, φ u ∈ SB _) → (∀ᶠ u in cofinite, φ u = M.vac u) →
        o (1, h) (pure f φ) = pure f (Function.update φ v (O (φ v))) := by
  obtain ⟨-, ι, b, -, r1⟩ := hS F E σ B n d Y W M _ _ o _ _ _ _ p v t
  obtain ⟨j, -, j2⟩ := exists_inv' b
  let h₀ := Matrix.GeneralLinearGroup.map (piW t) h.1
  have k := fun φ hφ => acts_of_reads (r1 h hh h₀ rfl) j2 (φ := φ) hφ
  refine ⟨j ∘ₗ GlobalTheory.SplitFlip.repB (chrW χ' t) (chrW χ t) (1, h₀) ∘ₗ ι, k, fun f φ p1 p2 => ?_⟩
  obtain ⟨T, t1, -, t3⟩ := intersection_update_fsHerm_neg_one v f p1 ((p2.and p.good.std).mono fun _ h => h.1.trans h.2)
  have := t3 _ _ (p1 v) _ (k _ (p1 v)).2
  rwa [t1, t1, Function.update_eq_self] at this

theorem pm_fin (hS : SplitModel) (hm : IsMatched B G X om om' R Rf) {v : Pl F} (t : E →ₐ[F] Fv F v) {h : UA σ G.W.J}
    (hh : h ∈ UAt σ G.W (evFin F v)) {Φ Φ'} (H : PolMatch B G X R Rf Φ Φ') :
    PolMatch B G X R Rf (om (1, h) Φ) (om' (1, h) Φ') := by
  obtain ⟨T, hT, H⟩ := H
  obtain ⟨m, m', f, φ, f', φ', h1, h2, rfl, rfl, e⟩ := On.mono hm hT (Finset.subset_insert v T) H
  obtain ⟨O, o1, o2⟩ := loc_op hS (pairV hm.triple) t hh
  obtain ⟨O', o1', o2'⟩ := loc_op hS (pairV' hm.triple) t hh
  obtain ⟨s, hs⟩ := ((Rf.p v).domRestrict (SB _)).exists_rightInverse_of_surjective
    ((LinearMap.range_domRestrict _ _).trans (hm.fin.onto v))
  let A : Module.End ℂ (Rf.Pi v) := Rf.p v ∘ₗ O ∘ₗ (SB _).subtype ∘ₗ s
  have q : ∀ x ∈ SB _, ∀ x' ∈ SB _, Rf.p v x = Rf.p' v x' → Rf.p v (O x) = Rf.p' v (O' x') := fun x hx x' hx' =>
    hm.fin.equiv v h hh x hx x' hx' _ (o1 x hx).1 _ (o1' x' hx').1 (o1 x hx).2 (o1' x' hx').2
  have A' : ∀ x' ∈ SB _, A (Rf.p' v x') = Rf.p' v (O' x') := fun x' hx' =>
    q _ (s _).2 x' hx' (LinearMap.congr_fun hs _)
  have A1 : ∀ x ∈ SB _, A (Rf.p v x) = Rf.p v (O x) := fun x hx => by
    obtain ⟨x', hx', k⟩ : Rf.p v x ∈ (SB _).map (Rf.p' v) := hm.fin.onto' v ▸ Submodule.mem_top
    rw [q x hx x' hx' k.symm, ← k, A' x' hx']
  have up : ∀ {P : ∀ u : Pl F, Type} (Q : ∀ u, P u → Prop) (x : ∀ u, P u) (y : P v), Q v y → (∀ u ≠ v, Q u (x u)) →
      ∀ u, Q u (Function.update x v y u) := fun Q x y a b u => by
    by_cases hu : u = v
    · subst hu; rwa [Function.update_self]
    · rw [Function.update_of_ne hu]; exact b u hu
  have ne : ∀ u ∉ insert v T, u ≠ v := fun u hu k => hu (k ▸ Finset.mem_insert_self _ _)
  refine ⟨_, hT.trans (Finset.subset_insert v T), m, m', f, fun i => Function.update (φ i) v (O (φ i v)), f',
    fun i => Function.update (φ' i) v (O' (φ' i v)), fun i => ⟨(h1 i).1,
      up (fun u x => x ∈ SB _) _ _ (o1 _ ((h1 i).2.1 v)).1 fun u _ => (h1 i).2.1 u,
      fun u hu => (Function.update_of_ne (ne u hu) _ _).trans ((h1 i).2.2 u hu)⟩, fun i => ⟨(h2 i).1,
      up (fun u x => x ∈ SB _) _ _ (o1' _ ((h2 i).2.1 v)).1 fun u _ => (h2 i).2.1 u,
      fun u hu => (Function.update_of_ne (ne u hu) _ _).trans ((h2 i).2.2 u hu)⟩, ?_, ?_, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => o2 _ _ (h1 i).2.1 ((insert v T).eventually_cofinite_notMem.mono (h1 i).2.2)
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => o2' _ _ (h2 i).2.1 ((insert v T).eventually_cofinite_notMem.mono (h2 i).2.2)
  let D : ∀ u, Module.End ℂ (Rf.Pi u) := Function.update (fun _ => LinearMap.id) v A
  have := congrArg ((PiTensorProduct.map fun u : (insert v T : Finset _) => D u).lTensor R.Pi) e
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.lTensor_tmul, PiTensorProduct.map_tprod] at this
  refine (Finset.sum_congr rfl fun i _ => ?_).trans (this.trans (Finset.sum_congr rfl fun i _ => ?_)) <;> congr 2 <;> funext ⟨u, _⟩ <;>
    by_cases hu : u = v
  · subst hu; simp only [D, Function.update_self, A1 _ ((h1 i).2.1 _)]
  · simp only [D, Function.update_of_ne hu, LinearMap.id_apply]
  · subst hu; simp only [D, Function.update_self, A' _ ((h2 i).2.1 _)]
  · simp only [D, Function.update_of_ne hu, LinearMap.id_apply]

end GlobalTheory.ThK.Dbl.TC

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.ThConstSplit
section
noncomputable section

namespace GlobalTheory.ThK.Dbl.TC

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem splitModel_of (h : PositivityTheory.KCo.DictX) : SplitModel := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' p v t
  obtain ⟨⟨ι, hι⟩, -, s2, k⟩ := h F E σ n d B X W M om χX χW p.base ⟨_, _, p.herm⟩ ⟨_, _, p.skew⟩ p.weil v t
  exact ⟨s2, ι, hι.bij, fun g hg => ⟨Matrix.GeneralLinearGroup.map (piW t) g.1, (k ι hι).1 g hg _ rfl⟩, (k ι hι).2⟩

theorem splitModel : SplitModel := splitModel_of PositivityTheory.KCo.dictionary_extended

end GlobalTheory.ThK.Dbl.TC

end
end

