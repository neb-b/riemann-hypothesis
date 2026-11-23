module

public import Mathlib
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0007
public import ReciprocityTheory.Chebotarev.Bundle0001
public import Development.WeilBound.ThetaLifts.LatticeBasics.FdEqZero
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0001
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0006

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.BadStmt
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

def Bump : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → n ≤ d → ∀ v ∈ B.P, ∃ φ ∈ SB (Fin n × Fin d → Fv F v), φ ≠ 0 ∧ ∀ g ∈ UAt σ X (evFin F v),
      (IntAt v g ∧ Acts (evFin F v) (om (g, 1)) φ φ) ∨ ∃ (u : Matrix (Fin n) (Fin d) (AE F E)) (c c' : ℂ), At (evFin F v) u ∧ c ≠ c' ∧
        Acts (evFin F v) (M.co.rho B.ψ u) φ (c • φ) ∧ Acts (evFin F v) (M.co.rho B.ψ (mat g * u)) φ (c' • φ)

def VacFix2 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) r s r' s', B.IsGood σ → X.IsHerm σ B r s →
    W.IsSkew σ B r' s' → M.IsGood B.ψ → ∀ χ : Chr F E, IsHecke F E χ → ∀ dd om, IsDblCoordX M dd →
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F W.J) (dbl (incM F X.J)) dd χ (diagCols (Fin n)) om →
    ∀ K, IsStab2 (σ := σ) (Y := X) B K → ∀ v, (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt χ w) →
    ∀ k ∈ K, At (evFin F v) (mat2 k - 1) →
      Acts (evFin F v) (om k) (boxFun (M.vac v) (star (M.vac v))) (boxFun (M.vac v) (star (M.vac v)))

end GlobalTheory.ThK.Dbl

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.EulerHalf
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem euler_half {ι : Type} (q : ι → ℕ) (hq : ∀ v, 2 ≤ q v) (hs : ∀ s : ℝ, 1 < s → Summable fun v => (q v : ℝ) ^ (-s))
    (c : ι → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1) (k : ℕ) : ∃ d : ℂ → ℂ, DifferentiableOn ℂ d {z | 0 < z.re} ∧ ∀ z : ℂ, 0 < z.re →
      d z ≠ 0 ∧ HasProd (fun v => (1 - c v * (q v : ℂ) ^ (-(2 * z + (k + 1 : ℕ))))⁻¹) (d z) := by
  let x : ι → ℂ → ℂ := fun v z => -(c v * (q v : ℂ) ^ (-(2 * z + (k + 1 : ℕ))))
  have h1 : ∀ v, (1 : ℝ) ≤ q v := fun v => by exact_mod_cast one_le_two.trans (hq v)
  have hx : ∀ v z (t : ℝ), t ≤ 2 * z.re + 1 → ‖x v z‖ ≤ (q v : ℝ) ^ (-t) := fun v z t ht => by
    rw [norm_neg, norm_mul, Complex.norm_natCast_cpow_of_pos (two_pos.trans_le (hq v))]
    refine (mul_le_of_le_one_left (by positivity) (hc v)).trans (Real.rpow_le_rpow_of_exponent_le (h1 v) ?_)
    have : (0 : ℝ) ≤ k := k.cast_nonneg
    simp only [Complex.neg_re, Complex.add_re, Complex.natCast_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat]
    push_cast
    linarith
  have hh : ∀ v z, 0 < z.re → ‖x v z‖ ≤ 1 / 2 := fun v z hz => by
    refine (hx v z 1 (by linarith)).trans ?_
    rw [Real.rpow_neg_one, one_div]
    exact inv_anti₀ two_pos (by exact_mod_cast hq v)
  have hb : ∀ v z (t : ℝ), 0 < z.re → t ≤ 2 * z.re + 1 → ‖Complex.log (1 + x v z)‖ ≤ 3 / 2 * (q v : ℝ) ^ (-t) :=
    fun v z t hz ht => (Complex.norm_log_one_add_half_le_self (hh v z hz)).trans (by gcongr; exact hx v z t ht)
  have hsl : ∀ v z, 0 < z.re → 1 + x v z ∈ Complex.slitPlane := fun v z hz =>
    Complex.mem_slitPlane_of_norm_lt_one ((hh v z hz).trans_lt (by norm_num))
  refine ⟨fun z => Complex.exp (-∑' v, Complex.log (1 + x v z)), fun z hz => ?_, fun z hz => ⟨Complex.exp_ne_zero _, ?_⟩⟩
  · have hz' : 0 < z.re := hz
    have ho : IsOpen {w : ℂ | z.re / 2 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have := Complex.differentiableOn_tsum_of_summable_norm (F := fun v w => Complex.log (1 + x v w))
      ((hs (z.re + 1) (by linarith)).mul_left (3 / 2)) (fun v w hw => ?_) ho
      fun v w (hw : z.re / 2 < w.re) => hb v w _ (by linarith) (by linarith)
    · exact (this.differentiableAt (ho.mem_nhds (show z.re / 2 < z.re by linarith))).neg.cexp.differentiableWithinAt
    · have hw' : z.re / 2 < w.re := hw
      have hw0 : 0 < w.re := by linarith
      refine (DifferentiableAt.clog (f := fun w => 1 + x v w) ?_ (hsl v w hw0)).differentiableWithinAt
      have : (q v : ℂ) ≠ 0 := by exact_mod_cast (two_pos.trans_le (hq v)).ne'
      exact (((by fun_prop : DifferentiableAt ℂ (fun z : ℂ => -(2 * z + (k + 1 : ℕ))) w).const_cpow
        (Or.inl this)).const_mul _).neg.const_add _
  · have := (Summable.of_norm_bounded ((hs (2 * z.re + 1) (by linarith)).mul_left (3 / 2))
      fun v => hb v z _ hz le_rfl).hasSum.neg.cexp
    convert this using 2 with v
    rw [Function.comp, Complex.exp_neg, Complex.exp_log (Complex.slitPlane_ne_zero (hsl v z hz)), sub_eq_add_neg]

open Classical in
theorem dProd : DProd := by
  intro F E _ _ _ _ _ n T
  choose d h1 h2 using fun i => euler_half (ι := {v : Pl F // v ∉ T}) (fun v => Ideal.absNorm v.1.asIdeal)
    (fun v => NumberField.HeightOneSpectrum.one_lt_absNorm v.1)
    (fun s hs => (ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal F hs).comp_injective
      (HeightOneSpectrum.asIdeal_injective.comp Subtype.val_injective))
    (fun v => (if Nonempty (E →ₐ[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v.1) then 1 else -1) ^ (n - (i + 1)))
    (fun v => by split_ifs <;> simp) i
  exact ⟨fun z => ∏ i ∈ Finset.range n, d i z, DifferentiableOn.fun_finsetProd fun i _ => h1 i, fun z hz =>
    ⟨Finset.prod_ne_zero_iff.2 fun i _ => (h2 i z hz).1, hasProd_prod fun i _ => (h2 i z hz).2⟩⟩

end GlobalTheory.ThK.Dbl

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.EulerProd
section
noncomputable section

namespace GlobalTheory.ThK.Dbl.Euler

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

section Cut

variable {S R k : Type} [CommRing S] [CommRing R] [Algebra S R] [Fintype k] [DecidableEq k] {e : S}

def cut (e : S) (A : Matrix k k R) : Matrix k k R := (1 - e) • 1 + e • A

theorem mix (he : e * e = e) (A B C D : Matrix k k R) :
    ((1 - e) • A + e • B) * ((1 - e) • C + e • D) = (1 - e) • (A * C) + e • (B * D) := by
  have h1 : (1 - e) * (1 - e) = 1 - e := by linear_combination he
  have h2 : (1 - e) * e = 0 := by linear_combination -he
  have h3 : e * (1 - e) = 0 := by linear_combination -he
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, h1, h2, h3, he, zero_smul, add_zero,
    zero_add]

theorem cut_mul (he : e * e = e) (A B : Matrix k k R) : cut e A * cut e B = cut e (A * B) := by
  rw [cut, cut, mix he, mul_one, cut]

theorem cut_sub (A : Matrix k k R) : cut e A - 1 = e • (A - 1) := by
  rw [cut, sub_smul, one_smul, smul_sub]; abel

theorem cut_eq {A : Matrix k k R} : cut e A = A ↔ e • (A - 1) = A - 1 := by rw [← cut_sub, sub_left_inj]

theorem cut_one : cut e (1 : Matrix k k R) = 1 := cut_eq.2 (by simp)

theorem cut_cut (he : e * e = e) (A : Matrix k k R) : cut e (cut e A) = cut e A :=
  cut_eq.2 (by rw [cut_sub, smul_smul, he])

theorem cut_form (he : e * e = e) (c : R →ₐ[S] R) {J A : Matrix k k R} (h : Aᵀ * J * A.map c = J) :
    (cut e A)ᵀ * J * (cut e A).map c = J := by
  have e1 : (cut e A).map c = (1 - e) • 1 + e • A.map c := by
    ext i j
    simp [cut, Matrix.one_apply, apply_ite c]
  have e2 : J = (1 - e) • J + e • J := by rw [← add_smul, sub_add_cancel, one_smul]
  rw [e1, cut, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_one]
  conv_lhs => rw [e2]
  rw [mix he, mix he, h, one_mul, mul_one, ← e2]

end Cut

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

theorem lcsc_UA (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    LocallyCompactSpace (UA σ J) ∧ SecondCountableTopology (UA σ J) ∧ T2Space (UA σ J) := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  have : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology (AE F E) := e.secondCountableTopology
  have : T2Space (AE F E) := e.isEmbedding.t2Space
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → AE F E))
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  have : LocallyCompactSpace (GL (Fin n) (AE F E)) :=
    Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AE F E))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  have : SecondCountableTopology (GL (Fin n) (AE F E)) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  have : T2Space (GL (Fin n) (AE F E)) := Units.isEmbedding_embedProduct.t2Space
  have hs : Continuous (cA σ : AE F E → AE F E) :=
    IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hc : IsClosed (UG (cA σ) (incM F J) : Set (GL (Fin n) (AE F E))) := by
    have hv : Continuous fun g : GL (Fin n) (AE F E) => (g : Matrix (Fin n) (Fin n) (AE F E)) :=
      Units.continuous_val
    exact isClosed_eq ((hv.matrix_transpose.matrix_mul continuous_const).matrix_mul (hv.matrix_map hs))
      continuous_const
  exact ⟨hc.isClosedEmbedding_subtypeVal.locallyCompactSpace, IsEmbedding.subtypeVal.secondCountableTopology,
    IsEmbedding.subtypeVal.t2Space⟩

variable {Y : Spc F E n} {v : Pl F}

theorem mm (g h : UA σ Y.J) : mat (g * h) = mat g * mat h := rfl

def prj (v : Pl F) : UA σ Y.J →* UA σ Y.J := MonoidHom.mk' (fun g => ⟨⟨cut (idem v) (mat g), cut (idem v) (mat g⁻¹),
    by rw [cut_mul (idem_sq v), ← mm, mul_inv_cancel]; exact cut_one, by rw [cut_mul (idem_sq v), ← mm, inv_mul_cancel]; exact cut_one⟩,
    cut_form (idem_sq v) _ g.2⟩) fun g h => Subtype.ext (Units.ext (cut_mul (idem_sq v) _ _).symm)

theorem mem_loc {g : UA σ Y.J} : g ∈ locGrp σ Y v ↔ prj v g = g := by
  have e : ∀ g : UA σ Y.J, g ∈ UAt σ Y (evFin F v) ↔ prj v g = g := fun g =>
    at_iff.trans (cut_eq.symm.trans ⟨fun h => Subtype.ext (Units.ext h), fun h => congrArg mat h⟩)
  refine ⟨fun h => ?_, fun h => Subgroup.subset_closure ((e g).2 h)⟩
  exact (Subgroup.closure_le ((prj v).eqLocus (MonoidHom.id _))).2 (fun g hg => (e g).1 hg) h

theorem prj_mem (g : UA σ Y.J) : prj v g ∈ locGrp σ Y v := mem_loc.2 (Subtype.ext (Units.ext (cut_cut (idem_sq v) _)))

theorem cont_mat : Continuous fun g : UA σ Y.J => mat g := Units.continuous_val.comp continuous_subtype_val

theorem cont_prj : Continuous (prj v : UA σ Y.J → UA σ Y.J) := by
  have : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul _ _
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  have c1 : Continuous fun g : UA σ Y.J => cut (idem v) (mat g) := by
    have := cont_mat (σ := σ) (Y := Y)
    unfold cut
    refine continuous_matrix fun i j => ?_
    have := this.matrix_elem i j
    simp only [Matrix.add_apply, Matrix.smul_apply]
    fun_prop
  have c2 : Continuous fun g : UA σ Y.J => cut (idem v) (mat g⁻¹) := c1.comp continuous_inv
  exact Continuous.subtype_mk (Units.continuous_iff.2 ⟨c1, c2⟩) _

theorem off_of {g : UA σ Y.J} (h : prj v g = 1) : OffAt v g := by
  have e : idem v • (mat g - 1) = 0 := by rw [← cut_sub, show cut (idem v) (mat g) = 1 from congrArg mat h, sub_self]
  have c : ∀ x : AE F E, compFin F E v (idem v • x) = compFin F E v x := fun x => by
    rw [Algebra.smul_def, map_mul, show compFin F E v (algebraMap _ _ (idem v)) = evFin F v (idem v) ⊗ₜ 1 from rfl, ev_self]
    exact one_mul _
  rw [OffAt, ← Matrix.map_one (compFin F E v) (map_zero _) (map_one _)]
  ext i j
  have := c ((mat g - 1) i j)
  rw [show idem v • (mat g - 1) i j = 0 from congrFun (congrFun e i) j, map_zero, Matrix.sub_apply, map_sub] at this
  exact sub_eq_zero.1 this.symm

theorem at_mulVec (A : Matrix (Fin n) (Fin n) (AE F E)) {z : Fin n → AE F E} (h : At (evFin F v) z) : At (evFin F v) (A *ᵥ z) :=
  fun u hu => by rw [← Matrix.mulVec_smul, h u hu, Matrix.mulVec_zero]

theorem prj_mulVec (g : UA σ Y.J) {z : Fin n → AE F E} (h : At (evFin F v) z) : mat (prj v g) *ᵥ z = mat g *ᵥ z := by
  show cut (idem v) (mat g) *ᵥ z = _
  rw [cut, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_smul, one_smul, at_iff.1 h,
    at_iff.1 (at_mulVec _ h), sub_self, zero_add]

theorem int_prj {g : UA σ Y.J} : IntAt v (prj v g) ↔ IntAt v g :=
  forall₂_congr fun z _ => forall_congr' fun h => by rw [← map_inv, prj_mulVec _ h, prj_mulVec _ h]

theorem prj_ne {u : Pl F} (h : u ≠ v) {g : UA σ Y.J} (hg : g ∈ locGrp σ Y v) : prj u g = 1 := by
  refine Subtype.ext (Units.ext (sub_eq_zero.1 ((cut_sub (mat g)).trans ?_)))
  rw [← cut_eq.1 (congrArg mat (mem_loc.1 hg)), smul_smul, mul_idem (ev_ne h.symm), zero_smul]

theorem int_mul_ne {u : Pl F} (h : u ≠ v) {x : UA σ Y.J} (hx : x ∈ locGrp σ Y v) (g : UA σ Y.J) : IntAt u (x * g) ↔ IntAt u g := by
  rw [← int_prj, map_mul, prj_ne h hx, one_mul, int_prj]


variable (σ Y) in
def intGrp (v : Pl F) : Subgroup (UA σ Y.J) where
  carrier := {g | IntAt v g}
  one_mem' := fun z hz _ => by rw [inv_one, show mat (1 : UA σ Y.J) = 1 from rfl, Matrix.one_mulVec]; exact ⟨hz, hz⟩
  mul_mem' := fun ha hb z hz h => by
    rw [mul_inv_rev, mm, mm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact ⟨(ha _ (hb z hz h).1 (at_mulVec _ h)).1, (hb _ (ha z hz h).2 (at_mulVec _ h)).2⟩
  inv_mem' := fun ha z hz h => by rw [inv_inv]; exact (ha z hz h).symm

theorem isClosed_int (hL : Y.L.IsLattice E) (v : Pl F) : IsClosed {g : UA σ Y.J | IntAt v g} := by
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  simp only [IntAt, Set.setOf_forall]
  exact isClosed_iInter fun z => isClosed_iInter fun _ => isClosed_iInter fun _ =>
    ((isClosed_latHat hL).preimage (cont_mat.matrix_mulVec continuous_const)).inter
      ((isClosed_latHat hL).preimage ((cont_mat.comp continuous_inv).matrix_mulVec continuous_const))

theorem isClosed_loc : IsClosed (locGrp σ Y v : Set (UA σ Y.J)) := by
  have := (lcsc_UA σ Y.J).2.2
  rw [show (locGrp σ Y v : Set (UA σ Y.J)) = {g | prj v g = g} from Set.ext fun _ => mem_loc]
  exact isClosed_eq cont_prj continuous_id

theorem lcsc_loc (v : Pl F) : LocallyCompactSpace (locGrp σ Y v) ∧ SecondCountableTopology (locGrp σ Y v) := by
  obtain ⟨a1, a2, a3⟩ := lcsc_UA σ Y.J
  exact ⟨isClosed_loc.isClosedEmbedding_subtypeVal.locallyCompactSpace, IsEmbedding.subtypeVal.secondCountableTopology⟩

theorem step (hL : Y.L.IsLattice E) {μ : Measure (UA σ Y.J)} (hμ : μ.IsHaarMeasure) {ν : Measure (locGrp σ Y v)}
    (hν : ν.IsHaarMeasure) (h1 : ν {g | IntAt v g.1} = 1) {f l : UA σ Y.J → ℂ} (hf : Integrable f μ)
    (hl : ∀ u ∈ locGrp σ Y v, ∀ g, OffAt v g → f (u * g) = l u * f g) (hl1 : ∀ u ∈ locGrp σ Y v, IntAt v u → l u = 1)
    {P : Set (Pl F)} (hv : v ∉ P) :
    ∫ g in {g | ∀ u ∈ P, IntAt u g}, f g ∂μ = (∫ u, l u.1 ∂ν) * ∫ g in {g | ∀ u ∈ insert v P, IntAt u g}, f g ∂μ := by
  obtain ⟨a1, a2, a3⟩ := lcsc_UA σ Y.J
  obtain ⟨b1, b2⟩ := lcsc_loc (σ := σ) (Y := Y) v
  have mA : MeasurableSet {g : UA σ Y.J | ∀ u ∈ P, IntAt u g} := by
    simp only [Set.setOf_forall]
    exact (isClosed_iInter fun u => isClosed_iInter fun _ => isClosed_int hL u).measurableSet
  rw [factor (ν := ν) (K := (intGrp σ Y v).subgroupOf (locGrp σ Y v)) (l := fun u => l u.1)
    ((isClosed_int hL v).preimage continuous_subtype_val).measurableSet h1 (locGrp σ Y v).subtype continuous_subtype_val
    (fun g => ⟨prj v g, prj_mem g⟩) (cont_prj.subtype_mk _)
    (fun u g => Subtype.ext ((map_mul _ _ _).trans (congrArg (· * prj v g) (mem_loc.1 u.2)))) hf
    (fun u g h => hl u u.2 g (off_of (congrArg Subtype.val h))) (fun u hu => hl1 u u.2 hu) mA
    (fun u g => forall₂_congr fun w hw => int_mul_ne (fun e : w = v => hv (e ▸ hw)) u.2 g)]
  congr 3
  ext g
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, Set.forall_mem_insert]
  rw [and_comm]
  exact and_congr_left' (int_prj (σ := σ) (Y := Y) (v := v) (g := g))

theorem _root_.GlobalTheory.ThK.Dbl.eulerProd : EulerProd := by
  intro F E _ _ _ _ _ σ B n Y r s _ hY T μ hμ μl hl f fl hf h
  classical
  let A : Finset {v : Pl F // v ∉ T} → Set (UA σ Y.J) := fun S => {g | ∀ u ∈ {u | ∃ h : u ∉ T, ⟨u, h⟩ ∉ S}, IntAt u g}
  have e : ∀ S, (∏ v ∈ S, ∫ u, fl v.1 u.1 ∂μl v.1) * ∫ g in {g | ∀ v ∉ T, IntAt v g}, f g ∂μ = ∫ g in A S, f g ∂μ := fun S => by
    induction S using Finset.induction_on with
    | empty => simp [A]
    | insert v S hv ih =>
      rw [Finset.prod_insert hv, mul_assoc, ih]
      refine Eq.trans ?_ (step hY.lat.toIsLattice hμ (hl v).1 (hl v).2 hf (h v v.2).1 (h v v.2).2.1
        (P := {u | ∃ h : u ∉ T, ⟨u, h⟩ ∉ insert v S}) (by rintro ⟨_, h'⟩; exact h' (Finset.mem_insert_self _ _))).symm
      congr 3
      ext g
      refine forall_congr' fun u => imp_congr_left ⟨fun ⟨h1, h2⟩ => ?_, ?_⟩
      · by_cases e : u = v.1
        · exact .inl e
        · exact .inr ⟨h1, fun h3 => (Finset.mem_insert.1 h3).elim (fun h4 => e (congrArg Subtype.val h4)) h2⟩
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨v.2, hv⟩
        · exact ⟨h1, fun h3 => h2 (Finset.mem_insert_of_mem h3)⟩
  have u : ⋃ S, A S = Set.univ := Set.eq_univ_of_forall fun g => by
    have c := Filter.eventually_cofinite.1 ((ae_mulVec hY.lat (mat g)).and (ae_mulVec hY.lat (mat g⁻¹)))
    refine Set.mem_iUnion.2 ⟨c.toFinset.subtype _, fun u ⟨_, h2⟩ => ?_⟩
    rw [Finset.mem_subtype, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at h2
    exact fun z hz h3 => ⟨h2.1 z hz h3, h2.2 z hz h3⟩
  have := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum F
  have := tendsto_setIntegral_of_monotone (s := A) (f := f) (μ := μ) (fun S => by
    simp only [A, Set.setOf_forall]
    exact (isClosed_iInter fun u => isClosed_iInter fun _ => isClosed_int hY.lat.toIsLattice u).measurableSet)
    (fun S S' hS g hg u ⟨h1, h2⟩ => hg u ⟨h1, fun h3 => h2 (hS h3)⟩) hf.integrableOn
  simpa only [e, u, Measure.restrict_univ] using this

end GlobalTheory.ThK.Dbl.Euler

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.HeightGLLe
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Matrix

namespace Ht

variable {p q : Type} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]

theorem htOf_le {R : Type} [CommRing R] {N₁ : Matrix p p R → ℝ≥0} {N₂ : Matrix q q R → ℝ≥0}
    {N : Matrix (p ⊕ q) (p ⊕ q) R → ℝ≥0} (hN : ∀ a b, N (fromBlocks a 0 0 b) ≤ max (N₁ a) (N₂ b))
    {X : GL (p ⊕ q) R} {x : GL p R} {y : GL q R} (h1 : X.1 = fromBlocks x.1 0 0 y.1) :
    htOf N X ≤ htOf N₁ x * htOf N₂ y := by
  have h2 : (X⁻¹).1 = fromBlocks (x⁻¹).1 0 0 (y⁻¹).1 :=
    Units.inv_eq_of_mul_eq_one_right (by rw [h1, fromBlocks_multiply]; simp)
  have hx := one_le_htOf N₁ x
  have hy := one_le_htOf N₂ y
  refine max_le (one_le_mul_of_one_le_of_one_le hx hy) (max_le ?_ ?_)
  · rw [h1]
    exact (hN _ _).trans (max_le ((le_htOf N₁ x).trans (le_mul_of_one_le_right' hy))
      ((le_htOf N₂ y).trans (le_mul_of_one_le_left' hx)))
  · rw [h2]
    exact (hN _ _).trans (max_le ((inv_le_htOf N₁ x).trans (le_mul_of_one_le_right' hy))
      ((inv_le_htOf N₂ y).trans (le_mul_of_one_le_left' hx)))

theorem opNorm_le (a : Matrix p p ℂ) (b : Matrix q q ℂ) : opNorm (fromBlocks a 0 0 b) ≤ max (opNorm a) (opNorm b) := by
  refine ContinuousLinearMap.opNNNorm_le_bound _ _ fun x => ?_
  rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnnorm, coe_nnnorm]
  obtain ⟨v, rfl⟩ : ∃ v : p ⊕ q → ℂ, x = WithLp.toLp 2 v := ⟨x.ofLp, rfl⟩
  set c : ℝ := ((max (opNorm a) (opNorm b) : ℝ≥0) : ℝ) with hc
  have h0 : 0 ≤ c := NNReal.coe_nonneg _
  have ha : ‖(WithLp.toLp 2 (a *ᵥ v ∘ .inl) : EuclideanSpace ℂ p)‖ ≤ c * ‖(WithLp.toLp 2 (v ∘ .inl) : EuclideanSpace ℂ p)‖ := by
    rw [← Matrix.toEuclideanCLM_toLp]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
      (NNReal.coe_le_coe.2 (le_max_left (opNorm a) (opNorm b))) (norm_nonneg _))
  have hb : ‖(WithLp.toLp 2 (b *ᵥ v ∘ .inr) : EuclideanSpace ℂ q)‖ ≤ c * ‖(WithLp.toLp 2 (v ∘ .inr) : EuclideanSpace ℂ q)‖ := by
    rw [← Matrix.toEuclideanCLM_toLp]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
      (NNReal.coe_le_coe.2 (le_max_right (opNorm a) (opNorm b))) (norm_nonneg _))
  have kn : ∀ w : p ⊕ q → ℂ, ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (p ⊕ q))‖ ^ 2 =
      ‖(WithLp.toLp 2 (w ∘ .inl) : EuclideanSpace ℂ p)‖ ^ 2 + ‖(WithLp.toLp 2 (w ∘ .inr) : EuclideanSpace ℂ q)‖ ^ 2 := fun w => by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]; rfl
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg h0 (norm_nonneg _)) two_ne_zero).1 ?_
  rw [Matrix.toEuclideanCLM_toLp, fromBlocks_mulVec, kn, mul_pow, kn, mul_add, ← mul_pow, ← mul_pow]
  simp only [zero_mulVec, add_zero, zero_add, Sum.elim_comp_inl, Sum.elim_comp_inr]
  exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) ha 2) (pow_le_pow_left₀ (norm_nonneg _) hb 2)

variable (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]

omit [DecidableEq p] [DecidableEq q] in
theorem normFin_le (v : Pl F) (a : Matrix p p (Fv F v ⊗[F] E)) (b : Matrix q q (Fv F v ⊗[F] E)) :
    normFin F v (fromBlocks a 0 0 b) ≤ max (normFin F v a) (normFin F v b) := by
  refine (normFin_le_iff F v).2 ?_
  rintro (i | i) (j | j)
  · exact (absFin_le_normFin F v a i j).trans (le_max_left _ _)
  · rw [fromBlocks_apply₁₂, Matrix.zero_apply, absFin_zero]; exact zero_le
  · rw [fromBlocks_apply₂₁, Matrix.zero_apply, absFin_zero]; exact zero_le
  · exact (absFin_le_normFin F v b i j).trans (le_max_right _ _)

theorem normInf_le (w : InfinitePlace F) (a : Matrix p p (w.Completion ⊗[F] E)) (b : Matrix q q (w.Completion ⊗[F] E)) :
    normInf F w (fromBlocks a 0 0 b) ≤ max (normInf F w a) (normInf F w b) :=
  (normInf_le_iff F w).2 fun τ => by
    rw [fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _)]
    exact (opNorm_le _ _).trans (max_le_max ((normInf_le_iff F w).1 le_rfl τ) ((normInf_le_iff F w).1 le_rfl τ))

theorem heightGL_le {X : GL (p ⊕ q) (AE F E)} {x : GL p (AE F E)} {y : GL q (AE F E)} (h : X.1 = fromBlocks x.1 0 0 y.1) :
    heightGL F X ≤ heightGL F x * heightGL F y := by
  have b : ∀ {R : Type} [CommRing R] (φ : AE F E →+* R), (Formalism.UG.bc φ X).1 = fromBlocks (Formalism.UG.bc φ x).1 0 0 (Formalism.UG.bc φ y).1 := fun φ => by
    show X.1.map φ = _
    rw [h, fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _)]; rfl
  unfold heightGL
  rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib,
    ← finprod_mul_distrib (finite_mulSupport_htFin F x) (finite_mulSupport_htFin F y)]
  refine mul_le_mul' (Finset.prod_le_prod' fun w _ => htOf_le (normInf_le F w) (b _))
    (finprod_le_finprod' (finite_mulSupport_htFin F _) ?_ fun v => htOf_le (normFin_le F v) (b _))
  exact ((finite_mulSupport_htFin F x).union (finite_mulSupport_htFin F y)).subset (Function.mulSupport_mul _ _)

end Ht

theorem htEmb : HtEmb := fun F _ _ _ _ _ _ _ _ _ =>
  ⟨1, fun _ _ _ h => (Ht.heightGL_le F h).trans_eq (one_mul _).symm,
    fun h h' => (heightGL_mul_le F h.1 h'.1).trans_eq (one_mul _).symm, fun h => one_le_heightGL F h.1⟩

end GlobalTheory.ThK.Dbl

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesS
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

def SiegelWeilStd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (m n : ℕ)
    (A : Spc F E m) (Y : Spc F E n) r s r' s', B.IsGood σ → 1 ≤ m → 1 ≤ n → min r s = 0 →
    (A.IsHerm σ B r s ∧ Y.IsSkew σ B r' s' ∨ A.IsSkew σ B r s ∧ Y.IsHerm σ B r' s') →
    ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
    ∀ (κ : Type) [Fintype κ] dd om S l, IsDbl (σ := σ) (A := A) (Y := Y) (κ := κ) B.ψ dd χ om S l →
    ∀ b K a, IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a →
    ∀ (μ : Measure (UA σ A.J)) (D : Set (UA σ A.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ A.J) D μ →
    ∀ Φ ∈ schA F κ, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => om k.1 Φ)) →
      EisValueAt (flat a (fun x => l (om x Φ)) (((m : ℂ) - n) / 2)) (((m : ℂ) - n) / 2)
        fun x => (if n < m then 1 else 2) * ⨍ g in D, thetaSum F (om x (S g Φ)) ∂μ

end GlobalTheory.ThK.Dbl

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.SecondFromFirstStatement
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {m n : ℕ}

variable {Y : Spc F E n} {A : Spc F E m}

def FinLevel : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (m n : ℕ) (A : Spc F E m) (Y : Spc F E n), B.IsGood σ → ∀ (κ : Type) [Fintype κ]
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) κ) (K : Subgroup (G2 σ Y)),
    IsCompact (K : Set (G2 σ Y)) → ∀ Φ ∈ schA F κ, ∃ Λ : Set (Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)),
      (∀ u ∈ Λ, (∀ i, evI F ((dd.e u).1 i) = 0) ∧ (∀ i, evI F ((dd.e u).2 i) = 0) ∧ ∀ k ∈ K, actB (cA σ) k u ∈ Λ) ∧
      (∀ u ∈ Λ, dd.rho B.ψ u Φ = Φ) ∧ ∃ s : Finset (κ → AF F), (∀ y ∈ s, ∀ i, evI F (y i) = 0) ∧
        ∀ Ψ : (κ → AF F) → ℂ, (∀ u ∈ Λ, dd.rho B.ψ u Ψ = Ψ) → ∀ x : κ → AF F, At (evI F) x → (∀ y ∈ s, Ψ (x + y) = 0) →
          ∀ y : κ → AF F, (∀ i, evI F (y i) = 0) → Ψ (x + y) = 0

end GlobalTheory.ThK.Dbl

end
end

