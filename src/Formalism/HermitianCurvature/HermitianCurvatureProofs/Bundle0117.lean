module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCSplit
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0112
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ScalarCommuteTransposedRMatrixEntry
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelCoordinatesCommute
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0110
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BasicLift

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCHerg
section
namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {H : Type} {f : ℕ}

def psiG (g : ℝ) (l c : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((2 * (l * c).re / g : ℝ) : ℂ))

def Fz (Y : Finset H) (κ : H → H → ℂ) (D : Fin f → H → H → ℂ → ℂ) (z : crystallineComparison.V f) : ℂ :=
  ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, D v h h' (z v)

def Nz (Y : Finset H) (κ : H → H → ℂ) (D : Fin f → H → H → ℂ → ℂ) (z : crystallineComparison.V f) : ℝ :=
  if Good z then (Fz Y κ D z).re else 0

theorem Fz_nonneg (Y : Finset H) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (D : Fin f → H → H → ℂ → ℂ)
    (hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z)) (z : crystallineComparison.V f) (hz : Good z) :
    0 ≤ Fz Y κ D z := by
  let k : Option (Fin f) → H → H → ℂ := fun o => match o with
    | none => κ
    | some v => fun h h' => D v h h' (z v)
  have hk : ∀ o, TB.PSDOn Y (k o) := by
    intro o; rcases o with _ | v
    · exact hκ
    · exact hD v (z v) (hz v)
  have hS := Formalism.FourierDecayAlt.P.schur_product _ (Option (Fin f)) Y k hk
  have hC := JCx1.decay.psd_compress Y _ hS (fun _ : Unit => Y) (fun _ => id) (fun _ h hh => hh)
  have := hC.diag_nonneg (i := ())
  simp only [Matrix.of_apply, id] at this
  convert this using 1
  unfold Fz
  simp [Fintype.prod_option, k]

theorem Nz_nonneg (Y : Finset H) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (D : Fin f → H → H → ℂ → ℂ)
    (hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z)) (z : crystallineComparison.V f) : 0 ≤ Nz Y κ D z := by
  unfold Nz; split_ifs with hz
  · exact (Complex.nonneg_iff.1 (Fz_nonneg Y κ hκ D hD z hz)).1
  · exact le_rfl

theorem isOpen_good : IsOpen {z : crystallineComparison.V f | Good z} := by
  have : {z : crystallineComparison.V f | Good z} = ⋂ v, (fun z : crystallineComparison.V f => z v) ⁻¹' {0}ᶜ := by
    ext z; simp [Good]
  rw [this]
  exact isOpen_iInter_of_finite fun v => (continuous_apply v).isOpen_preimage _ isOpen_compl_singleton

theorem Fz_continuousAt (Y : Finset H) (κ : H → H → ℂ) (D : Fin f → H → H → ℂ → ℂ)
    (hDc : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, ContinuousOn (D v h h') {0}ᶜ) (z : crystallineComparison.V f) (hz : Good z) :
    ContinuousAt (Fz Y κ D) z := by
  unfold Fz ContinuousAt
  refine tendsto_finsetSum _ fun h hh => tendsto_finsetSum _ fun h' hh' => ?_
  refine tendsto_const_nhds.mul (tendsto_finsetProd _ fun v _ => ?_)
  have := (hDc v h hh h' hh').continuousAt (isOpen_compl_singleton.mem_nhds (hz v))
  exact this.tendsto.comp (continuous_apply v).continuousAt.tendsto

theorem Nz_lsc (Y : Finset H) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (D : Fin f → H → H → ℂ → ℂ)
    (hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z))
    (hDc : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, ContinuousOn (D v h h') {0}ᶜ) : LowerSemicontinuous (Nz Y κ D) := by
  intro z y hy
  by_cases hz : Good z
  · have hc : ContinuousAt (fun z => (Fz Y κ D z).re) z :=
      Complex.continuous_re.continuousAt.comp (Fz_continuousAt Y κ D hDc z hz)
    have h1 : ∀ᶠ z' in 𝓝 z, Good z' := isOpen_good.mem_nhds hz
    have hy' : y < (Fz Y κ D z).re := by simpa [Nz, hz] using hy
    filter_upwards [h1, hc.eventually (lt_mem_nhds hy')] with z' hg hl
    simpa [Nz, hg] using hl
  · have hy' : y < 0 := by simpa [Nz, hz] using hy
    exact Filter.Eventually.of_forall fun z' => hy'.trans_le (Nz_nonneg Y κ hκ D hD z')

theorem ae_good : ∀ᵐ z : crystallineComparison.V f, Good z := by
  have : ∀ v : Fin f, ∀ᵐ z : crystallineComparison.V f, z v ≠ 0 := by
    intro v
    rw [ae_iff]
    simp only [ne_eq, not_not]
    rw [MeasureTheory.volume_pi]
    exact Measure.pi_hyperplane _ v 0
  exact (ae_all_iff.2 this).mono fun z hz => hz

theorem Fz_integrable (Y : Finset H) (κ : H → H → ℂ) (D : Fin f → H → H → ℂ → ℂ)
    (hDi : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, Integrable (D v h h')) : Integrable (Fz Y κ D) := by
  unfold Fz
  refine integrable_finsetSum _ fun h hh => integrable_finsetSum _ fun h' hh' => ?_
  exact (Integrable.fintype_prod (f := fun v => D v h h') fun v => hDi v h hh h' hh').const_mul _

theorem Nz_integrable (Y : Finset H) (κ : H → H → ℂ) (D : Fin f → H → H → ℂ → ℂ)
    (hDi : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, Integrable (D v h h')) : Integrable (Nz Y κ D) := by
  refine (Fz_integrable Y κ D hDi).re.congr ?_
  filter_upwards [ae_good] with z hz
  simp [Nz, hz]

end

end Formalism.FourierDecayAlt.P.PBC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PairOperatorCommute
section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Fr

section Abstract

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {r : ℕ}

theorem fn_comm6 (L : R.LevelData A r) {x y : A} (hx : x ∈ L.fns) (hy : y ∈ L.fns) : x * y = y * x := L.fns_comm x hx y hy

theorem c_fns (L : R.LevelData A r) (l : Fin r) : L.c l ∈ L.fns := by
  exact Or.inl (Or.inl (Or.inl (Or.inl ⟨l, rfl⟩)))
theorem ci_fns (L : R.LevelData A r) (l : Fin r) : L.ci l ∈ L.fns := by
  exact Or.inl (Or.inl (Or.inl (Or.inr ⟨l, rfl⟩)))
theorem cb_fns (L : R.LevelData A r) (l : Fin r) : L.cb l ∈ L.fns := by
  exact Or.inl (Or.inl (Or.inr ⟨l, rfl⟩))
theorem cbi_fns (L : R.LevelData A r) (l : Fin r) : L.cbi l ∈ L.fns := by
  exact Or.inl (Or.inr ⟨l, rfl⟩)

theorem hol_comm_star (L : R.LevelData A r) (hp : ∀ l, star (L.p l) = -L.pb l) (hc : ∀ l, star (L.c l) = L.cb l)
    (hci : ∀ l, star (L.ci l) = L.cbi l) (l m : Fin r) :
    ∀ x ∈ hol (⟨L.p l, L.c l, L.ci l⟩ : Site A), ∀ y ∈ hol (⟨L.p m, L.c m, L.ci m⟩ : Site A), Commute x (star y) := by
  have hf : ∀ x ∈ L.fns, ∀ y ∈ L.fns, Commute x y := fun x hx y hy => L.fns_comm x hx y hy
  intro x hx y hy
  simp only [hol, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hy with rfl | rfl | rfl
  · rw [hp]
    refine Commute.neg_right ?_
    rcases hx with rfl | rfl | rfl
    · exact L.p_pb l m
    · exact (L.pb_c m l).symm
    · exact (L.pb_ci m l).symm
  · rw [hc]
    rcases hx with rfl | rfl | rfl
    · exact L.p_cb l m
    · exact hf _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨l, rfl⟩)))) _ (Or.inl (Or.inl (Or.inr ⟨m, rfl⟩)))
    · exact hf _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨l, rfl⟩)))) _ (Or.inl (Or.inl (Or.inr ⟨m, rfl⟩)))
  · rw [hci]
    rcases hx with rfl | rfl | rfl
    · exact L.p_cbi l m
    · exact hf _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨l, rfl⟩)))) _ (Or.inl (Or.inr ⟨m, rfl⟩))
    · exact hf _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨l, rfl⟩)))) _ (Or.inl (Or.inr ⟨m, rfl⟩))

theorem hol_comm_hol (L : R.LevelData A r) {l m : Fin r} (hlm : l ≠ m) :
    ∀ x ∈ hol (⟨L.p l, L.c l, L.ci l⟩ : Site A), ∀ y ∈ hol (⟨L.p m, L.c m, L.ci m⟩ : Site A), Commute x y := by
  have hf : ∀ x ∈ L.fns, ∀ y ∈ L.fns, Commute x y := fun x hx y hy => L.fns_comm x hx y hy
  have hlm' : m ≠ l := fun h => hlm h.symm
  intro x hx y hy
  simp only [hol, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  · exact L.p_p l m
  · have := L.p_c l m; rw [if_neg hlm, add_zero] at this; exact this
  · have := L.p_ci l m; rw [if_neg hlm, sub_zero] at this; exact this
  · have := L.p_c m l; rw [if_neg hlm', add_zero] at this; exact this.symm
  · exact hf _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨l, rfl⟩)))) _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨m, rfl⟩))))
  · exact hf _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨l, rfl⟩)))) _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨m, rfl⟩))))
  · have := L.p_ci m l; rw [if_neg hlm', sub_zero] at this; exact this.symm
  · exact hf _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨l, rfl⟩)))) _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨m, rfl⟩))))
  · exact hf _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨l, rfl⟩)))) _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨m, rfl⟩))))

theorem good_of_adm {S : Type} (st : Fr.Start A) (w : List (Letter ℂ S)) (hw : Fr.admitted st w) : Good w := by
  obtain ⟨h1, h2, -, h4⟩ := hw
  refine ⟨h1, h2, h4.imp fun {l l'} h => ?_⟩
  unfold RegL
  split_ifs
  · simpa using h 1 (by norm_num)
  · intro h'
    apply h (-1) (by norm_num)
    push_cast
    linear_combination -h'

end Abstract

section Pairs

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem pair_operator_commute {a b c d : Module.End ℂ V} (h1 : a * c = c * a) (h2 : d * b = b * d) :
    (mkP a b : Pr V) * mkP c d = mkP c d * mkP a b := by
  refine Prod.ext ?_ ?_
  · show a * c = c * a
    exact h1
  · show MulOpposite.op b * MulOpposite.op d = MulOpposite.op d * MulOpposite.op b
    rw [← MulOpposite.op_mul, ← MulOpposite.op_mul, h2]

end Pairs

section Levels

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem star_site_ops {X : ActualOps k r z z' π π'} {L : R.LevelData (Pr (RadSp k r z z' π π')) r}
    (hL : IsActualLevel X L) :
    (∀ l, star (L.p l) = -L.pb l) ∧ (∀ l, star (L.c l) = L.cb l) ∧ ∀ l, star (L.ci l) = L.cbi l := by
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, -⟩ := hL
  have hs : ∀ a b : Module.End ℂ (RadSp k r z z' π π'), star (mkP a b : Pr (RadSp k r z z' π π')) = mkP b a :=
    fun a b => rfl
  refine ⟨fun l => ?_, fun l => ?_, fun l => ?_⟩
  · rw [hp, hpb, hs]
    refine Prod.ext rfl ?_
    show MulOpposite.op (X.op l 0) = -MulOpposite.op (-X.op l 0)
    rw [← MulOpposite.op_neg, neg_neg]
  · rw [hc, hcb, hs]
  · rw [hci, hcbi, hs]

theorem isSite_actual {X : ActualOps k r z z' π π'} {L : R.LevelData (Pr (RadSp k r z z' π π')) r}
    (hL : IsActualLevel X L) (l : Fin r) : IsSite (site L l) := by
  obtain ⟨hp, hc, hci⟩ := star_site_ops hL
  refine ⟨⟨L.c_ci l, L.ci_c l, ?_⟩, hol_comm_star L hp hc hci l l⟩
  have h := L.p_c l l
  rw [if_pos rfl] at h
  exact h

theorem QQi_mem_all (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
    (𝒜 : StarSubalgebra ℂ (Pr (RadSp k r z z' π π'))) (i : Fin (r + 1)) (Y : ℂ)
    (hQ : ∀ a b, st.QQ Y a b ∈ 𝒜)
    (hS : ∀ l : Fin r, i.val ≤ l.val → L.p l ∈ 𝒜 ∧ L.c l ∈ 𝒜 ∧ L.ci l ∈ 𝒜) (a b : Fin 2) :
    QQi L st i Y a b ∈ 𝒜 := by
  have hmul : ∀ M N : M2 (Pr (RadSp k r z z' π π')), (∀ a b, M a b ∈ 𝒜) → (∀ a b, N a b ∈ 𝒜) →
      ∀ a b, (M * N) a b ∈ 𝒜 := by
    intro M N hM hN a b
    rw [Matrix.mul_apply]
    exact Subalgebra.sum_mem _ fun c _ => Subalgebra.mul_mem _ (hM a c) (hN c b)
  have hone : ∀ a b, (1 : M2 (Pr (RadSp k r z z' π π'))) a b ∈ 𝒜 := by
    intro a b
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hct : ∀ M : M2 (Pr (RadSp k r z z' π π')), (∀ a b, M a b ∈ 𝒜) → ∀ a b, Mᴴ a b ∈ 𝒜 := by
    intro M hM a b
    rw [Matrix.conjTranspose_apply]
    exact star_mem (hM b a)
  have hts : ∀ (Y' : ℂ) (l : Fin r), i.val ≤ l.val → ∀ a b, Ts (site L l) Y' a b ∈ 𝒜 := by
    intro Y' l hl a b
    obtain ⟨hp, hc, hci⟩ := hS l hl
    fin_cases a <;> fin_cases b
    · exact add_mem (algebraMap_mem 𝒜 Y') hp
    · exact neg_mem hc
    · exact hci
    · exact zero_mem _
  have htp : ∀ (Y' : ℂ) (n j : ℕ), r - j = n → i.val ≤ j → ∀ a b, tprod L Y' j a b ∈ 𝒜 := by
    intro Y' n
    induction n with
    | zero =>
      intro j hj hij
      rw [tprod, dite_eq_right (by omega)]
      exact hone
    | succ n ih =>
      intro j hj hij
      rw [tprod, dite_eq_left (by omega)]
      exact hmul _ _ (ih (j + 1) (by omega) (by omega)) (hts Y' ⟨j, by omega⟩ hij)
  unfold QQi
  exact hmul _ _ (hmul _ _ (hct _ (htp _ _ _ rfl le_rfl)) hQ) (htp _ _ _ rfl le_rfl) a b

theorem QQi_castSucc (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
    (l : Fin r) (Y : ℂ) (hY : star Y = Y) :
    QQi L st l.castSucc Y = (Ts (site L l) Y)ᴴ * QQi L st l.succ Y * Ts (site L l) Y := by
  have ht : ∀ Y' : ℂ, tprod L Y' (l.castSucc : ℕ) = tprod L Y' (l.succ : ℕ) * Ts (site L l) Y' := by
    intro Y'
    rw [tprod, dite_eq_left (show (l.castSucc : ℕ) < r from l.isLt)]
    rfl
  unfold QQi
  rw [ht, ht, hY, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

end Levels

section Top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem qqCommutes_actual (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (hD : IsData P z z' π π' X μ L st l0) (l : Fin P.r) : QQCommutes (QQi L st l.succ) (site L l) := by
  obtain ⟨hpl, -, hL, hQQ, -⟩ := hD
  obtain ⟨sp, sc, sci⟩ := star_site_ops hL
  obtain ⟨hp, -, hc, hci, -⟩ := hL
  have ht : ∀ (i : Fin 6) (Y : ℂ) (a b : Fin 2), X.t Y a b * X.op l i = X.op l i * X.t Y a b :=
    fun i => (Formalism.FourierDecayAlt.P.level_coordinates_commute Wp Wq P z z' π π' hpl X l i).1
  have htn : ∀ (i : Fin 6) (Y : ℂ) (a b : Fin 2), X.t Y a b * -X.op l i = -X.op l i * X.t Y a b := by
    intro i Y a b; rw [mul_neg, neg_mul, ht]
  intro Y
  have hmem : ∀ a b, QQi L st l.succ Y a b ∈ StarSubalgebra.centralizer ℂ (hol (site L l)) := by
    refine QQi_mem_all L st _ l.succ Y ?_ ?_
    · intro a b
      rw [hQQ Y, Matrix.smul_apply]
      refine SMulMemClass.smul_mem _ ?_
      simp only [ActualOps.QQ, Matrix.of_apply]
      rw [StarSubalgebra.mem_centralizer_iff]
      intro g hg
      simp only [hol, site, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · rw [hp l]
        exact ⟨pair_operator_commute (ht _ _ _ _).symm (htn _ _ _ _), pair_operator_commute (htn _ _ _ _).symm (ht _ _ _ _)⟩
      · rw [hc l]
        exact ⟨pair_operator_commute (ht _ _ _ _).symm (ht _ _ _ _), pair_operator_commute (ht _ _ _ _).symm (ht _ _ _ _)⟩
      · rw [hci l]
        exact ⟨pair_operator_commute (ht _ _ _ _).symm (ht _ _ _ _), pair_operator_commute (ht _ _ _ _).symm (ht _ _ _ _)⟩
    · intro m hm
      have hne : l ≠ m := by
        intro h; rw [← h, Fin.val_succ] at hm; omega
      have key : ∀ y ∈ hol (site L m), y ∈ StarSubalgebra.centralizer ℂ (hol (site L l)) := by
        intro y hy
        rw [StarSubalgebra.mem_centralizer_iff]
        intro g hg
        exact ⟨hol_comm_hol L hne g hg y hy, (hol_comm_star L sp sc sci m l y hy g hg).symm⟩
      exact ⟨key _ (by simp [hol, site]), key _ (by simp [hol, site]), key _ (by simp [hol, site])⟩
  intro a b x hx
  have h := hmem a b
  rw [StarSubalgebra.mem_centralizer_iff] at h
  rcases hx with hx | hx
  · exact (h x hx).1.symm
  · have h2 := (h _ hx).2
    rw [star_star] at h2
    exact h2.symm

theorem siteStep_actual (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (w : List (Letter ℂ S)) (hD : IsData P z z' π π' X μ L st l0) (hw : WordOK P z z' π π' st l0 w) (l : Fin P.r) :
    star (bTl L l w) * RRi L st l.succ w * bTl L l w = RRi L st l.castSucc w := (by
    have hL := hD.2.2.1
    exact Formalism.FourierDecayAlt.P.site_exchange_relation ℂ _ S (site L l) (QQi L st l.succ) (QQi L st l.castSucc) w
      (isSite_actual hL l) (qqCommutes_actual P z z' π π' X μ L st l0 hD l)
      (fun Y hY => QQi_castSucc L st l Y hY) (good_of_adm st w hw.1))

end Top

end Formalism.FourierDecayAlt.P5.HerA
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TLChoiceChk
section
namespace Formalism.FourierDecayAlt.TL

open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr

theorem wordLiftOfParts : WordLiftOfParts := by
  intro hstep hlet A S _ _ _ _ _ _ r n L st Lf w hA hL hn
  induction w with
  | nil =>
    intro _ e
    have h1 : ((ofWord L st ([] : List (Letter ℂ S))).F * bTA L ([] : List (Letter ℂ S))) = 1 := by
      simp [ofWord, bTA, bT, Start.frame]
    rw [h1, Matrix.one_apply]
    split_ifs
    · simpa using hL.one
    · exact hL.zero _ _
  | cons l w ih =>
    intro hw e
    have hw' : admitted st w := by
      obtain ⟨h1, h2, h3, h4⟩ := hw
      refine ⟨?_, fun l' hl' => h2 l' (List.mem_cons_of_mem _ hl'),
        fun l' hl' => h3 l' (List.mem_cons_of_mem _ hl'), h4.of_cons⟩
      simp only [List.map_cons, List.nodup_cons] at h1
      exact h1.2
    rw [hstep A S r L st l w hA hw e, Matrix.mul_apply]
    refine Finset.sum_induction _ (Lf _ _) (fun a b ha hb => hL.add ha hb) (hL.zero _ _) ?_
    intro f _
    have hcoef : Lf n (9 * (r + 1) * n) ((∑ i : Fin 2, eU l.intersection_update_fsHerm_neg_one i 0 * letterCol L st l w i : SlopeTestRemainingChoices S A) e f) := by
      rw [Matrix.sum_apply]
      refine Finset.sum_induction _ (Lf _ _) (fun a b ha hb => hL.add ha hb) (hL.zero _ _) ?_
      intro i _
      rw [Matrix.mul_apply]
      refine Finset.sum_induction _ (Lf _ _) (fun a b ha hb => hL.add ha hb) (hL.zero _ _) ?_
      intro g _
      simp only [eU, Matrix.of_apply]
      split_ifs
      · rw [one_mul]
        exact hlet A S r n L st Lf l w hA hL hn hw i g f
      · rw [zero_mul]
        exact hL.zero _ _
    refine hL.mono ?_ ?_ (hL.mul hcoef (ih hw' f))
    · simp only [List.length_cons]
      exact le_of_eq (by ring)
    · simp only [List.length_cons]
      exact le_of_eq (by ring)

end Formalism.FourierDecayAlt.TL
end

