module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0046
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0160
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0132
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVnice

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDAsm
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt MeasureTheory

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

section gen

variable (P : M.Par)

theorem jd_actA_add (a b : MA.A P (MA.DQ P)) (x : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (a + b) x = MA.actA P a x + MA.actA P b x := by
  funext π
  show ∑ π', ((a + b) π π').1 (x π') = ∑ π', (a π π').1 (x π') + ∑ π', (b π π').1 (x π')
  rw [← Finset.sum_add_distrib]
  rfl

theorem jd_actA_zero (x : M.Ty P → MA.SmQ P.r P.TT) : MA.actA P 0 x = 0 := by
  funext π
  show ∑ π', ((0 : MA.A P (MA.DQ P)) π π').1 (x π') = 0
  exact Finset.sum_eq_zero fun _ _ => rfl

theorem jd_actA_addR (a : MA.A P (MA.DQ P)) (x y : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P a (x + y) = MA.actA P a x + MA.actA P a y := by
  funext π
  show ∑ π', (a π π').1 (x π' + y π') = ∑ π', (a π π').1 (x π') + ∑ π', (a π π').1 (y π')
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => map_add _ _ _

theorem jd_actA_smulR (a : MA.A P (MA.DQ P)) (c : ℂ) (x : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P a (c • x) = c • MA.actA P a x := by
  funext π
  show ∑ π', (a π π').1 (c • x π') = c • ∑ π', (a π π').1 (x π')
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun _ _ => map_smul _ _ _

theorem jd_actA_zeroR (a : MA.A P (MA.DQ P)) : MA.actA P a 0 = 0 := by
  have h := jd_actA_smulR P a 0 0
  rw [zero_smul, zero_smul] at h
  exact h

theorem jd_actA_listsum {ι : Type} (a : MA.A P (MA.DQ P)) (l : List ι) (g : ι → M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P a (l.map g).sum = (l.map fun i => MA.actA P a (g i)).sum := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil]; exact jd_actA_zeroR P a
  | cons i l ih => rw [List.map_cons, List.sum_cons, jd_actA_addR, ih, List.map_cons, List.sum_cons]

variable {P}

theorem jd_word_span {Fn : Type} (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (Good : ℕ → Fn → Prop)
    (tr : Fn → M.Ty P → MA.SmQ P.r P.TT) (m : ℕ)
    (hBdd : ∀ X ∈ MA.hatSet P L, ∀ b ∈ Submonoid.closure (MA.bddSet P L), X * b ∈ Submodule.span ℂ (bddHat P L))
    (hStep : ∀ i, i < m → ∀ F, Good i F → ∀ X ∈ MA.hatSet P L,
      ∃ ts : List (MA.A P (MA.DQ P) × Fn), (∀ t ∈ ts, t.1 ∈ Submonoid.closure (MA.bddSet P L) ∧ Good (i + 1) t.2) ∧
        MA.actA P X (tr F) = (ts.map fun t => MA.actA P t.1 (tr t.2)).sum) :
    ∀ w : List (MA.A P (MA.DQ P)), w.length ≤ m → (∀ a ∈ w, a ∈ MA.hatSet P L) → ∀ F, Good 0 F →
      MA.actA P w.prod (tr F) ∈ Submodule.span ℂ
        {u | ∃ b ∈ Submonoid.closure (MA.bddSet P L), ∃ F', Good w.length F' ∧ u = MA.actA P b (tr F')} := by
  intro w
  induction w with
  | nil =>
    intro _ _ F hF
    refine Submodule.subset_span ⟨1, Submonoid.one_mem _, F, hF, ?_⟩
    rw [List.prod_nil, actA_one]
  | cons a w ih =>
    intro hlen hw F hF
    have ha : a ∈ MA.hatSet P L := hw a (List.mem_cons_self ..)
    have hlt : w.length < m := by simp only [List.length_cons] at hlen; omega
    have hIH := ih hlt.le (fun x hx => hw x (List.mem_cons_of_mem _ hx)) F hF
    rw [List.prod_cons, actA_mul]
    have hgen : ∀ c ∈ Submodule.span ℂ (bddHat P L), ∀ F', Good w.length F' →
        MA.actA P c (tr F') ∈ Submodule.span ℂ
          {u | ∃ b ∈ Submonoid.closure (MA.bddSet P L), ∃ F', Good (a :: w).length F' ∧ u = MA.actA P b (tr F')} := by
      intro c hc F' hF'
      induction hc using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨b', hb', X', hX', rfl⟩ := hx
        obtain ⟨ts, hts, he⟩ := hStep w.length hlt F' hF' X' hX'
        rw [actA_mul, he, jd_actA_listsum]
        refine list_sum_mem fun u hu => ?_
        obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hu
        rw [← actA_mul]
        exact Submodule.subset_span ⟨b' * t.1, Submonoid.mul_mem _ hb' (hts t ht).1, t.2, (hts t ht).2, rfl⟩
      | zero => rw [jd_actA_zero]; exact Submodule.zero_mem _
      | add x y _ _ h1 h2 => rw [jd_actA_add]; exact Submodule.add_mem _ h1 h2
      | smul c x _ h1 => rw [actA_smul]; exact Submodule.smul_mem _ c h1
    have key : ∀ x ∈ Submodule.span ℂ
        {u | ∃ b ∈ Submonoid.closure (MA.bddSet P L), ∃ F', Good w.length F' ∧ u = MA.actA P b (tr F')},
        MA.actA P a x ∈ Submodule.span ℂ
          {u | ∃ b ∈ Submonoid.closure (MA.bddSet P L), ∃ F', Good (a :: w).length F' ∧ u = MA.actA P b (tr F')} := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨b, hb, F', hF', rfl⟩ := hx
        rw [← actA_mul]
        exact hgen _ (hBdd a ha b hb) F' hF'
      | zero => rw [jd_actA_zeroR]; exact Submodule.zero_mem _
      | add x y _ _ h1 h2 => rw [jd_actA_addR]; exact Submodule.add_mem _ h1 h2
      | smul c x _ h1 => rw [jd_actA_smulR]; exact Submodule.smul_mem _ c h1
    exact key _ hIH

variable (P)

theorem jd_evQ_meas (g : MA.SmQ P.r P.TT) : AEStronglyMeasurable (MA.evQ P g) (MA.mu0 P.r P.TT) := by
  have hs : ContDiffOn ℝ MA.sm (MA.ext (g : MA.Qp P.r P.TT → ℂ)) (MA.Qset P.r P.TT) := g.2
  have h2 := hs.continuousOn.comp_continuous continuous_subtype_val (fun q => q.2)
  have hc : Continuous (MA.evQ P g) := h2.congr fun q => by
    simp only [Function.comp, MA.ext, dif_pos q.2]
    rfl
  exact hc.aestronglyMeasurable

def componentwiseL2 (u : M.Ty P → MA.SmQ P.r P.TT) : Prop := ∀ π, MemLp (MA.evQ P (u π)) 2 (MA.mu0 P.r P.TT)

theorem componentwiseL2_iff_integrable (u : M.Ty P → MA.SmQ P.r P.TT) :
    componentwiseL2 P u ↔ ∀ π, Integrable (fun q => ‖MA.evQ P (u π) q‖ ^ 2) (MA.mu0 P.r P.TT) :=
  forall_congr' fun π => memLp_two_iff_integrable_sq_norm (jd_evQ_meas P (u π))

theorem componentwiseL2_of_span (G : Set (M.Ty P → MA.SmQ P.r P.TT)) (h : ∀ u ∈ G, componentwiseL2 P u) :
    ∀ u ∈ Submodule.span ℂ G, componentwiseL2 P u := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => intro π; exact MemLp.zero
  | add x y _ _ h1 h2 => intro π; exact (h1 π).add (h2 π)
  | smul c x _ h1 => intro π; exact (h1 π).const_smul c

end gen

theorem jd_arith (C2 C3 C5 R n N A₀ : ℝ) (hC2 : 0 ≤ C2) (hR : 0 ≤ R) (hn : 1 ≤ n) (hN : 0 ≤ N)
    (hA : (8 * C2 + |C3| + |C5|) * (R + 1) ^ 4 * (N * n ^ 2 + n ^ 3) ≤ A₀) :
    (∀ i o : ℝ, i + 1 ≤ 2 * N + 2 → o ≤ C2 * n →
      C3 * (R + 1) * n ^ 2 + 6 * R * o + C2 * (R + 1) * n ≤ A₀ - i * (C2 * (R + 1) * n)) ∧
      (∀ i : ℝ, i ≤ 2 * N + 2 → C5 * (R + 1) ^ 2 * n ≤ A₀ - i * (C2 * (R + 1) * n)) := by
  have hρ : 1 ≤ R + 1 := by linarith
  have hρ0 : 0 ≤ R + 1 := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hρ4 : R + 1 ≤ (R + 1) ^ 4 := le_self_pow₀ hρ (by norm_num)
  have hR4 : R ≤ (R + 1) ^ 4 := by linarith
  have hρ24 : (R + 1) ^ 2 ≤ (R + 1) ^ 4 := pow_le_pow_right₀ hρ (by norm_num)
  have hn2 : n ≤ n ^ 2 := le_self_pow₀ hn (by norm_num)
  have hn3 : n ≤ n ^ 3 := le_self_pow₀ hn (by norm_num)
  have hn23 : n ^ 2 ≤ n ^ 3 := pow_le_pow_right₀ hn (by norm_num)
  have hNn : 0 ≤ N * n ^ 2 := by positivity
  set X : ℝ := (R + 1) ^ 4 * (N * n ^ 2 + n ^ 3) with hX
  have hX0 : 0 ≤ X := by positivity
  have hY : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a ≤ (R + 1) ^ 4 → b ≤ n ^ 3 → a * b ≤ X := by
    intro a b ha hb h1 h2
    calc a * b ≤ (R + 1) ^ 4 * n ^ 3 := mul_le_mul h1 h2 hb (by positivity)
      _ ≤ X := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hXa : (R + 1) * n ^ 2 ≤ X := hY _ _ hρ0 (by positivity) hρ4 hn23
  have hXa' : (R + 1) ^ 2 * n ≤ X := hY _ _ (by positivity) hn0 hρ24 hn3
  have hXc : R * n ≤ X := hY _ _ hR hn0 hR4 hn3
  have hXb : (2 * N + 2) * ((R + 1) * n) ≤ 2 * X := by
    have h1' : N * n ≤ N * n ^ 2 := mul_le_mul_of_nonneg_left hn2 hN
    have h2' : (R + 1) * (N * n + n) ≤ (R + 1) ^ 4 * (N * n ^ 2 + n ^ 3) :=
      mul_le_mul hρ4 (by linarith) (by positivity) (by positivity)
    have e : (2 * N + 2) * ((R + 1) * n) = 2 * ((R + 1) * (N * n + n)) := by ring
    rw [e, hX]; linarith
  have hdm0 : 0 ≤ C2 * (R + 1) * n := by positivity
  have e2 : (2 * N + 2) * (C2 * (R + 1) * n) ≤ 2 * C2 * X := by
    have := mul_le_mul_of_nonneg_left hXb hC2
    have e : (2 * N + 2) * (C2 * (R + 1) * n) = C2 * ((2 * N + 2) * ((R + 1) * n)) := by ring
    rw [e]; linarith
  have e3 : C3 * (R + 1) * n ^ 2 ≤ |C3| * X :=
    calc C3 * (R + 1) * n ^ 2 = C3 * ((R + 1) * n ^ 2) := by ring
      _ ≤ |C3| * ((R + 1) * n ^ 2) := mul_le_mul_of_nonneg_right (le_abs_self C3) (by positivity)
      _ ≤ |C3| * X := mul_le_mul_of_nonneg_left hXa (abs_nonneg C3)
  have e3' : C5 * (R + 1) ^ 2 * n ≤ |C5| * X :=
    calc C5 * (R + 1) ^ 2 * n = C5 * ((R + 1) ^ 2 * n) := by ring
      _ ≤ |C5| * ((R + 1) ^ 2 * n) := mul_le_mul_of_nonneg_right (le_abs_self C5) (by positivity)
      _ ≤ |C5| * X := mul_le_mul_of_nonneg_left hXa' (abs_nonneg C5)
  have e4 : 0 ≤ |C5| * X := mul_nonneg (abs_nonneg _) hX0
  have e4' : 0 ≤ |C3| * X := mul_nonneg (abs_nonneg _) hX0
  have hA2 : (8 * C2 + |C3| + |C5|) * X ≤ A₀ := by
    have e : (8 * C2 + |C3| + |C5|) * X = (8 * C2 + |C3| + |C5|) * (R + 1) ^ 4 * (N * n ^ 2 + n ^ 3) := by
      rw [hX]; ring
    rw [e]; exact hA
  have hsplit : (8 * C2 + |C3| + |C5|) * X = 2 * C2 * X + 6 * C2 * X + |C3| * X + |C5| * X := by ring
  have e6 : 0 ≤ 6 * C2 * X := by positivity
  constructor
  · intro i o hi ho
    have e1 : (i + 1) * (C2 * (R + 1) * n) ≤ (2 * N + 2) * (C2 * (R + 1) * n) := mul_le_mul_of_nonneg_right hi hdm0
    have e5 : 6 * R * o ≤ 6 * C2 * X := by
      have h1 : R * o ≤ R * (C2 * n) := mul_le_mul_of_nonneg_left ho hR
      have h2 : R * (C2 * n) = C2 * (R * n) := by ring
      have h3 : C2 * (R * n) ≤ C2 * X := mul_le_mul_of_nonneg_left hXc hC2
      linarith
    have e : C3 * (R + 1) * n ^ 2 + 6 * R * o + C2 * (R + 1) * n + i * (C2 * (R + 1) * n) =
        C3 * (R + 1) * n ^ 2 + 6 * R * o + (i + 1) * (C2 * (R + 1) * n) := by ring
    linarith
  · intro i hi
    have e1 : i * (C2 * (R + 1) * n) ≤ (2 * N + 2) * (C2 * (R + 1) * n) := mul_le_mul_of_nonneg_right hi hdm0
    linarith

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapAVTr
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open Gauge Gauge.VLem

noncomputable section

section model

variable (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r)

def capaVpM (Y : ℂ) (i : ℕ) : Matrix (Fin 2) (Fin 2) (MA.A P (MA.DQ P)) :=
  (((List.finRange P.r).take i).reverse.map fun l => L.Tvl Y l).prod

theorem capaVpM_zero (Y : ℂ) : capaVpM P L Y 0 = 1 := by
  simp [capaVpM]

theorem capaVpM_succ (Y : ℂ) (i : ℕ) (h : i < P.r) :
    capaVpM P L Y (i + 1) = L.Tvl Y ⟨i, h⟩ * capaVpM P L Y i := by
  simp [capaVpM, List.take_add_one, h]

theorem capa_tvprod (Y : ℂ) : L.Tvprod Y = capaVpM P L Y P.r := by
  simp [R.LevelData.Tvprod, capaVpM, List.ofFn_eq_map, List.map_reverse, List.take_of_length_le]

theorem capa_Tvl_mul_0 (Y : ℂ) (l : Fin P.r) (V : Matrix (Fin 2) (Fin 2) (MA.A P (MA.DQ P))) :
    (L.Tvl Y l * V) 0 0 = (algebraMap ℂ (MA.A P (MA.DQ P)) Y - L.pb l) * V 0 0 + -L.cb l * V 1 0 := by
  simp [R.LevelData.Tvl, Matrix.mul_apply, Fin.sum_univ_two]

theorem capa_Tvl_mul_1 (Y : ℂ) (l : Fin P.r) (V : Matrix (Fin 2) (Fin 2) (MA.A P (MA.DQ P))) :
    (L.Tvl Y l * V) 1 0 = L.cbi l * V 0 0 := by
  simp [R.LevelData.Tvl, Matrix.mul_apply, Fin.sum_univ_two]

theorem capa_actA_pb (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (MA.pbA P (MA.DQ P) l) f = fun ρ => MA.eulerQ (TT := P.TT) (M.vcb l) (f ρ) := by
  show MA.actA P (MA.sc P (MA.DQ P) _) f = _
  rw [actA_sc]
  rfl

theorem capa_actA_cb (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (MA.cbA P (MA.DQ P) l) f = fun ρ => MA.coordQ (TT := P.TT) (M.vcb l) * f ρ := by
  show MA.actA P (MA.sc P (MA.DQ P) _) f = _
  rw [actA_sc]
  rfl

theorem capa_actA_cbi (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (MA.cbiA P (MA.DQ P) l) f = fun ρ => Ring.inverse (MA.coordQ (TT := P.TT) (M.vcb l)) * f ρ := by
  show MA.actA P (MA.sc P (MA.DQ P) _) f = _
  rw [actA_sc]
  rfl

end model

section ind

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)}

theorem capa_vab_ind (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (he : IsFrameB P Bs e) (Y : ℂ) :
    ∀ i : ℕ, i ≤ P.r → ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)),
      FamR P Bs Dc Φ →
      (FamR P Bs Dc (Q.crd (Q.cmp (Q.vAB P.r Y i) 0) Φ) ∧
        trR P Bs.μsec e (Q.crd (Q.cmp (Q.vAB P.r Y i) 0) Φ) =
          MA.actA P (Vp P Y i 0 0) (trR P Bs.μsec e Φ)) ∧
      (FamR P Bs Dc (Q.crd (Q.cmp (Q.vAB P.r Y i) 1) Φ) ∧
        trR P Bs.μsec e (Q.crd (Q.cmp (Q.vAB P.r Y i) 1) Φ) =
          MA.actA P (Vp P Y i 1 0) (trR P Bs.μsec e Φ)) := by
  intro i
  induction i with
  | zero =>
    intro _ Dc Φ hΦ
    have h0 : Q.crd (Q.cmp (Q.vAB P.r Y 0) 0) Φ = Φ := rfl
    have h1 : Q.crd (Q.cmp (Q.vAB P.r Y 0) 1) Φ = 0 := rfl
    have v0 : Vp P Y 0 0 0 = 1 := by simp [Vp_zero]
    have v1 : Vp P Y 0 1 0 = 0 := by simp [Vp_zero]
    rw [h0, h1, v0, v1, actA_one, actA_zero, trR_zero]
    refine ⟨⟨hΦ, rfl⟩, ⟨?_, rfl⟩⟩
    have := famR_smul hΦ 0
    rwa [zero_smul] at this
  | succ i ih =>
    intro hi Dc Φ hΦ
    have h : i < P.r := hi
    obtain ⟨⟨hA, tA⟩, ⟨hB, tB⟩⟩ := ih (Nat.le_of_lt h) Dc Φ hΦ
    set ΦA := Q.crd (Q.cmp (Q.vAB P.r Y i) 0) Φ with hΦA
    set ΦB := Q.crd (Q.cmp (Q.vAB P.r Y i) 1) Φ with hΦB
    have hv : Q.vAB (E := Wq →L[ℂ] Wp) P.r Y (i + 1) =
        (fun f => Y • (Q.vAB P.r Y i).1 f + pOp ⟨i, h⟩ ((Q.vAB P.r Y i).1 f) -
          cOp ⟨i, h⟩ ((Q.vAB P.r Y i).2 f), fun f => ciOp ⟨i, h⟩ ((Q.vAB P.r Y i).1 f)) := by
      simp only [Q.vAB, dif_pos h]
    have e0 : Q.crd (Q.cmp (Q.vAB P.r Y (i + 1)) 0) Φ =
        Y • ΦA + Q.crd (pOp ⟨i, h⟩) ΦA - Q.crd (cOp ⟨i, h⟩) ΦB := by
      rw [hv]; rfl
    have e1 : Q.crd (Q.cmp (Q.vAB P.r Y (i + 1)) 1) Φ = Q.crd (ciOp ⟨i, h⟩) ΦA := by
      rw [hv]; rfl
    have hpA : FamR P Bs Dc (Q.crd (pOp ⟨i, h⟩) ΦA) := famR_opL hA ⟨i, h⟩ 0
    have hcB : FamR P Bs Dc (Q.crd (cOp ⟨i, h⟩) ΦB) := famR_opL hB ⟨i, h⟩ 1
    have hciA : FamR P Bs Dc (Q.crd (ciOp ⟨i, h⟩) ΦA) := famR_opL hA ⟨i, h⟩ 2
    have hsum : FamR P Bs Dc (Y • ΦA + Q.crd (pOp ⟨i, h⟩) ΦA) := famR_add (famR_smul hA _) hpA
    have tc : trR P Bs.μsec e (Q.crd (cOp ⟨i, h⟩) ΦB) =
        fun ρ => MA.coordQ (TT := P.TT) (M.vc ⟨i, h⟩) * trR P Bs.μsec e ΦB ρ :=
      trR_mul hpl hk he hB _ hcB (fun c => c ⟨i, h⟩) (fun _ _ => rfl) _ (fun q => coordE_vc _ _)
    have tci : trR P Bs.μsec e (Q.crd (ciOp ⟨i, h⟩) ΦA) =
        fun ρ => Ring.inverse (MA.coordQ (TT := P.TT) (M.vc ⟨i, h⟩)) * trR P Bs.μsec e ΦA ρ :=
      trR_mul hpl hk he hA _ hciA (fun c => (c ⟨i, h⟩)⁻¹) (fun _ _ => rfl) _ (fun q => by
        rw [inv_coordQ_apply _ (fun x hx => by rw [coordE_vc]; exact hx.1 _), coordE_vc])
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [e0]; exact famR_sub hsum hcB
    · rw [e0, trR_sub _ _ _ _ (fun ρ => smR hpl hk he hsum ρ) (fun ρ => smR hpl hk he hcB ρ),
        trR_add _ _ _ _ (fun ρ => smR hpl hk he (famR_smul hA _) ρ) (fun ρ => smR hpl hk he hpA ρ), trR_smul,
        trR_p hpl hk he hA, tc, tA, tB, Vp_succ P Y i h, Ts_mul_0, actA_add, actA_mul, actA_mul,
        actA_neg, actA_add, actA_algebraMap, actA_p, actA_c, sub_eq_add_neg]
    · rw [e1]; exact hciA
    · rw [e1, tci, tA, Vp_succ P Y i h, Ts_mul_1, actA_mul, actA_ci]

theorem capa_vabm_ind (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (he : IsFrameB P Bs e)
    (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (hL : MA.IsModelLevel P (MA.DQ P) L) (Y : ℂ) :
    ∀ i : ℕ, i ≤ P.r → ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)),
      FamR P Bs Dc Φ →
      (FamR P Bs Dc (Q.crd (Q.cmp (vABm P.r Y i) 0) Φ) ∧
        trR P Bs.μsec e (Q.crd (Q.cmp (vABm P.r Y i) 0) Φ) =
          MA.actA P (capaVpM P L Y i 0 0) (trR P Bs.μsec e Φ)) ∧
      (FamR P Bs Dc (Q.crd (Q.cmp (vABm P.r Y i) 1) Φ) ∧
        trR P Bs.μsec e (Q.crd (Q.cmp (vABm P.r Y i) 1) Φ) =
          MA.actA P (capaVpM P L Y i 1 0) (trR P Bs.μsec e Φ)) := by
  obtain ⟨-, hpb, -, -, hcb, hcbi, -⟩ := hL
  intro i
  induction i with
  | zero =>
    intro _ Dc Φ hΦ
    have h0 : Q.crd (Q.cmp (vABm P.r Y 0) 0) Φ = Φ := rfl
    have h1 : Q.crd (Q.cmp (vABm P.r Y 0) 1) Φ = 0 := rfl
    have v0 : capaVpM P L Y 0 0 0 = 1 := by simp [capaVpM_zero]
    have v1 : capaVpM P L Y 0 1 0 = 0 := by simp [capaVpM_zero]
    rw [h0, h1, v0, v1, actA_one, actA_zero, trR_zero]
    refine ⟨⟨hΦ, rfl⟩, ⟨?_, rfl⟩⟩
    have := famR_smul hΦ 0
    rwa [zero_smul] at this
  | succ i ih =>
    intro hi Dc Φ hΦ
    have h : i < P.r := hi
    obtain ⟨⟨hA, tA⟩, ⟨hB, tB⟩⟩ := ih (Nat.le_of_lt h) Dc Φ hΦ
    set ΦA := Q.crd (Q.cmp (vABm P.r Y i) 0) Φ with hΦA
    set ΦB := Q.crd (Q.cmp (vABm P.r Y i) 1) Φ with hΦB
    have hv : vABm (X := Wq →L[ℂ] Wp) P.r Y (i + 1) =
        (fun f => Y • (vABm P.r Y i).1 f - pbOp ⟨i, h⟩ ((vABm P.r Y i).1 f) -
          cbOp ⟨i, h⟩ ((vABm P.r Y i).2 f), fun f => cbiOp ⟨i, h⟩ ((vABm P.r Y i).1 f)) := by
      simp only [vABm, dif_pos h]
    have e0 : Q.crd (Q.cmp (vABm P.r Y (i + 1)) 0) Φ =
        Y • ΦA - Q.crd (pbOp ⟨i, h⟩) ΦA - Q.crd (cbOp ⟨i, h⟩) ΦB := by
      rw [hv]; rfl
    have e1 : Q.crd (Q.cmp (vABm P.r Y (i + 1)) 1) Φ = Q.crd (cbiOp ⟨i, h⟩) ΦA := by
      rw [hv]; rfl
    have hpA : FamR P Bs Dc (Q.crd (pbOp ⟨i, h⟩) ΦA) := famR_opL hA ⟨i, h⟩ 3
    have hcB : FamR P Bs Dc (Q.crd (cbOp ⟨i, h⟩) ΦB) := famR_opL hB ⟨i, h⟩ 4
    have hciA : FamR P Bs Dc (Q.crd (cbiOp ⟨i, h⟩) ΦA) := famR_opL hA ⟨i, h⟩ 5
    have hdif : FamR P Bs Dc (Y • ΦA - Q.crd (pbOp ⟨i, h⟩) ΦA) := famR_sub (famR_smul hA _) hpA
    have tc : trR P Bs.μsec e (Q.crd (cbOp ⟨i, h⟩) ΦB) =
        fun ρ => MA.coordQ (TT := P.TT) (M.vcb ⟨i, h⟩) * trR P Bs.μsec e ΦB ρ :=
      trR_mul hpl hk he hB _ hcB (fun c => star (c ⟨i, h⟩)) (fun _ _ => rfl) _ (fun q => coordE_vcb _ _)
    have tci : trR P Bs.μsec e (Q.crd (cbiOp ⟨i, h⟩) ΦA) =
        fun ρ => Ring.inverse (MA.coordQ (TT := P.TT) (M.vcb ⟨i, h⟩)) * trR P Bs.μsec e ΦA ρ :=
      trR_mul hpl hk he hA _ hciA (fun c => (star (c ⟨i, h⟩))⁻¹) (fun _ _ => rfl) _ (fun q => by
        rw [inv_coordQ_apply _ (fun x hx => by rw [coordE_vcb]; exact (star_ne_zero).2 (hx.1 _)), coordE_vcb])
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [e0]; exact famR_sub hdif hcB
    · rw [e0, trR_sub _ _ _ _ (fun ρ => smR hpl hk he hdif ρ) (fun ρ => smR hpl hk he hcB ρ),
        trR_sub _ _ _ _ (fun ρ => smR hpl hk he (famR_smul hA _) ρ) (fun ρ => smR hpl hk he hpA ρ), trR_smul,
        trR_pb hpl hk he hA, tc, tA, tB, capaVpM_succ P L Y i h, capa_Tvl_mul_0, hpb, hcb, actA_add, actA_mul,
        actA_mul, actA_neg, sub_eq_add_neg ((algebraMap ℂ (MA.A P (MA.DQ P))) Y), actA_add, actA_algebraMap, actA_neg,
        capa_actA_pb, capa_actA_cb, sub_eq_add_neg, sub_eq_add_neg]
    · rw [e1]; exact hciA
    · rw [e1, tci, tA, capaVpM_succ P L Y i h, capa_Tvl_mul_1, actA_mul, hcbi, capa_actA_cbi]

end ind

theorem capelli_transition_holds : JDAVTr := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk e he L hL Dc Φ hΦ y
  have hA := (capa_vab_ind hpl hk he y P.r le_rfl Dc Φ hΦ).1
  have hAv := (capa_vabm_ind hpl hk he L hL y P.r le_rfl Dc Φ hΦ).1
  refine ⟨⟨hA.1, ?_⟩, ⟨hAv.1, ?_⟩⟩
  · rw [hA.2, R.LevelData.Ar, ← site_vector_eq_tensor_product P L hL y 0, sitesCommonSpace_v0_eq_Vp]
  · rw [hAv.2, R.LevelData.Avr, capa_tvprod]

theorem jDCapA_of_grp (hG : JDAGrp) : JDCapA := jDCapA_of_parts hG capelli_transition_holds residue_derivative_transition

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.NormLetterScal
section
noncomputable section

namespace Formalism.FourierDecayAlt.P.StandardPairingDecay

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Matrix
open scoped ComplexConjugate

theorem norm_letter_scal (σ : ℂ) (b : Bool) : ‖(if b then σ else conj σ)‖ = ‖σ‖ := by
  cases b <;> simp

theorem uInv_ccle {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (A : ℝ) (m : ℕ) (σ : ℂ)
    (hσ : ‖σ‖ ≤ 2) :
    ∀ (w : List C.Letter) (x : Wd.Ix (Fin w.length) → B.Mat k r → E) (c : ℝ), (∀ e, B.CCle A m (x e) c) →
      ∀ e, B.CCle A m (KB.uInv σ w x e) (3 ^ w.length * c) ∧
        B.CCle A m (fun g => KB.uInv σ w x e g - x e g) (3 ^ w.length * ‖σ‖ * c) := by
  intro w
  induction w with
  | nil =>
    intro x c hx e
    have hc : 0 ≤ c := JCx2.pd_ccle_nonneg (hx e)
    refine ⟨by simpa [KB.uInv] using hx e, ?_⟩
    simp only [KB.uInv, sub_self, List.length_nil, pow_zero, one_mul]
    exact JCx2.pd_ccle_mono_c BetaSesquilinearity.CCle_zero (by positivity)
  | cons l w ih =>
    intro x c hx e
    have hc : 0 ≤ c := JCx2.pd_ccle_nonneg (hx e)
    have ih0 := ih (fun e' => x (Fin.cons (0 : Fin 2) e')) c (fun e' => hx _) (fun a => e a.succ)
    have ih1 := ih (fun e' => x (Fin.cons (1 : Fin 2) e')) c (fun e' => hx _) (fun a => e a.succ)
    have hs : ‖(if l.1 then σ else conj σ)‖ = ‖σ‖ := norm_letter_scal σ l.1
    have h3 : (0 : ℝ) ≤ 3 ^ w.length := by positivity
    have hσ0 : 0 ≤ ‖σ‖ := norm_nonneg _
    have hlen : (l :: w).length = w.length + 1 := rfl
    have hce : e = Fin.cons (e 0) (fun a => e a.succ) := (Fin.cons_self_tail e).symm
    have hp : (3 : ℝ) ^ (l :: w).length = 3 * 3 ^ w.length := by rw [hlen, pow_succ, mul_comm]
    simp only [KB.uInv]
    by_cases he : e 0 = 0
    · rw [ite_eq_left he]
      have hxe : x e = x (Fin.cons (0 : Fin 2) (fun a => e a.succ)) := by
        conv_lhs => rw [hce, he]
      refine ⟨JCx2.pd_ccle_mono_c ih0.1 (by rw [hp]; nlinarith), ?_⟩
      rw [hxe]
      exact JCx2.pd_ccle_mono_c ih0.2 (by rw [hp]; nlinarith [mul_nonneg h3 hσ0])
    · rw [ite_eq_right he]
      have he1 : e 0 = 1 := by
        rcases Fin.exists_fin_two.1 ⟨e 0, rfl⟩ with h | h
        · exact absurd h he
        · exact h
      have hxe : x e = x (Fin.cons (1 : Fin 2) (fun a => e a.succ)) := by
        conv_lhs => rw [hce, he1]
      refine ⟨?_, ?_⟩
      · have := BetaSesquilinearity.CCle_add ih1.1 (BetaSesquilinearity.CCle_smul (if l.1 then σ else conj σ) ih0.1)
        rw [hs] at this
        exact JCx2.pd_ccle_mono_c (show B.CCle A m ((KB.uInv σ w (fun e' => x (Fin.cons (1 : Fin 2) e')) (fun a => e a.succ)) +
          (if l.1 then σ else conj σ) • KB.uInv σ w (fun e' => x (Fin.cons (0 : Fin 2) e')) (fun a => e a.succ)) _ from this)
          (by rw [hp]; nlinarith [mul_nonneg h3 hc])
      · have := BetaSesquilinearity.CCle_add ih1.2 (BetaSesquilinearity.CCle_smul (if l.1 then σ else conj σ) ih0.1)
        rw [hs] at this
        rw [hxe]
        have hf : (fun g => (KB.uInv σ w (fun e' => x (Fin.cons (1 : Fin 2) e')) (fun a => e a.succ) +
            (if l.1 then σ else conj σ) • KB.uInv σ w (fun e' => x (Fin.cons (0 : Fin 2) e')) (fun a => e a.succ)) g -
            x (Fin.cons (1 : Fin 2) (fun a => e a.succ)) g) =
            fun g => (KB.uInv σ w (fun e' => x (Fin.cons (1 : Fin 2) e')) (fun a => e a.succ) g -
              x (Fin.cons (1 : Fin 2) (fun a => e a.succ)) g) +
              (if l.1 then σ else conj σ) • KB.uInv σ w (fun e' => x (Fin.cons (0 : Fin 2) e')) (fun a => e a.succ) g := by
          funext g
          simp only [Pi.add_apply, Pi.smul_apply]
          abel
        rw [hf]
        exact JCx2.pd_ccle_mono_c this (by rw [hp]; nlinarith [mul_nonneg h3 hc, mul_nonneg (mul_nonneg h3 hσ0) hc])

end Formalism.FourierDecayAlt.P.StandardPairingDecay
end
end

