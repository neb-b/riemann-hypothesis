module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsOrthGen
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0010
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0011
public import Mathlib
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0027

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocFMapSubtype
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G1

open Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem locF_map_subtype (X : Submodule K V) (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] (N : Submodule (𝓞 K) X) :
    locF 𝔭 (N.map (X.subtype.restrictScalars (𝓞 K))) =
      (locF 𝔭 N).map (X.subtype.restrictScalars (𝓞 K)) := by
  ext y
  rw [Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF, Submodule.mem_map]
  constructor
  · rintro ⟨t, ht, z, hz, hzy⟩
    have ht0 : t ≠ 0 := fun h0 => ht (h0 ▸ 𝔭.zero_mem)
    have hne : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := by
      have e : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = algebraMap F K (t : F) := rfl
      rw [e, map_ne_zero]
      exact fun h => ht0 (by exact_mod_cast h)
    have hmem : algebraMap (𝓞 F) (𝓞 K) t • y ∈ X := by
      rw [← hzy]; exact z.2
    rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) y] at hmem
    have hyX : y ∈ X := (X.smul_mem_iff hne).mp hmem
    refine ⟨⟨y, hyX⟩, ?_, rfl⟩
    rw [Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF]
    refine ⟨t, ht, ?_⟩
    have e2 : algebraMap (𝓞 F) (𝓞 K) t • (⟨y, hyX⟩ : X) = z := by
      apply Subtype.ext
      simpa using hzy.symm
    rw [e2]; exact hz
  · rintro ⟨z, hz, rfl⟩
    rw [Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF] at hz
    obtain ⟨t, ht, hz⟩ := hz
    exact ⟨t, ht, _, hz, by simp⟩

variable [FiniteDimensional K V]

theorem exists_basis_in {X : Submodule K V} {L : Submodule (𝓞 K) V} (hL : Cnt.IsLatIn X L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ x : Fin (finrank K X) → V, (∀ i, x i ∈ L) ∧ LinearIndependent K x ∧
      Submodule.span K (Set.range x) = X ∧
      locF 𝔭 (Submodule.span (𝓞 K) (Set.range x)) = locF 𝔭 L := by
  haveI : 𝔭.IsPrime := h𝔭.isPrime
  obtain ⟨hfg, hspan⟩ := hL
  have hLX : ∀ v ∈ L, v ∈ X := fun v hv => hspan ▸ Submodule.subset_span hv
  have hmapN : (L.comap (X.subtype.restrictScalars (𝓞 K))).map
      (X.subtype.restrictScalars (𝓞 K)) = L := by
    rw [Submodule.map_comap_eq]
    refine inf_eq_right.mpr ?_
    intro v hv
    exact ⟨⟨v, hLX v hv⟩, rfl⟩
  have hinj : Function.Injective (X.subtype.restrictScalars (𝓞 K)) := X.injective_subtype
  have hfgN : (L.comap (X.subtype.restrictScalars (𝓞 K))).FG :=
    Submodule.fg_of_fg_map_injective _ hinj (by rw [hmapN]; exact hfg)
  have himg : X.subtype '' ((L.comap (X.subtype.restrictScalars (𝓞 K)) : Submodule (𝓞 K) X) : Set X)
      = (L : Set V) := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hv
      exact ⟨⟨v, hLX v hv⟩, hv, rfl⟩
  have hspanN : Submodule.span K
      ((L.comap (X.subtype.restrictScalars (𝓞 K)) : Submodule (𝓞 K) X) : Set X) = ⊤ := by
    apply Submodule.map_injective_of_injective X.injective_subtype
    rw [Submodule.map_span, himg, hspan, Submodule.map_top, Submodule.range_subtype]
  have hNlat : Submodule.IsFullLattice K (L.comap (X.subtype.restrictScalars (𝓞 K))) :=
    { toIsLattice := Submodule.IsLattice.of_fg K hfgN
      span_eq_top := hspanN }
  obtain ⟨b, hbN, hbloc⟩ := Formalism.HermitianLattices.Ext.L3.LocalSpans.exists_basis_locF hNlat h𝔭
  refine ⟨fun i => (b i : V), fun i => hbN i, ?_, ?_, ?_⟩
  · exact b.linearIndependent.map' X.subtype X.ker_subtype
  · have hx : Set.range (fun i => (b i : V)) = X.subtype '' Set.range b := Set.range_comp _ _
    rw [hx, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  · have hx : Set.range (fun i => (b i : V)) =
        (X.subtype.restrictScalars (𝓞 K)) '' Set.range b := Set.range_comp _ _
    rw [hx, Submodule.span_image, locF_map_subtype, hbloc, ← locF_map_subtype, hmapN]

theorem det_gram_ne_zero [StarRing K] {h : V →ₗ⋆[K] V →ₗ[K] K} {X : Submodule K V}
    (hnd : Cnt.NondegOn h X) {n : ℕ} {x : Fin n → V} (hli : LinearIndependent K x)
    (hsp : Submodule.span K (Set.range x) = X) : (U0.gram h x).det ≠ 0 := by
  intro hdet
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  have hyX : (∑ i, star (c i) • x i) ∈ X := by
    rw [← hsp]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have key : ∀ j, h (∑ i, star (c i) • x i) (x j) = 0 := by
    intro j
    have hj := congrFun hc j
    simp only [Matrix.vecMul, dotProduct, U0.gram, Matrix.of_apply, Pi.zero_apply] at hj
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smulₛₗ, starRingEnd_apply, star_star, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul]
    exact hj
  have hall : ∀ z ∈ X, h (∑ i, star (c i) • x i) z = 0 := by
    intro z hz
    rw [← hsp] at hz
    have hle : Submodule.span K (Set.range x) ≤ LinearMap.ker (h (∑ i, star (c i) • x i)) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact key j
    exact hle hz
  have hy0 := hnd _ hyX hall
  have hcoef := Fintype.linearIndependent_iff.mp hli (fun i => star (c i)) hy0
  apply hc0
  funext i
  simpa using hcoef i

end Formalism.L2.SG.Pf.G1
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXECPfB
section
noncomputable section

open MeasureTheory Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.EC

open Formalism.QuantumDeterminants WlocSk.NB
open Formalism.MainNotions.BridgeCSB (Fil lieN dg)

variable {k r : ℕ}

theorem mp_toC : MeasurePreserving (toC (k := k) (r := r)) volume volume := by
  have h1 := volume_measurePreserving_sumPiEquivProdPi (fun _ : J k r => ℝ)
  have h2 := volume_measurePreserving_sumPiEquivProdPi (fun _ : CI k r ⊕ CI k r => ℝ)
  have h3 := (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (CI k r)).symm
  have h4 : MeasurePreserving (fun (w : CI k r → ℝ × ℝ) (i : CI k r) =>
      Complex.measurableEquivRealProd.symm (w i)) volume volume :=
    volume_preserving_pi (fun _ => Complex.volume_preserving_equiv_real_prod.symm)
  have h5 := ((h4.comp h3).comp h2).prod (MeasurePreserving.id (volume : Measure (Fin r → ℝ)))
  have h6 := h5.comp h1
  convert h6 using 1
  all_goals first | rfl | (funext y; rfl)

def fromC (t : (CI k r → ℂ) × (Fin r → ℝ)) : J k r → ℝ
  | Sum.inl (Sum.inl c) => (t.1 c).re
  | Sum.inl (Sum.inr c) => (t.1 c).im
  | Sum.inr a => t.2 a

theorem toC_fromC (t : (CI k r → ℂ) × (Fin r → ℝ)) : toC (fromC t) = t := by
  rfl

theorem continuous_fromC : Continuous (fromC (k := k) (r := r)) := by
  refine continuous_pi fun j => ?_
  rcases j with (c | c) | a
  · exact Complex.continuous_re.comp ((continuous_apply c).comp continuous_fst)
  · exact Complex.continuous_im.comp ((continuous_apply c).comp continuous_fst)
  · exact (continuous_apply a).comp continuous_snd

section Cont

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem continuous_expLJ : Continuous fun y : J k r → ℝ => (NormedSpace.exp (LJ y) : Mx k r) :=
  NormedSpace.exp_continuous.comp continuous_LJ

end Cont

def sJ (y : J k r → ℝ) : J k r → ℝ := fromC (psiC (NormedSpace.exp (LJ y)), psiR (NormedSpace.exp (LJ y)))

theorem continuous_sJ : Continuous (sJ (k := k) (r := r)) :=
  continuous_fromC.comp ((continuous_psiC.comp continuous_expLJ).prodMk (continuous_psiR.comp continuous_expLJ))

theorem entry_of_fil {D E : Mx k r} {p : ℕ} (h : Fil (p + 1) (D - E)) {i j : Fin (2 * r + k + 1)}
    (hij : dg k r j ≤ dg k r i + p) : D i j = E i j := by
  have h1 := h i j (by omega)
  rw [Matrix.sub_apply, sub_eq_zero] at h1
  exact h1

theorem mof_sub {g g' : Mx k r} (hg : g ∈ Nset k r) (hg' : g' ∈ Nset k r) (a b : Fin r)
    (hG : Fil (2 * r - a.val - b.val) (g - g')) :
    mof g a b - mof g' a b = g (eI k r a) (esI k r b) - g' (eI k r a) (esI k r b) := by
  have h1 := ((Formalism.MainNotions.BridgeCSB.mem_N_iff g).1 hg).2
  have h1' := ((Formalism.MainNotions.BridgeCSB.mem_N_iff g').1 hg').2
  have key : ∀ c : Fin r, star (g (esI k r c) (esI k r a)) * g (eI k r c) (esI k r b) -
      star (g' (esI k r c) (esI k r a)) * g' (eI k r c) (esI k r b) =
      if c = a then g (eI k r a) (esI k r b) - g' (eI k r a) (esI k r b) else 0 := by
    intro c
    have ha := a.isLt; have hb := b.isLt; have hc := c.isLt
    rcases lt_trichotomy c a with h | rfl | h
    · have hca : c.val < a.val := h
      have e1 := h1 (esI k r c) (esI k r a) (by rw [dg_esI, dg_esI]; omega)
      have e2 := h1' (esI k r c) (esI k r a) (by rw [dg_esI, dg_esI]; omega)
      rw [Matrix.sub_apply, Matrix.one_apply, if_neg (fun e => (ne_of_lt h) (esI_inj.1 e)), sub_zero] at e1 e2
      rw [e1, e2, if_neg (ne_of_lt h)]; simp
    · have e1 := h1 (esI k r c) (esI k r c) (by rw [dg_esI]; omega)
      have e2 := h1' (esI k r c) (esI k r c) (by rw [dg_esI]; omega)
      rw [Matrix.sub_apply, Matrix.one_apply, if_pos rfl, sub_eq_zero] at e1 e2
      rw [e1, e2, if_pos rfl]; simp
    · have hac : a.val < c.val := h
      have e1 := hG (esI k r c) (esI k r a) (by rw [dg_esI, dg_esI]; omega)
      have e2 := hG (eI k r c) (esI k r b) (by rw [dg_esI, dg_eI]; omega)
      rw [Matrix.sub_apply, sub_eq_zero] at e1 e2
      rw [e1, e2, if_neg (ne_of_gt h), sub_self]
  simp only [mof, Matrix.mul_apply, conjTranspose_apply, bF, bC]
  rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun c _ => key c)]
  simp

theorem psiC_sub (t t' : (CI k r → ℂ) × (Fin r → ℝ)) (c : CI k r)
    (hG : Fil (hC c) (NormedSpace.exp (Lm t) - NormedSpace.exp (Lm t')))
    (hE : Fil (hC c + 1) ((NormedSpace.exp (Lm t) - NormedSpace.exp (Lm t')) - (Lm t - Lm t'))) :
    psiC (NormedSpace.exp (Lm t)) c - psiC (NormedSpace.exp (Lm t')) c = t.1 c - t'.1 c := by
  have hg := Formalism.MainNotions.BridgeCSB.exp_mem_N (Lm_mem t)
  have hg' := Formalism.MainNotions.BridgeCSB.exp_mem_N (Lm_mem t')
  have ent : ∀ i j, dg k r j ≤ dg k r i + hC c →
      (NormedSpace.exp (Lm t) - NormedSpace.exp (Lm t')) i j = (Lm t - Lm t') i j :=
    fun i j h => entry_of_fil hE h
  rcases c with ⟨⟨a, b⟩, h⟩ | ⟨a, j⟩ | ⟨⟨a, b⟩, h⟩
  · have hab : a.val < b.val := h
    have := ent (eI k r a) (eI k r b) (by rw [dg_eI, dg_eI]; simp only [hC]; omega)
    simp only [Matrix.sub_apply, Lm_ee, chart_matrix_upper _ h] at this
    exact this
  · have := ent (eI k r a) (wI k r j) (by rw [dg_eI, dg_wI]; simp only [hC]; omega)
    simp only [Matrix.sub_apply, Lm_ew] at this
    exact this
  · have hab' : a.val < b.val := h
    have hb := b.isLt
    have eh : hC (Sum.inr (Sum.inr ⟨(a, b), h⟩) : CI k r) = 2 * r - a.val - b.val := rfl
    have hab := mof_sub hg hg' a b (by rw [← eh]; exact hG)
    have hba := mof_sub hg hg' b a (by
      have : 2 * r - b.val - a.val = 2 * r - a.val - b.val := by omega
      rw [this, ← eh]; exact hG)
    have e1 := ent (eI k r a) (esI k r b) (by rw [dg_eI, dg_esI, eh]; omega)
    have e2 := ent (eI k r b) (esI k r a) (by rw [dg_eI, dg_esI, eh]; omega)
    simp only [Matrix.sub_apply, Lm_es] at e1 e2
    have hba' := congrArg star hba
    have e2' := congrArg star e2
    simp only [star_sub] at hba' e2'
    have sk := cK_skew t.1 t.2 a b
    have sk' := cK_skew t'.1 t'.2 a b
    have hx : ∀ x : CI k r → ℂ, ∀ s, cK x s a b = x (Sum.inr (Sum.inr ⟨(a, b), h⟩)) := by
      intro x s; unfold cK; rw [dite_eq_left h]
    show kof _ a b - kof _ a b = _
    rw [← hx t.1 t.2, ← hx t'.1 t'.2]
    simp only [kof]
    linear_combination (1 / 2 : ℂ) * hab + (1 / 2 : ℂ) * e1 - (1 / 2 : ℂ) * hba' - (1 / 2 : ℂ) * e2' -
      (1 / 2 : ℂ) * sk + (1 / 2 : ℂ) * sk'

theorem psiR_sub (t t' : (CI k r → ℂ) × (Fin r → ℝ)) (a : Fin r)
    (hG : Fil (2 * r - 2 * a.val) (NormedSpace.exp (Lm t) - NormedSpace.exp (Lm t')))
    (hE : Fil (2 * r - 2 * a.val + 1) ((NormedSpace.exp (Lm t) - NormedSpace.exp (Lm t')) - (Lm t - Lm t'))) :
    psiR (NormedSpace.exp (Lm t)) a - psiR (NormedSpace.exp (Lm t')) a = t.2 a - t'.2 a := by
  have hg := Formalism.MainNotions.BridgeCSB.exp_mem_N (Lm_mem t)
  have hg' := Formalism.MainNotions.BridgeCSB.exp_mem_N (Lm_mem t')
  have ha := a.isLt
  have hm := mof_sub hg hg' a a (by
    have : 2 * r - a.val - a.val = 2 * r - 2 * a.val := by omega
    rw [this]; exact hG)
  have e1 := entry_of_fil hE (i := eI k r a) (j := esI k r a) (by rw [dg_eI, dg_esI]; omega)
  simp only [Matrix.sub_apply, Lm_es] at e1
  have hk : ∀ (x : CI k r → ℂ) (s : Fin r → ℝ), cK x s a a = (s a : ℂ) * Complex.I := by
    intro x s; unfold cK; rw [dite_eq_right (lt_irrefl a), dite_eq_right (lt_irrefl a)]
  rw [hk, hk] at e1
  have := congrArg Complex.im (hm.trans e1)
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_one, mul_zero, add_zero] at this
  simp only [psiR]
  linarith

theorem sJ_shear (i : J k r) (y y' : J k r → ℝ) (h : ∀ j, ht j < ht i → y j = y' j) :
    sJ y i - y i = sJ y' i - y' i := by
  have hF := Lm_fil_sub h
  have hE := Formalism.MainNotions.BridgeCSB.Fil.exp_sub_exp (chart_filtration_one (toC y)) (chart_filtration_one (toC y')) hF
  have hG : Fil (ht i) (NormedSpace.exp (Lm (toC y)) - NormedSpace.exp (Lm (toC y'))) := by
    have := (hE.mono (Nat.le_succ _)).add hF
    rwa [sub_add_cancel] at this
  rcases i with (c | c) | a
  · have := congrArg Complex.re (psiC_sub (toC y) (toC y') c hG hE)
    simp only [Complex.sub_re] at this
    show (psiC (NormedSpace.exp (Lm (toC y))) c).re - ((toC y).1 c).re =
      (psiC (NormedSpace.exp (Lm (toC y'))) c).re - ((toC y').1 c).re
    linarith
  · have := congrArg Complex.im (psiC_sub (toC y) (toC y') c hG hE)
    simp only [Complex.sub_im] at this
    show (psiC (NormedSpace.exp (Lm (toC y))) c).im - ((toC y).1 c).im =
      (psiC (NormedSpace.exp (Lm (toC y'))) c).im - ((toC y').1 c).im
    linarith
  · have := psiR_sub (toC y) (toC y') a hG hE
    show psiR (NormedSpace.exp (Lm (toC y))) a - (toC y).2 a =
      psiR (NormedSpace.exp (Lm (toC y'))) a - (toC y').2 a
    linarith

theorem shear_change_holds : ShearStep := by
  intro k r
  refine ⟨fun y => (psiC (NormedSpace.exp (LJ y)), psiR (NormedSpace.exp (LJ y))), ?_, ?_⟩
  · have hS := Formalism.MainNotions.BridgeCSB.shearMP (J k r) ht sJ continuous_sJ.measurable
      (fun i y y' h => sJ_shear i y y' h)
    have := mp_toC.comp hS
    convert this using 1
    funext y
    exact (toC_fromC _).symm
  · intro y
    exact nilpotent_chart_left_inverse (Formalism.MainNotions.BridgeCSB.exp_mem_N (Lm_mem (toC y)))

end Formalism.L2.SG.Pf.NcReal.JX.EC
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SplitAtOf
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

def spanS {K V : Type} [Field K] [AddCommGroup V] [Module K V] (S : Subring K) {ι : Type}
    [Fintype ι] (b : ι → V) : AddSubgroup V where
  carrier := {v | ∃ c : ι → K, (∀ i, c i ∈ S) ∧ v = ∑ i, c i • b i}
  zero_mem' := ⟨0, fun _ => S.zero_mem, by simp⟩
  add_mem' := by
    rintro x y ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
    exact ⟨c + d, fun i => S.add_mem (hc i) (hd i), by
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]⟩
  neg_mem' := by
    rintro x ⟨c, hc, rfl⟩
    exact ⟨-c, fun i => S.neg_mem (hc i), by
      simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]⟩

section Abs

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

def SplitAt (S : Subring K) (π : K) (h : V →ₗ⋆[K] V →ₗ[K] K) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (b : ι → V) (e : ι → ℕ) (i₀ : ι),
    (∀ i j, i ≠ j → h (b i) (b j) = 0) → (∀ i, IsUnitIn S (h (b i) (b i) * (π ^ e i)⁻¹)) →
    (∀ i, e i₀ ≤ e i) → ∀ ξ ∈ Submodule.span K (Set.range b),
    IsUnitIn S (h ξ ξ * (π ^ e i₀)⁻¹) →
    ∃ c : ι → V, (∀ i j, i ≠ j → h (c i) (c j) = 0) ∧
      (∀ i, IsUnitIn S (h (c i) (c i) * (π ^ e i)⁻¹)) ∧ h (c i₀) (c i₀) = h ξ ξ ∧
      Submodule.span K (Set.range c) = Submodule.span K (Set.range b) ∧
      ∀ v, v ∈ spanS S c ↔ v ∈ spanS S b

def ExactAt (S : Subring K) (π : K) (h : V →ₗ⋆[K] V →ₗ[K] K) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (b : ι → V) (e : ι → ℕ) (i₀ : ι),
    (∀ i j, i ≠ j → h (b i) (b j) = 0) → (∀ i, IsUnitIn S (h (b i) (b i) * (π ^ e i)⁻¹)) →
    (∀ i, e i₀ ≤ e i) → ∀ ξ ∈ Submodule.span K (Set.range b),
    IsUnitIn S (h ξ ξ * (π ^ e i₀)⁻¹) → ∃ X ∈ spanS S b, h X X = h ξ ξ

def RebaseAt (S : Subring K) (π : K) (h : V →ₗ⋆[K] V →ₗ[K] K) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (b : ι → V) (e : ι → ℕ) (i₀ : ι),
    (∀ i j, i ≠ j → h (b i) (b j) = 0) → (∀ i, IsUnitIn S (h (b i) (b i) * (π ^ e i)⁻¹)) →
    (∀ i, e i₀ ≤ e i) → ∀ X ∈ spanS S b, IsUnitIn S (h X X * (π ^ e i₀)⁻¹) →
    ∃ c : ι → V, (∀ i j, i ≠ j → h (c i) (c j) = 0) ∧
      (∀ i, IsUnitIn S (h (c i) (c i) * (π ^ e i)⁻¹)) ∧ c i₀ = X ∧
      Submodule.span K (Set.range c) = Submodule.span K (Set.range b) ∧
      ∀ v, v ∈ spanS S c ↔ v ∈ spanS S b

theorem splitAt_of {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K} (hE : ExactAt S π h)
    (hR : RebaseAt S π h) : SplitAt S π h := by
  intro ι _ _ b e i₀ horth hunit hmin ξ hξ hξu
  obtain ⟨X, hX, hXX⟩ := hE ι b e i₀ horth hunit hmin ξ hξ hξu
  have hXu : IsUnitIn S (h X X * (π ^ e i₀)⁻¹) := by rw [hXX]; exact hξu
  obtain ⟨c, hco, hcu, hc0, hsp, hmem⟩ := hR ι b e i₀ horth hunit hmin X hX hXu
  exact ⟨c, hco, hcu, by rw [hc0, hXX], hsp, hmem⟩

end Abs

def ExactVec : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → IsTotPosDef h →
    ∀ P : Ideal (𝓞 K), P.IsMaximal → ∀ π : K, IsUnif (locRing P) π → ExactAt (locRing P) π h

def Rebase : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (S : Subring K) (π : K)
    (h : V →ₗ⋆[K] V →ₗ[K] K), IsHermSemilocal S → IsUnif S π → h.IsSymm →
    (∀ x, h x x = 0 → x = 0) → RebaseAt S π h

def LocSpan : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ P : Ideal (𝓞 K), P.IsMaximal → ∀ (n : ℕ) (b : Fin n → V)
    (v : V), v ∈ Formalism.HermitianLatticesTheory.loc (K := K) P (Submodule.span (𝓞 K) (Set.range b)) ↔
      v ∈ spanS (locRing P) b

def UnifVal : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ P : Ideal (𝓞 K), P.IsMaximal →
    ∃ π : K, IsUnif (locRing P) π ∧ ∀ a : 𝓞 F, a ≠ 0 →
      IsUnitIn (locRing P)
        (algebraMap F K (a : F) * (π ^ vF (P.comap (algebraMap (𝓞 F) (𝓞 K))) a)⁻¹)

def JordSpan : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (L : Submodule (𝓞 K) V), Submodule.IsFullLattice K L → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
    ∀ (n : ℕ) (b : Fin n → V), locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L →
      Submodule.span K (Set.range b) = ⊤

end Formalism.L2.SG.Pf.G3
end
end

