module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0121
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0111
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFullLatticeOverUnramifiedExtIff
section
noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

theorem isLat_iff_of_coe_eq {O O' E E' A : Type} [CommRing O] [CommRing O'] [Field E] [Field E'] [CommRing A]
    [Algebra O A] [Algebra O' A] [Algebra E A] [Algebra E' A] {d : ℕ} (u : Fin d → O')
    (h1 : ∀ a : O, ∃ b : O', algebraMap O' A b = algebraMap O A a)
    (h2 : ∀ y : O', ∃ a : Fin d → O, algebraMap O' A y = ∑ i, algebraMap O A (a i) * algebraMap O' A (u i))
    (h3 : ∀ e : E, ∃ e' : E', algebraMap E' A e' = algebraMap E A e)
    (h4 : ∀ e' : E', ∃ (e : E) (b : O'), algebraMap E' A e' = algebraMap E A e * algebraMap O' A b)
    (L : Submodule O' A) (M : Submodule O A) (h : (L : Set A) = (M : Set A)) :
    IsLat O' E' L ↔ IsLat O E M := by
  classical
  have hm : ∀ y, y ∈ L ↔ y ∈ M := fun y => by
    rw [← SetLike.mem_coe, h, SetLike.mem_coe]
  refine and_congr ⟨?_, ?_⟩ ⟨?_, ?_⟩
  · rintro ⟨S, hS⟩
    refine ⟨(Finset.univ ×ˢ S).image fun p : Fin d × A => u p.1 • p.2, le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le]
      intro x hx
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product] at hx
      obtain ⟨p, hp, rfl⟩ := hx
      exact (hm _).1 (L.smul_mem _ (hS ▸ Submodule.subset_span hp.2))
    · intro x hx
      have hx' : x ∈ Submodule.span O' (S : Set A) := hS ▸ (hm x).2 hx
      set N := Submodule.span O
        ((((Finset.univ ×ˢ S).image fun p : Fin d × A => u p.1 • p.2 : Finset A)) : Set A) with hN
      have key : ∀ c : O', c • x ∈ N := by
        clear hx
        induction hx' using Submodule.span_induction with
        | mem s hs =>
          intro c
          obtain ⟨a, ha⟩ := h2 c
          rw [Algebra.smul_def, ha, Finset.sum_mul]
          refine N.sum_mem fun i _ => ?_
          rw [mul_assoc, ← Algebra.smul_def, ← Algebra.smul_def]
          refine N.smul_mem _ (Submodule.subset_span ?_)
          simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product]
          exact ⟨(i, s), ⟨Finset.mem_univ _, hs⟩, rfl⟩
        | zero => intro c; simp
        | add x z _ _ hx hz => intro c; rw [smul_add]; exact N.add_mem (hx c) (hz c)
        | smul e x _ hx => intro c; rw [smul_smul]; exact hx _
      simpa using key 1
  · rintro ⟨S, hS⟩
    refine ⟨S, le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le, h, ← hS]
      exact Submodule.subset_span
    · intro x hx
      have hx' : x ∈ Submodule.span O (S : Set A) := hS ▸ (hm x).1 hx
      clear hx
      induction hx' using Submodule.span_induction with
      | mem s hs => exact Submodule.subset_span hs
      | zero => exact zero_mem _
      | add x z _ _ hx hz => exact add_mem hx hz
      | smul e x _ hx =>
        obtain ⟨b, hb⟩ := h1 e
        rw [Algebra.smul_def, ← hb, ← Algebra.smul_def]
        exact Submodule.smul_mem _ _ hx
  · intro hL
    rw [eq_top_iff]
    intro x hx0
    clear hx0
    have hx' : x ∈ Submodule.span E' (L : Set A) := hL ▸ Submodule.mem_top
    have key : ∀ c : E', c • x ∈ Submodule.span E (M : Set A) := by
      induction hx' using Submodule.span_induction with
      | mem s hs =>
        intro c
        obtain ⟨e, b, hb⟩ := h4 c
        rw [Algebra.smul_def, hb, mul_assoc, ← Algebra.smul_def, ← Algebra.smul_def]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ((hm _).1 (L.smul_mem _ hs)))
      | zero => intro c; simp
      | add x z _ _ hx hz => intro c; rw [smul_add]; exact add_mem (hx c) (hz c)
      | smul e x _ hx => intro c; rw [smul_smul]; exact hx _
    simpa using key 1
  · intro hM
    rw [eq_top_iff]
    intro x hx0
    clear hx0
    have hx' : x ∈ Submodule.span E (M : Set A) := hM ▸ Submodule.mem_top
    induction hx' using Submodule.span_induction with
    | mem s hs => exact Submodule.subset_span ((hm s).2 hs)
    | zero => exact zero_mem _
    | add x z _ _ hx hz => exact add_mem hx hz
    | smul e x _ hx =>
      obtain ⟨b, hb⟩ := h3 e
      rw [Algebra.smul_def, ← hb, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ hx

theorem exists_eq_base_mul_int {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E} (hU : IsUnrExt K K' d φ) (z : K'.E) :
    ∃ (e : K.E) (b : K'.O), z = φ e * algebraMap K'.O K'.E b := by
  by_cases hz : z = 0
  · exact ⟨0, 0, by simp [hz]⟩
  obtain ⟨π, hπ⟩ := (IsDiscreteValuationRing.maximalIdeal K.O).valuation_exists_uniformizer K.E
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hφ0 : φ π ≠ 0 := by simpa using hπ0
  set v := (IsDiscreteValuationRing.maximalIdeal K'.O).valuation K'.E with hv
  have h1 : WithZero.log (v (φ π)) = -1 := by
    have := hU.2.2.1 π
    unfold val at this
    rw [hπ, WithZero.log_exp, ← hv] at this
    omega
  have hv0 : v (φ π) ≠ 0 := by simpa using hφ0
  have hz0 : v z ≠ 0 := by simpa using hz
  obtain ⟨b, hb⟩ := mem_range_of_val_nonneg K' (z * φ π ^ (WithZero.log (v z))) (by
    unfold val
    rw [← hv, map_mul, map_zpow₀, WithZero.log_mul hz0 (zpow_ne_zero _ hv0), WithZero.log_zpow, h1]
    simp)
  refine ⟨π ^ (-WithZero.log (v z)), b, ?_⟩
  rw [hb, map_zpow₀, zpow_neg]
  have := zpow_ne_zero (WithZero.log (v z)) hφ0
  field_simp

theorem isLat_overExt_iff : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (L : Submodule K'.O (overExt φ B ψ hψ hσ).A) (M : Submodule K.O B.A), (L : Set (overExt φ B ψ hψ hσ).A) = (M : Set B.A) → (IsLat K'.O K'.E L ↔ IsLat K.O K.E M) := by
  intro K K' d φ hU B ψ hψ hσ L M h
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_integer_spanning_family_of_unramifiedExt K K' d φ hU
  letI : Algebra K'.E B.A := ψ.toAlgebra
  letI : Algebra K'.O B.A := (ψ.comp (algebraMap K'.O K'.E)).toAlgebra
  have hO' : ∀ b : K'.O, algebraMap K'.O B.A b = ψ (algebraMap K'.O K'.E b) := fun _ => rfl
  have hE' : ∀ b : K'.E, algebraMap K'.E B.A b = ψ b := fun _ => rfl
  have hO : ∀ a : K.O, algebraMap K.O B.A a = ψ (φ (algebraMap K.O K.E a)) := fun a => by
    rw [hψ, ← IsScalarTower.algebraMap_apply]
  have key := isLat_iff_of_coe_eq (O := K.O) (O' := K'.O) (E := K.E) (E' := K'.E) (A := B.A) u ?_ ?_ ?_ ?_
  · exact key L M h
  · intro a
    obtain ⟨b, hb⟩ := exists_int_image hU a
    exact ⟨b, by rw [hO', hO, hb]⟩
  · intro y
    obtain ⟨a, ha⟩ := hu y
    refine ⟨a, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hO', ha, map_sum]
    simp only [map_mul, hO, hO']
  · intro e
    exact ⟨φ e, by rw [hE', hψ]⟩
  · intro z
    obtain ⟨e, b, hb⟩ := exists_eq_base_mul_int hU z
    exact ⟨e, b, by rw [hE', hO', ← hψ, ← map_mul, ← hb]⟩

end GlobalTheory.UnitLemma.Unr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantCompactSupportJacquetRallisDesc
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.LinDesc

theorem norm_eq_of_sub_lt {F : Type} [NormedField F] [IsUltrametricDist F] {x y : F}
    (h : ‖x - y‖ < ‖y‖) : ‖x‖ = ‖y‖ := by
  have h1 : ‖x‖ ≤ max ‖x - y‖ ‖y‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (x - y) y
  have h2 : ‖y‖ ≤ max ‖y - x‖ ‖x‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (y - x) x
  rw [norm_sub_rev] at h2
  rcases le_total ‖x - y‖ ‖y‖ with h3 | h3
  · rw [max_eq_right h3] at h1
    rcases le_total ‖x - y‖ ‖x‖ with h4 | h4
    · rw [max_eq_right h4] at h2; exact le_antisymm h1 h2
    · rw [max_eq_left h4] at h2; exact absurd h (not_lt.mpr h2)
  · exact absurd h (not_lt.mpr h3)

theorem eta_det_isLocallyConstant {F : Type} [NontriviallyNormedField F] [IsUltrametricDist F] (r : ℕ) :
    IsLocallyConstant (fun g : GL (Fin r) F => eta ((g : Matrix (Fin r) (Fin r) F).det)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have hd : ((g : Matrix (Fin r) (Fin r) F).det) ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
  have hc : Continuous (fun h : GL (Fin r) F => (h : Matrix (Fin r) (Fin r) F).det) :=
    Units.continuous_val.matrix_det
  have hpos : 0 < ‖(g : Matrix (Fin r) (Fin r) F).det‖ := norm_pos_iff.mpr hd
  have hev : ∀ᶠ h : GL (Fin r) F in 𝓝 g, ‖((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).det - (g : Matrix (Fin r) (Fin r) F).det‖ <
      ‖(g : Matrix (Fin r) (Fin r) F).det‖ := by
    have : Continuous (fun h : GL (Fin r) F =>
        ‖(h : Matrix (Fin r) (Fin r) F).det - (g : Matrix (Fin r) (Fin r) F).det‖) :=
      (hc.sub continuous_const).norm
    exact (this.tendsto g).eventually_lt_const (by rw [sub_self, norm_zero]; exact hpos)
  filter_upwards [hev] with h hh
  unfold eta
  rw [norm_eq_of_sub_lt hh]


set_option maxHeartbeats 800000 in
theorem desc_isTest : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∀ (M : Meas r F E) (α : GL (Fin r) F → ℝ) (f' : Gl r F → ℂ), IsTest f' → IsLocallyConstant α → HasCompactSupport α → IsTest (LinDesc.desc A M hG lam α f') := by
  intro F E _ _ _ _ hU A r τ p hG lam M α f' hf hα hαc
  haveI : IsUltrametricDist F := hU.ultraF

  let ρL : A.K →ₗ[F] (Fin r → F) :=
    LinearMap.pi fun i => (Algebra.trace F A.K).comp (LinearMap.mulLeft F (τ ^ (i : ℕ)))
  have hρL : ∀ c, ρL c = fun i : Fin r => Algebra.trace F A.K (τ ^ (i : ℕ) * c) := fun c => rfl
  have hbij : Function.Bijective ρL := by
    have := (_root_.GlobalTheory.JR.EtInv.invK_regular_iff_isUnit F E A r τ p lam hG).1
    rw [show (⇑ρL) = fun (a : A.K) (i : Fin r) => Algebra.trace F A.K (τ ^ (i : ℕ) * a) from funext hρL]
    exact this
  let ρE : A.K ≃ₗ[F] (Fin r → F) := LinearEquiv.ofBijective ρL hbij
  have hι : Continuous (bas A hG).equivFun :=
    IsModuleTopology.continuous_of_linearMap (R := F) (bas A hG).equivFun.toLinearMap
  have hρ : Continuous ρL := IsModuleTopology.continuous_of_linearMap (R := F) ρL
  have hιs : Continuous (bas A hG).equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap (R := F) (bas A hG).equivFun.symm.toLinearMap
  have hρs : Continuous ρE.symm :=
    IsModuleTopology.continuous_of_linearMap (R := F) ρE.symm.toLinearMap
  have hpt : Continuous (fun x : A.K × A.K => pt A hG lam x.1 x.2) := by
    unfold pt
    exact continuous_const.prodMk ((hι.comp continuous_fst).prodMk
      ((hρ.comp continuous_snd).prodMk continuous_const))
  have hact : Continuous (fun q : GL (Fin r) F × Gl r F => act q.1 q.2) := by
    unfold act
    have h1 : Continuous (fun q : GL (Fin r) F × Gl r F => ((q.1 : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) :=
      Units.continuous_val.comp continuous_fst
    have h2 : Continuous (fun q : GL (Fin r) F × Gl r F => ((q.1⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) :=
      Units.continuous_val.comp (continuous_inv.comp continuous_fst)
    exact ((h1.matrix_mul (continuous_fst.comp continuous_snd)).matrix_mul h2).prodMk
      ((h1.matrix_mulVec (continuous_fst.comp (continuous_snd.comp continuous_snd))).prodMk
        (((continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))).matrix_vecMul h2).prodMk
          (continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_snd)))))
  have heta := eta_det_isLocallyConstant (F := F) r

  have hΦ : IsLocallyConstant (fun q : (A.K × A.K) × GL (Fin r) F =>
      f' (act q.2 (pt A hG lam q.1.1 q.1.2)) * eta ((q.2 : Matrix (Fin r) (Fin r) F).det) * (α q.2 : ℂ)) := by
    have a1 : IsLocallyConstant (fun q : (A.K × A.K) × GL (Fin r) F => f' (act q.2 (pt A hG lam q.1.1 q.1.2))) :=
      hf.1.comp_continuous (hact.comp (continuous_snd.prodMk (hpt.comp continuous_fst)))
    have a2 : IsLocallyConstant (fun q : (A.K × A.K) × GL (Fin r) F => eta ((q.2 : Matrix (Fin r) (Fin r) F).det)) :=
      heta.comp_continuous continuous_snd
    have a3 : IsLocallyConstant (fun q : (A.K × A.K) × GL (Fin r) F => (α q.2 : ℂ)) :=
      (hα.comp_continuous continuous_snd).comp (fun t : ℝ => (t : ℂ))
    exact (a1.mul a2).mul a3
  have hloc : IsLocallyConstant (LinDesc.desc A M hG lam α f') := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x₀
    have h1 : ∀ᶠ x in 𝓝 x₀, ∀ g ∈ tsupport α,
        f' (act g (pt A hG lam x.1 x.2)) * eta ((g : Matrix (Fin r) (Fin r) F).det) * (α g : ℂ) =
          f' (act g (pt A hG lam x₀.1 x₀.2)) * eta ((g : Matrix (Fin r) (Fin r) F).det) * (α g : ℂ) := by
      refine hαc.eventually_forall_of_forall_eventually fun g _ => ?_
      have h2 := (hΦ.prodMk (hΦ.comp_continuous (f := fun q : (A.K × A.K) × GL (Fin r) F => (x₀, q.2))
        (continuous_const.prodMk continuous_snd))).eventually_eq (x₀, g)
      filter_upwards [h2] with q hq
      simp only [Prod.mk.injEq, Function.comp] at hq
      rw [hq.1, hq.2]
    filter_upwards [h1] with x hx
    unfold desc
    congr 1
    funext g
    by_cases hg : g ∈ tsupport α
    · exact hx g hg
    · rw [image_eq_zero_of_notMem_tsupport hg]; simp
  refine ⟨hloc, ?_⟩

  let L : (Fin r → F) × (Fin r → F) → A.K × A.K := fun u => ((bas A hG).equivFun.symm u.1, ρE.symm u.2)
  have hL : Continuous L := (hιs.comp continuous_fst).prodMk (hρs.comp continuous_snd)
  let T : GL (Fin r) F × Gl r F → A.K × A.K := fun q => L ((act q.1⁻¹ q.2).2.1, (act q.1⁻¹ q.2).2.2.1)
  have hT : Continuous T := by
    have : Continuous (fun q : GL (Fin r) F × Gl r F => act q.1⁻¹ q.2) :=
      hact.comp ((continuous_inv.comp continuous_fst).prodMk continuous_snd)
    exact hL.comp ((continuous_fst.comp (continuous_snd.comp this)).prodMk
      (continuous_fst.comp (continuous_snd.comp (continuous_snd.comp this))))
  have hS : IsCompact (T '' (tsupport α ×ˢ tsupport f')) := (hαc.prod hf.2).image hT
  have hsub : Function.support (LinDesc.desc A M hG lam α f') ⊆ T '' (tsupport α ×ˢ tsupport f') := by
    intro x hx
    by_contra hxS
    apply hx
    have h0 : ∀ g : GL (Fin r) F,
        f' (act g (pt A hG lam x.1 x.2)) * eta ((g : Matrix (Fin r) (Fin r) F).det) * (α g : ℂ) = 0 := by
      intro g
      by_contra hne
      apply hxS
      have hαg : α g ≠ 0 := by
        intro h0; apply hne; rw [h0]; simp
      have hfg : f' (act g (pt A hG lam x.1 x.2)) ≠ 0 := by
        intro h0; apply hne; rw [h0]; simp
      refine ⟨(g, act g (pt A hG lam x.1 x.2)), ⟨subset_tsupport _ hαg, subset_tsupport _ hfg⟩, ?_⟩
      have hback : act g⁻¹ (act g (pt A hG lam x.1 x.2)) = pt A hG lam x.1 x.2 := by
        rw [← act_mul, inv_mul_cancel, act_one]
      show L ((act g⁻¹ (act g (pt A hG lam x.1 x.2))).2.1, (act g⁻¹ (act g (pt A hG lam x.1 x.2))).2.2.1) = x
      rw [hback]
      show ((bas A hG).equivFun.symm ((bas A hG).equivFun x.1), ρE.symm (ρL x.2)) = x
      rw [LinearEquiv.symm_apply_apply]
      have : ρE.symm (ρL x.2) = x.2 := ρE.symm_apply_apply x.2
      rw [this]
    unfold desc
    simp only [h0, integral_zero]
  have hcl : IsClosed (Function.support (LinDesc.desc A M hG lam α f')) := by
    have := hloc.isOpen_fiber 0
    rw [← isOpen_compl_iff]
    convert this using 1
    ext x; simp
  unfold HasCompactSupport tsupport
  rw [hcl.closure_eq]
  exact hS.of_isClosed_subset hcl hsub

end GlobalTheory.JR.LinDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitDetConjugationMatrixIntegralBasisStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_det_conjugationMatrix_integralBasis :
    ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), (∀ x, φ (K.c x) = K'.c (φ x)) →
      (letI : Algebra K.E K'.E := φ.toAlgebra
       ∀ w : Module.Basis (Fin d) K.E K'.E,
         (∀ z : K'.E, (∃ y : K'.O, algebraMap K'.O K'.E y = z) ↔
           ∀ k, ∃ a : K.O, algebraMap K.O K.E a = w.repr z k) →
         ∃ u : K.O, IsUnit u ∧
           algebraMap K.O K.E u = (Matrix.of fun m l => w.repr (K'.c (w l)) m).det) := by
  intro K K' d φ hφ
  let : Algebra K.E K'.E := φ.toAlgebra
  intro w hw
  have hunit : ∃ u : K.O, IsUnit u ∧
      algebraMap K.O K.E u = (Matrix.of fun m l => w.repr (K'.c (w l)) m).det := by
    set C : Matrix (Fin d) (Fin d) K.E := Matrix.of fun m l => w.repr (K'.c (w l)) m with hC
    have hsm : ∀ (e : K.E) (x : K'.E), e • x = φ e * x := fun e x => rfl
    have hint : ∀ m l, ∃ a : K.O, algebraMap K.O K.E a = C m l := by
      intro m l
      have h1 : ∃ y : K'.O, algebraMap K'.O K'.E y = w l := by
        rw [hw]
        intro k
        rw [w.repr_self]
        by_cases h : l = k
        · subst h; exact ⟨1, by simp⟩
        · exact ⟨0, by simp [h]⟩
      obtain ⟨y, hy⟩ := h1
      obtain ⟨y', hy'⟩ := K'.c_int y
      have h2 : ∃ y : K'.O, algebraMap K'.O K'.E y = K'.c (w l) := ⟨y', by rw [← hy', hy]⟩
      exact (hw _).1 h2 m
    choose A hA using hint
    have hrep : ∀ (x : K'.E) (n : Fin d), w.repr (K'.c x) n = ∑ m, K.c (w.repr x m) * C n m := by
      intro x n
      have hx : K'.c x = ∑ m, K.c (w.repr x m) • K'.c (w m) := by
        conv_lhs => rw [← w.sum_repr x]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [hsm, hsm, map_mul, ← hφ]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hx, map_sum, Finsupp.finsetSum_apply]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      rfl
    have hCC : C * (K.c : K.E →+* K.E).mapMatrix C = 1 := by
      ext n l
      have h := hrep (K'.c (w l)) n
      rw [K'.c_c, w.repr_self, Finsupp.single_apply] at h
      rw [Matrix.mul_apply, Matrix.one_apply]
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.coe_coe]
      rw [eq_comm]
      convert h using 1
      · exact if_congr eq_comm rfl rfl
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [mul_comm]
      rfl
    have hdet : C.det * K.c C.det = 1 := by
      have h := congrArg Matrix.det hCC
      rw [Matrix.det_mul, Matrix.det_one, ← RingHom.map_det] at h
      exact h
    have hdetA : algebraMap K.O K.E (Matrix.of A).det = C.det := by
      rw [RingHom.map_det]
      congr 1
      ext m l
      simp [hA]
    refine ⟨(Matrix.of A).det, ?_, hdetA⟩
    obtain ⟨β, hβ⟩ := K.c_int (Matrix.of A).det
    apply IsUnit.of_mul_eq_one β
    apply IsFractionRing.injective K.O K.E
    rw [map_mul, ← hβ, hdetA, hdet, map_one]
  exact hunit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JHypUnipotentTorusEquivariance
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JHypEquiv

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem secondCountable_K [Unram F E] (A : Et F E) : SecondCountableTopology A.K := by
  haveI : LocallyCompactSpace F := Unram.lcF E
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  let e : A.K ≃ₗ[F] (Fin (Module.finrank F A.K) → F) := (Module.finBasis F A.K).equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  exact (Homeomorph.mk e.toEquiv h1 h2).secondCountableTopology

theorem t2Space_K (A : Et F E) : T2Space A.K := by
  let e : A.K ≃ₗ[F] (Fin (Module.finrank F A.K) → F) := (Module.finBasis F A.K).equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  exact (Homeomorph.mk e.toEquiv h1 h2).symm.t2Space

theorem row_one (A : Et F E) (z : A.K) (s : A.Kˣ) (g : SpecialLinearGroup (Fin 2) A.K) (j : Fin 2) :
    (nS z * mS s * g) 1 j = ((s⁻¹ : A.Kˣ) : A.K) * g 1 j := by
  show ((nS z).1 * (mS s).1 * g.1) 1 j = ((s⁻¹ : A.Kˣ) : A.K) * g.1 1 j
  simp [nS, mS, Matrix.mul_apply, Fin.sum_univ_two]

theorem absK_unit (A : Et F E) (s : A.Kˣ) : A.absK (s : A.K) = (distribHaarChar A.K s : ℝ) := by
  unfold Et.absK
  rw [dite_eq_left s.isUnit]
  congr 2
  exact Units.ext (IsUnit.unit_spec _)

theorem integral_inv_mul [Unram F E] (A : Et F E) (μK : Measure A.K) [μK.IsAddHaarMeasure] (s : A.Kˣ)
    (H : A.K → ℂ) :
    ∫ t, H (((s⁻¹ : A.Kˣ) : A.K) * t) ∂μK = (distribHaarChar A.K s : ℝ) * ∫ u, H u ∂μK := by
  haveI := secondCountable_K A
  haveI := t2Space_K A
  have hmap : μK.map (fun x => (s⁻¹ : A.Kˣ) • x) = (distribHaarChar A.K s : ENNReal) • μK := by
    ext S hS
    rw [Measure.map_apply (measurable_const_smul _) hS, Set.preimage_smul, Measure.smul_apply, smul_eq_mul,
      distribHaarChar_mul, inv_inv]
  have e := integral_map_equiv (MeasurableEquiv.smul (s⁻¹ : A.Kˣ) : A.K ≃ᵐ A.K) (μ := μK) H
  rw [show (⇑(MeasurableEquiv.smul (s⁻¹ : A.Kˣ) : A.K ≃ᵐ A.K)) = fun x => (s⁻¹ : A.Kˣ) • x from rfl, hmap,
    integral_smul_measure] at e
  rw [show (fun t => H (((s⁻¹ : A.Kˣ) : A.K) * t)) = fun t => H ((s⁻¹ : A.Kˣ) • t) from rfl, ← e]
  simp [Complex.real_smul]

theorem etaK_mul [Unram F E] (A : Et F E) (s : A.Kˣ) (u : A.K) (hu : IsUnit u) :
    A.etaK ((s : A.K) * u) = A.etaK s * A.etaK u := by
  unfold Et.etaK
  rw [map_mul]
  exact (_root_.GlobalTheory.EtaChar.main F E).1 _ _ (s.isUnit.map (Algebra.norm F)).ne_zero (hu.map (Algebra.norm F)).ne_zero

theorem jHyp_nm : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (ψ : AddChar F ℂ)
    (φ' : A.K × A.K → ℂ) (z : A.K) (s : A.Kˣ) (g : SpecialLinearGroup (Fin 2) A.K),
    A.jHyp μK ψ φ' (nS z * mS s * g) = A.etaK s * (A.absK s : ℂ) * A.jHyp μK ψ φ' g := by
  intro F E _ _ _ _ _ A μK hμ ψ φ' z s g
  haveI := hμ
  unfold Et.jHyp
  simp only [row_one]
  set H : A.K → ℂ := fun u => A.tilde μK ψ φ' (u * g 1 0) (u * g 1 1) * A.etaK ((s : A.K) * u) with hH
  have h1 : (fun t => A.tilde μK ψ φ' (t * (((s⁻¹ : A.Kˣ) : A.K) * g 1 0)) (t * (((s⁻¹ : A.Kˣ) : A.K) * g 1 1)) *
      A.etaK t) = fun t => H (((s⁻¹ : A.Kˣ) : A.K) * t) := by
    funext t
    simp only [hH]
    rw [Units.mul_inv_cancel_left]
    congr 2 <;> ring
  rw [h1, integral_inv_mul A μK s H]
  have hnull : μK {t | ¬ IsUnit t} = 0 := (_root_.GlobalTheory.JR.EtFacts.main F E A).2.2.2.2.2.2.2.2.1 μK hμ
  have hae : ∀ᵐ u ∂μK, IsUnit u := ae_iff.mpr hnull
  have h2 : ∫ u, H u ∂μK = ∫ u, A.tilde μK ψ φ' (u * g 1 0) (u * g 1 1) * A.etaK u * A.etaK s ∂μK := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with u hu
    simp only [hH]
    rw [etaK_mul A s u hu]
    ring
  rw [h2, integral_mul_const, absK_unit]
  ring

end GlobalTheory.JHypEquiv
end

