module

public import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.StarMemSchA
public import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.ArchCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0914
public import Development.WeilBound.ThetaLifts.CartanFactorisation.TensOfEval
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle0005
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1586
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.PresOfHat
section
noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone.Vf

open scoped Matrix TensorProduct GlobalTheory.VacAny
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.LatVac
open PositivityTheory.ThK PositivityTheory.ThK.Vac PositivityTheory.ThKH.Iwas PositivityTheory.ThKH.Locrep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {v : Pl F}

theorem pres_of_hat {X : Spc F E n} {g : Matrix (Fin n) (Fin n) (AE F E)}
    (hg : ∀ z ∈ GlobalTheory.ThK.latHat X, g *ᵥ z ∈ GlobalTheory.ThK.latHat X) : g ∈ Pres v X := by
  have up : ∀ y ∈ latW X v, y ∈ GlobalTheory.ThK.latHat X := fun y hy => by
    refine AddSubgroup.closure_mono ?_ hy
    rintro _ ⟨a, ha, hav, x, hx, rfl⟩
    refine ⟨a, ?_, fun u => ?_, x, hx, rfl⟩
    · rw [eq_liftV ha]; exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    · rcases eq_or_ne u v with rfl | h
      · exact hav
      · rw [eq_liftV ha, show evFin F u (liftV v (evFin F v a)) = 0 from evalV_singleFin_ne h _]; exact zero_mem _
  have dn : ∀ y ∈ GlobalTheory.ThK.latHat X, sg v 1 • y ∈ latW X v := fun y hy => by
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, -, ha, x, hx, rfl⟩ := hz
      refine AddSubgroup.subset_closure ⟨sg v 1 * a, ?_, ?_, x, hx, ?_⟩
      · rw [mul_comm, mul_sg]; exact at_sg _
      · rw [map_mul, ev_sg, one_mul]; exact ha v
      · rw [smul_smul]; rfl
    | zero => rw [smul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
    | neg y _ hy => rw [smul_neg]; exact neg_mem hy
  intro y hy
  have := dn _ (hg y (up y hy))
  rwa [show sg v 1 • (g *ᵥ y) = g *ᵥ y from idem_smul (at_mulVec_right g ((mem_latW_loc X y).1 hy).1)] at this


variable (σ) in
def USub' (X : Spc F E n) (v : Pl F) : Subgroup (UA σ X.J) where
  carrier := UAt σ X (evFin F v)
  one_mem' := one_mem_UAt X v
  mul_mem' := mul_mem_UAt
  inv_mem' := fun {g} hg => by
    have e0 : mat g⁻¹ * mat g = 1 := g.1.inv_mul
    have e : mat g⁻¹ - 1 = 0 - mat g⁻¹ * (mat g - 1) := by rw [mul_sub, e0, mul_one, zero_sub, neg_sub]
    change At _ (mat g⁻¹ - 1)
    rw [e]
    exact at_sub at_zero (at_mul_right _ hg)

theorem at_conj {ι : Type} [Fintype ι] [DecidableEq ι] {C g C' : Matrix ι ι (AE F E)} (h : C * C' = 1)
    (hg : At (evFin F v) (g - 1)) : At (evFin F v) (C * g * C' - 1) := by
  rw [show C * g * C' - 1 = C * (g - 1) * C' by rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h]]
  exact at_mul_left (at_mul_right _ hg) _

theorem norm_eq_one {G : Type} [Group G] [TopologicalSpace G] {K : Subgroup G} (hK : IsCompact (K : Set G)) {f : G → ℂ}
    (hf : Continuous f) {k : G} (hk : k ∈ K) {c a : ℂ} (ha : a ≠ 0) (h : ∀ j : ℕ, f (k ^ j) = c ^ j * a) : ‖c‖ ≤ 1 := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  by_contra hn
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (C / ‖a‖) (not_le.1 hn)
  have := hC _ (pow_mem hk j)
  rw [h, norm_mul, norm_pow] at this
  exact absurd ((div_lt_iff₀ (norm_pos_iff.2 ha)).1 hj) (not_lt.2 this)

end PositivityTheory.ThKG.Loc.Cone.Vf

namespace PositivityTheory.ThKG.Loc.Cone

open scoped Matrix TensorProduct GlobalTheory.VacAny
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.LatVac
open PositivityTheory.ThK PositivityTheory.ThK.Vac PositivityTheory.ThKH.Iwas PositivityTheory.ThKH.Locrep Vf

theorem vacFixX_of (hSt : GlobalTheory.ThK.StabEx) : VacFixX := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' P K hK v hv k hk
  have hB := P.base
  have hL := P.herm.lat
  have hs := IsUWeilPair.isUSplitting P.weil
  have hKc : IsCompact (K : Set (UA σ X.J)) := by
    obtain ⟨K', -, -, h1, h2, -⟩ := hSt F E σ B n X r s hB P.herm
    rwa [show K = K' from Subgroup.ext fun g => (hK g).trans (h1 g).symm]
  have hU : ∀ k ∈ kAt K (evFin F v), k ∈ UAt σ X (evFin F v) := fun k hk =>
    (Subgroup.closure_le (USub' σ X v)).2 (fun _ h => h) hk.2
  have hP : ∀ k ∈ kAt K (evFin F v), mat k ∈ Pres v X := fun k hk => pres_of_hat fun z hz => (((hK k).1 hk.1).2 z hz).1
  obtain ⟨hsb, h0, θ, hθ1, hθ⟩ := P.good.vac v
  have hAt := (latAtV_at_stable X W v).1
  obtain ⟨r₀, x₀, h₀, h₁⟩ := exists_base (Fin n × Fin d) v
  have eig : ∀ k ∈ kAt K (evFin F v), ∃ c : ℂ, Acts (evFin F v) (om (k, 1)) (M.vac v) (c • M.vac v) := fun k hk => by
    refine eigen M.co hB.std (latAtV X W v) hAt (fun z hz h => mem_latAtV hB P.herm P.skew v hz h) _ hsb h0
      (fun γ hγ => (eq_of_acts v h₁ (h₀ _ hsb) (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v γ (hAt γ hγ) _)).trans
        (eq_of_acts v h₁ (h₀ _ hsb) (hθ γ hγ)).symm) (om (k, 1)) (hs.pres _) (hs.adm _) (actAB (cA σ) (k, 1)) (hs.impl _)
      (fun u hu => act_away (hU k hk) (one_mem_UAt W v) hu) fun γ hγ => ⟨mat k⁻¹ * γ, mul_latAtV (hP _ (inv_mem hk)) hγ, ?_, ?_⟩
    · have : mat k * mat k⁻¹ = 1 := k.1.mul_inv
      change mat k * (mat k⁻¹ * γ) * (1 : Matrix _ _ _)ᵀ = γ
      rw [← Matrix.mul_assoc, this, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]
    · rw [symp, symp, ← hTens_tr, ← hTens_tr _ _ _ γ, Matrix.transpose_mul, hTens_mul (cA σ) _ (k := mat k⁻¹) (k⁻¹).2]
  set Φ := tens (evFin F v) (M.vac v) r₀ with hΦ
  have hΦs : Φ ∈ schA F _ := (h₀ _ hsb).2
  obtain ⟨y, hy⟩ := Function.ne_iff.1 h0
  have hΦy : Φ (putA v x₀ y) = M.vac v y := by
    change M.vac v (evA _ v (putA v x₀ y)) * r₀ (putA v x₀ y) = _
    rw [ev_put (evA_inA v), inv_putA v (h₀ _ hsb).1, h₁, mul_one]
  have hΦ0 : Φ ≠ 0 := fun e => hy (by rw [← hΦy, e]; rfl)
  have bd : ∀ k ∈ kAt K (evFin F v), ∀ c : ℂ, om (k, 1) Φ = c • Φ → ‖c‖ ≤ 1 := fun k hk c hc => by
    refine norm_eq_one hKc (f := fun g => (LinearMap.proj y ∘ₗ res v x₀) (om (g, 1) Φ))
      ((hs.cont _ (res_adm v x₀ _) _ hΦs).comp (continuous_id.prodMk continuous_const)) hk.1 (a := M.vac v y) hy fun j => ?_
    have : om (k ^ j, 1) Φ = c ^ j • Φ := by
      induction j with
      | zero => rw [pow_zero, pow_zero, one_smul, Prod.mk_one_one, map_one]; rfl
      | succ j ih =>
        rw [show ((k ^ (j + 1), 1) : _ × UA σ W.J) = (k ^ j, 1) * (k, 1) by simp [pow_succ], map_mul, Module.End.mul_apply, hc,
          map_smul, ih, smul_smul, pow_succ']
    rw [this, map_smul, smul_eq_mul, ← hΦy]; rfl
  obtain ⟨c, hc⟩ := eig k hk
  have hcΦ : om (k, 1) Φ = c • Φ := by rw [hΦ, hc r₀ (h₀ _ hsb), tens_smul]
  suffices h : c = 1 by rwa [h, one_smul] at hc
  obtain ⟨-, ⟨d', hd', -, dd, omd, hdd, ⟨-, hsp, hrule⟩, hres⟩, -⟩ := P.weil
  obtain ⟨b, b', f', b1, b2, hb, pb, pf, hf⟩ := exists_beta hB hL k (hU k hk) (hP k hk) (hP _ (inv_mem hk))
  obtain ⟨gd, hgd⟩ := GlobalTheory.unitary_diag_one_mem_dbl (AF F) (AE F E) (cA σ) (Fin n) (incM F X.J) k
  have hm : At (evFin F v) (1 - mat k) := by simpa using at_sub at_zero (hU k hk)
  have pm : 1 - mat k ∈ Pres v X := sub_mem (one_mem _) (hP k hk)
  have hJ : incM F X.J * incM F X.J⁻¹ = 1 := by
    change X.J.map (inclR (F := F) (AF F)) * X.J⁻¹.map (inclR (F := F) (AF F)) = 1
    rw [← Matrix.map_mul (f := (inclR (F := F) (AF F) : E →+* AE F E)), Matrix.mul_nonsing_inv _ (herm_det P.herm)]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  obtain ⟨s₀, n₀, p, t, ss, eg, es, en, en', hn, hp, et, et'⟩ :=
    exists_decomp hJ k b1 b2 hb hf (ε := Vf.eps v) eps_mul ((cA σ).commutes _) (eps_smul hm) gd hgd
  have o1 := one_mem (Pres v X)
  have z0 := zero_mem (Pres v X)
  have pC : PresD v X (CC b) := ⟨_, o1, _, add_mem o1 pb, _, o1, _, pb, rfl⟩
  have pCi : PresD v X (Ci b) := ⟨_, neg_mem pb, _, add_mem o1 pb, _, o1, _, neg_mem o1, rfl⟩
  have c1 : compFin F E v (Vf.eps v : AE F E) = 1 := by rw [Vf.eps, comp_alg, ev_sg]; rfl
  have pe : (Vf.eps v : AE F E) • (1 : Matrix _ _ _) ∈ Pres v X := smul_mem_Pres hL (by rw [c1]; exact one_mem _) o1
  have pe' : (1 - Vf.eps v : AE F E) • (1 : Matrix _ _ _) ∈ Pres v X :=
    smul_mem_Pres hL (by rw [map_sub, map_one, c1, sub_self]; exact zero_mem _) o1
  have vd : M.IsVac B.ψ v (M.vac v) := ⟨hsb, h0, θ, hθ1, hθ⟩
  have bt : boxFun Φ (star Φ) = tens (evFin F v) (boxFun (M.vac v) (star (M.vac v))) (boxFun r₀ (star r₀)) := by
    funext x
    simp only [hΦ, boxFun, tens, Pi.star_apply, star_mul']
    exact mul_mul_mul_comm _ _ _ _
  have hΦd := GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Φ hΦs _ (star_mem_schA hΦs)
  have rd : Rest (evFin F v) (boxFun (M.vac v) (star (M.vac v))) (boxFun r₀ (star r₀)) := by
    refine ⟨fun x z hz => ?_, bt ▸ hΦd⟩
    have i1 := (h₀ _ hsb).1 (x ∘ Sum.inl) (z ∘ Sum.inl) fun u hu => funext fun i => congrFun (hz u hu) _
    have i2 := (h₀ _ hsb).1 (x ∘ Sum.inr) (z ∘ Sum.inr) fun u hu => funext fun i => congrFun (hz u hu) _
    change r₀ (x ∘ Sum.inl + z ∘ Sum.inl) * star (r₀ (x ∘ Sum.inr + z ∘ Sum.inr)) = _
    rw [i1, i2]; rfl
  have ev : ∀ g : UG (cA σ) (dbl (incM F X.J)), At (evFin F v) (g.1.1 - 1) → PresD v X (g⁻¹).1.1 →
      ∃ a : ℂ, omd g (boxFun Φ (star Φ)) = a • boxFun Φ (star Φ) := fun g h1 h2 => by
    obtain ⟨a, ha⟩ := dbl_eigen hB P.herm P.skew vd hd' hdd hsp.toIsSplitting g h1 h2
    exact ⟨a, by rw [bt, ha _ rd, tens_smul]⟩
  obtain ⟨a, ha⟩ := ev s₀ (by
      rw [es]
      refine at_conj (CC_Ci b) fun u hu => ?_
      have : u • (Vf.eps v : AE F E) = 0 := at_eps u hu
      ext (i | i) (j | j) <;> simp [SS, Matrix.one_apply, smul_ite, this, apply_ite (u • ·)] <;> split_ifs <;> simp [this])
    (by rw [inv_eq_of_mul_eq_one_right ss, es]; exact (pC.mul ⟨_, pe', _, pe, _, pe, _, pe', rfl⟩).mul pCi)
  obtain ⟨a', ha'⟩ := ev n₀ (by
      rw [en]
      refine at_conj (CC_Ci b) fun u hu => ?_
      have := at_mul_right f' hm u hu
      rw [← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add, Matrix.fromBlocks_smul]
      simp only [add_neg_cancel, neg_zero, add_zero, smul_zero, smul_neg]
      rw [show u • (f' * (1 - k.1.1)) = 0 from this, neg_zero, Matrix.fromBlocks_zero])
    (by rw [en']; exact (pC.mul ⟨_, o1, _, mul_mem pf pm, _, z0, _, o1, rfl⟩).mul pCi)
  have a1 : a' = 1 := by
    rw [rule_diag hdd hrule n₀ 1 hn (by rw [map_one, map_one]) hΦs hΦ0 ha']
    simp
  have aa : a * a = 1 := by
    have e : omd (s₀ * s₀) (boxFun Φ (star Φ)) = (a * a) • boxFun Φ (star Φ) := by
      rw [map_mul, Module.End.mul_apply, ha, map_smul, ha, smul_smul]
    rw [ss, map_one, Module.End.one_apply] at e
    have := congrArg (GlobalTheory.DiagForm.lDiag F _) e
    rw [map_smul, smul_eq_mul] at this
    exact (mul_right_cancel₀ (lDiag_ne hΦs hΦ0) (this.symm.trans (one_mul _).symm))
  have e1 : omd gd (boxFun Φ (star Φ)) = c • boxFun Φ (star Φ) := by
    rw [hres k gd hgd Φ hΦs _ (star_mem_schA hΦs)]
    change boxFun (om (k, 1) Φ) _ = _
    rw [hcΦ]; funext x; simp [boxFun, mul_assoc]
  have e2 : omd p (boxFun Φ (star Φ)) = c • boxFun Φ (star Φ) := by
    have e3 : omd (s₀ * n₀ * s₀) (boxFun Φ (star Φ)) = boxFun Φ (star Φ) := by
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ha, map_smul, ha', a1, one_smul, map_smul, ha, smul_smul,
        aa, one_smul]
    have : p = (s₀ * n₀ * s₀)⁻¹ * gd := by rw [eg]; group
    rw [this, map_mul, Module.End.mul_apply, e1, map_smul]
    conv_lhs => rw [← e3, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have hpos := rule_diag hdd hrule p t hp (chi_det hL χW (fun w hw => (hv w hw).2) t
    (by rw [et]; exact add_mem o1 (mul_mem pb pm)) (by rw [et']; exact sub_mem o1 (mul_mem pb (mul_mem pf pm)))
    (by rw [et, add_sub_cancel_left]; exact at_mul_right _ hm)) hΦs hΦ0 e2
  obtain ⟨c', hc'⟩ := eig k⁻¹ (inv_mem hk)
  have hc'Φ : om (k⁻¹, 1) Φ = c' • Φ := by rw [hΦ, hc' r₀ (h₀ _ hsb), tens_smul]
  have cc : c * c' = 1 := by
    have e : om ((k⁻¹, 1) * (k, 1)) Φ = (c * c') • Φ := by rw [map_mul, Module.End.mul_apply, hcΦ, map_smul, hc'Φ, smul_smul]
    rw [Prod.mk_mul_mk, inv_mul_cancel, one_mul, Prod.mk_one_one, map_one, Module.End.one_apply] at e
    have := congrFun e (putA v x₀ y)
    rw [Pi.smul_apply, hΦy, smul_eq_mul] at this
    exact mul_right_cancel₀ hy (this.symm.trans (one_mul _).symm)
  have n1 := bd k hk c hcΦ
  have n2 := bd _ (inv_mem hk) c' hc'Φ
  have n3 : ‖c‖ * ‖c'‖ = 1 := by rw [← norm_mul, cc, norm_one]
  have n4 : ‖c‖ = 1 := le_antisymm n1 (by nlinarith [norm_nonneg c, norm_nonneg c'])
  rw [hpos] at n4 ⊢
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)] at n4
  rw [n4, Complex.ofReal_one]

end PositivityTheory.ThKG.Loc.Cone

end
end

-- bundled from Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.PureCancel
section
noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone.Fin

open scoped TensorProduct NNReal Matrix nonZeroDivisors GlobalTheory.VacAny Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.LatVac
open GlobalTheory.Doubling (absE)

theorem int_fin {α Y : Type} [MeasurableSpace α] (μ : Measure α) (G : α → Y → ℂ) (w : α → ℂ) (hf : (Set.range G).Finite)
    (hm : ∀ g, MeasurableSet {a | G a = g}) (D : Set α) (hD : ∀ a ∉ D, G a = 0) (hw : IntegrableOn w D μ)
    (S : Submodule ℂ (Y → ℂ)) (hS : ∀ a, G a ∈ S) :
    (∀ y, Integrable (fun a => G a y * w a) μ) ∧ (fun y => ∫ a, G a y * w a ∂μ) ∈ S := by
  let s := hf.toFinset.erase 0
  have e : ∀ y a, G a y * w a = ∑ g ∈ s, g y * ({a | G a = g} : Set α).indicator w a := fun y a => by
    by_cases h0 : G a = 0
    · rw [h0, Pi.zero_apply, zero_mul, Finset.sum_eq_zero]
      intro g hg
      rw [Set.indicator_of_notMem, mul_zero]
      exact fun h => (Finset.mem_erase.1 hg).1 (h.symm.trans h0)
    · rw [Finset.sum_eq_single (G a), Set.indicator_of_mem (by rfl)]
      · intro g _ hne
        rw [Set.indicator_of_notMem (s := {a | G a = g}) (fun h => hne (Eq.symm h)), mul_zero]
      · intro h
        exact absurd (Finset.mem_erase.2 ⟨h0, hf.mem_toFinset.2 ⟨a, rfl⟩⟩) h
  have hi : ∀ g ∈ s, Integrable (({a | G a = g} : Set α).indicator w) μ := fun g hg =>
    (integrable_indicator_iff (hm g)).2 (hw.mono_set fun a ha => by
      by_contra hn
      exact (Finset.mem_erase.1 hg).1 (Eq.trans (Eq.symm ha) (hD a hn)))
  refine ⟨fun y => ?_, ?_⟩
  · simp only [e y]
    exact integrable_finsetSum _ fun g hg => (hi g hg).const_mul _
  · have : (fun y => ∫ a, G a y * w a ∂μ) = ∑ g ∈ s, (∫ a, ({a | G a = g} : Set α).indicator w a ∂μ) • g := by
      funext y
      simp only [e y, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [integral_finsetSum _ fun g hg => (hi g hg).const_mul _]
      exact Finset.sum_congr rfl fun g _ => by rw [integral_const_mul, mul_comm]
    rw [this]
    refine S.sum_mem fun g hg => S.smul_mem _ ?_
    obtain ⟨a, rfl⟩ := hf.mem_toFinset.1 (Finset.mem_erase.1 hg).2
    exact hS a

section Schr
variable {k κ : Type} [CommRing k] [Invertible (2 : k)] [TopologicalSpace k] [IsTopologicalRing k] [Fintype κ]
  {ψ : AddChar k ℂ}

omit [TopologicalSpace k] [IsTopologicalRing k] in
theorem schr_mul (w w' : (κ → k) × (κ → k)) (φ : (κ → k) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (⅟(2 : k) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') φ := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add, add_assoc, ← mul_assoc,
    ← AddChar.map_add_eq_mul, add_dotProduct, dotProduct_add]
  congr 2
  have := invOf_two_add_invOf_two (R := k)
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * this

theorem schr_fix (hψ : IsLocallyConstant ψ) {φ : (κ → k) → ℂ} (hφ : φ ∈ SB (κ → k)) :
    ∀ᶠ w in 𝓝 (0 : (κ → k) × (κ → k)), schr ψ w φ = φ := by
  have h : ∀ᶠ w in 𝓝 (0 : (κ → k) × (κ → k)), ∀ x ∈ tsupport φ,
      ψ (x ⬝ᵥ w.2 + ⅟(2 : k) * (w.1 ⬝ᵥ w.2)) = 1 ∧ φ (x + w.1) = φ x ∧ φ (x - w.1) = φ x := by
    refine IsCompact.eventually_forall_of_forall_eventually hφ.2 fun x _ => ?_
    have c1 : Continuous fun z : ((κ → k) × (κ → k)) × (κ → k) => z.2 ⬝ᵥ z.1.2 + ⅟(2 : k) * (z.1.1 ⬝ᵥ z.1.2) := by
      unfold dotProduct; fun_prop
    have c2 : Continuous fun z : ((κ → k) × (κ → k)) × (κ → k) => z.2 + z.1.1 := by fun_prop
    have c3 : Continuous fun z : ((κ → k) × (κ → k)) × (κ → k) => z.2 - z.1.1 := by fun_prop
    have e1 := (hψ.comp_continuous c1).eventually_eq (0, x)
    have e2 := (hφ.1.comp_continuous c2).eventually_eq (0, x)
    have e3 := (hφ.1.comp_continuous c3).eventually_eq (0, x)
    have e4 := (hφ.1.comp_continuous (continuous_snd (X := (κ → k) × (κ → k)))).eventually_eq (0, x)
    filter_upwards [e1, e2, e3, e4] with z a b c d
    simp only [Function.comp_apply, Prod.snd_zero, Prod.fst_zero, dotProduct_zero, mul_zero, add_zero, sub_zero,
      AddChar.map_zero_eq_one] at a b c d
    exact ⟨a, b.trans d.symm, c.trans d.symm⟩
  filter_upwards [h] with w hw
  funext x
  by_cases hx : x ∈ tsupport φ
  · rw [schr, (hw x hx).1, (hw x hx).2.1, one_mul]
  · have h0 : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
    rw [schr, h0]
    by_cases h1 : x + w.1 ∈ tsupport φ
    · have := (hw _ h1).2.2
      rw [add_sub_cancel_right, h0] at this
      rw [← this, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport h1, mul_zero]

theorem schr_lc (hψ : IsLocallyConstant ψ) {φ : (κ → k) → ℂ} (hs : ∀ w, schr ψ w φ ∈ SB (κ → k)) :
    IsLocallyConstant fun w => schr ψ w φ := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun w₀ => ?_
  have c : Continuous fun w : (κ → k) × (κ → k) => ⅟(2 : k) * (w.1 ⬝ᵥ w₀.2 - w₀.1 ⬝ᵥ w.2) := by
    unfold dotProduct; fun_prop
  have h : ∀ᶠ w in 𝓝 (0 : (κ → k) × (κ → k)), schr ψ (w + w₀) φ = schr ψ w₀ φ := by
    filter_upwards [schr_fix hψ (hs w₀), (hψ.comp_continuous c).eventually_eq 0] with w a b
    simp only [Function.comp_apply, Prod.snd_zero, Prod.fst_zero, dotProduct_zero, zero_dotProduct, sub_zero, mul_zero,
      AddChar.map_zero_eq_one] at b
    rw [schr_mul, b, one_smul] at a
    exact a
  have t : Tendsto (fun w : (κ → k) × (κ → k) => w - w₀) (𝓝 w₀) (𝓝 0) := by
    have := (continuous_sub_right w₀).tendsto w₀
    rwa [sub_self] at this
  filter_upwards [t.eventually h] with w hw
  rwa [sub_add_cancel] at hw

omit [TopologicalSpace k] [IsTopologicalRing k] in
theorem schr_comm (w w' : (κ → k) × (κ → k)) (φ : (κ → k) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) • schr ψ w' (schr ψ w φ) := by
  rw [schr_mul, schr_mul, smul_smul, ← AddChar.map_add_eq_mul, add_comm w' w]
  congr 2
  have := invOf_two_add_invOf_two (R := k)
  linear_combination (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) * this

omit [TopologicalSpace k] [IsTopologicalRing k] in
theorem schr_lin (w : (κ → k) × (κ → k)) (φ φ' : (κ → k) → ℂ) (c : ℂ) :
    schr ψ w (φ + c • φ') = schr ψ w φ + c • schr ψ w φ' := by
  funext x; simp only [schr, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

end Schr

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem acts_uniq {v : Pl F} {T} {φ φ₁ φ₂ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB _) (h₁ : Acts (evFin F v) T φ φ₁)
    (h₂ : Acts (evFin F v) T φ φ₂) : φ₁ = φ₂ :=
  GlobalTheory.TensUniq.eq_of_tens_eq v φ φ₁ φ₂ hφ fun r hr => (h₁ r hr).symm.trans (h₂ r hr)

theorem opF_eq {v : Pl F} {T} {φ φ₁ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB _) (h₁ : φ₁ ∈ SB _) (h : Acts (evFin F v) T φ φ₁) :
    opF v T φ = φ₁ := by
  have ex : ∃ φ₁ ∈ SB (κ → Fv F v), Acts (evFin F v) T φ φ₁ := ⟨φ₁, h₁, h⟩
  rw [opF, dite_eq_left ex]
  exact acts_uniq hφ ex.choose_spec.2 h

theorem acts_comp {v : Pl F} {S T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {φ φ₁ φ₂ : (κ → Fv F v) → ℂ}
    (hT : ∀ Φ ∈ schA F κ, T Φ ∈ schA F κ) (h₁ : Acts (evFin F v) T φ φ₁) (h₂ : Acts (evFin F v) S φ₁ φ₂) :
    Acts (evFin F v) (fun Φ => S (T Φ)) φ φ₂ := fun r hr => by
  show S (T _) = _
  rw [h₁ r hr]
  exact h₂ r ⟨hr.1, h₁ r hr ▸ hT _ hr.2⟩

theorem pure_cancel {w : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hne : ∀ v, w v ≠ 0)
    (hstd : ∀ᶠ v in cofinite, w v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) (v : Pl F) {g : SInf F κ}
    (hg : g ≠ 0) {a b : (κ → Fv F v) → ℂ}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (Function.update w v a) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (Function.update w v b)) : a = b := by
  have := PositivityTheory.ThKF.tensInj F κ w hne hstd {v} 2 ![1, -1] ![g, g] ![Function.update w v a, Function.update w v b]
    (fun i u hu => by
      have : u ≠ v := fun e => hu (Finset.mem_singleton.2 e)
      fin_cases i <;> simp [Function.update_of_ne this]) (by simp [Fin.sum_univ_two, h])
  obtain ⟨z, hz⟩ : ∃ z, g z ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hg (SchwartzMap.ext hn)
  funext y
  let y' : ∀ u : ({v} : Finset (Pl F)), κ → Fv F u := fun u => (Finset.mem_singleton.1 u.2).symm ▸ y
  let m : MultilinearMap (RingHom.id ℂ) (fun u : ({v} : Finset (Pl F)) => (κ → Fv F u) → ℂ) ℂ :=
    (MultilinearMap.mkPiAlgebra ℂ _ ℂ).compLinearMap fun u => LinearMap.proj (y' u)
  let ez : SInf F κ →ₗ[ℂ] ℂ := ⟨⟨fun f => f z, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  have h2 := congrArg (TensorProduct.lift ((LinearMap.mul ℂ ℂ).compl₁₂ ez (PiTensorProduct.lift m))) this
  have hm : ∀ c : (κ → Fv F v) → ℂ, m (fun u => Function.update w v c u) = c y := fun c => by
    simp only [m, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply, LinearMap.proj_apply]
    rw [Fintype.prod_eq_single (⟨v, Finset.mem_singleton_self v⟩ : ({v} : Finset (Pl F)))
      fun u hu => absurd (Subtype.ext (Finset.mem_singleton.1 u.2)) hu]
    simp [y']
  simp only [Fin.sum_univ_two, map_add (f := _), map_smul, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, PiTensorProduct.lift.tprod,
    Matrix.cons_val_zero, Matrix.cons_val_one, map_zero, LinearMap.mul_apply', hm] at h2
  have h3 : g z * (a y - b y) = 0 := by
    change (1 : ℂ) • (g z * a y) + (-1 : ℂ) • (g z * b y) = 0 at h2
    simp only [smul_eq_mul] at h2
    linear_combination h2
  exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left hz)

end PositivityTheory.ThKG.Loc.Cone.Fin

end
end

