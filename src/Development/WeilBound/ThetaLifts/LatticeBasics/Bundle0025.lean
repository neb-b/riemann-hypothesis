module

public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0016
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0010
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0023
public import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.AdelInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1664
public import Mathlib
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0006
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0013
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0021
public import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.BadFactor
section
noncomputable section

namespace GlobalTheory.ThK.Dbl.Bad

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
open PositivityTheory.ThKG.Loc (idem)
open PositivityTheory.ThKG.Loc.Cone

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

variable {X : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}

theorem orth (P : IsPair B M χX χW om r s r' s') {ν} (hν : @Measure.IsAddHaarMeasure _ _ _ (borel _) ν) {Φ} (h : Φ ∈ schA F _)
    (h0 : Φ ≠ 0) {g u} {c c' : ℂ} (hc : c ≠ c') (h1 : M.co.rho B.ψ u Φ = c • Φ) (h2 : M.co.rho B.ψ (mat g * u) Φ = c' • Φ) :
    coef om ν Φ g = 0 := by
  by_contra hn
  have i := P.weil.isUSplitting.impl (g, 1) u Φ h
  rw [h1, map_smul, show actAB (cA σ) (g, 1) u = mat g * u from (congrArg _ Matrix.transpose_one).trans (Matrix.mul_one _)] at i
  have a1 := schr_unit P.base.std ν hν (M.co.e (mat g * u)) (om (g, 1) Φ) Φ
  have a2 := schr_unit P.base.std ν hν (M.co.e (mat g * u)) Φ Φ
  have k : ∀ (A : Fn F n d) (t : ℂ), ∫ x, (t • A) x * star ((c' • Φ) x) ∂ν = t * star c' * ∫ x, A x * star (Φ x) ∂ν := fun A t => by
    rw [← integral_const_mul]
    exact integral_congr_ae (.of_forall fun x => by simp only [Pi.smul_apply, smul_eq_mul, star_mul']; ring)
  rw [show schr B.ψ (M.co.e (mat g * u)) Φ = _ from h2] at a1 a2
  rw [show schr B.ψ (M.co.e (mat g * u)) (om (g, 1) Φ) = _ from i.symm, k] at a1
  rw [k] at a2
  have b1 := (mul_eq_right₀ hn).1 a1
  have b2 := (mul_eq_right₀ (sq_ne ν hν h h0)).1 a2
  exact hc (mul_right_cancel₀ (right_ne_zero_of_mul_eq_one b1) (b1.trans b2.symm))

theorem fix_of_parts (P : IsPair B M χX χW om r s r' s') {Φ} (h : Φ ∈ schA F _) {g : UA σ X.J}
    (h1 : om (partU real_mul_self g, 1) Φ = Φ) (h2 : ∀ v, om (partU (idem_mul_self v) g, 1) Φ = Φ) : om (g, 1) Φ = Φ := by
  classical
  have step : ∀ S : Finset (Pl F), om (partU (aS_mul_self S) g, 1) Φ = Φ := fun S => by
    induction S using Finset.induction_on with
    | empty => rwa [show partU (aS_mul_self ∅) g = partU real_mul_self g from
        mat_inj (by rw [mat_partU, mat_partU, aS, Finset.sum_empty, add_zero])]
    | insert v S hv ih =>
      have e : partU (aS_mul_self (insert v S)) g = partU (idem_mul_self v) g * partU (aS_mul_self S) g := by
        rw [← partU_add (idem_mul_self v) (aS_mul_self S) (idem_mul_aS hv) (aS_insert hv ▸ aS_mul_self (insert v S))]
        exact mat_inj (by rw [mat_partU, mat_partU, aS_insert hv])
      rw [e, ← mul_one (1 : UA σ W.J), ← Prod.mk_mul_mk, map_mul, Module.End.mul_apply, ih, h2]
  funext x
  have t := ((P.weil.2.2 _ (ev_adm x) _ h).continuousAt (x := (g, 1))).tendsto.comp
    ((tendsto_partU g).prodMk_nhds tendsto_const_nhds)
  exact tendsto_nhds_unique t (tendsto_const_nhds.congr fun S => (congrFun (step S) x).symm)

theorem prj_eq (v : Pl F) (g : UA σ X.J) : partU (idem_mul_self v) g = Euler.prj v g := mat_inj (add_comm _ _)

theorem cont_emb {e : UA σ X.J × UA σ X.J →* G2 σ X} (he : ∀ g g', IsEmb g g' (e (g, g'))) : Continuous fun g => e (g, 1) := by
  have c : Continuous fun g => mat2 (e (g, 1)) :=
    (Euler.cont_mat.matrix_fromBlocks continuous_const continuous_const continuous_const).congr fun g => (he g 1).symm
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨c, (c.comp continuous_inv).congr fun g => ?_⟩)
  change mat2 (e (g⁻¹, 1)) = mat2 (e (g, 1))⁻¹
  rw [← map_inv, Prod.inv_mk, inv_one]

theorem par_one : IsPar (1 : G2 σ X) 1 := (Matrix.one_mul _).trans (Matrix.mul_one _).symm

theorem hgt_mul {K : Subgroup (G2 σ X)} {a : G2 σ X → ℝ} (ha : IsHgt K a) (y) {k} (hk : k ∈ K) : a (y * k) = a y := by
  obtain ⟨p, t, hp, k', hk', rfl⟩ := ha.iwa y
  rw [mul_assoc, ha.val p t hp _ (mul_mem hk' hk), ha.val p t hp _ hk']

theorem hgt_one {K : Subgroup (G2 σ X)} {a : G2 σ X → ℝ} (ha : IsHgt K a) {k} (hk : k ∈ K) : a k = 1 := by
  simpa using ha.val 1 1 par_one k hk

theorem law {dd om₂ S l} (hB : B.IsGood σ) (h : IsDbl (σ := σ) (A := W) (Y := X) (κ := (Fin n × Fin d) ⊕ (Fin n × Fin d)) B.ψ dd χW om₂ S l)
    {Ψ} (hΨ : Ψ ∈ schA F _) : Law χW (d / 2) fun x => l (om₂ x Ψ) := fun p t x hp => by
  have := hB.cm.1
  beta_reduce
  rw [map_mul, Module.End.mul_apply, h.weil.2.2 l h.adm h.kill p t hp _ (h.weil.2.1.pres x Ψ hΨ), PositivityTheory.ThKF0.Chr.absE_eq,
    Complex.ofReal_cpow (NNReal.coe_nonneg _), Fintype.card_fin]
  push_cast
  rfl

theorem at_emb {e : UA σ X.J × UA σ X.J →* G2 σ X} (he : ∀ g g', IsEmb g g' (e (g, g'))) {v} {u : UA σ X.J} (hu : u ∈ locGrp σ X v) :
    At (evFin F v) (mat2 (e (u, 1)) - 1) := fun t ht => by
  have : t • (mat u - 1) = 0 := by rw [← Euler.mem_loc.1 hu, ← prj_eq]; exact partU_idem_mem v u t ht
  rw [he u 1, show mat (1 : UA σ X.J) = 1 from rfl, ← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg,
    Matrix.fromBlocks_add, Matrix.fromBlocks_smul, ← sub_eq_add_neg, this]
  simp

theorem int_all {v} {u : UA σ X.J} (hu : u ∈ locGrp σ X v) (h : IntAt v u) (w) : IntAt w u := by
  rcases eq_or_ne w v with rfl | hw
  · exact h
  · rw [← mul_one u, Euler.int_mul_ne hw hu]; exact (Euler.intGrp σ X w).one_mem

theorem _root_.GlobalTheory.ThK.Dbl.badFactor_of (hD : DblX) (hS : StabEx) (hV : VacFix2) (hB : Bump) : BadFactor := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' P h0 _ hn _ T hT _ uW f₀ p0 n0 i0 K a e hK ha he ν hν
  classical
  choose! β β1 β2 β3 using hB F E σ B n d X W M χX χW om r s r' s' P hn
  let φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ := fun v => if v ∈ T then β v else M.vac v
  have φ1 : ∀ v ∈ T, φ v = β v := fun v h => if_pos h
  have φ2 : ∀ v ∉ T, φ v = M.vac v := fun v h => if_neg h
  have hSB : ∀ v, φ v ∈ SB _ := fun v => by
    by_cases h : v ∈ T
    exacts [φ1 v h ▸ β1 v (hT h), φ2 v h ▸ (P.good.vac v).1]
  have hne : ∀ v, φ v ≠ 0 := fun v => by
    by_cases h : v ∈ T
    exacts [φ1 v h ▸ β2 v (hT h), φ2 v h ▸ (P.good.vac v).2.1]
  have hv : ∀ᶠ v in cofinite, φ v = M.vac v := T.eventually_cofinite_notMem.mono φ2
  have hs := (hv.and P.good.std).mono fun v h => h.1.trans h.2
  refine ⟨pure f₀ φ, Submodule.subset_span ⟨f₀, p0, φ, hSB, hv, rfl⟩, ?_⟩
  have m := GlobalTheory.TensUniq.pure_mem_schA f₀ φ hSB hs
  have m0 := GlobalTheory.EvNonzero.pure_ne_zero f₀ n0 φ hne hs
  obtain ⟨dd, om₂, S, l, d1, d2, d3, d4⟩ := hD F E σ B n d X W M χX χW om r s r' s' P
  obtain ⟨c, c0, hc⟩ := d4 ν hν
  have c1 := Complex.ofReal_ne_zero.2 c0.ne'
  have fx : ∀ v ∉ T, ∀ k ∈ K, At (evFin F v) (mat2 k - 1) → om₂ k (boxFun (pure f₀ φ) (star (pure f₀ φ))) = _ := fun v h k hk h' =>
    fix_box hSB hs (φ2 v h ▸ hV F E σ B n d X W M r s r' s' P.base P.herm P.skew P.good χW P.hW dd om₂ d3 d1.weil K hK v
      (fun w hw => uW w (by show ¬ w.under (𝓞 F) ∈ (T : Set (Pl F)); rw [hw]; exact h)) k hk h')
  have e1 := fun v (h : v ∈ T) S (c : ℂ) (h' : Acts (evFin F v) S (β v) (c • β v)) => eig (f := f₀) hSB hs (φ1 v h ▸ h')
  have e2 := fun S => fix_real (f := f₀) (S := S) hSB hs
  generalize pure f₀ φ = Φ at *
  have bx : ∀ g, om₂ (e (g, 1)) (boxFun Φ (star Φ)) = boxFun (om (g, 1) Φ) (star Φ) := fun g => by
    simpa [detInv, show ((1, 1) : UA σ X.J × UA σ W.J) = 1 from rfl] using ((d2 Φ m Φ m).2 1 g 1 _ (he g 1)).2
  have cf : ∀ g, l (om₂ (e (g, 1)) (boxFun Φ (star Φ))) = c * coef om ν Φ g := fun g => by
    rw [bx, hc _ (P.weil.isUSplitting.pres _ _ m) _ m]; rfl
  have N : coef om ν Φ 1 ≠ 0 := by
    rw [coef, show ((1, 1) : UA σ X.J × UA σ W.J) = 1 from rfl, map_one]; exact sq_ne ν hν m m0
  have a0 : ∀ x, 0 < a x := fun x => by
    obtain ⟨p, t, hp, k, hk, rfl⟩ := ha.iwa x
    rw [ha.val p t hp k hk]; exact absE_pos _
  refine ⟨fun z v hvT => ?_, ?_⟩
  · set G := flat a (fun x => l (om₂ x (boxFun Φ (star Φ)))) (((d : ℂ) - n) / 2) z with hG
    have L : Law χW (z + n / 2) G := by
      have := (law P.base d1 (d2 Φ m Φ m).1).flat (s₀ := ((d : ℂ) - n) / 2) ha a0 z
      rwa [show z - ((d : ℂ) - n) / 2 + d / 2 = z + n / 2 by ring] at this
    have R : ∀ k ∈ K, At (evFin F v) (mat2 k - 1) → ∀ y, G (y * k) = G y := fun k hk h y => by
      simp only [hG, flat, hgt_mul ha y hk, map_mul, Module.End.mul_apply, fx v hvT k hk h]
    have Z : ∀ g, G (e (g, 1)) = c * zint om ν a e Φ z g := fun g => by rw [hG, flat, cf, zint]; ring
    have G1 : G 1 ≠ 0 := by
      rw [← map_one e, show (1 : UA σ X.J × UA σ X.J) = (1, 1) from rfl, Z, zint, hgt_one ha (show e (1, 1) ∈ K from map_one e ▸ K.one_mem)]
      simpa using ⟨c0.ne', N⟩
    refine ⟨fun x => G x / G 1, fun p t hp _ k hk h => ?_, fun u hu => ⟨fun hi => ?_, fun g hg => ?_⟩⟩ <;> beta_reduce
    · rw [L p t k hp, ← one_mul k, R k hk h, mul_div_cancel_right₀ _ G1]
    · rw [← one_mul (e (u, 1)), R _ (emb_mem P.base P.herm h0 hK he (int_all hu hi)) (at_emb he hu), div_self G1]
    · obtain ⟨p, t, k, hp, hk, h, e'⟩ := loc_iwa hK ha (at_emb he hu)
      refine mul_left_cancel₀ c1 ?_
      rw [mul_left_comm, ← Z, ← Z, show e (u * g, 1) = e (u, 1) * e (g, 1) by rw [← map_mul, Prod.mk_mul_mk, mul_one], e',
        mul_assoc, L p t _ hp, L p t _ hp, comm_off he hg h, R k hk h, ← one_mul k, R k hk h, mul_div_cancel_right₀ _ G1]
  have key : ∀ g, (∀ v ∉ T, IntAt v g) → coef om ν Φ g ≠ 0 → (∀ v, IntAt v g) ∧ coef om ν Φ g = coef om ν Φ 1 := fun g hg h => by
    have b : ∀ v ∈ T, IntAt v g ∧ om (partU (idem_mul_self v) g, 1) Φ = Φ := fun v hv => by
      rcases β3 v (hT hv) _ (partU_idem_mem v g) with ⟨b1, b2⟩ | ⟨u, c, c', b1, b2, b3, b4⟩
      · exact ⟨Euler.int_prj.1 (prj_eq v g ▸ b1), (e1 v hv _ 1 (by rwa [one_smul])).trans (one_smul _ _)⟩
      · refine absurd (orth P hν m m0 b2 (e1 v hv _ _ b3) (e1 v hv _ _ ?_)) h
        rwa [mat_partU, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, sub_smul, one_smul, idem_smul b1,
          sub_self, add_zero, ← Matrix.mul_smul, idem_smul b1] at b4
    have hi : ∀ v, IntAt v g := fun v => (em (v ∈ T)).elim (fun h => (b v h).1) (hg v)
    refine ⟨hi, ?_⟩
    rw [coef, coef, show ((1, 1) : UA σ X.J × UA σ W.J) = 1 from rfl, map_one, fix_of_parts P m
      (e2 _ (i0 _ ⟨partU_real_mem g, fun w => commute_theta P.base P.herm h0 w _⟩)) fun v => ?_]
    · rfl
    by_cases h : v ∈ T
    · exact (b v h).2
    have l1 : partU (idem_mul_self v) g ∈ locGrp σ X v := Subgroup.subset_closure (partU_idem_mem v g)
    have := fx v h _ (emb_mem P.base P.herm h0 hK he (int_all l1 (prj_eq v g ▸ Euler.int_prj.2 (hi v)))) (at_emb he l1)
    obtain ⟨y, hy⟩ := Function.ne_iff.1 m0
    rw [bx] at this
    exact funext fun x => mul_right_cancel₀ (star_ne_zero.2 hy) (congrFun this (Sum.elim x y))
  have cl : IsClosed {g : UA σ X.J | ∀ v ∉ T, IntAt v g} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun v => isClosed_iInter fun _ => Euler.isClosed_int P.herm.lat.toIsLattice v
  have ct : Continuous (coef om ν Φ) := by
    refine (((d1.weil.2.1.cont l d1.adm _ (d2 Φ m Φ m).1).comp (cont_emb he)).div_const (c : ℂ)).congr fun g => ?_
    exact (congrArg (· / (c : ℂ)) (cf g)).trans (mul_div_cancel_left₀ _ c1)
  have op : IsOpen {g | coef om ν Φ g ≠ 0} := isOpen_ne_fun ct continuous_const
  have val : ∀ z, ∫ g in {g | ∀ v ∉ T, IntAt v g}, zint om ν a e Φ z g ∂M.μ =
      M.μ.real ({g | coef om ν Φ g ≠ 0} ∩ {g | ∀ v ∉ T, IntAt v g}) • coef om ν Φ 1 := fun z => by
    rw [← measureReal_restrict_apply op.measurableSet, ← integral_indicator_const _ op.measurableSet]
    refine setIntegral_congr_fun cl.measurableSet fun g hg => ?_
    by_cases h : coef om ν Φ g = 0
    · rw [zint, h, mul_zero, Set.indicator_of_notMem (not_not.2 h)]
    · rw [zint, hgt_one ha (emb_mem P.base P.herm h0 hK he (key g hg h).1), (key g hg h).2, Set.indicator_of_mem h]
      simp
  simp only [val]
  refine ⟨differentiable_const _, smul_ne_zero (ENNReal.toReal_ne_zero.2 ⟨?_, ?_⟩) N⟩
  · have := P.good.haar
    refine (M.μ.measure_pos_of_mem_nhds (x := 1) (inter_mem (op.mem_nhds N) ?_)).ne'
    exact mem_of_superset (int_nhds P.herm.lat) fun g h v _ => h v
  · have := P.good.haar
    obtain ⟨K₁, -, -, k1, k2, -⟩ := hS F E σ B n X r s P.base P.herm
    exact ((measure_mono fun g (h : g ∈ {g | coef om ν Φ g ≠ 0} ∩ {g | ∀ v ∉ T, IntAt v g}) =>
      (stab_iff P.base P.herm h0 k1).2 (key g h.2 h.1).1).trans_lt k2.measure_lt_top).ne

end GlobalTheory.ThK.Dbl.Bad

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.BoxSec
section
noncomputable section

namespace GlobalTheory.ThK.Dbl.Box

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl.Dense

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {κ β : Type} [Fintype κ] [Fintype β] {m n : ℕ}

variable {A : Spc F E m} {Y : Spc F E n} {B : Base F E}

theorem isSec_of {dd} {χ : Chr F E} {om S l} (h : IsDbl (σ := σ) (A := A) (Y := Y) (κ := κ ⊕ κ) B.ψ dd χ om S l)
    {K : Subgroup (G2 σ Y)} {Φ} (hΦ : Φ ∈ kfin om K) : IsSec K χ (((m : ℂ) - n) / 2) fun x => l (om x Φ) := by
  obtain ⟨N, _, h0, h1, h2⟩ := hΦ
  obtain ⟨c1, c2⟩ := sec_cont_law h (h0 h1)
  refine ⟨c1, c2, Submodule.finiteDimensional_of_le (S₂ := N.map (LinearMap.pi fun x => l ∘ₗ om x)) (Submodule.span_le.2 ?_)⟩
  rintro _ ⟨k, rfl⟩
  exact ⟨_, h2 k.1 k.2 Φ h1, funext fun x => by simp [map_mul]⟩

theorem polData_kfin {a d : ℕ} {X : Spc F E a} {W : Spc F E d} {M : Model σ X W} (hM : M.IsGood B.ψ)
    {N : Submodule ℂ (((Fin a × Fin d) ⊕ (Fin a × Fin d) → AF F) → ℂ)}
    (h : ∀ g₁ ∈ SB _, ∀ g₂ ∈ SB _, ∀ f₁ ∈ M.Pol B.ψ B.emb, ∀ f₂ ∈ M.Pol B.ψ B.emb,
      boxFun (pureA F f₁ g₁) (star (pureA F f₂ g₂)) ∈ N) {Φ₁ Φ₂} (h1 : Φ₁ ∈ PolData B M) (h2 : Φ₂ ∈ PolData B M) :
    boxFun Φ₁ (star Φ₂) ∈ N := by
  induction h1 using Submodule.span_induction with
  | mem Φ₁ m1 =>
    obtain ⟨f, hf, φ, a1, a2, rfl⟩ := m1
    induction h2 using Submodule.span_induction with
    | mem Φ₂ m2 =>
      obtain ⟨f', hf', φ', b1, b2, rfl⟩ := m2
      exact h _ (pf_mem ⟨a1, (a2.and hM.std).mono fun v hv => hv.1.trans hv.2⟩) _
        (pf_mem ⟨b1, (b2.and hM.std).mono fun v hv => hv.1.trans hv.2⟩) f hf f' hf'
    | zero => convert N.zero_mem; funext z; simp [boxFun]
    | add _ _ _ _ i j => convert N.add_mem i j; funext z; simp [boxFun, mul_add]
    | smul c _ _ i => convert N.smul_mem (star c) i; funext z; simp [boxFun, mul_left_comm]
  | zero => convert N.zero_mem; funext z; simp [boxFun]
  | add _ _ _ _ i j => convert N.add_mem i j; funext z; simp [boxFun, add_mul]
  | smul c _ _ i => convert N.smul_mem c i; funext z; simp [boxFun, mul_assoc]

theorem _root_.GlobalTheory.ThK.Dbl.boxSec_of (hL : FinLevel) (hC : Stab2Cpt) : BoxSec := by
  intro F E _ _ _ _ _ σ B m n A Y M r s r' s' hB _ _ _ _ hY hM χ _ _ dd om S l hd h K a hK _ Φ₁ h1 Φ₂ h2
  refine isSec_of h (polData_kfin hM (fun g₁ s1 g₂ s2 f₁ p1 f₂ p2 => box_kfin hL hB hK (hC F E σ B n Y r' s' hB (.inr hY) K hK)
    h.weil.2.1.toIsSplitting hd (fun N n1 n2 => (sInf_le (a := N) ⟨fun f ⟨ε, hε⟩ => n1 ε f fun u u' hu hu' e => ?_,
      fun u hu f hf f₁ e => ?_⟩ : M.Pol B.ψ B.emb ≤ N)) s1 s2 p1 p2) h1 h2)
  · exact hε u u' hu hu' e _ _ (actsD_dop M hB.std hu f) (actsD_dop M hB.std hu' f)
  · rw [actsD_unique' M hB.std hu e]; exact n2 u hu f hf

theorem _root_.GlobalTheory.ThK.Dbl.boxSecX_of (hL : FinLevel) (hC : Stab2Cpt) : BoxSecX := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB _ _ hX _ _ hM χ _ _ dd om S l ⟨d', ht, hd⟩ h K a hK _ Φ₁ h1 Φ₂ h2
  have tr : ∀ {p q : ℕ} {u : Matrix (Fin p) (Fin q) (AE F E)}, At (evI F) u → At (evI F) uᵀ := fun hu c hc => by
    rw [← Matrix.transpose_smul, hu c hc, Matrix.transpose_zero]
  refine isSec_of h (polData_kfin hM (fun g₁ s1 g₂ s2 f₁ p1 f₂ p2 => box_kfin hL hB hK (hC F E σ B n X r s hB (.inl hX) K hK)
    h.weil.2.1.toIsSplitting hd (fun N n1 n2 => (sInf_le (a := N) ⟨fun f ⟨ε, hε⟩ => n1 ε f fun u u' hu hu' e => ?_,
      fun u hu f hf f₁ e => ?_⟩ : M.Pol B.ψ B.emb ≤ N)) s1 s2 p1 p2) h1 h2)
  · rw [← u.transpose_transpose, ← u'.transpose_transpose, ht, ht]
    refine hε uᵀ u'ᵀ (tr hu) (tr hu') (fun w => ?_) _ _ (actsD_dop M hB.std (tr hu) f) (actsD_dop M hB.std (tr hu') f)
    rw [Matrix.transpose_map, Matrix.transpose_map, e w, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.mul_assoc]
  · rw [actsD_unique' M hB.std hu e]
    have := n2 uᵀ (tr hu) f hf
    rwa [ht] at this

end GlobalTheory.ThK.Dbl.Box

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.PresDOf
section
noncomputable section

namespace GlobalTheory.ThK.Dbl.Vf2

open scoped Matrix TensorProduct GlobalTheory.VacAny
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.LatVac
open PositivityTheory.ThK PositivityTheory.ThK.Vac PositivityTheory.ThKH.Iwas PositivityTheory.ThKH.Locrep PositivityTheory.ThKG.Loc.Cone.Vf

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {v : Pl F}

theorem presD_of {X : Spc F E n} {g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)}
    (h : ∀ z z', z ∈ latHat X → z' ∈ latHat X →
      (g *ᵥ Sum.elim z z') ∘ Sum.inl ∈ latHat X ∧ (g *ᵥ Sum.elim z z') ∘ Sum.inr ∈ latHat X) : PresD v X g := by
  rw [← Matrix.fromBlocks_toBlocks g] at h ⊢
  simp only [Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr] at h
  exact ⟨_, pres_of_hat fun z hz => by simpa using (h z 0 hz (zero_mem _)).1, _,
    pres_of_hat fun z hz => by simpa using (h 0 z (zero_mem _) hz).1, _,
    pres_of_hat fun z hz => by simpa using (h z 0 hz (zero_mem _)).2, _,
    pres_of_hat fun z hz => by simpa using (h 0 z (zero_mem _) hz).2, rfl⟩

theorem _root_.GlobalTheory.ThK.Dbl.vacFix2 : VacFix2 := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB hX hW hM χ _ dd omd ⟨d', hd', hdd⟩ ⟨_, hsp, hrule⟩ K hK v hv g hk hg
  have hL := hX.lat
  have vd := hM.vac v
  obtain ⟨hsb, h0, -⟩ := hM.vac v
  obtain ⟨r₀, x₀, h₀, h₁⟩ := exists_base (Fin n × Fin d) v
  set Φ := tens (evFin F v) (M.vac v) r₀ with hΦ
  have hΦs : Φ ∈ schA F _ := (h₀ _ hsb).2
  obtain ⟨y₀, hy⟩ := Function.ne_iff.1 h0
  have hΦy : Φ (putA v x₀ y₀) = M.vac v y₀ := by
    change M.vac v (evA _ v (putA v x₀ y₀)) * r₀ (putA v x₀ y₀) = _
    rw [ev_put (evA_inA v), inv_putA v (h₀ _ hsb).1, h₁, mul_one]
  have hΦ0 : Φ ≠ 0 := fun e => hy (by rw [← hΦy, e]; rfl)
  have q1 : PresD v X g.1.1 := presD_of fun z z' a b => ((hK g).1 hk).2 z z' a b g (.inl rfl)
  have q2 : PresD v X (g⁻¹).1.1 := presD_of fun z z' a b => ((hK g).1 hk).2 z z' a b g⁻¹ (.inr rfl)
  obtain ⟨c, hc⟩ := dbl_eigen hB hX hW vd hd' hdd hsp.toIsSplitting g hg q2
  suffices h : c = 1 by rwa [h, one_smul] at hc
  obtain ⟨g₁, m₁, g₂, m₂, g₃, m₃, g₄, m₄, eg⟩ := q1
  obtain ⟨a₁, n₁, a₂, n₂, a₃, -, a₄, -, ea⟩ := q2
  have hD : g.1.1 * (diagCols (Fin n) : Matrix _ _ (AE F E)) = Matrix.fromRows (g₁ + g₂) (g₃ + g₄) := by
    rw [eg, diagCols, Matrix.fromBlocks_mul_fromRows]; simp
  have hI : a₁ * (g₁ + g₂) + a₂ * (g₃ + g₄) = 1 := by
    have : (g⁻¹).1.1 * (g.1.1 * (diagCols (Fin n) : Matrix _ _ (AE F E))) = diagCols (Fin n) := by
      rw [← Matrix.mul_assoc, show (g⁻¹).1.1 * g.1.1 = 1 from g.1.inv_mul, Matrix.one_mul]
    rw [hD, ea, Matrix.fromBlocks_mul_fromRows, diagCols] at this
    exact (Matrix.fromRows_inj this).1
  have aD := at_mul_left (M := g.1.1 - 1) hg (diagCols (Fin n) : Matrix _ _ (AE F E))
  rw [Matrix.sub_mul, Matrix.one_mul, hD] at aD
  have ax : At (evFin F v) (g₁ + g₂ - 1) := fun u hu => congrArg Matrix.toRows₁ (aD u hu)
  have ay : At (evFin F v) (g₃ + g₄ - 1) := fun u hu => congrArg Matrix.toRows₂ (aD u hu)
  have px := add_mem m₁ m₂
  have py := add_mem m₃ m₄
  generalize g₁ + g₂ = x at *
  generalize g₃ + g₄ = y at *
  obtain ⟨b, b', t', b1, hb, pb, pt, ht⟩ := exists_beta hB hX g hD px py n₁ n₂ hI ax ay
  have hm : At (evFin F v) (y - x) := by simpa using at_sub ay ax
  have pm := sub_mem py px
  obtain ⟨s₀, n₀, p, t, ss, eg', es, en, en', hn, hp, et, et'⟩ :=
    Vf2.exists_decomp b1 hb g hD ht (ε := PositivityTheory.ThKG.Loc.Cone.Vf.eps v) eps_mul ((cA σ).commutes _) (eps_smul hm)
  have o1 := one_mem (Pres v X)
  have z0 := zero_mem (Pres v X)
  have pC : PresD v X (CC b) := ⟨_, o1, _, add_mem o1 pb, _, o1, _, pb, rfl⟩
  have pCi : PresD v X (Ci b) := ⟨_, neg_mem pb, _, add_mem o1 pb, _, o1, _, neg_mem o1, rfl⟩
  have c1 : compFin F E v (PositivityTheory.ThKG.Loc.Cone.Vf.eps v : AE F E) = 1 := by rw [PositivityTheory.ThKG.Loc.Cone.Vf.eps, comp_alg, ev_sg]; rfl
  have pe : (PositivityTheory.ThKG.Loc.Cone.Vf.eps v : AE F E) • (1 : Matrix _ _ _) ∈ Pres v X := smul_mem_Pres hL (by rw [c1]; exact one_mem _) o1
  have pe' : (1 - PositivityTheory.ThKG.Loc.Cone.Vf.eps v : AE F E) • (1 : Matrix _ _ _) ∈ Pres v X :=
    smul_mem_Pres hL (by rw [map_sub, map_one, c1, sub_self]; exact zero_mem _) o1
  have bt : boxFun Φ (star Φ) = tens (evFin F v) (boxFun (M.vac v) (star (M.vac v))) (boxFun r₀ (star r₀)) := by
    funext x
    simp only [hΦ, boxFun, tens, Pi.star_apply, star_mul']
    exact mul_mul_mul_comm _ _ _ _
  have hΦd := GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Φ hΦs _ (star_mem_schA hΦs)
  have hd0 : boxFun Φ (star Φ) ≠ 0 := fun e => lDiag_ne hΦs hΦ0 (by rw [e, map_zero])
  have rd : Rest (evFin F v) (boxFun (M.vac v) (star (M.vac v))) (boxFun r₀ (star r₀)) := by
    refine ⟨fun x z hz => ?_, bt ▸ hΦd⟩
    have i1 := (h₀ _ hsb).1 (x ∘ Sum.inl) (z ∘ Sum.inl) fun u hu => funext fun i => congrFun (hz u hu) _
    have i2 := (h₀ _ hsb).1 (x ∘ Sum.inr) (z ∘ Sum.inr) fun u hu => funext fun i => congrFun (hz u hu) _
    change r₀ (x ∘ Sum.inl + z ∘ Sum.inl) * star (r₀ (x ∘ Sum.inr + z ∘ Sum.inr)) = _
    rw [i1, i2]; rfl
  have ev : ∀ g : UG (cA σ) (dbl (incM F X.J)), At (evFin F v) (g.1.1 - 1) → PresD v X (g⁻¹).1.1 →
      ∃ a : ℂ, omd g (boxFun Φ (star Φ)) = a • boxFun Φ (star Φ) := fun g h1 h2 => by
    obtain ⟨a, ha⟩ := dbl_eigen hB hX hW vd hd' hdd hsp.toIsSplitting g h1 h2
    exact ⟨a, by rw [bt, ha _ rd, tens_smul]⟩
  obtain ⟨a, ha⟩ := ev s₀ (by
      rw [es]
      refine at_conj (CC_Ci b) fun u hu => ?_
      have : u • (PositivityTheory.ThKG.Loc.Cone.Vf.eps v : AE F E) = 0 := at_eps u hu
      rw [SS, ← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add, Matrix.fromBlocks_smul]
      simp only [sub_smul, one_smul, neg_zero, add_zero, ← sub_eq_add_neg, sub_sub_cancel_left, smul_neg, ← smul_assoc, this,
        zero_smul, Matrix.fromBlocks_zero])
    (by rw [inv_eq_of_mul_eq_one_right ss, es]; exact (pC.mul ⟨_, pe', _, pe, _, pe, _, pe', rfl⟩).mul pCi)
  obtain ⟨a', ha'⟩ := ev n₀ (by
      rw [en]
      refine at_conj (CC_Ci b) fun u hu => ?_
      rw [← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add, Matrix.fromBlocks_smul]
      simp only [add_neg_cancel, neg_zero, add_zero, smul_zero, smul_neg]
      rw [at_mul_left hm t' u hu, neg_zero, Matrix.fromBlocks_zero])
    (by rw [en']; exact (pC.mul ⟨_, o1, _, mul_mem pm pt, _, z0, _, o1, rfl⟩).mul pCi)
  have a1 : a' = 1 := by
    rw [rule_diag hdd hrule n₀ 1 hn (by rw [map_one, map_one]) hΦs hΦ0 ha']
    simp
  have aa : a * a = 1 := by
    have e : omd (s₀ * s₀) (boxFun Φ (star Φ)) = (a * a) • boxFun Φ (star Φ) := by
      rw [map_mul, Module.End.mul_apply, ha, map_smul, ha, smul_smul]
    rw [ss, map_one, Module.End.one_apply] at e
    exact smul_left_injective ℂ hd0 (e.symm.trans (one_smul _ _).symm)
  have e1 : omd g (boxFun Φ (star Φ)) = c • boxFun Φ (star Φ) := by rw [bt, hc _ rd, tens_smul]
  have e2 : omd p (boxFun Φ (star Φ)) = c • boxFun Φ (star Φ) := by
    have e3 : omd (s₀ * n₀ * s₀) (boxFun Φ (star Φ)) = boxFun Φ (star Φ) := by
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ha, map_smul, ha', a1, one_smul, map_smul, ha, smul_smul,
        aa, one_smul]
    have : p = (s₀ * n₀ * s₀)⁻¹ * g := by rw [eg']; group
    rw [this, map_mul, Module.End.mul_apply, e1, map_smul]
    conv_lhs => rw [← e3, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have hpos := rule_diag hdd hrule p t hp (chi_det hL χ hv t (by rw [et]; exact add_mem py (mul_mem pb pm)) (by rw [et']; exact pt)
    (by rw [et, add_sub_right_comm]; exact at_add ay (at_mul_right _ hm))) hΦs hΦ0 e2
  have n4 := Bad.norm_eig hsp.unit hsp.pres hΦd hd0 e1
  rw [hpos] at n4 ⊢
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)] at n4
  rw [n4, Complex.ofReal_one]

end GlobalTheory.ThK.Dbl.Vf2

end
end

