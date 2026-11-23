module

public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.SatakeEigenvalues
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.lift_levelP_alt₂

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WeilJacquetShalikaLaw
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.jumpWindows

namespace WeilJacquetShalikaLaw

section Loc

variable {F : Type} [Field F] {a : ℕ}

def WS (χ : AddChar F ℂ) (a : ℕ) : Submodule ℂ (GL (Fin a) F → ℂ) where
  carrier := {W | ∀ n ∈ GroundTheory.Automorphic.Iwasawa.unipotent F a, ∀ g,
    W (n * g) = GroundTheory.Automorphic.Whittaker.psiN χ n * W g}
  add_mem' {W W'} hW hW' n hn g := by
    simp only [Pi.add_apply, hW n hn g, hW' n hn g, mul_add]
  zero_mem' n hn g := by simp
  smul_mem' c W hW n hn g := by
    simp only [Pi.smul_apply, smul_eq_mul, hW n hn g]
    ring

theorem WS_stable (χ : AddChar F ℂ) (a : ℕ) :
    ∀ g, ∀ v ∈ WS χ a, GlobalTheory.PRep.rightReg ℂ (GL (Fin a) F) ℂ g v ∈ WS χ a := by
  intro g v hv n hn x
  change v (n * x * g) = _ * v (x * g)
  rw [mul_assoc]
  exact hv n hn _

def rhoW (χ : AddChar F ℂ) (a : ℕ) : Representation ℂ (GL (Fin a) F) (WS χ a) :=
  GlobalTheory.PRep.sub (GlobalTheory.PRep.rightReg ℂ (GL (Fin a) F) ℂ) (WS χ a) (WS_stable χ a)

@[simp] theorem rhoW_apply (χ : AddChar F ℂ) (g x : GL (Fin a) F) (v : WS χ a) :
    (rhoW χ a g v : GL (Fin a) F → ℂ) x = (v : GL (Fin a) F → ℂ) (x * g) := rfl

def ev (χ : AddChar F ℂ) (a : ℕ) : WS χ a →ₗ[ℂ] ℂ :=
  (LinearMap.proj (R := ℂ) (φ := fun _ : GL (Fin a) F => ℂ) 1).comp (WS χ a).subtype

theorem ev_apply (χ : AddChar F ℂ) (v : WS χ a) : ev χ a v = (v : GL (Fin a) F → ℂ) 1 := rfl

theorem sd_eq (M : Matrix (Fin a) (Fin a) F) :
    GroundTheory.Automorphic.Whittaker.superdiagSum M = ∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, M p.1 p.2 := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  rfl

end Loc

theorem exists_unit_one_add_generator {a : ℕ} (B : Multiset ℂˣ) (hB : B.card = a) : ∃ z : Fin a → ℂˣ, B = Finset.univ.val.map z := by
  subst hB
  refine ⟨fun i => B.toList.get ⟨i, by simp⟩, ?_⟩
  rw [Fin.univ_val_map]
  conv_lhs => rw [← Multiset.coe_toList B]
  congr 1
  refine List.ext_get (by simp) fun n h1 h2 => ?_
  simp

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def psiW (ψ : AddChar (Ad E) ℂ) (w : Pl E) : AddChar (w.adicCompletion E) ℂ :=
  ψ.compAddMonoidHom ((sFin E).toAddMonoidHom.comp (sLoc E w).toAddMonoidHom)

theorem psiOK {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) {w : Pl E} (hc : Cond ψ w) :
    PositivityTheory.JacquetShalikaLocal.PsiOK (psiW ψ w) := by
  obtain ⟨h1, ϖ, y, hϖ, hy, hne⟩ := hc
  refine ⟨fun x hx => h1 x (by rw [← PositivityTheory.JacquetShalikaLocal.SatakeEigenvalues.O_eq w]; exact hx), ⟨y, ?_, hne⟩, fun x => hψ.norm _⟩
  refine (SetLike.ext_iff.1 (PositivityTheory.JacquetShalikaLocal.SatakeEigenvalues.O_eq w) _).2 ?_
  have hu := PositivityTheory.JacquetShalikaLocal.SatakeEigenvalues.isUnifV_uniformizer w
  change Valued.v (_ * y) ≤ 1
  change Valued.v (ϖ * y) ≤ 1 at hy
  rw [map_mul] at hy ⊢
  rw [hu]
  rw [hϖ] at hy
  exact hy

theorem dot_eLast {k : ℕ} (y : UnipotentBlockColumnIndex a k k → Ad E) : dot (eLast a k) y = lastE k y := by
  simp only [dot, eLast, lastE]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> simp

theorem law [_root_.NumberField.IsTotallyComplex E] {ψ : AddChar (Ad E) ℂ} {f : GA E a → ℂ}
    (hf : ∀ k, 0 < k → ∀ (y : UnipotentBlockColumnIndex a k k → Ad E) g, f (blkU y * g) = ψ (lastE k y) * f g)
    (w : Pl E) (n : GL (Fin a) (w.adicCompletion E)) (hn : n ∈ GroundTheory.Automorphic.Iwasawa.unipotent _ a)
    (g : GA E a) : f (fl a w n * g) = GroundTheory.Automorphic.Whittaker.psiN (psiW ψ w) n * f g := by
  obtain ⟨t1, t2, t3⟩ := _root_.GlobalTheory.CuspRep.locTri_adelic E a w n (fun i j hij => hn.1 hij) hn.2
  have := GlobalTheory.T.whittakerLaw_upperTriangularUnipotent_adelic E a ψ f (fun k hk y g => by rw [dot_eLast]; exact hf k hk y g) _ t1 t2 g
  change f (finGL E a (locGL E a w n) * g) = _
  rw [this, t3, GroundTheory.Automorphic.Whittaker.psiN, sd_eq]
  rfl

theorem whitW (w : Pl E) (χ : AddChar (w.adicCompletion E) ℂ) :
    PositivityTheory.JacquetShalikaLocal.Whit (rhoW χ a) χ (ev χ a) := by
  intro g hg u
  rw [ev_apply, ev_apply, rhoW_apply, one_mul]
  have := u.2 g hg 1
  rwa [mul_one] at this

end WeilJacquetShalikaLaw

theorem whittaker_uniqueness_local : PositivityTheory.JacquetShalikaLocal.L7 → PositivityTheory.JacquetShalikaLocal.lift_levelP_alt₂ → G0 → G5 → G9 := by
  intro hL7 hL12 hG0 hG5 E _ _ _ a ψ hψ w hc B φ hφ hsat h hh hWh u
  have hcomm := (hG0 E a).2.2.2.2.2.2.2.1 w h hh
  obtain ⟨hΛ, hrt, hgood, hreg⟩ := hG5 E a ψ hψ
  rcases hsat with rfl | hsat
  · obtain ⟨Λ, hΛ'⟩ := hΛ (h * fl a w u)
    rw [← hΛ' 0 hφ, map_zero]
  obtain ⟨z, hz⟩ := WeilJacquetShalikaLaw.exists_unit_one_add_generator B hsat.2.2.1
  let v : GL (Fin a) (w.adicCompletion E) → ℂ := fun x => Wh ψ φ (h * fl a w x)
  have hfix : ∀ k ∈ KGL w (n := a), Rt E a (fl a w k) φ = φ := fun k hk => GlobalTheory.LGrp.mem_fixed.1 hsat.2.1 k hk
  have hv : v ∈ WeilJacquetShalikaLaw.WS (WeilJacquetShalikaLaw.psiW ψ w) a := by
    intro n hn x
    change Wh ψ φ (h * fl a w (n * x)) = _ * Wh ψ φ (h * fl a w x)
    rw [map_mul, ← mul_assoc, hcomm n, mul_assoc]
    exact WeilJacquetShalikaLaw.law (hreg φ hφ).2.2 w n hn _
  let vs : WeilJacquetShalikaLaw.WS (WeilJacquetShalikaLaw.psiW ψ w) a := ⟨v, hv⟩
  have hv1 : (vs : GL (Fin a) (w.adicCompletion E) → ℂ) 1 = 0 := by
    change Wh ψ φ (h * fl a w 1) = 0
    rw [map_one, mul_one]
    exact hWh
  by_cases h0 : vs = 0
  · exact congrFun (congrArg Subtype.val h0) u
  have hK := Final.GLintComm E w a
  have hsv : IsSatVecGL w (WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a) vs (Finset.univ.val.map z) := by
    refine ⟨h0, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, by simp, fun ϖ hϖ j hj => ?_⟩
    · apply Subtype.ext
      funext x
      change Wh ψ φ (h * fl a w (x * k)) = Wh ψ φ (h * fl a w x)
      rw [map_mul, ← mul_assoc, ← hrt, hfix k hk]
    · rw [← hz]
      apply Subtype.ext
      have e := map_heckeVec (ρ := WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a)
        (ρ' := GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ) hK (Tj_mem_hecke hϖ j) (WeilJacquetShalikaLaw.WS (WeilJacquetShalikaLaw.psiW ψ w) a).subtype (fun _ _ => rfl) vs
      rw [Submodule.subtype_apply, Submodule.subtype_apply] at e
      rw [e, Submodule.coe_smul]
      funext x
      obtain ⟨Λ, hΛ'⟩ := hΛ (h * fl a w x)
      have hfin := finite_heckeVec hK (Tj_mem_hecke hϖ j) (GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ) v
      have hfin2 := finite_heckeVec hK (Tj_mem_hecke hϖ j) (repW a w) φ
      have e1 := (LinearMap.proj (R := ℂ) (φ := fun _ : GL (Fin a) (w.adicCompletion E) => ℂ) x).toAddMonoidHom.map_finsum hfin
      have e2 := (Λ : XB E a →L[ℂ] ℂ).toLinearMap.toAddMonoidHom.map_finsum hfin2
      have e3 := hsat.2.2.2 ϖ hϖ j hj
      have key : ∀ c : GL (Fin a) (w.adicCompletion E) ⧸ KGL w (n := a),
          (Tj ℂ a (Ov E w) ϖ j c.out • GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ c.out v) x =
            Λ (Tj ℂ a (Ov E w) ϖ j c.out • repW a w c.out φ) := by
        intro c
        rw [map_smul, hΛ' (repW a w c.out φ) (hgood φ (fl a w c.out) hφ)]
        change _ * v (x * c.out) = _ • Wh ψ (Rt E a (fl a w c.out) φ) (h * fl a w x)
        rw [hrt, smul_eq_mul]
        change _ * Wh ψ φ (h * fl a w (x * c.out)) = _
        rw [map_mul, mul_assoc]
      have LHS : heckeVec (GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ) (KGL w (n := a))
          (Tj ℂ a (Ov E w) ϖ j) v x = Λ (heckeVec (repW a w) (KGL w (n := a)) (Tj ℂ a (Ov E w) ϖ j) φ) := by
        rw [heckeVec, heckeVec]
        exact e1.trans ((finsum_congr key).trans e2.symm)
      refine LHS.trans ?_
      rw [e3, map_smul, hΛ' φ hφ]
      rfl
  have heig := (hL12 E w).2 a _ (WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a) vs z hsv
  have := hL7 (w.adicCompletion E) (WeilJacquetShalikaLaw.psiW ψ w) (WeilJacquetShalikaLaw.psiOK hψ hc) a _ (WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a) vs z heig
    (WeilJacquetShalikaLaw.ev _ a) (WeilJacquetShalikaLaw.whitW w _) u
  rw [WeilJacquetShalikaLaw.ev_apply, WeilJacquetShalikaLaw.ev_apply, WeilJacquetShalikaLaw.rhoW_apply, one_mul, hv1, zero_mul] at this
  exact this

end PositivityTheory.jumpWindows

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerFunctional
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host
open GlobalTheory.CuspRep.Generic

namespace PositivityTheory.jumpWindows.WhittakerFunctional

section Avg

variable {G : Type} [AddCommGroup G] [TopologicalSpace G]

theorem norm_avg_le (Γ : AddSubgroup G) (Φ : G → ℂ) {C : ℝ} (h0 : 0 ≤ C) (hC : ∀ x, ‖Φ x‖ ≤ C) :
    ‖avg Γ Φ‖ ≤ C := by
  let _ : MeasurableSpace G := borel G
  unfold avg
  split_ifs with h
  · have h1 := h.choose_spec.2.2
    have hs : h.choose.1 h.choose.2 < ⊤ := by rw [h1]; exact ENNReal.one_lt_top
    have := norm_setIntegral_le_of_norm_le_const hs (f := Φ) (fun x _ => hC x)
    simpa [Measure.real, h1] using this
  · simpa using h0

end Avg

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {ψ : AddChar (Ad E) ℂ}

theorem norm_colT_le (hψ : StdPsi ψ) (k : ℕ) {f : GA E a → ℂ} {C : ℝ} (h0 : 0 ≤ C) (hf : ∀ g, ‖f g‖ ≤ C)
    (g : GA E a) : ‖colT ψ k f g‖ ≤ C := by
  refine norm_avg_le _ _ h0 fun x => ?_
  rw [norm_mul, hψ.norm, one_mul]
  exact hf _

theorem norm_whit_le (hψ : StdPsi ψ) (m : ℕ) {f : GA E a → ℂ} {C : ℝ} (h0 : 0 ≤ C) (hf : ∀ g, ‖f g‖ ≤ C)
    (g : GA E a) : ‖whit ψ m f g‖ ≤ C := by
  induction m generalizing f g with
  | zero => exact hf g
  | succ m ih =>
    rw [whit_succ]
    exact ih (fun g => norm_colT_le hψ (m + 1) h0 hf g) g

theorem good_add {m : ℕ} {f f' : GA E a → ℂ} (hf : Good ψ m f) (hf' : Good ψ m f') :
    Good ψ m (fun g => f g + f' g) := by
  refine ⟨hf.cont.add hf'.cont, ?_, ?_, ?_⟩
  · intro γ hγ g
    simp only [hf.left γ hγ g, hf'.left γ hγ g]
  · intro k hk y g
    simp only [hf.law k hk y g, hf'.law k hk y g, mul_add]
  · intro r hr hrm g
    have := _root_.GlobalTheory.CuspGeneric.avg_add_of_per _ (ratV E (UnipotentBlockColumnIndex a r m)) (isCoLat_ratV E _) _ _
      (per_blk hf.cont (fun c g => hf.left _ (isMir_blkU c) g) g)
      (per_blk hf'.cont (fun c g => hf'.left _ (isMir_blkU c) g) g)
    rw [this, hf.van r hr hrm g, hf'.van r hr hrm g, add_zero]

theorem good_smul (c : ℂ) {m : ℕ} {f : GA E a → ℂ} (hf : Good ψ m f) : Good ψ m (fun g => c * f g) := by
  refine ⟨continuous_const.mul hf.cont, ?_, ?_, ?_⟩
  · intro γ hγ g
    simp only [hf.left γ hγ g]
  · intro k hk y g
    simp only [hf.law k hk y g]
    ring
  · intro r hr hrm g
    show avg _ (fun x => c * f (blkU x * g)) = 0
    rw [avg_const_mul, hf.van r hr hrm g, mul_zero]

theorem good_zero (m : ℕ) : Good ψ m (fun _ : GA E a => (0 : ℂ)) := by
  refine ⟨continuous_const, fun _ _ _ => rfl, ?_, ?_⟩
  · intro _ _ _ _
    simp
  · intro r _ _ g
    have := avg_const_mul (ratV E (UnipotentBlockColumnIndex a r m)) 0 (fun _ => 0)
    simpa using this

theorem good_rt {m : ℕ} {f : GA E a → ℂ} (hf : Good ψ m f) (h : GA E a) : Good ψ m (fun x => f (x * h)) := by
  refine ⟨hf.cont.comp (continuous_id.mul continuous_const), ?_, ?_, ?_⟩
  · intro γ hγ g
    simp only [mul_assoc, hf.left γ hγ (g * h)]
  · intro k hk y g
    simp only [mul_assoc, hf.law k hk y (g * h)]
  · intro r hr hrm g
    simp only [mul_assoc]
    exact hf.van r hr hrm (g * h)

theorem dot_eLast (k : ℕ) (y : UnipotentBlockColumnIndex a k k → Ad E) : dot (eLast a k) y = lastE k y := by
  simp only [dot, eLast, lastE]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> simp


variable (E a) in
def Yg (hψ : StdPsi ψ) : Submodule ℂ (XB E a) where
  carrier := {φ | Good ψ (a - 1) φ}
  add_mem' h h' := good_add h h'
  zero_mem' := good_zero (a - 1)
  smul_mem' c _ h := good_smul c h

def whL (hψ : StdPsi ψ) (g : GA E a) : Yg E a hψ →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun φ => whit ψ (a - 1) (φ.1 : GA E a → ℂ) g
      map_add' := fun φ φ' => congrFun (whit_add hψ (a - 1) (by omega) φ.2 φ'.2) g
      map_smul' := fun c φ => congrFun (whit_smul (a - 1) c (φ.1 : GA E a → ℂ)) g } 1
    fun φ => by
      rw [one_mul]
      exact norm_whit_le hψ _ (norm_nonneg _) (fun g => φ.1.norm_coe_le_norm g) g

end PositivityTheory.jumpWindows.WhittakerFunctional

namespace PositivityTheory.jumpWindows

theorem local_group_averaging_tensor : G5 := by
  intro E _ _ _ a ψ hψ
  have h0 : a - 1 < a ∨ a - 1 = 0 := by omega
  refine ⟨fun g => ?_, fun φ g h => ?_, fun φ h hφ => ?_, fun φ hφ => ⟨?_, fun hne => ?_, fun k hk y g => ?_⟩⟩
  · obtain ⟨Λ, hΛ, -⟩ := exists_extension_norm_eq (WhittakerFunctional.Yg E a hψ) (WhittakerFunctional.whL hψ g)
    refine ⟨Λ, fun φ hφ => ?_⟩
    have := hΛ ⟨φ, hφ⟩
    rw [WhittakerFunctional.whL, LinearMap.mkContinuous_apply] at this
    exact this
  · exact whit_rt (a - 1) φ h g
  · exact WhittakerFunctional.good_rt hφ h
  · exact (whit_good hψ (a - 1) h0 hφ).1.cont
  · have hf : (φ : GA E a → ℂ) ≠ 0 := fun h => hne (DFunLike.coe_injective (by simpa using h))
    obtain ⟨g, hg⟩ := Function.ne_iff.1 ((whit_good hψ (a - 1) h0 hφ).2 hf)
    exact ⟨g, hg⟩
  · rw [← WhittakerFunctional.dot_eLast]
    exact (whit_good hψ (a - 1) h0 hφ).1.law k hk y g

end PositivityTheory.jumpWindows

end
end

