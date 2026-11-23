module

public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0024
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0009
public import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
public import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj

@[expose] public section

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open PositivityTheory.ThKEst (GrpTop EpsOf FinVolU)
open PositivityTheory.ThKF (Unimod)
open PositivityTheory.KCo (SoSt)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n n' d : ℕ}

namespace TC

theorem chrW_div {v : Pl F} (χ χ' : Chr F E) (t : E →ₐ[F] Fv F v) (x : (Fv F v)ˣ) : chrW (χ / χ') t x = chrW χ t x / chrW χ' t x :=
  map_div Circle.toUnits _ _

theorem chrW_norm {v : Pl F} (χ : Chr F E) (t : E →ₐ[F] Fv F v) (x : (Fv F v)ˣ) : ‖(chrW χ t x : ℂ)‖ = 1 := Circle.norm_coe _

theorem const_of (hL : LocDist) (hC : ConstOfGood) (hT : ThetaBasic) (h1 : GrpTop) (h2 : EpsOf) (h3 : FinVolU) (h4 : Unimod)
    (hS : SplitModel) {B : Base F E} {X : Spc F E n} {X' : Spc F E n'} {W : Spc F E d} {M : Model σ X W} {M' : Model σ X' W}
    {om : Rep σ X W} {om' : Rep σ X' W} {χ χ' χ₂ : Chr F E} {r s r₁ s₁ r' s' : ℕ} (p : IsPair B M χ (χ / χ') om r s r' s')
    (p' : IsPair B M' χ' χ₂ om' r₁ s₁ r' s') (e : Fin n ⊕ Fin n' ≃ Fin d) (hn : 2 ≤ n) (T : Finset (Pl F))
    (hne : ∀ v ∉ T, SplitsFully E v → ∃ t : E →ₐ[F] Fv F v, chrW (χ / χ') t (unifAt v) ≠ 1)
    (C : Fn F n' d →ₗ[ℂ] (UA σ W.J → ℂ)) (hr : ∀ Φ ∈ PolData B M', IsRapid (C Φ))
    (he : ∀ v (_ : E →ₐ[F] Fv F v), ∀ h ∈ UAt σ W (evFin F v), ∀ Φ ∈ PolData B M', om' (1, h) Φ ∈ PolData B M' ∧ C (om' (1, h) Φ) = fun x => C Φ (x * h))
    {μ : Measure (UA σ W.J)} {D : Set (UA σ W.J)} (hμ : μ.IsHaarMeasure) (hD : IsFundamentalDomain (ratU σ W.J) D μ) :
    ∀ Φ ∈ PolData B M', ∀ Ψ ∈ schA F _, ∀ g, th om μ D (C Φ) Ψ g = th om μ D (C Φ) Ψ 1 := by
  classical
  letI := GlobalTheory.LocalData.complRel (F := F)
  letI := GlobalTheory.LocalData.isLocalField (F := F)
  have inv_loc (hL : LocDist) (e : Fin n ⊕ Fin n' ≃ Fin d) (hM' : M'.IsGood B.ψ) {v : Pl F} {om : Rep σ X W} {om' : Rep σ X' W}
      {ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)}
      {ι' : ((Fin n' × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n') (Fin d) (Fv F v) → ℂ)}
      (b : Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _))
      (b' : Set.BijOn ι' (SB (Fin n' × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n') (Fin d) (Fv F v)) : Set _))
      {ν ν' α α' : (Fv F v)ˣ →* ℂˣ} (n1 : ∀ x, ‖(ν x : ℂ)‖ = 1) (n2 : ∀ x, ‖(α x : ℂ)‖ = 1) (hν : ∀ x, ν x = α x / α' x)
      (hne : ν (unifAt v) ≠ 1) (L : Fn F n' d →ₗ[ℂ] Fn F n d →ₛₗ[starRingEnd ℂ] ℂ)
      (hh : ∀ h₀, ∃ h, PositivityTheory.KCo.Reads v ι (om (1, h)) (GlobalTheory.SplitFlip.omB ν α 1 h₀) ∧ PositivityTheory.KCo.Reads v ι' (om' (1, h)) (GlobalTheory.SplitFlip.omB ν' α' 1 h₀) ∧
        ∀ Φ ∈ PolData B M', ∀ Ψ ∈ schA F _, L (om' (1, h) Φ) (om (1, h) Ψ) = L Φ Ψ)
      {u g₀} (hu : PositivityTheory.KCo.Reads v ι (om (u, 1)) (GlobalTheory.SplitFlip.omB ν α g₀ 1)) : ∀ Φ ∈ PolData B M', ∀ Ψ ∈ schA F _, L Φ (om (u, 1) Ψ) = L Φ Ψ := by
    obtain ⟨j, j1, j2⟩ := exists_inv' b
    obtain ⟨j', j1', j2'⟩ := exists_inv' b'
    intro Φ hΦ Ψ hΨ
    refine LinearMap.eqOn_span' (f := L.flip (om (u, 1) Ψ)) (g := L.flip Ψ) ?_ hΦ
    rintro _ ⟨f', hf', φ', p1', p2', rfl⟩
    refine PositivityTheory.KCo.schA_le (LinearMap.eqLocus (L (pure f' φ') ∘ₛₗ om (u, 1)) (L (pure f' φ'))) (fun f φ p1 p2 => ?_) hΨ
    obtain ⟨T, t1, t2, t3⟩ := intersection_update_fsHerm_neg_one v f p1 p2
    obtain ⟨T', t1', -, t3'⟩ := intersection_update_fsHerm_neg_one v f' p1' ((p2'.and hM'.std).mono fun _ h => h.1.trans h.2)
    have t2' : ∀ ψ ∈ SB _, T' ψ ∈ PolData B M' := fun ψ hψ => Submodule.subset_span ⟨f', hf', _, fun w => by
      by_cases hw : w = v
      · subst hw; rwa [Function.update_self]
      · rw [Function.update_of_ne hw]; exact p1' w, by
        filter_upwards [p2', eventually_cofinite_ne v] with w h hw using (Function.update_of_ne hw _ _).trans h, t1' ψ⟩
    let N : (Fv F v)ˣ →* ℂˣ := MonoidHom.toHomUnits ⟨⟨fun x => GlobalTheory.SplitFlip.apow x ((d : ℂ) / 2), GlobalTheory.SplitFlip.apow_one _⟩, fun x y => GlobalTheory.SplitFlip.apow_mul x y _⟩
    have hN : ∀ x, ((ν * N⁻¹) x : ℂ) = ν x * (GlobalTheory.SplitFlip.apow x ((d : ℂ) / 2))⁻¹ := fun x => by simp [N]
    have cj : ∀ {z : ℂ}, ‖z‖ = 1 → starRingEnd ℂ z = z⁻¹ := fun h => (Complex.inv_eq_conj h).symm
    have cj' : ∀ (x : (Fv F v)ˣ) (m : ℕ), starRingEnd ℂ (GlobalTheory.SplitFlip.apow x ((m : ℂ) / 2)) = GlobalTheory.SplitFlip.apow x ((m : ℂ) / 2) := fun x m => by
      obtain ⟨r, -, h⟩ := apow_real x m
      rw [h, Complex.conj_ofReal]
    let β : SB (Matrix (Fin n) (Fin d) (Fv F v)) →ₗ[ℂ] SB (Matrix (Fin n') (Fin d) (Fv F v)) →ₗ[ℂ] ℂ :=
      LinearMap.mk₂ ℂ (fun a b => L (T' (j' b.1)) (T (j (star a.1)))) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
        (fun _ _ _ => by simp) fun _ _ _ => by simp
    let g₁ := Matrix.GeneralLinearGroup.mkOfDetNeZero g₀.1ᵀ (by rw [Matrix.det_transpose]; exact g₀.det_ne_zero)
    have key := locBil hL v e (ν * N⁻¹) (fun t ht h => hne (Units.ext ?_)) β (fun a b h₀ => ?_)
      ⟨_, sb_star (b.1 (p1 v))⟩ ⟨_, b'.1 (p1' v)⟩ g₁
    · have k2 := t3 _ _ (p1 v) _ (acts_of_reads hu j2 (p1 v)).2
      rw [omB_left, map_smul, map_smul, t1, Function.update_eq_self] at k2
      change L _ (T (j (star fun y => star (ι (φ v) (g₀.1ᵀ * y))))) = _ * L _ (T (j (star (star _)))) at key
      rw [star_star, j2 _ (p1 v), j2' _ (p1' v), t1', t1 (φ v), Function.update_eq_self, Function.update_eq_self, hN,
        show Matrix.GeneralLinearGroup.det g₁ = GlobalTheory.SplitFlip.gdet g₀ from Units.ext (Matrix.det_transpose _), ← Pi.star_def, star_star] at key
      change L _ (om (u, 1) _) = _
      rw [k2, map_smulₛₗ, key, map_mul, cj (n1 _), cj', smul_eq_mul]
      have := GlobalTheory.SplitFlip.apow_ne_zero (GlobalTheory.SplitFlip.gdet g₀) ((d : ℂ) / 2)
      field_simp
    · obtain ⟨r, hr, e1⟩ := apow_real (unifAt v) d
      rw [hN, e1, mul_inv_eq_iff_eq_mul₀ (by exact_mod_cast hr.ne'), ← Complex.ofReal_mul] at h
      have := n1 (unifAt v)
      rw [h, Complex.norm_real, Real.norm_of_nonneg (mul_pos ht hr).le] at this
      rw [h, this]; rfl
    · obtain ⟨h, r1, r2, r3⟩ := hh h₀
      have a1 := j1 _ (sb_star a.2)
      have b1 := j1' _ b.2
      have k1 := t3 _ _ a1.1 _ (acts_of_reads r1 j2 a1.1).2
      have k2 := t3' _ _ b1.1 _ (acts_of_reads r2 j2' b1.1).2
      have k3 := r3 _ (t2' _ b1.1) _ (t2 _ a1.1)
      rw [k1, k2, a1.2, b1.2, omB_right, omB_right] at k3
      simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul, cj (n2 _), cj'] at k3
      have hd : (d : ℂ) / 2 = (n : ℂ) / 2 + (n' : ℂ) / 2 := by
        have := Fintype.card_congr e
        simp only [Fintype.card_sum, Fintype.card_fin] at this
        rw [← this]; push_cast; ring
      change L (T' (j' fun y => b.1 (y * h₀.1))) (T (j fun y => star a.1 (y * h₀.1))) = _ * L (T' (j' b.1)) (T (j (star a.1)))
      rw [← k3, hN, hν, hd, GlobalTheory.SplitFlip.apow_add]
      have := GlobalTheory.SplitFlip.apow_ne_zero (GlobalTheory.SplitFlip.gdet h₀) ((n : ℂ) / 2)
      have := GlobalTheory.SplitFlip.apow_ne_zero (GlobalTheory.SplitFlip.gdet h₀) ((n' : ℂ) / 2)
      simp only [Units.val_div_eq_div_val]
      field_simp
  intro Φ hΦ Ψ hΨ
  have hB := p.base
  have eW := (h2 F E σ B hB d W r' s' (.inr p.skew)).1
  obtain ⟨a1, a2, -, -, -, -, -, a5⟩ := h1 F E σ hB.cm n X.J (h2 F E σ B hB n X r s (.inl p.herm)).1
  obtain ⟨u0, -, u2⟩ := h4 F E σ hB.cm d W.J (-1) (fun i j => by simp [p.skew.skew]) eW.2
  have := u2 μ hμ
  have : FirstCountableTopology (UA σ X.J) := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  have fin := h3 F E σ hB.cm d W.J eW μ D hμ hD
  have hk : ∀ Ψ ∈ schA F (Fin n × Fin d), Ker (theta om Ψ) := (hT F E σ B n d X W M _ _ om _ _ _ _ p).1
  have hp := p.weil.isUSplitting.pres
  refine hC F E σ B n X r s hB p.herm hn T _ ((hk Ψ hΨ).cont a5 (hr Φ hΦ) fin) (fun γ hγ g => ?_) fun v hv hs u hu g => ?_
  · have : theta om Ψ (γ * g) = theta om Ψ g := funext fun h => by
      rw [← (hk Ψ hΨ).2.1 γ hγ 1 (one_mem _) g h, one_mul]
    rw [th, th, this]
  obtain ⟨t, ht⟩ := hne v hv hs
  obtain ⟨s1, ι, b, l1, r1⟩ := hS F E σ B n d X W M _ _ om _ _ _ _ p v t
  obtain ⟨-, ι', b', -, r2⟩ := hS F E σ B n' d X' W M' _ _ om' _ _ _ _ p' v t
  obtain ⟨L, hl⟩ := exists_form hp hk fin (PolData B M') C hr g
  obtain ⟨g₀, hg⟩ := l1 u hu
  have key := inv_loc hL e p'.good b b' (chrW_norm _ t) (chrW_norm _ t) (chrW_div χ χ' t) ht L (fun h₀ => by
    obtain ⟨h, hh, e0⟩ := s1 h₀
    refine ⟨h, r1 h hh h₀ e0, r2 h hh h₀ e0, fun Φ hΦ Ψ hΨ => ?_⟩
    rw [hl _ (he v t h hh Φ hΦ).1 _ (hp _ _ hΨ), hl _ hΦ _ hΨ, (he v t h hh Φ hΦ).2, th_right hD (hk Ψ hΨ) (hr Φ hΦ)]) hg Φ hΦ Ψ hΨ
  rw [hl _ hΦ _ (hp _ _ hΨ), hl _ hΦ _ hΨ] at key
  rw [← key, th, th]
  congr 1
  funext x
  rw [theta_act, mul_one]

variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
  {R : RealMaps F a a'} {Rf : FinMaps F a a'}

theorem pol_mem {Φ Φ'} (h : PolMatch B G X R Rf Φ Φ') : Φ ∈ PolData B G.M ∧ Φ' ∈ PolData B G.M' := by
  obtain ⟨T, -, m, m', f, φ, f', φ', h1, h2, rfl, rfl, -⟩ := h
  exact ⟨Submodule.sum_mem _ fun i _ => Submodule.subset_span
      ⟨f i, (h1 i).1, φ i, (h1 i).2.1, T.eventually_cofinite_notMem.mono (h1 i).2.2, rfl⟩,
    Submodule.sum_mem _ fun i _ => Submodule.subset_span
      ⟨f' i, (h2 i).1, φ' i, (h2 i).2.1, T.eventually_cofinite_notMem.mono (h2 i).2.2, rfl⟩⟩

theorem pol_le {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} (hM : M.IsGood B.ψ) : PolData B M ≤ schA F _ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, -, φ, h1, h2, rfl⟩
  exact PositivityTheory.KCo.pure_mem_schA f φ h1 ((h2.and hM.std).mono fun _ h => h.1.trans h.2)

theorem I_add {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {o : Rep σ Y W}
    (hp : ∀ x, ∀ Ψ ∈ schA F (Fin n × Fin d), o x Ψ ∈ schA F _) {Φ Ψ : Fn F n d} (hΦ : Φ ∈ schA F _) (hΨ : Ψ ∈ schA F _)
    (c1 : M.Conv o Φ) (c2 : M.Conv o Ψ) : M.I o (Φ + Ψ) = M.I o Φ + M.I o Ψ := funext fun h => by
  simp only [Model.I, theta_add hp hΦ hΨ]
  exact integral_add (c1 h) (c2 h)

theorem I_smul {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) (o : Rep σ Y W) (c : ℂ) (Φ : Fn F n d) :
    M.I o (c • Φ) = c • M.I o Φ := funext fun h => by
  simp only [Model.I, theta_smul, integral_const_mul, Pi.smul_apply, smul_eq_mul]

theorem I_zero {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) (o : Rep σ Y W) : M.I o 0 = 0 := by
  simpa using I_smul M o 0 0

def matched (hm : IsMatched B G X om om' R Rf) : Submodule ℂ (Fn F a (a + a') × Fn F a' (a + a')) where
  carrier := {y | PolMatch B G X R Rf y.1 y.2}
  zero_mem' := pm_zero
  add_mem' h h' := by simpa using pm_add hm 1 h h'
  smul_mem' c _ h := by simpa using pm_add hm c h pm_zero

theorem exists_maps (hD : KDecay) (hF : Factor) (hm : IsMatched B G X om om' R Rf) (s t : ℂ) :
    ∃ (C : Fn F a (a + a') →ₗ[ℂ] (UA σ G.W.J → ℂ)) (C' : Fn F a' (a + a') →ₗ[ℂ] (UA σ G.W.J → ℂ)),
      (∀ y ∈ pairs B G X R Rf, C y.1 = comb G om om' s t y) ∧ ∀ Φ Φ', PolMatch B G X R Rf Φ Φ' → C' Φ' = C Φ := by
  obtain ⟨d1, d2⟩ := hD F E σ B a a' G X om om' hm.triple
  obtain ⟨f1, f2⟩ := hF F E σ B a a' G X om om' R Rf hm
  let P := (G.M'.So B.ψ B.τ₁).comap (LinearMap.snd ℂ _ _) ⊓ matched hm
  have m1 : ∀ y : P, y.1.1 ∈ schA F _ := fun y => pol_le hm.triple.geo.hM (pol_mem y.2.2).1
  have m2 : ∀ y : P, y.1.2 ∈ schA F _ := fun y => pol_le hm.triple.geo.hM' (pol_mem y.2.2).2
  let c : P →ₗ[ℂ] (UA σ G.W.J → ℂ) :=
    { toFun := fun y => comb G om om' s t y.1
      map_add' := fun y z => by
        simp only [comb, Submodule.coe_add, Prod.fst_add, Prod.snd_add]
        rw [I_add hm.triple.weil.isUSplitting.pres (m1 y) (m1 z) (d1 _ (m1 y)) (d1 _ (m1 z)),
          I_add hm.triple.weil'.isUSplitting.pres (m2 y) (m2 z) (d2 _ y.2.1).2.1 (d2 _ z.2.1).2.1]
        module
      map_smul' := fun x y => by
        simp only [comb, Submodule.coe_smul, Prod.smul_fst, Prod.smul_snd, I_smul, RingHom.id_apply]
        module }
  obtain ⟨C, hC⟩ := exists_fac (LinearMap.fst ℂ _ _ ∘ₗ P.subtype) c fun y h => by
    have h0 : y.1.1 = 0 := h
    have h1 : PolMatch B G X R Rf y.1.1 y.1.2 := y.2.2
    change comb G om om' s t y.1 = 0
    rw [comb, f2 y.1.2 y.2.1 (h0 ▸ h1), h0, I_zero, smul_zero, smul_zero, add_zero]
  have k : ∀ y ∈ pairs B G X R Rf, C y.1 = comb G om om' s t y := fun y hy => hC ⟨y, hy⟩
  obtain ⟨C', hC'⟩ := exists_fac (LinearMap.snd ℂ _ _ ∘ₗ (matched hm).subtype) (C ∘ₗ LinearMap.fst ℂ _ _ ∘ₗ (matched hm).subtype)
    fun y h => by
      have h0 : y.1.2 = 0 := h
      have h1 : PolMatch B G X R Rf y.1.1 y.1.2 := y.2
      change C y.1.1 = 0
      rw [k y.1 ⟨h0 ▸ zero_mem _, h1⟩, comb, f1 _ (h0 ▸ h1), h0, I_zero, smul_zero, smul_zero, add_zero]
  exact ⟨C, C', k, fun Φ Φ' h => hC' ⟨(Φ, Φ'), h⟩⟩

end TC

open TC in
theorem thConst_of (hL : LocDist) (hG : GoodNe) (hC : ConstOfGood) (hF : Factor) (hM : MatchEx) (hT : ThetaBasic) (hD : KDecay)
    (h1 : GrpTop) (h2 : EpsOf) (h3 : FinVolU) (h4 : Unimod) (hS : SplitModel) (hO : SoSt) : ThConst := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf hm s t hr μ D hμ hD' y hy
  obtain ⟨C, C', c1, c2⟩ := exists_maps hD hF hm s t
  obtain ⟨m1, m2, -⟩ := hM F E σ B a a' G X om om' R Rf hm
  have hg := hG F E σ B a a' G X om om' hm.triple
  have r1 : ∀ Φ ∈ PolData B G.M, IsRapid (C Φ) := fun Φ hΦ => by
    obtain ⟨Φ', h, h'⟩ := m1 Φ hΦ
    exact c1 (Φ, Φ') ⟨h, h'⟩ ▸ hr (Φ, Φ') ⟨h, h'⟩
  have e1 : ∀ v (_ : E →ₐ[F] Fv F v), ∀ h ∈ UAt σ G.W (evFin F v), ∀ Φ ∈ PolData B G.M,
      om (1, h) Φ ∈ PolData B G.M ∧ C (om (1, h) Φ) = fun x => C Φ (x * h) := fun v w h hh Φ hΦ => by
    obtain ⟨Φ', k, k'⟩ := m1 Φ hΦ
    have k2 := pm_fin hS hm w hh k'
    refine ⟨(pol_mem k2).1, ?_⟩
    rw [c1 (_, _) ⟨hO F E σ B a a' G X om om' hm.triple _ _ k, k2⟩, c1 (Φ, Φ') ⟨k, k'⟩]
    funext x
    simp only [comb, Model.I, Pi.add_apply, Pi.smul_apply, theta_act, mul_one]
  have l1 := hm.triple.geo.lt
  have l2 := hm.triple.geo.aBig
  rw [← c1 y hy]
  refine ⟨c2 _ _ hy.2 ▸ const_of hL hC hT h1 h2 h3 h4 hS (pairV hm.triple) (pairV' hm.triple) finSumFinEquiv (by omega) X.T
    (fun v hv hs => ?_) C' (fun Φ' h => ?_) (fun v w h hh Φ' hΦ => ?_) hμ hD' _ (pol_mem hy.2).2,
    const_of hL hC hT h1 h2 h3 h4 hS (pairV' hm.triple) (pairV hm.triple) ((Equiv.sumComm _ _).trans finSumFinEquiv) (by omega) X.T
    (fun v hv hs => ?_) C r1 e1 hμ hD' _ (pol_mem hy.2).1⟩
  · obtain ⟨⟨t⟩, h⟩ := hg v ⟨hv, hs⟩
    refine ⟨t, fun h' => h t ?_⟩
    rw [chrW_div, div_eq_one] at h'
    rw [Chars.ν, chrW_div, h', div_self']
  · obtain ⟨Φ, k⟩ := m2 Φ' h
    exact c2 _ _ k ▸ r1 Φ (pol_mem k).1
  · obtain ⟨Φ, k⟩ := m2 Φ' hΦ
    have k2 := pm_fin hS hm w hh k
    exact ⟨(pol_mem k2).2, by rw [c2 _ _ k2, c2 _ _ k, (e1 v w h hh Φ (pol_mem k).1).2]⟩
  · obtain ⟨⟨t⟩, h⟩ := hg v ⟨hv, hs⟩
    exact ⟨t, h t⟩

end GlobalTheory.ThK.Dbl

end
