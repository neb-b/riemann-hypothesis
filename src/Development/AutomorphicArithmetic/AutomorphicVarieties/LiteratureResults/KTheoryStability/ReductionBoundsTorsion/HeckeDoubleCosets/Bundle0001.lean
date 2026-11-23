module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeckeDoubleCosets.PHeckeFormal

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeckeDoubleCosets.EvFinsetSum
section
noncomputable section

open UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.AffineStabilizerVanishing

open PositivityTheory.KB

theorem ev_finset_sum {G H Y : Type} [Group G] [Group H] [MulAction H Y] (ρ : G →* H) {m : ℕ}
    (F : (Fin (m + 1) → Y) → ℝ) (y : Y) {ι : Type} (s : Finset ι) (z : ι → Chn G m) :
    ev ρ F y (∑ i ∈ s, z i) = ∑ i ∈ s, ev ρ F y (z i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ev_eq, map_sum]

theorem inv_dC {G H Y : Type} [Group G] [Group H] [MulAction H Y] (ρ : G →* H) {m : ℕ}
    (E : (Fin (m + 1) → Y) → ℝ) (hE : Inv ρ E) : Inv ρ (dC E) := by
  intro g y
  simp only [dC]
  exact Finset.sum_congr rfl fun i _ => by rw [hE g (fun j => y (i.succAbove j))]

theorem pEvDC : PEvDC := by
  intro G H Y _ _ _ ρ m E hE y z
  refine Finsupp.induction_linear z ?_ ?_ ?_
  · simp [ev_zero]
  · intro a b ha hb
    rw [ev_add, map_add (f := _), ev_add, ha, hb]
  · intro g a
    have hbd : bd G m (Finsupp.single g a) = a • bd G m (Finsupp.single g 1) := by
      rw [← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hbd, ev_smul, ev_single]
    congr 1
    simp only [bd, Finsupp.linearCombination_single, one_smul]
    rw [ev_add, ev_single, one_mul, ev_finset_sum]
    simp only [ev_smul, ev_single, one_mul]
    simp only [dC]
    rw [Fin.sum_univ_succ]
    congr 1
    · simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
      have : (fun j : Fin (m + 1) => ρ (Fin.partialProd g j.succ) • y) =
          fun j => ρ (g 0) • (ρ (Fin.partialProd (fun i : Fin m => g i.succ) j) • y) := by
        funext j
        rw [Fin.partialProd_succ', map_mul, mul_smul]
        rfl
      rw [this, hE (g 0)]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [Fin.partialProd_contractNth]
      simp [Fin.val_succ]

theorem pCob : PCob := by
  intro G _ m F hF hz
  let φ : Chn G (m + 1) →ₗ[ℝ] ℝ :=
    Finsupp.linearCombination ℝ (fun g : Fin (m + 1) → G => F fun j => Fin.partialProd g j)
  have hφ : ∀ z, φ z = ev (MonoidHom.id G) F 1 z := fun z => by
    rw [ev_eq]; simp [φ]
  have hker : LinearMap.ker (bd G m) ≤ LinearMap.ker φ := fun z hz' => by
    rw [LinearMap.mem_ker] at hz' ⊢; rw [hφ]; exact hz z hz'
  let ψ₀ : LinearMap.range (bd G m) →ₗ[ℝ] ℝ :=
    (LinearMap.ker (bd G m)).liftQ φ hker ∘ₗ (bd G m).quotKerEquivRange.symm.toLinearMap
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend ψ₀
  have hψbd : ∀ z, ψ (bd G m z) = φ z := fun z => by
    have h1 := LinearMap.congr_fun hψ ⟨bd G m z, LinearMap.mem_range_self _ z⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at h1
    rw [h1]
    simp [ψ₀, LinearMap.quotKerEquivRange_symm_apply_image]
  let E : (Fin (m + 1) → G) → ℝ := fun y =>
    ψ (Finsupp.single (fun j : Fin m => (y j.castSucc)⁻¹ * y j.succ) 1)
  have hEinv : Inv (MonoidHom.id G) E := by
    intro g y
    simp only [E, MonoidHom.id_apply, smul_eq_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  have hevE : ∀ w : Chn G m, ev (MonoidHom.id G) E 1 w = ψ w := by
    intro w
    refine Finsupp.induction_linear w ?_ ?_ ?_
    · simp [ev_zero]
    · intro a b ha hb; rw [ev_add, ha, hb, map_add (f := _)]
    · intro g a
      rw [ev_single]
      simp only [E, MonoidHom.id_apply, smul_eq_mul, mul_one, Fin.partialProd_right_inv]
      rw [← smul_eq_mul, ← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
  refine ⟨E, hEinv, ?_⟩
  funext y
  set g' : Fin (m + 1) → G := fun i => (y i.castSucc)⁻¹ * y i.succ
  have hy : y = fun j => y 0 * Fin.partialProd g' j := by
    have := Fin.partialProd_left_inv y
    funext j
    exact (congrFun this j).symm
  have h1 : dC E y = dC E (fun j => Fin.partialProd g' j) := by
    conv_lhs => rw [hy]
    exact inv_dC (MonoidHom.id G) E hEinv (y 0) _
  have h2 : F y = F (fun j => Fin.partialProd g' j) := by
    conv_lhs => rw [hy]
    exact hF (y 0) _
  rw [h1, h2]
  have h3 := pEvDC G G G (MonoidHom.id G) m E hEinv 1 (Finsupp.single g' 1)
  rw [ev_single, hevE, hψbd, hφ, ev_single] at h3
  simpa using h3

end PositivityTheory.KB.AffineStabilizerVanishing

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeckeDoubleCosets.Formal
section
noncomputable section

open UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.AffineStabilizerVanishing

open PositivityTheory.KB

section

variable {G K : Type} [Group G] [Group K]

theorem mem_Gq {ρ : G →* K} {q : K} {δ : G} : δ ∈ Gq ρ q ↔ ∃ γ, q⁻¹ * ρ γ * q = ρ δ := by
  unfold Gq
  simp [MulAut.conj_apply]

theorem F_rep {m : ℕ} (ρ : G →* K) (q : K) (F : (Fin (m + 1) → K) → ℝ) (hF : Inv ρ F) (a b : G)
    (h : b * a⁻¹ ∈ Gq ρ q) (y : Fin (m + 1) → K) :
    F (fun j => q * ρ b * y j) = F (fun j => q * ρ a * y j) := by
  obtain ⟨γ, hγ⟩ := mem_Gq.mp h
  have hρ : ρ γ = q * ρ b * (ρ a)⁻¹ * q⁻¹ := by
    rw [map_mul, map_inv] at hγ
    calc ρ γ = q * (q⁻¹ * ρ γ * q) * q⁻¹ := by group
      _ = q * ρ b * (ρ a)⁻¹ * q⁻¹ := by rw [hγ]; group
  have key : (fun j => q * ρ b * y j) = fun j => ρ γ • (q * ρ a * y j) := by
    funext j
    rw [smul_eq_mul, hρ]
    group
  rw [key]
  exact hF γ _

theorem rel_out_mul (s : Subgroup G) (c : Quotient (QuotientGroup.rightRel s)) (g : G) :
    (c.out * g) * (Quotient.mk'' (c.out * g) : Quotient (QuotientGroup.rightRel s)).out⁻¹ ∈ s := by
  have hx := Quotient.mk_out (s := QuotientGroup.rightRel s) (c.out * g)
  exact QuotientGroup.rightRel_apply.mp hx

def actQ (s : Subgroup G) (c : Quotient (QuotientGroup.rightRel s)) (g : G) : Quotient (QuotientGroup.rightRel s) :=
  Quotient.mk'' (c.out * g)

theorem actQ_one (s : Subgroup G) (c : Quotient (QuotientGroup.rightRel s)) : actQ s c 1 = c := by
  simp [actQ]

theorem actQ_mul (s : Subgroup G) (c : Quotient (QuotientGroup.rightRel s)) (g h : G) :
    actQ s c (g * h) = actQ s (actQ s c g) h := by
  unfold actQ
  apply Quotient.sound'
  apply QuotientGroup.rightRel_apply.mpr
  convert s.inv_mem (rel_out_mul s c g) using 1
  group

theorem actQ_bij (s : Subgroup G) (g : G) : Function.Bijective fun c => actQ s c g := by
  refine Function.bijective_iff_has_inverse.2 ⟨fun c => actQ s c g⁻¹, fun c => ?_, fun c => ?_⟩
  · show actQ s (actQ s c g) g⁻¹ = c
    rw [← actQ_mul, mul_inv_cancel, actQ_one]
  · show actQ s (actQ s c g⁻¹) g = c
    rw [← actQ_mul, inv_mul_cancel, actQ_one]

theorem hecke_apply {m : ℕ} (ρ : G →* K) (q : K) (F : (Fin (m + 1) → K) → ℝ) (y : Fin (m + 1) → K) :
    hecke ρ (MonoidHom.id K) q F y =
      ((Gq ρ q).index : ℝ)⁻¹ * ∑ᶠ c : Quotient (QuotientGroup.rightRel (Gq ρ q)), F (fun j => q * ρ c.out * y j) :=
  rfl

end

theorem pHeckeFormal : PHeckeFormal := by
  intro G K _ _ ρ q hfin m F F' c hF
  haveI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel (Gq ρ q)))
  refine ⟨?_, ?_, ?_⟩
  · intro g y
    rw [hecke_apply, hecke_apply]
    congr 1
    refine Eq.trans ?_ (finsum_comp_equiv (Equiv.ofBijective _ (actQ_bij (Gq ρ q) g)))
    apply finsum_congr
    intro c'
    simp only [Equiv.ofBijective_apply]
    rw [← F_rep ρ q F hF (actQ (Gq ρ q) c' g).out (c'.out * g) (rel_out_mul _ c' g) y]
    congr 1
    funext j
    rw [smul_eq_mul, map_mul]
    group
  · funext y
    rw [hecke_apply]
    unfold dC
    simp only [hecke_apply, finsum_eq_sum_of_fintype, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun i _ => ?_))
    ring
  · funext y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hecke_apply, finsum_eq_sum_of_fintype,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    ring

theorem bd_cmap {G H : Type} [Group G] [Group H] (f : G →* H) (m : ℕ) (z : Chn G (m + 1)) :
    bd H m (cmap f (m + 1) z) = cmap f m (bd G m z) := by
  have hc : ∀ (j : Fin (m + 1)) (g : Fin (m + 1) → G),
      (fun i => f (Fin.contractNth j (· * ·) g i)) = Fin.contractNth j (· * ·) (fun i => f (g i)) :=
    fun j g => Fin.comp_contractNth _ _ (map_mul f) j g
  have key : (bd H m).comp (cmap f (m + 1)) = (cmap f m).comp (bd G m) := by
    apply Finsupp.lhom_ext
    intro g r
    set_option synthInstance.maxHeartbeats 100000 in
      simp [bd, cmap, Finsupp.mapDomain_single, map_sum, Finsupp.mapDomain_add, Finsupp.mapDomain_smul, hc]
    rw [Finsupp.mapDomain_finsetSum]
    simp only [Finsupp.mapDomain_single, hc]
  exact LinearMap.congr_fun key z

theorem pHeckeKer (hT : PTransfer) (hE : PEvDC) : PHeckeKer := by
  intro hSEv G K _ _ ρ hρ q hfin m F hF hdF hcyc z hz
  haveI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel (Gq ρ q)))
  have heq : ∀ (c : Quotient (QuotientGroup.rightRel (Gq ρ q))) (g : G) (y : Fin (m + 2) → G),
      ((Gq ρ q).index : ℝ)⁻¹ * F (fun j => q * ρ (actQ (Gq ρ q) c g).out * ρ (y j)) =
        ((Gq ρ q).index : ℝ)⁻¹ * F (fun j => q * ρ c.out * ρ (g * y j)) := by
    intro c g y
    have e := F_rep ρ q F hF (actQ (Gq ρ q) c g).out (c.out * g) (rel_out_mul _ c g) (fun j => ρ (y j))
    rw [← e]
    congr 1
    congr 1
    funext j
    rw [map_mul, map_mul]
    group
  have hcoc : ∀ c : Quotient (QuotientGroup.rightRel (Gq ρ q)),
      dC (fun y : Fin (m + 2) → G => ((Gq ρ q).index : ℝ)⁻¹ * F (fun j => q * ρ c.out * ρ (y j))) = 0 := by
    intro c
    funext y
    have h := congrFun hdF (fun j => q * ρ c.out * ρ (y j))
    unfold dC at h ⊢
    simp only [Pi.zero_apply] at h ⊢
    rw [← mul_zero (((Gq ρ q).index : ℝ)⁻¹), ← h, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have hpp : ∀ {S T : Type} [Group S] [Group T] (φ : S →* T) {n : ℕ} (g : Fin n → S) (j : Fin (n + 1)),
      Fin.partialProd (fun i => φ (g i)) j = φ (Fin.partialProd g j) := by
    intro S T _ _ φ n g j
    refine Fin.inductionOn j ?_ ?_
    · simp
    · intro j ih
      rw [Fin.partialProd_succ, Fin.partialProd_succ, ih, map_mul]
  have hstab : ∀ (c : Quotient (QuotientGroup.rightRel (Gq ρ q)))
      (w : Chn (stabR (actQ (Gq ρ q)) (actQ_one _) (actQ_mul _) c) (m + 1)), IsCyc w →
      ev (stabR (actQ (Gq ρ q)) (actQ_one _) (actQ_mul _) c).subtype
        (fun y : Fin (m + 2) → G => ((Gq ρ q).index : ℝ)⁻¹ * F (fun j => q * ρ c.out * ρ (y j))) 1 w = 0 := by
    intro c w hw
    have hmem : ∀ h : stabR (actQ (Gq ρ q)) (actQ_one _) (actQ_mul _) c,
        q * ρ c.out * ρ h * (q * ρ c.out)⁻¹ ∈ ρ.range := by
      intro h
      have h1 : actQ (Gq ρ q) c h = c := h.2
      have h3 : (Quotient.mk'' (c.out * (h : G)) : Quotient (QuotientGroup.rightRel (Gq ρ q))) =
          Quotient.mk'' c.out := by
        rw [Quotient.out_eq']
        exact h1
      have h2 : c.out * (c.out * (h : G))⁻¹ ∈ Gq ρ q := QuotientGroup.rightRel_apply.mp (Quotient.exact' h3)
      obtain ⟨γ, hγ⟩ := mem_Gq.mp h2
      refine ⟨γ⁻¹, ?_⟩
      rw [map_inv]
      rw [map_mul, map_inv, map_mul] at hγ
      calc (ρ γ)⁻¹ = (q * (q⁻¹ * ρ γ * q) * q⁻¹)⁻¹ := by group
        _ = _ := by rw [hγ]; group
    let ψ : (stabR (actQ (Gq ρ q)) (actQ_one _) (actQ_mul _) c) →* K :=
      (MulAut.conj (q * ρ c.out)).toMonoidHom.comp (ρ.comp (stabR (actQ (Gq ρ q)) (actQ_one _) (actQ_mul _) c).subtype)
    have hψ : ∀ h, ψ h ∈ ρ.range := fun h => by
      convert hmem h using 1
      simp only [ψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype]
      done
    let φ := (MonoidHom.ofInjective hρ).symm.toMonoidHom.comp (ψ.codRestrict ρ.range hψ)
    have hφ : ∀ h, ρ (φ h) = q * ρ c.out * ρ h * (q * ρ c.out)⁻¹ := by
      intro h
      rw [← MonoidHom.ofInjective_apply hρ (x := φ h)]
      simp [φ, ψ, MulAut.conj_apply]
      group
    have hz' : IsCyc (cmap φ (m + 1) w) := by
      unfold IsCyc at hw ⊢
      rw [bd_cmap, hw, map_zero]
    have hsev := (hSEv G K K ρ m F hF hdF).2 (q * ρ c.out) 1 _ hz'
    have hcalc : ev (stabR (actQ (Gq ρ q)) (actQ_one _) (actQ_mul _) c).subtype
        (fun y : Fin (m + 2) → G => ((Gq ρ q).index : ℝ)⁻¹ * F (fun j => q * ρ c.out * ρ (y j))) 1 w =
        ((Gq ρ q).index : ℝ)⁻¹ * ev ρ F (q * ρ c.out) (cmap φ (m + 1) w) := by
      unfold ev cmap
      rw [Finsupp.lmapDomain_apply, Finsupp.sum_mapDomain_index (by intro b; simp) (by intro b r1 r2; ring),
        Finsupp.mul_sum]
      apply Finsupp.sum_congr
      intro g _
      simp only [hpp, hφ, smul_eq_mul, Subgroup.coe_subtype, mul_one, inv_mul_cancel_right]
      ring
    rw [hcalc, hsev, hcyc _ hz', mul_zero]
  have hfinal := hT G (Quotient (QuotientGroup.rightRel (Gq ρ q))) (actQ (Gq ρ q)) (actQ_one _) (actQ_mul _) m
    (fun c y => ((Gq ρ q).index : ℝ)⁻¹ * F (fun j => q * ρ c.out * ρ (y j))) heq hcoc hstab z hz
  refine Eq.trans ?_ hfinal
  unfold ev
  apply Finsupp.sum_congr
  intro g _
  congr 1
  simp only [hecke_apply, finsum_eq_sum_of_fintype, Finset.mul_sum, smul_eq_mul, mul_one, MonoidHom.id_apply]

end PositivityTheory.KB.AffineStabilizerVanishing

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeckeDoubleCosets.Transfer
section
noncomputable section

open UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.AffineStabilizerVanishing

open PositivityTheory.KB

theorem dC_translate {Γ : Type} [Group Γ] {m : ℕ} (F : (Fin (m + 1) → Γ) → ℝ) (g : Γ) (y : Fin (m + 2) → Γ) :
    dC (fun y : Fin (m + 1) → Γ => F fun j => g * y j) y = dC F (fun j => g * y j) := rfl

theorem pTransfer (hC : PCobSub) (hE : PEvDC) : PTransfer := by
  intro Γ X _ _ act h1 hm m Φ hΦ hd hcyc z hz
  classical
  haveI : Fintype X := Fintype.ofFinite X
  have hinv : ∀ x, Inv (stabR act h1 hm x).subtype (Φ x) := by
    intro x g y
    have hg : act x (g : Γ) = x := g.2
    show (Φ x fun j => (g : Γ) * y j) = Φ x y
    rw [← hΦ x g y, hg]
  have hex : ∀ x, ∃ Ψ : (Fin (m + 1) → Γ) → ℝ, Inv (stabR act h1 hm x).subtype Ψ ∧ dC Ψ = Φ x :=
    fun x => hC Γ (stabR act h1 hm x) m (Φ x) (hinv x) (hd x) (hcyc x)
  choose Ψ hΨi hΨd using hex
  obtain ⟨rep, hrep1, hrep2⟩ : ∃ rep : X → X, (∀ x h, rep (act x h) = rep x) ∧
      ∀ x, ∃ g, act (rep x) g = x := by
    letI S : Setoid X := ⟨fun a b => ∃ g, act a g = b, ⟨fun a => ⟨1, h1 a⟩,
      fun ⟨g, hg⟩ => ⟨g⁻¹, by rw [← hg, ← hm, mul_inv_cancel, h1]⟩,
      fun ⟨g, hg⟩ ⟨k, hk⟩ => ⟨g * k, by rw [hm, hg, hk]⟩⟩⟩
    refine ⟨fun x => (Quotient.mk S x).out, fun x h => ?_, fun x => ?_⟩
    · exact congrArg Quotient.out (@Quotient.sound _ S _ _ ⟨h⁻¹, by rw [← hm, mul_inv_cancel, h1]⟩)
    · exact @Quotient.mk_out _ S x
  obtain ⟨gs, hgs⟩ : ∃ gs : X → Γ, ∀ x, act (rep x) (gs x) = x :=
    ⟨fun x => (hrep2 x).choose, fun x => (hrep2 x).choose_spec⟩
  have hshift : ∀ x h (y : Fin (m + 1) → Γ),
      Ψ (rep x) (fun j => gs x * (h * y j)) = Ψ (rep (act x h)) (fun j => gs (act x h) * y j) := by
    intro x h y
    have e2 := hgs (act x h)
    rw [hrep1] at e2 ⊢
    have hk : act (rep x) (gs x * h * (gs (act x h))⁻¹) = rep x := by
      have t : act (act (rep x) (gs (act x h))) (gs (act x h))⁻¹ = rep x := by
        rw [← hm, mul_inv_cancel, h1]
      rw [e2] at t
      rw [hm, hm, hgs x, t]
    have := hΨi (rep x) ⟨gs x * h * (gs (act x h))⁻¹, hk⟩ (fun j => gs (act x h) * y j)
    rw [← this]
    congr 1
    funext j
    show gs x * (h * y j) = (gs x * h * (gs (act x h))⁻¹) * (gs (act x h) * y j)
    group
  have hEinv : Inv (MonoidHom.id Γ) (fun y : Fin (m + 1) → Γ => ∑ x, Ψ (rep x) fun j => gs x * y j) := by
    intro g y
    show ∑ x, Ψ (rep x) (fun j => gs x * (g * y j)) = ∑ x, Ψ (rep x) fun j => gs x * y j
    rw [Finset.sum_congr rfl (fun x _ => hshift x g y)]
    exact Fintype.sum_equiv ⟨fun x => act x g, fun x => act x g⁻¹,
      fun x => by simp only; rw [← hm, mul_inv_cancel, h1],
      fun x => by simp only; rw [← hm, inv_mul_cancel, h1]⟩ _ _
      (fun x => rfl)
  have hdE : dC (fun y : Fin (m + 1) → Γ => ∑ x, Ψ (rep x) fun j => gs x * y j)
      = fun y => ∑ x, Φ x y := by
    funext y
    have hx : ∀ x, Φ x y = dC (fun y' : Fin (m + 1) → Γ => Ψ (rep x) fun j => gs x * y' j) y := by
      intro x
      rw [dC_translate (Ψ (rep x)) (gs x) y, hΨd (rep x), ← hΦ (rep x) (gs x) y, hgs x]
    simp only [hx, dC, Finset.mul_sum]
    exact Finset.sum_comm
  have key := hE Γ Γ Γ (MonoidHom.id Γ) m
    (fun y : Fin (m + 1) → Γ => ∑ x, Ψ (rep x) fun j => gs x * y j) hEinv 1 z
  rw [hdE] at key
  have hz' : bd Γ m z = 0 := hz
  rw [hz'] at key
  simp only [finsum_eq_sum_of_fintype]
  rw [key]
  simp [ev]

end PositivityTheory.KB.AffineStabilizerVanishing

end
end

