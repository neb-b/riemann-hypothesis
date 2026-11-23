module

public import ReciprocityTheory.GroupCohomology.Bundle0002
public import ReciprocityTheory.GroupCohomology.Bundle0003
public import ReciprocityTheory.GroupCohomology.Bundle0004
public import ReciprocityTheory.GroupCohomology.PrismOpZeroEval
public import ReciprocityTheory.GroupCohomology.Bundle0007
public import ReciprocityTheory.GroupCohomology.CupCorB
public import ReciprocityTheory.GroupCohomology.InfRes
public import ReciprocityTheory.GroupCohomology.ConnNatHolds
public import ReciprocityTheory.GroupCohomology.Bundle0005
public import ReciprocityTheory.GroupCohomology.Shapiro
public import ReciprocityTheory.GroupCohomology.ShiftA

@[expose] public section

-- bundled from ReciprocityTheory.GroupCohomology.CupCor
section
namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function

universe u


set_option maxHeartbeats 800000 in
theorem cupCor_holds : CupCorStatement.{u} := by
  unfold CupCorStatement
  intro R _ G _ _ _ M N P U _ b bU cup cupU corM corP hU hβ hcup hcupU hcorM hcorP p q x y
  obtain ⟨⟨a, ha⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨⟨c, hc⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have ha' : (M.resSub U).coch.d p a = 0 := LinearMap.mem_ker.mp ha
  have hc' : N.coch.d q c = 0 := LinearMap.mem_ker.mp hc
  obtain ⟨eM, hMh, hM1, -⟩ := homogIso_holds.{u} R U (M.resSub U)
  obtain ⟨eN, hNh, hN1, -⟩ := homogIso_holds.{u} R G N
  obtain ⟨eP, hPh, hP1, -⟩ := homogIso_holds.{u} R G P

  have hAM : (eM p a).1 = CCA.homz (M.resSub U).rho p a.1 := funext fun z => hM1 p a z
  have hAmemU : CCA.homz (M.resSub U).rho p a.1 ∈ hcoch (M.resSub U) U p := by
    rw [← hAM]; exact (eM p a).2
  have hA : (fun z : Fin (p + 1) → G => CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i)))
      ∈ hcoch (M.resSub U) G p :=
    CCA.retr_pull_mem (U := U) (hU := hU) (n := p) (F := CCA.homz (M.resSub U).rho p a.1)
      (hF := hAmemU)
  have hA0 : hd p (fun z : Fin (p + 1) → G =>
      CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i))) = 0 := by
    have h := hMh p a
    rw [ha', map_zero] at h
    funext z
    have h2 := congrFun h (fun i => retr U (z i))
    rw [← hAM]
    exact h2.symm

  have hFcE : (eN q c).1 = CCA.homz N.rho q c.1 := funext fun z => hN1 q c z
  have hFcN : CCA.homz N.rho q c.1 ∈ hcoch N G q := by
    rw [← hFcE]; exact (eN q c).2
  have hFc0 : hd q (CCA.homz N.rho q c.1) = 0 := by
    have h := hNh q c
    rw [hc', map_zero] at h
    rw [← hFcE]
    exact h.symm
  obtain ⟨FcA, hFcA⟩ : ∃ F : (HomogeneousCochainIso.hcx (N.resSub U) G).X q, F.1 = CCA.homz N.rho q c.1 :=
    ⟨⟨CCA.homz N.rho q c.1, CCA.res_mem (U := U) (n := q) (F := CCA.homz N.rho q c.1) (hF := hFcN)⟩,
      rfl⟩

  have hcont : Continuous (fun g : G => ((retr U g : U) : G)) :=
    continuous_subtype_val.comp (CCA.continuous_retr (U := U) hU)
  have hequiv : ∀ (v : U) (g : G), ((retr U (v • g) : U) : G) = v • ((retr U g : U) : G) := by
    intro v g
    show ((retr U ((v : G) * g) : U) : G) = (v : G) * ((retr U g : U) : G)
    rw [CCA.retr_mul, Subgroup.coe_mul]
  have hpr := prism_holds.{u} R U (N.resSub U) G G (HomogeneousCochainIso.hcx (N.resSub U) G)
    (HomogeneousCochainIso.hcx (N.resSub U) G) (fun n => LinearEquiv.refl R _) (fun n => LinearEquiv.refl R _)
    (fun n F => rfl) (fun n F => rfl)
  obtain ⟨φ, hφ⟩ := hpr.1 (fun g => ((retr U g : U) : G)) hcont hequiv
  have huq := hpr.2 (fun g => ((retr U g : U) : G)) id φ (Cx.Hom.id _) hcont continuous_id hequiv
    (fun _ _ => rfl) hφ (fun _ _ _ => rfl) q
  have h0 : (HomogeneousCochainIso.hcx (N.resSub U) G).d q FcA = 0 := by
    apply Subtype.ext
    show hd q FcA.1 = 0
    rw [hFcA]; exact hFc0
  have h1 : (HomogeneousCochainIso.hcx (N.resSub U) G).d q (φ.f q FcA) = 0 := by
    rw [← φ.comm, h0, map_zero]
  have hcls : (HomogeneousCochainIso.hcx (N.resSub U) G).cls q (φ.f q FcA) h1 =
      (HomogeneousCochainIso.hcx (N.resSub U) G).cls q FcA h0 :=
    congrArg (fun t => t ((HomogeneousCochainIso.hcx (N.resSub U) G).cls q FcA h0)) huq
  have hB : φ.f q FcA - FcA ∈ (HomogeneousCochainIso.hcx (N.resSub U) G).B q :=
    (Submodule.Quotient.eq (((HomogeneousCochainIso.hcx (N.resSub U) G).B q).comap
      ((HomogeneousCochainIso.hcx (N.resSub U) G).Z q).subtype)).mp hcls
  have hFr' : (φ.f q FcA).1 = fun z => CCA.homz N.rho q c.1 (fun i => ((retr U (z i) : U) : G)) := by
    funext z
    exact (hφ q FcA z).trans (congrFun hFcA _)

  have hrc : (N.resSub U).coch.d q ((Pair.res N U.subtype continuous_subtype_val).hom.f q c) = 0 := by
    rw [← (Pair.res N U.subtype continuous_subtype_val).hom.comm, hc', map_zero]
  obtain ⟨z1, hz1, hz1e, hz1c⟩ := hcupU p q a _ ha' hrc
  have hca : M.coch.d p (corM.f p a) = 0 := by rw [← corM.comm, ha', map_zero]
  obtain ⟨z2, hz2, hz2e, hz2c⟩ := hcup p q (corM.f p a) c hca hc'
  have hzz : P.coch.d (p + q) (corP.f (p + q) z1) = 0 := by rw [← corP.comm, hz1, map_zero]
  have hmem1 : CCA.hcup b.β p q (fun z : Fin (p + 1) → G =>
      CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i))) (φ.f q FcA).1
      ∈ hcoch (P.resSub U) G (p + q) := by
    have h := CCA.hcup_mem (b := bU) (p := p) (q := q) (hF := hA) (hF' := (φ.f q FcA).2)
    rw [hβ] at h; exact h
  have hmem2 : CCA.hcup b.β p q (fun z : Fin (p + 1) → G =>
      CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i))) (CCA.homz N.rho q c.1)
      ∈ hcoch (P.resSub U) G (p + q) := by
    have h := CCA.hcup_mem (b := bU) (p := p) (q := q) (hF := hA)
      (hF' := CCA.res_mem (U := U) (n := q) (F := CCA.homz N.rho q c.1) (hF := hFcN))
    rw [hβ] at h; exact h

  have hD1 : (eP (p + q) (corP.f (p + q) z1)).1 = CCA.normF P U (p + q) (CCA.hcup b.β p q
      (fun z : Fin (p + 1) → G => CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i)))
      (φ.f q FcA).1) := by
    refine CCA.homog_eq (e := eP) (h1 := hP1) (n := p + q) (f := corP.f (p + q) z1)
      (hF := CCA.normF_mem (M := P) (U := U) (n := p + q) (hF := hmem1)) (hf := fun g => ?_)
    rw [hcorP (p + q) z1, hz1e, hFr']
    exact CCA.cor_cup_eq (b := b) (bU := bU) (hb := hβ) (p := p) (q := q) (f := a.1) (f' := c.1)
      (g := g)
  have hD2 : (eP (p + q) z2).1 = CCA.normF P U (p + q) (CCA.hcup b.β p q
      (fun z : Fin (p + 1) → G => CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i)))
      (CCA.homz N.rho q c.1)) := by
    refine CCA.homog_eq (e := eP) (h1 := hP1) (n := p + q) (f := z2)
      (hF := CCA.normF_mem (M := P) (U := U) (n := p + q) (hF := hmem2)) (hf := fun g => ?_)
    rw [hz2e, hcorM p a]
    exact CCA.cup_cor_eq (U := U) (b := b) (p := p) (q := q) (f := a.1) (f' := c.1) (g := g)

  have key : P.coch.cls (p + q) (corP.f (p + q) z1) hzz = P.coch.cls (p + q) z2 hz2 := by
    apply (Submodule.Quotient.eq (p := _)).mpr
    show corP.f (p + q) z1 - z2 ∈ P.coch.B (p + q)
    cases q with
    | zero =>
      have hz : φ.f 0 FcA = FcA := sub_eq_zero.mp ((Submodule.mem_bot (R := R)).mp hB)
      have hD : corP.f (p + 0) z1 - z2 = 0 := by
        apply (eP (p + 0)).injective
        apply Subtype.ext
        rw [map_sub, map_zero, Submodule.coe_sub, Submodule.coe_zero, hD1, hD2, hz, hFcA, sub_self]
      rw [hD]; exact Submodule.zero_mem _
    | succ q' =>
      obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hB
      have hwv : hd q' w.1 = (φ.f (q' + 1) FcA).1 - FcA.1 := congrArg Subtype.val hw
      rw [hFcA] at hwv
      have hh := CCA.hd_hcup b.β p q' _ w.1 hA0
      have hWmem : ((-1 : ℤ) ^ p • CCA.normF P U (p + q') (CCA.hcup b.β p q'
          (fun z : Fin (p + 1) → G => CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i))) w.1))
          ∈ hcoch P G (p + q') := by
        refine zsmul_mem (CCA.normF_mem (M := P) (U := U) (n := p + q') (hF := ?_)) _
        have h := CCA.hcup_mem (b := bU) (p := p) (q := q') (hF := hA) (hF' := w.2)
        rw [hβ] at h; exact h
      show corP.f (p + (q' + 1)) z1 - z2 ∈ LinearMap.range (P.coch.d (p + q'))
      refine LinearMap.mem_range.mpr ⟨(eP (p + q')).symm ⟨_, hWmem⟩, ?_⟩
      apply (eP (p + (q' + 1))).injective
      apply Subtype.ext
      refine (hPh (p + q') _).trans ?_
      rw [LinearEquiv.apply_symm_apply, map_sub, Submodule.coe_sub, hD1, hD2]
      exact calc hd (p + q') ((-1 : ℤ) ^ p • CCA.normF P U (p + q') (CCA.hcup b.β p q'
            (fun z : Fin (p + 1) → G => CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i))) w.1))
          = (-1 : ℤ) ^ p • hd (p + q') (CCA.normF P U (p + q') (CCA.hcup b.β p q'
            (fun z : Fin (p + 1) → G => CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i))) w.1)) :=
            CCA.hd_zsmul _ _ _
        _ = (-1 : ℤ) ^ p • CCA.normF P U (p + q' + 1) (hd (p + q') (CCA.hcup b.β p q'
            (fun z : Fin (p + 1) → G => CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i))) w.1)) :=
            congrArg (fun F => (-1 : ℤ) ^ p • F) (CCA.normF_hd (M := P) (U := U) (n := p + q') _).symm
        _ = (-1 : ℤ) ^ p • CCA.normF P U (p + q' + 1) ((-1 : ℤ) ^ p • CCA.hcup b.β p (q' + 1)
            (fun z : Fin (p + 1) → G => CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i)))
            (hd q' w.1)) :=
            congrArg (fun F => (-1 : ℤ) ^ p • CCA.normF P U (p + q' + 1) F) hh
        _ = CCA.normF P U (p + q' + 1) (CCA.hcup b.β p (q' + 1)
            (fun z : Fin (p + 1) → G => CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i)))
            (hd q' w.1)) := by
            rw [CCA.normF_zsmul, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]
        _ = CCA.normF P U (p + q' + 1) (CCA.hcup b.β p (q' + 1)
            (fun z : Fin (p + 1) → G => CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i)))
            (Sub.sub (α := (Fin (q' + 1 + 1) → G) → N.V) (φ.f (q' + 1) FcA).1
              (CCA.homz N.rho (q' + 1) c.1))) :=
            congrArg (fun F => CCA.normF P U (p + q' + 1) (CCA.hcup b.β p (q' + 1)
              (fun z : Fin (p + 1) → G => CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i))) F)) hwv
        _ = _ := (congrArg (CCA.normF P U (p + q' + 1)) (CCA.hcup_sub_right b.β p (q' + 1)
              (fun z : Fin (p + 1) → G => CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i)))
              (φ.f (q' + 1) FcA).1 (CCA.homz N.rho (q' + 1) c.1))).trans
            (CCA.normF_sub (M := P) (U := U) (n := p + q' + 1) _ _)
  have L : cupU p q ((M.resSub U).coch.cls p a ha')
      ((Pair.res N U.subtype continuous_subtype_val).hom.H q (N.coch.cls q c hc')) =
      (P.resSub U).coch.cls (p + q) z1 hz1 := hz1c
  have Rr : cup p q (corM.H p ((M.resSub U).coch.cls p a ha')) (N.coch.cls q c hc') =
      P.coch.cls (p + q) z2 hz2 := hz2c
  exact (congrArg (corP.H (p + q)) L).trans (key.trans Rr.symm)

end ReciprocityTheory.Coh
end

-- bundled from ReciprocityTheory.GroupCohomology.FiniteLevel
section
namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Topology
open scoped Pointwise

universe u

namespace FiniteLevelCohomology

theorem exists_nhds_right_const {K X : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [TopologicalSpace X] [DiscreteTopology X] (f : K → X) (hf : Continuous f) :
    ∃ V ∈ 𝓝 (1 : K), ∀ g v, v ∈ V → f (g * v) = f g := by
  have hfin : (Set.range f).Finite := (isCompact_range hf).finite_of_discrete
  have hV : ∀ x ∈ Set.range f, ∃ V ∈ 𝓝 (1 : K), f ⁻¹' {x} * V ⊆ f ⁻¹' {x} := by
    intro x _
    have hc : IsClosed (f ⁻¹' {x}) := (isClosed_discrete {x}).preimage hf
    exact compact_open_separated_mul_right hc.isCompact ((isOpen_discrete {x}).preimage hf) subset_rfl
  choose! V hV1 hV2 using hV
  refine ⟨⋂ x ∈ hfin.toFinset, V x, ?_, ?_⟩
  · exact (Filter.biInter_finset_mem _).2 fun x hx => hV1 x (hfin.mem_toFinset.1 hx)
  · intro g v hv
    have hx : f g ∈ Set.range f := ⟨g, rfl⟩
    have hvx : v ∈ V (f g) := Set.mem_iInter₂.1 hv (f g) (hfin.mem_toFinset.2 hx)
    exact hV2 (f g) hx (Set.mul_mem_mul (show f g ∈ ({f g} : Set X) from rfl) hvx)

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem stab_mem_nhds (M : TRep R G) [DiscreteTopology M.V] (m : M.V) :
    {a : G | M.rho a m = m} ∈ 𝓝 (1 : G) := by
  have hc : Continuous fun a : G => M.rho a m :=
    M.cont.comp (Continuous.prodMk continuous_id continuous_const)
  exact (hc.isOpen_preimage {m} (isOpen_discrete _)).mem_nhds (by simp)

theorem exists_open_normal [CompactSpace G] [TotallyDisconnectedSpace G] (M : TRep R G)
    [DiscreteTopology M.V] {n : ℕ} (c : (Fin n → G) → M.V) (hc : Continuous c) :
    ∃ N : Subgroup G, N.Normal ∧ IsOpen (N : Set G) ∧
      (∀ (g v : Fin n → G), (∀ i, v i ∈ N) → c (g * v) = c g) ∧
      ∀ g, ∀ a ∈ N, M.rho a (c g) = c g := by
  classical
  obtain ⟨V0, hV0, hV0c⟩ := exists_nhds_right_const c hc
  rw [nhds_pi, Filter.mem_pi] at hV0
  obtain ⟨I, -, t, ht, htV⟩ := hV0
  have hU : (⋂ i, t i) ∈ 𝓝 (1 : G) := Filter.iInter_mem.mpr fun i => ht i
  have hfin : (Set.range c).Finite := (isCompact_range hc).finite_of_discrete
  have hS : (⋂ m ∈ Set.range c, {a : G | M.rho a m = m}) ∈ 𝓝 (1 : G) :=
    (Filter.biInter_mem hfin).mpr fun m _ => stab_mem_nhds M m
  have hW : (⋂ i, t i) ∩ (⋂ m ∈ Set.range c, {a : G | M.rho a m = m}) ∈ 𝓝 (1 : G) :=
    Filter.inter_mem hU hS
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one isOpen_interior
    (mem_interior_iff_mem_nhds.mpr hW)
  refine ⟨H.toOpenSubgroup.toSubgroup, H.isNormal', H.toOpenSubgroup.isOpen', fun g v hv => ?_,
    fun g a ha => ?_⟩
  · apply hV0c g v
    apply htV
    intro i _
    have hvi := interior_subset (hH (hv i))
    exact Set.mem_iInter.mp hvi.1 i
  · have hai := interior_subset (hH ha)
    exact Set.mem_iInter₂.mp hai.2 (c g) ⟨g, rfl⟩

end FiniteLevelCohomology

namespace FiniteLevelCohomology

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem exists_level [CompactSpace G] [TotallyDisconnectedSpace G] (M : TRep R G)
    [DiscreteTopology M.V] (n : ℕ) (x : M.H n) :
    ∃ (N : Subgroup G) (_ : N.Normal), IsOpen (N : Set G) ∧ ∀ (Q : TRep R (G ⧸ N)) (P : Pair Q M),
      IsInvRep M N Q P → x ∈ LinearMap.range (P.hom.H n) := by
  obtain ⟨⟨c, hc⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hc' : M.coch.d n c = 0 := hc
  obtain ⟨N, hN, hNo, hconst, hfix⟩ := exists_open_normal M c.1 c.2
  refine ⟨N, hN, hNo, fun Q P hP => ?_⟩
  have := QuotientGroup.discreteTopology hNo
  obtain ⟨hφ, hemb, hrange⟩ := hP
  have hval : ∀ q : Fin n → G ⧸ N, ∃ y, P.u y = c.1 (fun i => (q i).out) :=
    fun q => (hrange _).2 fun a ha => hfix _ a ha
  choose f' hf' using hval
  have hout : ∀ g : Fin n → G,
      c.1 (fun i => (QuotientGroup.mk (s := N) (g i) : G ⧸ N).out) = c.1 g := by
    intro g
    choose v hv using fun i => QuotientGroup.mk_out_eq_mul N (g i)
    have e : (fun i => (QuotientGroup.mk (s := N) (g i) : G ⧸ N).out) = g * fun i => (v i : G) :=
      funext fun i => hv i
    rw [e]
    exact hconst g _ fun i => (v i).2
  have hPf : ∀ g : Fin n → G, P.u (f' fun i => P.φ (g i)) = c.1 g := by
    intro g
    rw [hφ]
    exact (hf' _).trans (hout g)
  let F : Q.coch.X n := ⟨f', continuous_of_discreteTopology⟩
  have h2 : P.hom.f n F = c := Subtype.ext (funext hPf)
  have hF : Q.coch.d n F = 0 := by
    have h1 : P.hom.f (n + 1) (Q.coch.d n F) = M.coch.d n (P.hom.f n F) := P.hom.comm n F
    rw [h2, hc'] at h1
    apply Subtype.ext
    funext q
    have h3 := congrFun (congrArg Subtype.val h1) (fun i => (q i).out)
    have h4 : (fun i => P.φ ((q i).out)) = q := by
      funext i
      rw [hφ]
      exact QuotientGroup.out_eq' (q i)
    change P.u ((Q.coch.d n F).1 fun i => P.φ ((q i).out)) = 0 at h3
    rw [h4] at h3
    exact hemb.injective (h3.trans (map_zero _).symm)
  refine ⟨Submodule.Quotient.mk ⟨F, hF⟩, ?_⟩
  rw [Cx.Hom.H, Submodule.mapQ_apply]
  congr 1
  exact Subtype.ext h2

theorem sum_neg_one_pow (k : ℕ) :
    (1 : R) + ∑ j : Fin (k + 1), (-1 : R) ^ ((j : ℕ) + 1) = if Even k then 0 else 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc, ← add_assoc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [ih]
    rcases Nat.even_or_odd k with hk | hk
    · have h1 : ¬ Even (k + 1) := Nat.not_even_iff_odd.2 (Even.add_one hk)
      rw [if_pos hk, if_neg h1, pow_succ, pow_succ, Even.neg_one_pow hk]
      ring
    · have h1 : Even (k + 1) := Odd.add_one hk
      rw [if_neg (Nat.not_even_iff_odd.2 hk), if_pos h1, pow_succ, pow_succ, Odd.neg_one_pow hk]
      ring

theorem dn_subsingleton {K : Type u} [Group K] [TopologicalSpace K] [Subsingleton K]
    (M : TRep R K) (k : ℕ) (f : (Fin k → K) → M.V) (g : Fin (k + 1) → K) :
    dn M.rho k f g = (if Even k then (0 : R) else 1) • f (fun _ => 1) := by
  have e : ∀ x : Fin k → K, f x = f (fun _ => 1) := fun x => congrArg f (Subsingleton.elim _ _)
  have hs : (∑ j : Fin (k + 1), (-1 : R) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g)) =
      ∑ j : Fin (k + 1), (-1 : R) ^ ((j : ℕ) + 1) • f (fun _ => 1) :=
    Finset.sum_congr rfl fun j _ => by rw [e (Fin.contractNth j (· * ·) g)]
  rw [dn_apply, Subsingleton.elim (g 0) 1, map_one, e (fun i => g i.succ), hs, ← Finset.sum_smul,
    ← sum_neg_one_pow k, add_smul, one_smul]
  rfl

theorem H_succ_trivial {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [Subsingleton K] (M : TRep R K) (m : ℕ) (z : M.H (m + 1)) : z = 0 := by
  classical
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [Submodule.Quotient.mk_eq_zero]
  have hwf : ∀ g, dn M.rho (m + 1) w.1.1 g = 0 := fun g => by
    have h := congrArg (fun x : M.coch.X (m + 1 + 1) => x.1 g) w.2
    exact h
  show (w : M.coch.X (m + 1)) ∈ LinearMap.range (M.coch.d m)
  rcases Nat.even_or_odd m with hm | hm
  · have h1 : w.1.1 (fun _ => 1) = 0 := by
      have h := hwf (fun _ => 1)
      rwa [dn_subsingleton, if_neg (Nat.even_add_one.not.mpr (not_not.mpr hm)), one_smul] at h
    refine ⟨0, ?_⟩
    rw [map_zero]
    symm
    apply Subtype.ext
    funext g
    show w.1.1 g = 0
    rw [Subsingleton.elim g (fun _ => 1)]
    exact h1
  · refine ⟨⟨fun _ => w.1.1 (fun _ => 1), ?_⟩, ?_⟩
    · exact continuous_const
    · apply Subtype.ext
      funext g
      show dn M.rho m (fun _ => w.1.1 (fun _ => 1)) g = w.1.1 g
      rw [dn_subsingleton, if_neg (Nat.not_even_iff_odd.mpr hm), one_smul]
      rw [Subsingleton.elim g (fun _ => 1)]

theorem torsion_finite {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [DiscreteTopology H] [Finite H] (Q : TRep R H) (m : ℕ) (y : Q.H (m + 1)) :
    Nat.card H • y = 0 := by
  have : Subsingleton (⊥ : Subgroup H) :=
    ⟨fun a b => Subtype.ext ((Subgroup.mem_bot.1 a.2).trans (Subgroup.mem_bot.1 b.2).symm)⟩
  obtain ⟨cor, -, hcor⟩ := cor_holds R H Q ⊥ (isOpen_discrete _)
  have h := hcor (m + 1) y
  rw [H_succ_trivial _ m ((Pair.res Q (⊥ : Subgroup H).subtype continuous_subtype_val).hom.H (m + 1) y),
    map_zero, Subgroup.index_bot] at h
  exact h.symm

end FiniteLevelCohomology

theorem finiteLevel_holds : FiniteLevelStatement.{u} := by
  intro R _ G _ _ _ _ _ _ M _ n x
  obtain ⟨N, hN, hNo, hlev⟩ := FiniteLevelCohomology.exists_level M n x
  refine ⟨⟨N, hN, hNo, hlev⟩, fun hn => ?_⟩
  obtain ⟨y, hy⟩ := hlev _ _ (InflationRestrictionInvariants.invariants_isInvRep M N)
  haveI : DiscreteTopology (G ⧸ N) := QuotientGroup.discreteTopology hNo
  haveI : Finite (G ⧸ N) := Subgroup.quotient_finite_of_isOpen N hNo
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨Nat.card (G ⧸ N), Nat.card_pos, ?_⟩
  rw [← hy, ← map_nsmul, FiniteLevelCohomology.torsion_finite _ m y, map_zero]

end ReciprocityTheory.Coh
end

-- bundled from ReciprocityTheory.GroupCohomology.KilledHolds
section
namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

namespace KernelCokernelKilling

section KillLES

variable {R : Type u} [CommRing R] {A B C : Cx R} {i : Hom A B} {p : Hom B C}
  {δ : ∀ n, C.H n →ₗ[R] A.H (n + 1)}

end KillLES

section KillRep

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

end KillRep

end KernelCokernelKilling

open KernelCokernelKilling

theorem shift_holds : ShiftStatement.{u} := by
  intro R _ G _ _ _ _ N hN M _ hM n hn
  induction n, hn using Nat.le_induction generalizing M with
  | base => exact hN M hM
  | succ n hNn ih =>
    exact KernelCokernelKilling.shift_step M n (ih (KernelCokernelKilling.shQ M) (KernelCokernelKilling.shQ_tors M hM))

end

end ReciprocityTheory.Coh
end

