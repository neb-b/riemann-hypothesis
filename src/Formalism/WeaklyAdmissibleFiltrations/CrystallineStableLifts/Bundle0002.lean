module

public import Formalism.WeaklyAdmissibleFiltrations.Bundle0001

@[expose] public section

-- bundled from Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.TrivCrys
section
noncomputable section

namespace Formalism.WeaklyAdmissibleFiltrations

open Module TensorProduct

section TrivCrysProof

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B]
    [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR]
    [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]

include PD in
private theorem trivCrys_nontrivial_B : Nontrivial B := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  apply PD.not_mem_filtration_two
  rw [Subsingleton.elim PD.t 0, map_zero]
  exact zero_mem _

private def trivCrysIncl : K₀ →ₗ[Qp] B := (Algebra.linearMap K₀ B).restrictScalars Qp

private def trivCrysMap : LL ⊗[Qp] K₀ →ₗ[LL] LL ⊗[Qp] B :=
  AlgebraTensorModule.lTensor LL LL (trivCrysIncl (Qp := Qp) (K₀ := K₀) (B := B))

private theorem trivCrys_act_tmul (g : G) (l : LL) (b : B) :
    actVB PD (1 : Representation LL G LL) g (l ⊗ₜ[Qp] b) = l ⊗ₜ[Qp] PD.actB g b := by
  simp [actVB]

private theorem trivCrys_range_le (g : G) (y : LL ⊗[Qp] K₀) :
    actVB PD (1 : Representation LL G LL) g (trivCrysMap (LL := LL) (B := B) y) =
      trivCrysMap (LL := LL) (B := B) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul l c =>
    simp only [trivCrysMap, trivCrysIncl, AlgebraTensorModule.lTensor_tmul, LinearMap.restrictScalars_apply,
      Algebra.linearMap_apply, trivCrys_act_tmul]
    rw [AlgEquiv.commutes]
  | add y z hy hz => rw [map_add (f := _), map_add (f := _), hy, hz]

variable [FiniteDimensional Qp LL]

private def trivCrysCoord (b : Basis (Fin (finrank Qp LL)) Qp LL) (i : Fin (finrank Qp LL)) :
    LL ⊗[Qp] B →ₗ[Qp] B :=
  (TensorProduct.lid Qp B).toLinearMap ∘ₗ LinearMap.rTensor B (b.coord i)

private theorem trivCrysCoord_tmul (b : Basis (Fin (finrank Qp LL)) Qp LL) (i) (l : LL) (c : B) :
    trivCrysCoord (B := B) b i (l ⊗ₜ[Qp] c) = b.coord i l • c := by
  simp [trivCrysCoord]

private theorem trivCrys_decomp (b : Basis (Fin (finrank Qp LL)) Qp LL) (x : LL ⊗[Qp] B) :
    x = ∑ i, b i ⊗ₜ[Qp] trivCrysCoord (B := B) b i x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul l c =>
    simp only [trivCrysCoord_tmul, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Basis.coord_apply]
    rw [← TensorProduct.sum_tmul, Basis.sum_repr]
  | add y z hy hz =>
    conv_lhs => rw [hy, hz]
    rw [← Finset.sum_add_distrib]
    simp only [map_add (f := _), TensorProduct.tmul_add]

private theorem trivCrysCoord_act (b : Basis (Fin (finrank Qp LL)) Qp LL) (i) (g : G)
    (x : LL ⊗[Qp] B) :
    trivCrysCoord (B := B) b i (actVB PD (1 : Representation LL G LL) g x) =
      PD.actB g (trivCrysCoord (B := B) b i x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul l c =>
    rw [trivCrys_act_tmul, trivCrysCoord_tmul, trivCrysCoord_tmul]
    exact (((PD.actB g).toAlgHom.toLinearMap).restrictScalars Qp).map_smul _ _ |>.symm
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

private theorem trivCrys_Dcris_eq :
    Dcris PD (1 : Representation LL G LL) = LinearMap.range (trivCrysMap (LL := LL) (K₀ := K₀) (B := B)) := by
  apply le_antisymm
  · intro x hx
    simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero] at hx
    let b := Module.finBasis Qp LL
    have hc : ∀ i, ∃ c : K₀, algebraMap K₀ B c = trivCrysCoord (B := B) b i x := by
      intro i
      apply PD.invB
      intro g
      rw [← trivCrysCoord_act PD b i g x, hx g]
    choose c hc using hc
    refine ⟨∑ i, b i ⊗ₜ[Qp] c i, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, trivCrys_decomp b x]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [trivCrysMap, trivCrysIncl, AlgebraTensorModule.lTensor_tmul, LinearMap.restrictScalars_apply,
      Algebra.linearMap_apply, hc i]
  · rintro _ ⟨y, rfl⟩
    simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
    exact fun g => trivCrys_range_le PD g y

include PD in
private theorem trivCrysMap_injective :
    Function.Injective (trivCrysMap (Qp := Qp) (LL := LL) (K₀ := K₀) (B := B)) := by
  haveI := trivCrys_nontrivial_B PD
  have hi : Function.Injective (trivCrysIncl (Qp := Qp) (K₀ := K₀) (B := B)) :=
    (algebraMap K₀ B).injective
  have h2 := Module.Flat.lTensor_preserves_injective_linearMap (M := LL) _ hi
  exact h2

end TrivCrysProof

theorem trivialIsCrystalline_holds : TrivCrys := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ _ _
  unfold IsCrys
  rw [trivCrys_Dcris_eq PD (LL := LL), LinearMap.finrank_range_of_inj (trivCrysMap_injective PD),
    Module.finrank_baseChange, Module.finrank_self, mul_one]

end Formalism.WeaklyAdmissibleFiltrations
end
end

-- bundled from Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.WachCol
section
noncomputable section

namespace Formalism.WeaklyAdmissibleFiltrations

open Module

section Abstract

variable {O X H : Type} [CommRing O] [AddCommGroup X] [Module O X] [AddCommGroup H] [Module O H]

theorem wachCol_len_transfer (N I : Submodule O X) (f : N →ₗ[O] H) (Hf S : Submodule O H)
    (hr : LinearMap.range f = Hf) (hI : I.comap N.subtype = S.comap f) :
    Module.length O (↥N ⧸ I.comap N.subtype) = Module.length O (↥Hf ⧸ S.comap Hf.subtype) := by
  let g : N →ₗ[O] Hf := LinearMap.codRestrict Hf f (fun x => by rw [← hr]; exact LinearMap.mem_range_self f x)
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    rw [← hr] at hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, rfl⟩
  let q : N →ₗ[O] (↥Hf ⧸ S.comap Hf.subtype) := (S.comap Hf.subtype).mkQ ∘ₗ g
  have hq : Function.Surjective q := (Submodule.mkQ_surjective _).comp hg
  have hk : LinearMap.ker q = I.comap N.subtype := by
    ext x
    rw [hI, LinearMap.mem_ker, Submodule.mem_comap]
    simp [q, g]
  exact ((Submodule.quotEquivOfEq _ _ hk.symm).trans (q.quotKerEquivOfSurjective hq)).length_eq

theorem wachCol_lift_transfer (N I : Submodule O X) (f : N →ₗ[O] H) (Hf S : Submodule O H)
    (hr : LinearMap.range f = Hf) (hI : I.comap N.subtype = S.comap f) (a : O) :
    (∀ m ∈ N, a • m ∈ I) ↔ ∀ x ∈ Hf, a • x ∈ S := by
  have key : ∀ n : N, (a • (n : X) ∈ I ↔ a • f n ∈ S) := by
    intro n
    have h := SetLike.ext_iff.mp hI (a • n)
    simpa using h
  constructor
  · intro h x hx
    rw [← hr] at hx
    obtain ⟨n, rfl⟩ := hx
    exact (key n).mp (h n n.2)
  · intro h m hm
    exact (key ⟨m, hm⟩).mpr (h _ (by rw [← hr]; exact LinearMap.mem_range_self f _))

end Abstract

section WachSide

open Formalism.CoboundaryTransfers

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {Bw : Base O A} {M : ℕ}
  {D D' : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
  [AddCommGroup D'] [Module A D'] [Module O D'] [IsScalarTower O A D']

theorem wachModule_mem_cocycles_iff (W : WachMod Bw M D) (pr : D × D) :
    pr ∈ W.Z1 ↔ (W.γ pr.1 - pr.1) - (W.φ pr.2 - pr.2) = 0 := by
  unfold WachMod.Z1
  simp
  rw [← neg_sub (W.φ pr.2) pr.2, ← sub_eq_add_neg]

theorem wachModule_coboundaries_le_cocycles (W : WachMod Bw M D) : W.B1 ≤ W.Z1 := by
  intro pr hpr
  rw [wachModule_mem_cocycles_iff]
  unfold WachMod.B1 at hpr
  obtain ⟨d, rfl⟩ := hpr
  have key : W.γ (W.φ d) = W.φ (W.γ d) := by
    first
    | (cases W; simp_all)
    | (cases W; simp_all [LinearMap.ext_iff])
    | (cases W; simp_all [LinearMap.ext_iff, eq_comm])
  simp [key, Function.prod, map_add (f := _), map_sub, map_neg, neg_smul, LinearMap.add_apply] <;> abel

theorem wachModule_finiteCocycles_le_cocycles (W : WachMod Bw M D) : W.Zf ≤ W.Z1 := by
  unfold WachMod.Zf
  exact sup_le (Submodule.span_le.mpr (fun x hx => hx.1)) (wachModule_coboundaries_le_cocycles W)

theorem wachHom_prodMap_mem_cocycles {W : WachMod Bw M D} {W' : WachMod Bw M D'} (Fw : Hom W W') (pr : D × D)
    (h : pr ∈ W.Z1) : Fw.f2 pr ∈ W'.Z1 := by
  rw [wachModule_mem_cocycles_iff] at h ⊢
  have := congrArg Fw.f h
  simp only [map_sub, map_zero, Fw.φ_comm, Fw.γ_comm] at this
  exact this

end WachSide

theorem cokernelLengthEqWach_holds : WachCol := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ O _ _ V V'
    _ _ _ _ _ _ _ _ _ _ _ _ ρ ρ' _ _ _ _ _ _ _ L L' F A D D' _ _ _ _ _ _ _ _ _ _
    Bw M W W' Fw cl cl' hp hW hW' hnat
  set S : Submodule O (LatticeCohomology L') := (latticeFiniteCohomology PD L).map F.H1map with hS

  have hZf_le : latticeFiniteCocycles PD L' ≤ latticeCocycles L' := inf_le_left
  let ψ : ↥(latticeFiniteCocycles PD L') →ₗ[O] LatticeCohomology L' := (Submodule.mkQ _) ∘ₗ Submodule.inclusion hZf_le
  have hψr : LinearMap.range ψ = latticeFiniteCohomology PD L' := by
    rw [LinearMap.range_comp, Submodule.range_inclusion]; rfl
  have hψI : (F.ImF PD).comap (latticeFiniteCocycles PD L').subtype = S.comap ψ := by
    ext ⟨c, hc⟩
    simp only [Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · intro h
      obtain ⟨u, ⟨a, ha, rfl⟩, b, hb, hab⟩ := Submodule.mem_sup.1 h
      refine ⟨Submodule.mkQ _ ⟨a, ha.1⟩, ⟨⟨a, ha.1⟩, ha, rfl⟩, ?_⟩
      simp only [ψ, LinearMap.comp_apply, LatHom.H1map, Submodule.mkQ_apply]
      refine (Submodule.Quotient.eq _).2 ?_
      change F.post a - c ∈ latticeCoboundaries L'
      have e : F.post a - c = -b := by rw [← hab]; abel
      rw [e]; exact (latticeCoboundaries L').neg_mem hb
    · rintro ⟨κ, ⟨x, hx, rfl⟩, hκ⟩
      simp only [ψ, LinearMap.comp_apply, LatHom.H1map, Submodule.mkQ_apply] at hκ
      have hb := (Submodule.Quotient.eq _).1 hκ
      change F.post x - c ∈ latticeCoboundaries L' at hb
      refine Submodule.mem_sup.2 ⟨F.post x, ⟨(x : G → V), hx, rfl⟩, c - F.post x, ?_, by abel⟩
      have := (latticeCoboundaries L').neg_mem hb
      rwa [neg_sub] at this

  have hZ' : W'.Zf ≤ W'.Z1 := wachModule_finiteCocycles_le_cocycles W'
  let χ : ↥W'.Zf →ₗ[O] LatticeCohomology L' := cl' ∘ₗ Submodule.inclusion hZ'
  have hχr : LinearMap.range χ = latticeFiniteCohomology PD L' := by
    rw [LinearMap.range_comp, Submodule.range_inclusion]; exact hW'.2
  have hχI : Fw.ImF.comap W'.Zf.subtype = S.comap χ := by
    ext ⟨pr', hpr'⟩
    simp only [Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · intro h
      obtain ⟨u, ⟨pr, hpr, rfl⟩, b, hb, hab⟩ := Submodule.mem_sup.1 h
      have hpr1 : pr ∈ W.Z1 := wachModule_finiteCocycles_le_cocycles W hpr
      have hf1 : Fw.f2 pr ∈ W'.Z1 := wachHom_prodMap_mem_cocycles Fw pr hpr1
      have hb1 : b ∈ W'.Z1 := wachModule_coboundaries_le_cocycles W' hb
      refine ⟨cl ⟨pr, hpr1⟩, ?_, ?_⟩
      · rw [← hW.2]; exact ⟨⟨pr, hpr1⟩, hpr, rfl⟩
      · rw [hnat ⟨pr, hpr1⟩ ⟨Fw.f2 pr, hf1⟩ rfl]
        have e : (⟨pr', hZ' hpr'⟩ : W'.Z1) = ⟨Fw.f2 pr, hf1⟩ + ⟨b, hb1⟩ := by
          apply Subtype.ext
          simp [← hab]
        change _ = cl' ⟨pr', hZ' hpr'⟩
        rw [e, map_add (f := _), (hW'.1.2 ⟨b, hb1⟩).2 hb, add_zero]
    · rintro ⟨κ, hκ, hκ'⟩
      rw [← hW.2] at hκ
      obtain ⟨⟨pr, hpr1⟩, hpr, rfl⟩ := hκ
      have hf1 := wachHom_prodMap_mem_cocycles Fw pr hpr1
      rw [hnat ⟨pr, hpr1⟩ ⟨Fw.f2 pr, hf1⟩ rfl] at hκ'
      have h0 : cl' (⟨pr', hZ' hpr'⟩ - ⟨Fw.f2 pr, hf1⟩) = 0 := by
        rw [map_sub]; exact sub_eq_zero.2 hκ'.symm
      have hb := (hW'.1.2 _).1 h0
      exact Submodule.mem_sup.2 ⟨Fw.f2 pr, ⟨pr, hpr, rfl⟩, pr' - Fw.f2 pr, hb, by abel⟩
  have hcolG := wachCol_len_transfer (latticeFiniteCocycles PD L') (F.ImF PD) ψ (latticeFiniteCohomology PD L') S hψr hψI
  have hcolW := wachCol_len_transfer W'.Zf Fw.ImF χ (latticeFiniteCohomology PD L') S hχr hχI
  refine ⟨?_, fun e => ?_⟩
  · unfold LatHom.col Formalism.CoboundaryTransfers.Hom.col
    rw [hcolG, hcolW]
  · have hG := wachCol_lift_transfer (latticeFiniteCocycles PD L') (F.ImF PD) ψ (latticeFiniteCohomology PD L') S hψr hψI
      ((PD.p : O) ^ e)
    have hWl := wachCol_lift_transfer W'.Zf Fw.ImF χ (latticeFiniteCohomology PD L') S hχr hχI ((PD.p : O) ^ e)
    unfold LatHom.LiftF Formalism.CoboundaryTransfers.Hom.LiftF
    rw [hG]
    have hsm : ∀ pr : D' × D', ((Bw.p ^ e : ℕ)) • pr = ((PD.p : O) ^ e) • pr := by
      intro pr
      rw [hp, ← Nat.cast_smul_eq_nsmul O, Nat.cast_pow]
    simp only [hsm]
    exact hWl.symm

end Formalism.WeaklyAdmissibleFiltrations
end
end

