module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PlGen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Loc_fin
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.loc_fin :
    ∀ (l : ℕ) [Fact l.Prime] (Y : Type) [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y] [CompactSpace Y] [TotallyDisconnectedSpace Y] (H : Subgroup Y) [H.Normal], IsOpen (H : Set Y) → PhiCond Y l → ∃ (P : Subgroup Y) (_ : P.Normal), TopFG (Y ⧸ P) ∧ ∀ (Z : Type) [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z] [CompactSpace Z] [TotallyDisconnectedSpace Z] (f : Y →* Z) (H' : Subgroup Z), Continuous f → PL l H' = ⊥ → H ≤ H'.comap f → P ≤ f.ker := by
  intro l _ Y _ _ _ _ _ H _ hH hphi
  obtain ⟨hPn, hPc, hPH, -, -, -⟩ := pl_props l Y H hH
  refine ⟨PL l H, hPn, ?_, ?_⟩
  · let P := PL l H
    let m : Y →* Y ⧸ P := QuotientGroup.mk' P
    have hmc : Continuous m := continuous_quot_mk
    have hms : Function.Surjective m := QuotientGroup.mk'_surjective P
    haveI : TotallyDisconnectedSpace (Y ⧸ P) := (totallyDisconnected_quot Y P hPc).1
    let H' : Subgroup (Y ⧸ P) := H.map m
    haveI : H'.Normal := Subgroup.Normal.map inferInstance m hms
    have hcm : H'.comap m = H := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
      exact sup_eq_left.mpr hPH
    have hH'open : IsOpen (H' : Set (Y ⧸ P)) := by
      have : (H' : Set (Y ⧸ P)) = m '' (H : Set Y) := by simp [H']
      rw [this]
      exact QuotientGroup.isOpenMap_coe _ hH
    have hPL' : PL l H' = ⊥ := by
      rw [← pl_map l Y (Y ⧸ P) m H' hH'open hmc hms, hcm]
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    have hfin : Finite (HomL l (H'.comap m)) := by
      rw [hcm]
      exact hphi H hH
    exact (pl_gen l (Y ⧸ P) H' hH'open hPL' (homl_desc l Y (Y ⧸ P) m H' hmc hms hfin).1).1
  · intro Z _ _ _ _ _ f H' hf hPL hle g hg
    rw [MonoidHom.mem_ker]
    have hmem : f g ∈ PL l H' := by
      simp only [PL, Subgroup.mem_iInf] at hg ⊢
      intro U hU
      let V : OpenNormalSubgroup Y :=
        { toOpenSubgroup := U.toOpenSubgroup.comap f hf
          isNormal' := Subgroup.Normal.comap U.isNormal' f }
      have hV : ∀ y : Y, y ∈ V ↔ f y ∈ U := fun y => Iff.rfl
      have := hg V (by
        intro h hh
        obtain ⟨e, he⟩ := hU (f h) (hle hh)
        exact ⟨e, (hV _).mpr (by simpa using he)⟩)
      exact (hV g).mp this
    rw [hPL] at hmem
    exact (Subgroup.mem_bot).mp hmem
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SysCover
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.sys_cover :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0), T.ProL → ∃ (Ph : Type) (_ : Group Ph) (_ : TopologicalSpace Ph) (_ : IsTopologicalGroup Ph) (_ : CompactSpace Ph) (_ : TotallyDisconnectedSpace Ph) (π : ∀ N, Ph →* (T.GN N).Γ) (ct : Ph), TopFG Ph ∧ (∀ N, Continuous (π N) ∧ Function.Surjective (π N) ∧ π N ct = (T.GN N).c) ∧ ∀ N N' g, (T.h N).p (π N g) * ((T.h N').p (π N' g))⁻¹ ∈ T.H := by
  intro l _ L G0 T hT
  classical
  let H0 : Subgroup G0.Γ := (T.H : Subgroup G0.Γ)
  have hH0open : IsOpen (H0 : Set G0.Γ) := T.H.isOpen
  obtain ⟨n, e, he⟩ : ∃ n : ℕ, ∃ e : Fin n → G0.Γ ⧸ H0, Function.Surjective e := by
    obtain ⟨n, ⟨eq⟩⟩ := Finite.exists_equiv_fin (G0.Γ ⧸ H0)
    exact ⟨n, eq.symm, eq.symm.surjective⟩
  let lift : G0.Γ ⧸ H0 → G0.Γ := Function.surjInv QuotientGroup.mk_surjective
  have hlift : ∀ y, (QuotientGroup.mk (lift y) : G0.Γ ⧸ H0) = y :=
    Function.surjInv_eq QuotientGroup.mk_surjective
  let yc : Fin (n + 1) → G0.Γ := Fin.cons G0.c (fun i => lift (e i))
  let γ : Fin (n + 1) → G0.Γ ⧸ H0 := fun i => QuotientGroup.mk (yc i)
  have hγ : Function.Surjective γ := by
    intro y
    obtain ⟨i, rfl⟩ := he y
    exact ⟨i.succ, by simp [γ, yc, hlift]⟩
  obtain ⟨P, iG, iT, iTG, iC, iTD, x, hx, hfree⟩ := exists_free_profinite (n + 1 + T.hb)
  obtain ⟨f0, hf0c, hf0x⟩ := hfree G0.Γ (Fin.append yc (fun _ => 1))
  let π0 : P →* G0.Γ ⧸ H0 := (QuotientGroup.mk' H0).comp f0
  have hπ0ker : IsOpen (π0.ker : Set P) := by
    have : (π0.ker : Set P) = f0 ⁻¹' (H0 : Set G0.Γ) := by
      ext g
      simp [π0, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
    rw [this]
    exact hH0open.preimage hf0c
  have hcast : ∀ i : Fin (n + 1), π0 (x (Fin.castAdd T.hb i)) = γ i := by
    intro i
    simp [π0, γ, hf0x, Fin.append_left]
  have hnat : ∀ i : Fin T.hb, π0 (x (Fin.natAdd (n + 1) i)) = 1 := by
    intro i
    simp [π0, hf0x, Fin.append_right]
  have key : ∀ N : ℕ, ∃ f : P →* (T.GN N).Γ, Continuous f ∧ Function.Surjective f ∧
      ((QuotientGroup.mk' H0).comp (T.h N).p).comp f = π0 ∧
      f (x (Fin.castAdd T.hb 0)) = (T.GN N).c := by
    intro N
    let p := (T.h N).p
    let q : (T.GN N).Γ →* G0.Γ ⧸ H0 := (QuotientGroup.mk' H0).comp p
    let HN : Subgroup (T.GN N).Γ := H0.comap p
    haveI : HN.Normal := Subgroup.Normal.comap inferInstance p
    have hqker : q.ker = HN := by
      ext g
      simp [q, HN, p, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
    have hHNopen : IsOpen (HN : Set (T.GN N).Γ) := hH0open.preimage (T.h N).cont
    have hqopen : IsOpen (q.ker : Set (T.GN N).Γ) := by rw [hqker]; exact hHNopen
    let g : Fin (n + 1) → (T.GN N).Γ :=
      Fin.cons (T.GN N).c (fun i => Function.surjInv (T.h N).surj (yc i.succ))
    have hg : ∀ i, q (g i) = γ i := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [q, g, γ, yc, p, (T.h N).c]
      · simp [q, g, γ, p, Function.surjInv_eq (T.h N).surj]
    have hz : ∃ z : Fin T.hb → ↥q.ker, TopGen (Set.range z) := by
      rw [hqker]
      have hPL := hT.2 N
      have hfin := T.finN N
      exact (pl_gen l (T.GN N).Γ HN hHNopen hPL hfin.1).2 T.hb hfin.2
    obtain ⟨f, hfc, hfs, hfq, hfx⟩ :=
      exists_surj_over_finite P (G0.Γ ⧸ H0) (n + 1) T.hb x γ π0 hx hfree hγ hπ0ker hcast hnat
        (T.GN N).Γ q hqopen g hg hz
    exact ⟨f, hfc, hfs, hfq, by rw [hfx 0]; simp [g]⟩
  choose F hFc hFs hFq hFx using key
  refine ⟨P, iG, iT, iTG, iC, iTD, F, x (Fin.castAdd T.hb 0), ⟨Set.range x, Set.finite_range x, hx⟩,
    fun N => ⟨hFc N, hFs N, hFx N⟩, ?_⟩
  intro N N' g
  have h1 := congrArg (fun φ => φ g) (hFq N)
  have h2 := congrArg (fun φ => φ g) (hFq N')
  simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply] at h1 h2
  have h3 : (QuotientGroup.mk ((T.h N).p (F N g)) : G0.Γ ⧸ H0) = QuotientGroup.mk ((T.h N').p (F N' g)) := by
    rw [h1, h2]
  rw [QuotientGroup.eq_iff_div_mem, div_eq_mul_inv] at h3
  exact h3
end

