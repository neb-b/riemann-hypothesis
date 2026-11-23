module

public import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.Bundle0001

@[expose] public section

-- bundled from CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohCmp
section
open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel

namespace CompanionTheory.LocalTateOrthogonality.Gcoh

theorem gcRep : SgcRep := by
  intro G _ _ _ R _ M _ _ _ _ rho hrho
  letI : Module (ULift.{0} ℤ) M := Module.compHom M (ULift.ringEquiv : ULift.{0} ℤ ≃+* ℤ).toRingHom
  let σ : Representation (ULift.{0} ℤ) G M :=
    { toFun := fun g =>
        { toFun := rho g
          map_add' := map_add _
          map_smul' := fun c m => map_zsmul (rho g) c.down m }
      map_one' := LinearMap.ext fun m => by
        change rho 1 m = m
        rw [map_one]; rfl
      map_mul' := fun g h => LinearMap.ext fun m => by
        change rho (g * h) m = rho g (rho h m)
        rw [map_mul]; rfl }
  refine ⟨Rep.of σ, ⟨fun a => ?_⟩, AddEquiv.refl M, fun g m => rfl⟩
  have hc : Continuous fun g : G => rho g (a : M) :=
    hrho.comp (continuous_id.prodMk continuous_const)
  exact (isOpen_discrete {(a : M)}).preimage hc

attribute [local instance 2000] Rep.hV2

section

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  (A : Rep.{0} k G) (e : M ≃+ A.V)

omit [IsTopologicalGroup G] in
theorem lc_of_cont {X : Type} [TopologicalSpace X] {f : X → M} (hf : Continuous f) :
    IsLocallyConstant fun s => e (f s) :=
  ((IsLocallyConstant.iff_continuous f).2 hf).comp e

omit [IsTopologicalGroup G] in
theorem cont_of_lc {X : Type} [TopologicalSpace X] {f : X → A.V} (hf : IsLocallyConstant f) :
    Continuous fun s => e.symm (f s) :=
  (hf.comp e.symm).continuous

end

theorem gcn : Sgcn := by
  intro G _ _ _ R _ M _ _ _ _ rho A _ e he n
  let φ : Zn rho n →+ ((Fin n → G) → A) :=
    AddMonoidHom.mk' (fun z s => e (z.1 s)) (fun z z' => funext fun s => map_add e _ _)
  have hφ : ∀ z s, φ z s = e (z.1 s) := fun _ _ => rfl
  obtain ⟨e', -⟩ := core_quot A ((Bn rho n).comap (Zn rho n).subtype) n φ
    (fun z => exists_coc A n _ (lc_of_cont A e z.2.1) (by
      have hz : dn rho n z.1 = 0 := z.2.2
      refine (d_comp rho A e he n z.1).trans ?_
      funext s
      rw [hz]
      exact map_zero e))
    (fun x => by
      refine ⟨⟨fun s => e.symm (cochainOf A (cocycleι A n x) s),
        cont_of_lc A e (isLocallyConstant_cochainOf _), ?_⟩, ?_⟩
      · have h := d_comp rho A e he n fun s => e.symm (cochainOf A (cocycleι A n x) s)
        simp only [AddEquiv.apply_symm_apply] at h
        rw [d_cocycleι] at h
        change dn rho n _ = 0
        funext s
        apply e.injective
        rw [← congrFun h s]
        exact (map_zero e).symm
      · funext s
        exact (e.apply_symm_apply _).symm)
    (fun z x hx => by
      cases n with
      | zero =>
        rw [pi_zero_eq_zero_iff, hx]
        change _ ↔ z.1 = 0
        constructor
        · intro h
          funext s
          exact e.map_eq_zero_iff.1 (congrFun h s)
        · intro h
          funext s
          rw [hφ, h]
          exact map_zero e
      | succ n =>
        rw [pi_succ_eq_zero_iff, hx]
        constructor
        · rintro ⟨w, hw, h⟩
          refine ⟨fun s => e.symm (w s), cont_of_lc A e hw, ?_⟩
          have h' := d_comp rho A e he n fun s => e.symm (w s)
          simp only [AddEquiv.apply_symm_apply] at h'
          funext s
          apply e.injective
          exact (congrFun h' s).symm.trans (congrFun h s)
        · rintro ⟨c, hc, h⟩
          refine ⟨fun s => e (c s), lc_of_cont A e hc, (d_comp rho A e he n c).trans ?_⟩
          funext s
          rw [h]
          rfl)
  exact ⟨e'⟩

theorem gc0 : Sgc0 := by
  intro G _ _ _ R _ M _ _ _ _ rho A _ e he
  let φ : H0 rho →+ ((Fin 0 → G) → A) :=
    AddMonoidHom.mk' (fun z _ => e z.1) (fun z z' => funext fun s => map_add e _ _)
  have hex : ∀ z, ∃ x : cocycles A 0, cochainOf A (cocycleι A 0 x) = φ z := fun z =>
    exists_coc A 0 _ (IsLocallyConstant.const _) (by
      refine (d_comp rho A e he 0 fun _ => z.1).trans ?_
      funext s
      rw [dn_zero, z.2 (s 0), sub_self]
      exact map_zero e)
  obtain ⟨f, hs, hf⟩ := core_hom A 0 φ hex (fun x => by
    refine ⟨⟨e.symm (cochainOf A (cocycleι A 0 x) default), fun g => ?_⟩, ?_⟩
    · have h := d_comp rho A e he 0 fun s => e.symm (cochainOf A (cocycleι A 0 x) s)
      simp only [AddEquiv.apply_symm_apply] at h
      rw [d_cocycleι] at h
      have h' := congrFun h (fun _ => g)
      rw [dn_zero] at h'
      exact sub_eq_zero.1 (e.map_eq_zero_iff.1 h'.symm)
    · funext s
      rw [Subsingleton.elim s default]
      exact (e.apply_symm_apply _).symm)
  refine ⟨AddEquiv.ofBijective f ⟨?_, hs⟩, fun m x h => hf m x (funext h)⟩
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨x, hx⟩ := hex z
  rw [hf z x hx, pi_zero_eq_zero_iff, hx] at hz
  exact Subtype.ext (e.map_eq_zero_iff.1 (congrFun hz default))

theorem gc1 : Sgc1 := by
  intro G _ _ _ R _ M _ _ _ _ rho A _ e he
  let φ : Z1 rho →+ ((Fin 1 → G) → A) :=
    AddMonoidHom.mk' (fun z s => e (z.1 (s 0))) (fun z z' => funext fun s => map_add e _ _)
  have hex : ∀ z, ∃ x : cocycles A 1, cochainOf A (cocycleι A 1 x) = φ z := fun z =>
    exists_coc A 1 _ (lc_of_cont A e (z.2.1.comp (continuous_apply 0))) (by
      refine (d_comp rho A e he 1 fun s => z.1 (s 0)).trans ?_
      funext s
      rw [dn_one, z.2.2 (s 0) (s 1)]
      rw [show ∀ a b : M, b - (a + b) + a = 0 from fun a b => by abel]
      exact map_zero e)
  have hv : ∀ s : Fin 1 → G, s = fun _ => s 0 := fun s => funext fun i => by
    rw [Subsingleton.elim i 0]
  obtain ⟨e', he'⟩ := core_quot A ((B1 rho).comap (Z1 rho).subtype) 1 φ hex
    (fun x => by
      have hx : cochainOf A (cocycleι A 1 x) =
          fun s => e (e.symm (cochainOf A (cocycleι A 1 x) fun _ => s 0)) := by
        funext s
        rw [e.apply_symm_apply, ← hv]
      refine ⟨⟨fun g => e.symm (cochainOf A (cocycleι A 1 x) fun _ => g),
        (cont_of_lc A e (isLocallyConstant_cochainOf _)).comp
          (continuous_pi fun _ => continuous_id), fun g g' => ?_⟩, hx⟩
      have h := d_comp rho A e he 1 fun s => e.symm (cochainOf A (cocycleι A 1 x) fun _ => s 0)
      rw [← hx, d_cocycleι] at h
      have h' := congrFun h ![g, g']
      rw [dn_one rho (fun g => e.symm (cochainOf A (cocycleι A 1 x) fun _ => g))] at h'
      have h2 := e.map_eq_zero_iff.1 h'.symm
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h2
      rw [← sub_eq_zero, ← neg_eq_zero, ← h2]
      abel)
    (fun z x hx => by
      rw [pi_succ_eq_zero_iff, hx]
      constructor
      · rintro ⟨w, hw, h⟩
        refine ⟨e.symm (w default), ?_⟩
        have h' := d_comp rho A e he 0 fun s => e.symm (w s)
        simp only [AddEquiv.apply_symm_apply] at h'
        funext g
        apply e.injective
        have h2 := (congrFun h' fun _ => g).symm.trans (congrFun h fun _ => g)
        rw [dn_zero] at h2
        exact h2
      · rintro ⟨m, h⟩
        refine ⟨fun _ => e m, IsLocallyConstant.const _, (d_comp rho A e he 0 fun _ => m).trans ?_⟩
        funext s
        rw [dn_zero]
        exact congrArg e (congrFun h (s 0)))
  refine ⟨e', fun z => ?_, fun z x h => he' z x (funext h)⟩
  obtain ⟨x, hx⟩ := hex z
  exact ⟨x, congrFun hx⟩

theorem gc2 : Sgc2 := by
  intro G _ _ _ R _ M _ _ _ _ rho A _ e he
  let φ : Z2 rho →+ ((Fin 2 → G) → A) :=
    AddMonoidHom.mk' (fun z s => e (z.1 (s 0, s 1))) (fun z z' => funext fun s => map_add e _ _)
  have hex : ∀ z, ∃ x : cocycles A 2, cochainOf A (cocycleι A 2 x) = φ z := fun z =>
    exists_coc A 2 _
      (lc_of_cont A e (z.2.1.comp ((continuous_apply 0).prodMk (continuous_apply 1)))) (by
      refine (d_comp rho A e he 2 fun s => z.1 (s 0, s 1)).trans ?_
      funext s
      rw [dn_two, z.2.2 (s 0) (s 1) (s 2)]
      exact map_zero e)
  have hv : ∀ s : Fin 1 → G, s = fun _ => s 0 := fun s => funext fun i => by
    rw [Subsingleton.elim i 0]
  have hv2 : ∀ s : Fin 2 → G, s = ![s 0, s 1] := fun s => funext fun i => by
    fin_cases i <;> rfl
  obtain ⟨e', he'⟩ := core_quot A ((B2 rho).comap (Z2 rho).subtype) 2 φ hex
    (fun x => by
      have hx : cochainOf A (cocycleι A 2 x) =
          fun s => e (e.symm (cochainOf A (cocycleι A 2 x) ![s 0, s 1])) := by
        funext s
        rw [e.apply_symm_apply, ← hv2]
      refine ⟨⟨fun p => e.symm (cochainOf A (cocycleι A 2 x) ![p.1, p.2]),
        (cont_of_lc A e (isLocallyConstant_cochainOf _)).comp
          (continuous_pi fun i => by
            fin_cases i
            · exact continuous_fst
            · exact continuous_snd), fun g g' g'' => ?_⟩, hx⟩
      have h := d_comp rho A e he 2 fun s => e.symm (cochainOf A (cocycleι A 2 x) ![s 0, s 1])
      rw [← hx, d_cocycleι] at h
      have h' := congrFun h ![g, g', g'']
      rw [dn_two rho (fun p => e.symm (cochainOf A (cocycleι A 2 x) ![p.1, p.2]))] at h'
      exact e.map_eq_zero_iff.1 h'.symm)
    (fun z x hx => by
      rw [pi_succ_eq_zero_iff, hx]
      constructor
      · rintro ⟨w, hw, h⟩
        refine ⟨fun g => e.symm (w fun _ => g),
          (cont_of_lc A e hw).comp (continuous_pi fun _ => continuous_id), ?_⟩
        have hw' : w = fun s => e (e.symm (w fun _ => s 0)) := by
          funext s
          rw [e.apply_symm_apply, ← hv]
        have h' := d_comp rho A e he 1 fun s => e.symm (w fun _ => s 0)
        rw [← hw'] at h'
        funext p
        apply e.injective
        have h2 := (congrFun h' ![p.1, p.2]).symm.trans (congrFun h ![p.1, p.2])
        rw [dn_one rho (fun g => e.symm (w fun _ => g))] at h2
        exact h2
      · rintro ⟨c, hc, h⟩
        refine ⟨fun s => e (c (s 0)), lc_of_cont A e (Continuous.comp hc (continuous_apply 0)),
          (d_comp rho A e he 1 fun s => c (s 0)).trans ?_⟩
        funext s
        rw [dn_one]
        exact congrArg e (congrFun h (s 0, s 1)))
  refine ⟨e', fun z => ?_, fun z x h => he' z x (funext h)⟩
  obtain ⟨x, hx⟩ := hex z
  exact ⟨x, congrFun hx⟩

end CompanionTheory.LocalTateOrthogonality.Gcoh
end

-- bundled from CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohTateB
section
open CategoryTheory MonoidalCategory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel

namespace CompanionTheory.LocalTateOrthogonality.Gcoh

attribute [local instance 2000] Rep.hV2

section Core

variable {n : ℕ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M M' P : Type} [AddCommGroup M] [Module (ZMod n) M] [AddCommGroup M'] [Module (ZMod n) M']
  [AddCommGroup P] [Module (ZMod n) P]
  [TopologicalSpace M] [DiscreteTopology M] [TopologicalSpace M'] [DiscreteTopology M']
  [TopologicalSpace P] [DiscreteTopology P]
  (rho : Representation (ZMod n) G M) (rho' : Representation (ZMod n) G M')
  (rhoP : Representation (ZMod n) G P) (b : M →ₗ[ZMod n] M' →ₗ[ZMod n] P)
  (hbc : Continuous fun p : M × M' => b p.1 p.2)
  (hbe : ∀ g x y, b (rho g x) (rho' g y) = rhoP g (b x y))
  (A D : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep A] [IsDiscreteRep D]
  [IsDiscreteRep (dualRep D A)]
  (eA : M ≃+ A.V) (hA : ∀ g m, eA (rho g m) = A.ρ g (eA m))
  (eD : P ≃+ D.V) (hD : ∀ g m, eD (rhoP g m) = D.ρ g (eD m))
  (eB : M' ≃+ (dualRep D A).V) (hB : ∀ g y, eB (rho' g y) = (dualRep D A).ρ g (eB y))
  (hev : ∀ x y, (eB y : A →ₗ[ULift.{0} ℤ] D) (eA x) = eD (b x y))
  (t : cohomology D 2 ≃+ ZMod n)

omit [DiscreteTopology M] in
include hA in
theorem exists_cocycle_zero [IsTopologicalAddGroup M] [ContinuousConstSMul (ZMod n) M]
    (m : H0 rho) :
    ∃ x : cocycles A 0, ∀ s, cochainOf (A := A) (cocycleι (A := A) (p := 0) x) s = eA m.1 := by
  obtain ⟨z, -, hz⟩ := exists_cocycle_H0Iso_inv A ⟨eA m.1, fun g => by
    rw [← hA, (mem_riemannRochSpace_iff_regularAt_everywhere rho m.1).1 m.2 g]⟩
  exact ⟨z, fun s => by rw [hz]⟩

include hA hD hB hev in
theorem cup_product_H0_H2_bijective (h0 : Sgc0) (h2 : Sgc2)
    (hd : Function.Bijective (dualityMap D (rfl : 0 + 2 = 2) t.toAddMonoidHom A)) :
    Function.Bijective (cupProductH0H2 rho rho' rhoP b hbc hbe) := by
  obtain ⟨e0, he0⟩ := h0 G (ZMod n) M rho A eA hA
  obtain ⟨e2, hex, he2⟩ := h2 G (ZMod n) M' rho' (dualRep D A) eB hB
  obtain ⟨eP, -, heP⟩ := h2 G (ZMod n) P rhoP D eD hD
  refine bij_transport _ _ e0 e2 (eP.trans t) (fun m y => ?_) hd
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨x, hx⟩ := exists_cocycle_zero rho A eA hA m
  obtain ⟨w, hw⟩ := hex z
  rw [he0 m x hx, he2 z w hw, dualityMap_apply, cupPairing_cohomologyπ, AddEquiv.trans_apply]
  refine congrArg t (heP (cupCocycleH0Z2 rho rho' rhoP b hbc hbe m z) _ fun s => ?_)
  rw [cochainOf_cocycleι_cyclesMap_cupCocycles, hx, hw, ← hB]
  refine (evalPairing_tmul D A _ _).trans ?_
  rw [hev, cupCocycleH0Z2_apply]
  congr 2
  simp [Fin.partialProd]

include hA hD hB hev in
theorem cup_product_H2_H0_bijective (h0 : Sgc0) (h2 : Sgc2)
    (hd : Function.Bijective (dualityMap D (rfl : 2 + 0 = 2) t.toAddMonoidHom A)) :
    Function.Bijective (cupProductH2H0 rho rho' rhoP b hbc hbe) := by
  obtain ⟨e0, he0⟩ := h0 G (ZMod n) M' rho' (dualRep D A) eB hB
  obtain ⟨e2, hex, he2⟩ := h2 G (ZMod n) M rho A eA hA
  obtain ⟨eP, -, heP⟩ := h2 G (ZMod n) P rhoP D eD hD
  refine bij_transport _ _ e2 e0 (eP.trans t) (fun y m => ?_) hd
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨x, hx⟩ := exists_cocycle_zero rho' (dualRep D A) eB hB m
  obtain ⟨w, hw⟩ := hex z
  rw [he0 m x hx, he2 z w hw, dualityMap_apply, cupPairing_cohomologyπ, AddEquiv.trans_apply]
  refine congrArg t (heP (cupCocycleZ2H0 rho rho' rhoP b hbc hbe z m) _ fun s => ?_)
  rw [cochainOf_cocycleι_cyclesMap_cupCocycles, hx, hw, ← hB]
  refine (evalPairing_tmul D A _ _).trans ?_
  rw [hev, cupCocycleZ2H0_apply, (mem_riemannRochSpace_iff_regularAt_everywhere rho' m.1).1 m.2]

include hA hD hB hev in
theorem cup_product_H1_H1_bijective (h1 : Sgc1) (h2 : Sgc2) (hc : ContAction rho')
    (hd : Function.Bijective (dualityMap D (rfl : 1 + 1 = 2) t.toAddMonoidHom A)) :
    Function.Bijective (cupProductH1H1 rho rho' rhoP b hbc hbe hc) := by
  obtain ⟨e1, hex1, he1⟩ := h1 G (ZMod n) M rho A eA hA
  obtain ⟨e1', hex1', he1'⟩ := h1 G (ZMod n) M' rho' (dualRep D A) eB hB
  obtain ⟨eP, -, heP⟩ := h2 G (ZMod n) P rhoP D eD hD
  refine bij_transport _ _ e1 e1' (eP.trans t) (fun y y' => ?_) hd
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨z', rfl⟩ := Submodule.Quotient.mk_surjective _ y'
  obtain ⟨x, hx⟩ := hex1 z
  obtain ⟨w, hw⟩ := hex1' z'
  rw [he1 z x hx, he1' z' w hw, dualityMap_apply, cupPairing_cohomologyπ, AddEquiv.trans_apply]
  refine congrArg t (heP (cupCocycleZ1Z1 rho rho' rhoP b hbc hbe hc z z') _ fun s => ?_)
  rw [cochainOf_cocycleι_cyclesMap_cupCocycles, hx, hw, ← hB]
  refine (evalPairing_tmul D A _ _).trans ?_
  rw [hev, cupCocycleZ1Z1_apply]
  congr 2
  simp [Fin.partialProd]

end Core

end CompanionTheory.LocalTateOrthogonality.Gcoh
end

