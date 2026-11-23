module

public import Mathlib
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDefs
public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.Bundle0004
public import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateNineTermGs

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.ResH2BijectiveOfInverse
section
noncomputable section

open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem resH2_bijective_of_inverse {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {R M : Type} [CommRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    (rho : Representation R G M) (ψ : H →* G) (hψ : Continuous ψ)
    (χ : G →* H) (hχ : Continuous χ) (h1 : ∀ g, ψ (χ g) = g) (h2 : ∀ h, χ (ψ h) = h) :
    Function.Bijective (resH2 rho ψ hψ) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H z =>
      rw [Submodule.Quotient.mk_eq_zero]
      rw [resH2, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
      obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem _ _).1 hx
      refine (separated_dvr_second_cohomology_mem _ _).2 ⟨c ∘ χ, hc.comp hχ, ?_⟩
      funext p
      have e := congrFun hcf (χ p.1, χ p.2)
      simp only [Submodule.coe_subtype] at e ⊢
      change _ = z.1 (ψ (χ p.1), ψ (χ p.2)) at e
      rw [h1, h1] at e
      rw [← e]
      simp [d1, h1]
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H z =>
      refine ⟨Submodule.Quotient.mk ⟨fun p => z.1 (χ p.1, χ p.2),
        z.2.1.comp (hχ.prodMap hχ), fun g h k => ?_⟩, ?_⟩
      · have e := z.2.2 (χ g) (χ h) (χ k)
        simp only [map_mul]
        change rho (ψ (χ g)) _ - _ + _ - _ = 0 at e
        rw [h1] at e
        exact e
      · rw [resH2, Submodule.mapQ_apply]
        congr 1
        apply Subtype.ext
        funext p
        change z.1 (χ (ψ p.1), χ (ψ p.2)) = z.1 p
        rw [h2, h2]

theorem resCmp2B {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (θ : G ≃ₜ* H) {ι : Type} {Lv Hv : ι → Type}
    [∀ v, Group (Lv v)] [∀ v, TopologicalSpace (Lv v)] [∀ v, IsTopologicalGroup (Lv v)]
    [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)] [∀ v, IsTopologicalGroup (Hv v)]
    (lam : ∀ v, Lv v →* G) (hlam : ∀ v, Continuous (lam v)) (φ : ∀ v, Hv v →ₜ* H)
    (ev : ∀ v, Hv v ≃* Lv v) (hev1 : ∀ v, Continuous (ev v)) (hev2 : ∀ v, Continuous (ev v).symm)
    (hev : ∀ v σ, θ (lam v (ev v σ)) = φ v σ) {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [DiscreteTopology M] (rho : Representation R G M) (hc : ContAction rho)
    (A : Rep.{0} (ULift.{0} ℤ) H) [IsDiscreteRep A] (eM : M ≃+ A.V)
    (hM : ∀ g m, eM (rho g m) = A.ρ (θ g) (eM m)) :
    ∃ (E : H2 rho ≃+ cohomology A 2)
      (Ev : ∀ v, H2 (rho.comp (lam v)) ≃+ cohomology (Rep.res (φ v).toMonoidHom A) 2),
      ∀ v x, Ev v (resH2 rho (lam v) (hlam v) x) = ptRes φ A v 2 (E x) := by
  have hθs : Continuous (θ.symm : H ≃* G).toMonoidHom := θ.symm.continuous
  let rho' : Representation R H M := rho.comp (θ.symm : H ≃* G).toMonoidHom
  have hM' : ∀ h m, eM (rho' h m) = A.ρ h (eM m) := fun h m => by
    show eM (rho (θ.symm h) m) = _
    rw [hM]
    exact congrArg (fun t => A.ρ t (eM m)) (θ.apply_symm_apply h)
  obtain ⟨e2, he2a, he2b⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc2 H R M rho' A eM hM'
  have bij := resH2_bijective_of_inverse rho (θ.symm : H ≃* G).toMonoidHom hθs
    (θ : G ≃* H).toMonoidHom θ.continuous (fun g => θ.symm_apply_apply g)
    (fun h => θ.apply_symm_apply h)
  let r2 : H2 rho ≃ₗ[R] H2 rho' := LinearEquiv.ofBijective _ bij
  have hloc : ∀ v, ∀ σ m, eM (((rho.comp (lam v)).comp (ev v).toMonoidHom) σ m) =
      (Rep.res (φ v).toMonoidHom A).ρ σ (eM m) := fun v σ m => by
    show eM (rho (lam v (ev v σ)) m) = A.ρ (φ v σ) (eM m)
    rw [hM, hev]
  choose ev2 hev2a hev2b using fun v => PositivityTheory.LocalTateOrthogonality.Gcoh.gc2 (Hv v) R M
    ((rho.comp (lam v)).comp (ev v).toMonoidHom) (Rep.res (φ v).toMonoidHom A) eM (hloc v)
  have bijv := fun v => resH2_bijective_of_inverse (rho.comp (lam v)) (ev v).toMonoidHom (hev1 v)
    (ev v).symm.toMonoidHom (hev2 v) (fun g => (ev v).apply_symm_apply g)
    (fun h => (ev v).symm_apply_apply h)
  let rv : ∀ v, H2 (rho.comp (lam v)) ≃ₗ[R] H2 ((rho.comp (lam v)).comp (ev v).toMonoidHom) :=
    fun v => LinearEquiv.ofBijective _ (bijv v)
  refine ⟨r2.toAddEquiv.trans e2, fun v => (rv v).toAddEquiv.trans (ev2 v), fun v x => ?_⟩
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    obtain ⟨y, hy⟩ := he2a (restrictCocycles2 rho (θ.symm : H ≃* G).toMonoidHom hθs z)
    have hE : e2 (r2 (Submodule.Quotient.mk z)) = cohomologyπ A 2 y := he2b _ y hy
    show ev2 v (rv v (resH2 rho (lam v) (hlam v) (Submodule.Quotient.mk z))) =
      ptRes φ A v 2 (e2 (r2 (Submodule.Quotient.mk z)))
    rw [hE]
    have hP : ptRes φ A v 2 (cohomologyπ A 2 y) =
        cohomologyπ _ 2 (cocyclesMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (𝟙 _) 2 y) := by
      unfold ptRes
      exact congrArg (fun f => f.hom y) (cohomologyπ_cohomologyMapAlong (φ v).toMonoidHom
        (continuous_toMonoidHom (φ v)) (𝟙 _) 2)
    rw [hP]
    apply hev2b v
    intro s
    rw [cochainOf_cocycleι_cocyclesMapAlong]
    dsimp only
    rw [hy]
    change eM (z.1 (θ.symm (φ v (s 0)), θ.symm (φ v (s 1)))) =
      eM (z.1 (lam v (ev v (s 0)), lam v (ev v (s 1))))
    rw [← hev, ← hev]
    exact congrArg (fun t => eM (z.1 t))
      (Prod.ext (θ.symm_apply_apply _) (θ.symm_apply_apply _))

end PositivityTheory.Lit1.PTN
end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.RestrictionSquareDegreeOne
section
noncomputable section

open CategoryTheory MonoidalCategory TensorProduct GroundTheory.ProfCoh ReciprocityTheory.Gal

namespace PositivityTheory.Lit1.PTN

theorem cupPairing_swap_degree_one {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {A B C : Rep.{0} (ULift.{0} ℤ) Γ} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
    (μ : A ⊗ B ⟶ C) (x : cohomology A 1) (y : cohomology B 1) :
    cupPairing μ (rfl : 1 + 1 = 2) x y = - cupPairing ((β_ B A).hom ≫ μ) (rfl : 1 + 1 = 2) y x := by
  rw [cupPairing_apply, cupPairing_apply, cohomologyMap_comp, ConcreteCategory.comp_apply,
    cohomologyMap_braiding_cup (rfl : 1 + 1 = 2) (rfl : 1 + 1 = 2) y x]
  have h1 : ((-1 : ULift.{0} ℤ) ^ (1 * 1)) = -1 := by simp
  rw [h1, neg_one_smul, map_neg, neg_neg]

attribute [local instance 2000] Rep.hV2

theorem transfer_cup_degree_one_one {Lv Hv : Type} [Group Lv] [TopologicalSpace Lv] [IsTopologicalGroup Lv]
    [Group Hv] [TopologicalSpace Hv] [IsTopologicalGroup Hv] (ev : Hv ≃* Lv)
    (hevc : Continuous ev.toMonoidHom) {R : Type} [CommRing R] {M M' P : Type}
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [DiscreteTopology M']
    [AddCommGroup P] [Module R P] [TopologicalSpace P] [DiscreteTopology P]
    (rho : Representation R Lv M) (rho' : Representation R Lv M') (rhoP : Representation R Lv P)
    (b : M →ₗ[R] M' →ₗ[R] P) (hb : Continuous fun p : M × M' => b p.1 p.2)
    (hbe : ∀ g x y, b (rho g x) (rho' g y) = rhoP g (b x y)) (hc : ContAction rho')
    (A B C : Rep.{0} (ULift.{0} ℤ) Hv) [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
    (eA : M ≃+ A.V) (eB : M' ≃+ B.V)
    (heA : ∀ σ m, eA (rho (ev σ) m) = A.ρ σ (eA m))
    (heB : ∀ σ m, eB (rho' (ev σ) m) = B.ρ σ (eB m))
    (μ : A ⊗ B ⟶ C) (rel : P → C.V → Prop)
    (hbμ : ∀ x y, rel (b x y) (μ.hom (eA x ⊗ₜ[ULift.{0} ℤ] eB y)))
    (E : H1 rho ≃+ cohomology A 1)
    (hE : ∀ (z : ↥(Z1 rho)) (x : cocycles A 1),
      (∀ s, cochainOf A (cocycleι A 1 x) s = eA (z.1 (ev (s 0)))) →
        E (Submodule.Quotient.mk z) = cohomologyπ A 1 x)
    (E' : H1 rho' ≃+ cohomology B 1)
    (hE' : ∀ (z : ↥(Z1 rho')) (x : cocycles B 1),
      (∀ s, cochainOf B (cocycleι B 1 x) s = eB (z.1 (ev (s 0)))) →
        E' (Submodule.Quotient.mk z) = cohomologyπ B 1 x)
    {Q : Type} [AddCommGroup Q] (jp : H2 rhoP →+ Q) (J : cohomology C 2 →+ Q)
    (hJ : ∀ (W : ↥(Z2 rhoP)) (x : cocycles C 2),
      (∀ s, rel (W.1 (ev (s 0), ev (s 1))) (cochainOf C (cocycleι C 2 x) s)) →
        jp (Submodule.Quotient.mk W) = - J (cohomologyπ C 2 x))
    (z : ↥(Z1 rho)) (z' : ↥(Z1 rho')) :
    jp (cupProductH1H1 rho rho' rhoP b hb hbe hc (Submodule.Quotient.mk z) (Submodule.Quotient.mk z')) =
      - J (cupPairing μ (rfl : 1 + 1 = 2) (E (Submodule.Quotient.mk z)) (E' (Submodule.Quotient.mk z'))) := by
  obtain ⟨e1, he1a, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc1 Hv R M (rho.comp ev.toMonoidHom) A eA heA
  obtain ⟨x, hx⟩ := he1a (restrictCocycles1 rho ev.toMonoidHom hevc z)
  obtain ⟨e1', he1b, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc1 Hv R M' (rho'.comp ev.toMonoidHom) B eB heB
  obtain ⟨x', hx'⟩ := he1b (restrictCocycles1 rho' ev.toMonoidHom hevc z')
  have hEa : E (Submodule.Quotient.mk z) = cohomologyπ A 1 x := hE z x (fun s => hx s)
  have hEb : E' (Submodule.Quotient.mk z') = cohomologyπ B 1 x' := hE' z' x' (fun s => hx' s)
  have hcup : cupProductH1H1 rho rho' rhoP b hb hbe hc (Submodule.Quotient.mk z) (Submodule.Quotient.mk z') =
      Submodule.Quotient.mk (cupCocycleZ1Z1 rho rho' rhoP b hb hbe hc z z') := rfl
  rw [hEa, hEb, cupPairing_cohomologyπ, hcup]
  refine hJ _ _ (fun s => ?_)
  rw [cochainOf_cocycleι_cyclesMap_cupCocycles, hx, hx']
  have h1 : Fin.partialProd s ⟨1, by omega⟩ = s 0 := by
    show Fin.partialProd s (Fin.succ 0) = s 0
    rw [Fin.partialProd_succ]
    show Fin.partialProd s 0 * s 0 = s 0
    rw [Fin.partialProd_zero, one_mul]
  rw [h1]
  have := hbμ (z.1 (ev (s 0))) (rho' (ev (s 0)) (z'.1 (ev (s 1))))
  rw [heB] at this
  exact this

theorem transfer_cup_one_one_general {Lv Hv : Type} [Group Lv] [TopologicalSpace Lv] [IsTopologicalGroup Lv]
    [Group Hv] [TopologicalSpace Hv] [IsTopologicalGroup Hv] [CompactSpace Hv]
    [TotallyDisconnectedSpace Hv] (ev : Hv ≃* Lv)
    (hevc : Continuous ev.toMonoidHom) {R : Type} [CommRing R] {M M' P : Type}
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [DiscreteTopology M']
    [AddCommGroup P] [Module R P] [TopologicalSpace P] [DiscreteTopology P]
    (rho : Representation R Lv M) (rho' : Representation R Lv M') (rhoP : Representation R Lv P)
    (b : M →ₗ[R] M' →ₗ[R] P) (hb : Continuous fun p : M × M' => b p.1 p.2)
    (hbe : ∀ g x y, b (rho g x) (rho' g y) = rhoP g (b x y)) (hc : ContAction rho')
    (A B C : Rep.{0} (ULift.{0} ℤ) Hv) [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
    (eA : M ≃+ A.V) (eB : M' ≃+ B.V)
    (heA : ∀ σ m, eA (rho (ev σ) m) = A.ρ σ (eA m))
    (heB : ∀ σ m, eB (rho' (ev σ) m) = B.ρ σ (eB m))
    (μ' : B ⊗ A ⟶ C) (rel : P → C.V → Prop)
    (hbμ : ∀ y x, rel (b x y) (μ'.hom (eB y ⊗ₜ[ULift.{0} ℤ] eA x)))
    (E : H1 rho ≃+ cohomology A 1)
    (hE : ∀ (z : ↥(Z1 rho)) (x : cocycles A 1),
      (∀ s, cochainOf A (cocycleι A 1 x) s = eA (z.1 (ev (s 0)))) →
        E (Submodule.Quotient.mk z) = cohomologyπ A 1 x)
    (E' : H1 rho' ≃+ cohomology B 1)
    (hE' : ∀ (z : ↥(Z1 rho')) (x : cocycles B 1),
      (∀ s, cochainOf B (cocycleι B 1 x) s = eB (z.1 (ev (s 0)))) →
        E' (Submodule.Quotient.mk z) = cohomologyπ B 1 x)
    {Q : Type} [AddCommGroup Q] (jp : H2 rhoP →+ Q) (J : cohomology C 2 →+ Q)
    (hJ : ∀ (W : ↥(Z2 rhoP)) (x : cocycles C 2),
      (∀ s, rel (W.1 (ev (s 0), ev (s 1))) (cochainOf C (cocycleι C 2 x) s)) →
        jp (Submodule.Quotient.mk W) = - J (cohomologyπ C 2 x))
    (a : H1 rho') (b' : H1 rho) :
    jp (cupProductH1H1 rho rho' rhoP b hb hbe hc b' a) = J (cupPairing μ' (rfl : 1 + 1 = 2) (E' a) (E b')) := by
  induction a using Submodule.Quotient.induction_on with
  | H z' => ?_
  induction b' using Submodule.Quotient.induction_on with
  | H z => ?_
  have hbμ' : ∀ x y, rel (b x y) (((β_ A B).hom ≫ μ').hom (eA x ⊗ₜ[ULift.{0} ℤ] eB y)) :=
    fun x y => hbμ y x
  rw [cupPairing_swap_degree_one μ', map_neg,
    transfer_cup_degree_one_one ev hevc rho rho' rhoP b hb hbe hc A B C eA eB heA heB ((β_ A B).hom ≫ μ') rel hbμ'
      E hE E' hE' jp J hJ z z']

end PositivityTheory.Lit1.PTN
end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.TransferCupDegreeZeroTwo
section
noncomputable section

open CategoryTheory MonoidalCategory TensorProduct GroundTheory.ProfCoh ReciprocityTheory.Gal

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem transfer_cup_degree_zero_two {Lv Hv : Type} [Group Lv] [TopologicalSpace Lv] [IsTopologicalGroup Lv]
    [Group Hv] [TopologicalSpace Hv] [IsTopologicalGroup Hv] (ev : Hv ≃* Lv)
    (hevc : Continuous ev.toMonoidHom) {R : Type} [CommRing R] {M M' P : Type}
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [DiscreteTopology M']
    [AddCommGroup P] [Module R P] [TopologicalSpace P] [DiscreteTopology P]
    (rho : Representation R Lv M) (rho' : Representation R Lv M') (rhoP : Representation R Lv P)
    (b : M →ₗ[R] M' →ₗ[R] P) (hb : Continuous fun p : M × M' => b p.1 p.2)
    (hbe : ∀ g x y, b (rho g x) (rho' g y) = rhoP g (b x y))
    (A B C : Rep.{0} (ULift.{0} ℤ) Hv) [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
    (eA : M ≃+ A.V) (eB : M' ≃+ B.V)
    (heA : ∀ σ m, eA (rho (ev σ) m) = A.ρ σ (eA m))
    (heB : ∀ σ m, eB (rho' (ev σ) m) = B.ρ σ (eB m))
    (μ : A ⊗ B ⟶ C) (rel : P → C.V → Prop)
    (hbμ : ∀ x y, rel (b x y) (μ.hom (eA x ⊗ₜ[ULift.{0} ℤ] eB y)))
    (E : ↥(H0 rho) ≃+ cohomology A 0)
    (hE : ∀ (z : ↥(H0 rho)) (x : cocycles A 0),
      (∀ s, cochainOf A (cocycleι A 0 x) s = eA z.1) → E z = cohomologyπ A 0 x)
    (E' : H2 rho' ≃+ cohomology B 2)
    (hE' : ∀ (z : ↥(Z2 rho')) (x : cocycles B 2),
      (∀ s, cochainOf B (cocycleι B 2 x) s = eB (z.1 (ev (s 0), ev (s 1)))) →
        E' (Submodule.Quotient.mk z) = cohomologyπ B 2 x)
    {Q : Type} [AddCommGroup Q] (jp : H2 rhoP →+ Q) (J : cohomology C 2 →+ Q)
    (hJ : ∀ (W : ↥(Z2 rhoP)) (x : cocycles C 2),
      (∀ s, rel (W.1 (ev (s 0), ev (s 1))) (cochainOf C (cocycleι C 2 x) s)) →
        jp (Submodule.Quotient.mk W) = - J (cohomologyπ C 2 x))
    (m : ↥(H0 rho)) (z : ↥(Z2 rho')) :
    jp (cupProductH0H2 rho rho' rhoP b hb hbe m (Submodule.Quotient.mk z)) =
      - J (cupPairing μ (rfl : 0 + 2 = 2) (E m) (E' (Submodule.Quotient.mk z))) := by
  obtain ⟨e2, he2a, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc2 Hv R M' (rho'.comp ev.toMonoidHom) B eB heB
  obtain ⟨x2, hx2⟩ := he2a (restrictCocycles2 rho' ev.toMonoidHom hevc z)
  have hm : ∀ σ, (rho.comp ev.toMonoidHom) σ m.1 = m.1 := fun σ => (mem_riemannRochSpace_iff_regularAt_everywhere rho m.1).1 m.2 (ev σ)
  obtain ⟨x0, hx0⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.exists_coc A 0 (fun _ => eA m.1) (IsLocallyConstant.const _)
    (by
      refine (PositivityTheory.LocalTateOrthogonality.Gcoh.d_comp (rho.comp ev.toMonoidHom) A eA heA 0 fun _ => m.1).trans ?_
      funext s
      rw [PositivityTheory.LocalTateOrthogonality.Gcoh.dn_zero, hm (s 0), sub_self]
      exact map_zero eA)
  have hEm : E m = cohomologyπ A 0 x0 := hE m x0 (fun s => congrFun hx0 s)
  have hEz : E' (Submodule.Quotient.mk z) = cohomologyπ B 2 x2 := hE' z x2 (fun s => hx2 s)
  rw [hEm, hEz, cupPairing_cohomologyπ]
  refine hJ (cupCocycleH0Z2 rho rho' rhoP b hb hbe m z) _ (fun s => ?_)
  rw [cochainOf_cocycleι_cyclesMap_cupCocycles]
  have h0 : Fin.partialProd s ⟨0, by omega⟩ = 1 := Fin.partialProd_zero s
  rw [h0, map_one]
  rw [show (cochainOf _ (cocycleι _ 0 x0) fun i : Fin 0 => s ⟨i, by omega⟩) = eA m.1 from
    congrFun hx0 _]
  rw [show (cochainOf _ (cocycleι _ 2 x2) fun j : Fin 2 => s ⟨0 + j, by omega⟩) =
    eB (z.1 (ev (s 0), ev (s 1))) from by rw [hx2]; rfl]
  exact hbμ _ _

theorem hloc2 {G D L H : Type} [Group G] [Group D] [Group L] [Group H] {R M : Type} [CommRing R]
    [AddCommGroup M] [Module R M] (ρ : Representation R G M) (φ : D →* G) (ev : L ≃* D) (e : G → H)
    (A : Rep.{0} (ULift.{0} ℤ) H) (eM : M ≃+ A.V)
    (hM : ∀ g m, eM (ρ g m) = A.ρ (e g) (eM m)) (F : L →* H) (hev : ∀ σ, e (φ (ev σ)) = F σ) :
    ∀ σ m, eM ((ρ.comp φ) (ev σ) m) = (Rep.res F A).ρ σ (eM m) := by
  intro σ m
  rw [MonoidHom.comp_apply, hM, hev]
  rfl

end PositivityTheory.Lit1.PTN
end
end

