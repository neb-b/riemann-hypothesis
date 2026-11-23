module

public import Mathlib

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL6.CoordMapInjective
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Classical

section Induced

@[instance_reducible] def productMulActionFirstFactor (G Y : Type) [CommGroup G] : MulAction G (G × Y) where
  smul g x := (g * x.1, x.2)
  one_smul x := by
    show ((1 : G) * x.1, x.2) = x
    rw [one_mul]
  mul_smul g h x := by
    show ((g * h) * x.1, x.2) = (g * (h * x.1), x.2)
    rw [mul_assoc]

variable {G : Type} [CommGroup G] [Fintype G] {Cl : Type} [Fintype Cl] [MulAction G Cl] {d : ℕ}
  {M : Type} [AddCommGroup M] [Module ℂ M]

def t2xE (Φ : M ≃ₗ[ℂ] (Cl → Fin d → ℂ)) (ρ : G →* (M →ₗ[ℂ] M)) :
    M →ₗ[ℂ] (G × (MulAction.orbitRel.Quotient G Cl × Fin d) → ℂ) where
  toFun φ x := Φ (ρ x.1 φ) (Quotient.out x.2.1) x.2.2
  map_add' φ ψ := by funext x; simp
  map_smul' a φ := by funext x; simp

theorem coordMap_intertwines (Φ : M ≃ₗ[ℂ] (Cl → Fin d → ℂ)) (ρ : G →* (M →ₗ[ℂ] M)) (g : G) (φ : M)
    (x : G × (MulAction.orbitRel.Quotient G Cl × Fin d)) :
    t2xE Φ ρ (ρ g φ) x = t2xE Φ ρ φ (g * x.1, x.2) := by
  show Φ (ρ x.1 (ρ g φ)) (Quotient.out x.2.1) x.2.2 = Φ (ρ (g * x.1) φ) (Quotient.out x.2.1) x.2.2
  rw [mul_comm g x.1, map_mul]
  rfl

theorem exists_smul_out_eq (c : Cl) : ∃ g : G, g • Quotient.out (Quotient.mk (MulAction.orbitRel G Cl) c) = c := by
  have h := Quotient.mk_out (s := MulAction.orbitRel G Cl) c
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h)
  exact ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩

theorem t2xE_injective_of_monomial (Φ : M ≃ₗ[ℂ] (Cl → Fin d → ℂ)) (ρ : G →* (M →ₗ[ℂ] M))
    (hmono : ∀ (g : G) (c : Cl) (φ : M), Φ (ρ g φ) c = 0 → Φ φ (g • c) = 0) :
    Function.Injective (t2xE Φ ρ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro φ hE
  have h0 : ∀ (g : G) (q : MulAction.orbitRel.Quotient G Cl), Φ (ρ g φ) (Quotient.out q) = 0 :=
    fun g q => funext fun b => congrFun hE (g, q, b)
  have h1 : Φ φ = 0 := by
    funext c
    obtain ⟨g, hg⟩ := exists_smul_out_eq (G := G) c
    have := hmono g _ φ (h0 g (Quotient.mk (MulAction.orbitRel G Cl) c))
    rw [hg] at this
    exact this
  exact Φ.map_eq_zero_iff.1 h1

theorem card_mul_card_orbits (hfree : ∀ (g : G) (c : Cl), g • c = c → g = 1) :
    Fintype.card G * Fintype.card (MulAction.orbitRel.Quotient G Cl) = Fintype.card Cl := by
  rw [← Fintype.card_prod]
  refine Fintype.card_of_bijective (f := fun x : G × MulAction.orbitRel.Quotient G Cl => x.1 • Quotient.out x.2) ⟨?_, ?_⟩
  · rintro ⟨g, q⟩ ⟨g', q'⟩ h
    simp only at h
    have hq : ∀ (g0 : G) (q0 : MulAction.orbitRel.Quotient G Cl),
        (Quotient.mk (MulAction.orbitRel G Cl) (g0 • Quotient.out q0)) = q0 := by
      intro g0 q0
      conv_rhs => rw [← Quotient.out_eq q0]
      exact Quotient.sound (MulAction.orbitRel_apply.2 (MulAction.mem_orbit _ g0))
    have hqq : q = q' := by rw [← hq g q, ← hq g' q', h]
    subst hqq
    have h2 : (g'⁻¹ * g) • Quotient.out q = Quotient.out q := by rw [mul_smul, h, inv_smul_smul]
    have h3 := hfree _ _ h2
    rw [inv_mul_eq_one] at h3
    rw [h3]
  · intro c
    obtain ⟨g, hg⟩ := exists_smul_out_eq (G := G) c
    exact ⟨(g, _), hg⟩

theorem coordMap_bijective (Φ : M ≃ₗ[ℂ] (Cl → Fin d → ℂ)) (ρ : G →* (M →ₗ[ℂ] M))
    (hmono : ∀ (g : G) (c : Cl) (φ : M), Φ (ρ g φ) c = 0 → Φ φ (g • c) = 0)
    (hfree : ∀ (g : G) (c : Cl), g • c = c → g = 1) :
    Function.Bijective (t2xE Φ ρ) := by
  have : FiniteDimensional ℂ M := LinearEquiv.finiteDimensional Φ.symm
  have hinj := t2xE_injective_of_monomial Φ ρ hmono
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinj⟩
  rw [Φ.finrank_eq, Module.finrank_fintype_fun_eq_card, Module.finrank_pi_fintype]
  simp only [Module.finrank_fin_fun, Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_prod,
    Fintype.card_fin]
  rw [← card_mul_card_orbits hfree]
  ring

def orbitDecompositionLinearEquiv (Φ : M ≃ₗ[ℂ] (Cl → Fin d → ℂ)) (ρ : G →* (M →ₗ[ℂ] M))
    (hmono : ∀ (g : G) (c : Cl) (φ : M), Φ (ρ g φ) c = 0 → Φ φ (g • c) = 0)
    (hfree : ∀ (g : G) (c : Cl), g • c = c → g = 1) :
    M ≃ₗ[ℂ] (G × (MulAction.orbitRel.Quotient G Cl × Fin d) → ℂ) :=
  LinearEquiv.ofBijective (t2xE Φ ρ) (coordMap_bijective Φ ρ hmono hfree)

theorem t2xEquiv_apply (Φ : M ≃ₗ[ℂ] (Cl → Fin d → ℂ)) (ρ : G →* (M →ₗ[ℂ] M))
    (hmono : ∀ (g : G) (c : Cl) (φ : M), Φ (ρ g φ) c = 0 → Φ φ (g • c) = 0)
    (hfree : ∀ (g : G) (c : Cl), g • c = c → g = 1) (φ : M) :
    orbitDecompositionLinearEquiv Φ ρ hmono hfree φ = t2xE Φ ρ φ := rfl

end Induced

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL6.LinearIndependentProdRenameOfCard
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open MvPolynomial

variable {K : Type*} [Field K] {S₁ S₂ : Type*}

theorem sumAlgEquiv_rename_inl (a : MvPolynomial S₁ K) :
    sumAlgEquiv K S₁ S₂ (rename Sum.inl a) = map (C : K →+* MvPolynomial S₂ K) a := by
  have h := AlgHom.congr_fun (sumAlgEquiv_comp_rename_inl K S₁ S₂) a
  simpa [MvPolynomial.algebraMap_eq] using h

theorem sumAlgEquiv_rename_inr_eq_C' (b : MvPolynomial S₂ K) :
    sumAlgEquiv K S₁ S₂ (rename Sum.inr b) = C b := by
  have h := AlgHom.congr_fun (sumAlgEquiv_comp_rename_inr K S₁ S₂) b
  simpa [MvPolynomial.algebraMap_eq] using h

def mvPolynomialCoeffInFirstVariables (m : S₁ →₀ ℕ) : MvPolynomial (S₁ ⊕ S₂) K →ₗ[K] MvPolynomial S₂ K :=
  (lcoeff (MvPolynomial S₂ K) m).restrictScalars K ∘ₗ (sumAlgEquiv K S₁ S₂).toLinearMap

theorem leftCoeff_rename_mul (m : S₁ →₀ ℕ) (a : MvPolynomial S₁ K) (b : MvPolynomial S₂ K) :
    mvPolynomialCoeffInFirstVariables m (rename Sum.inl a * rename Sum.inr b) = AddMonoidAlgebra.coeff a m • b := by
  simp only [mvPolynomialCoeffInFirstVariables, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, LinearMap.restrictScalars_apply,
    lcoeff_apply, map_mul, sumAlgEquiv_rename_inl, sumAlgEquiv_rename_inr_eq_C']
  rw [mul_comm, coeff_C_mul, coeff_map, smul_eq_C_mul, mul_comm]

theorem linearIndependent_rename_mul {κ₁ κ₂ : Type*} (v : κ₁ → MvPolynomial S₁ K) (w : κ₂ → MvPolynomial S₂ K)
    (hv : LinearIndependent K v) (hw : LinearIndependent K w) :
    LinearIndependent K fun p : κ₁ × κ₂ => rename Sum.inl (v p.1) * rename Sum.inr (w p.2) := by
  have h := (hw.tmul_of_isDomain hv).comp Prod.swap Prod.swap_injective
  let e : TensorProduct K (MvPolynomial S₂ K) (MvPolynomial S₁ K) ≃ₗ[K] MvPolynomial (S₁ ⊕ S₂) K :=
    ((algebraTensorAlgEquiv K (MvPolynomial S₂ K) (σ := S₁)).restrictScalars K).toLinearEquiv.trans
      (sumAlgEquiv K S₁ S₂).symm.toLinearEquiv
  have he : ∀ p : κ₁ × κ₂, e (TensorProduct.tmul K (w p.2) (v p.1)) =
      rename Sum.inl (v p.1) * rename Sum.inr (w p.2) := by
    intro p
    apply (sumAlgEquiv K S₁ S₂).injective
    simp [e, algebraTensorAlgEquiv_tmul, sumAlgEquiv_rename_inl, sumAlgEquiv_rename_inr_eq_C', smul_eq_C_mul, MvPolynomial.algebraMap_eq,
      mul_comm]
  have h2 := h.map' e.toLinearMap e.ker
  simpa only [Function.comp_def, Prod.fst_swap, Prod.snd_swap, LinearEquiv.coe_coe, he] using h2

def sumComplementToProduct {ι σ : Type} (i : ι) : σ ⊕ ({j // j ≠ i} × σ) → ι × σ :=
  Sum.elim (fun x => (i, x)) (fun p => (p.1.1, p.2))

theorem splitIndex_injective {ι σ : Type} (i : ι) : Function.Injective (sumComplementToProduct (σ := σ) i) := by
  intro x y h
  rcases x with x | ⟨⟨j, hj⟩, x⟩ <;> rcases y with y | ⟨⟨j', hj'⟩, y⟩ <;>
    simp only [sumComplementToProduct, Sum.elim_inl, Sum.elim_inr, Prod.mk.injEq] at h
  all_goals first
    | exact absurd h.1.symm hj'
    | exact absurd h.1 hj
    | simp_all

theorem linearIndependent_prod_rename_of_card (n : ℕ) : ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n →
    ∀ {σ : Type} (κ : ι → Type) (b : ∀ τ, κ τ → MvPolynomial σ K), (∀ τ, LinearIndependent K (b τ)) →
    LinearIndependent K (fun g : (∀ τ, κ τ) => ∏ τ, rename (Prod.mk τ) (b τ (g τ))) := by
  induction n with
  | zero =>
    intro ι _ _ hι σ κ b hb
    haveI : IsEmpty ι := Fintype.card_eq_zero_iff.1 hι
    haveI : Unique (∀ τ, κ τ) := Pi.uniqueOfIsEmpty κ
    rw [linearIndependent_unique_iff]
    simp
  | succ n ih =>
    intro ι _ _ hι σ κ b hb
    obtain ⟨τ₀⟩ : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
    have hcard : Fintype.card {τ // τ ≠ τ₀} = n := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, hι]; omega
    have hW := ih {τ // τ ≠ τ₀} hcard (fun τ => κ τ.1) (fun τ => b τ.1) (fun τ => hb τ.1)
    have hP := linearIndependent_rename_mul (b τ₀) _ (hb τ₀) hW
    have hR := hP.map' (rename (sumComplementToProduct (σ := σ) τ₀)).toLinearMap
      (LinearMap.ker_eq_bot.2 (rename_injective _ (splitIndex_injective τ₀)))
    have h2 := hR.comp (Equiv.piSplitAt τ₀ κ) (Equiv.piSplitAt τ₀ κ).injective
    have key : ∀ g : (∀ τ, κ τ), ∏ τ, rename (Prod.mk τ) (b τ (g τ)) =
        rename (sumComplementToProduct (σ := σ) τ₀) (rename Sum.inl (b τ₀ (g τ₀)) *
          rename Sum.inr (∏ τ : {τ // τ ≠ τ₀}, rename (Prod.mk τ) (b τ.1 (g τ.1)))) := by
      intro g
      simp only [map_mul, map_prod, rename_rename]
      rw [Fintype.prod_eq_mul_prod_subtype_ne _ τ₀]
      rfl
    have hfun : (fun g : (∀ τ, κ τ) => ∏ τ, rename (Prod.mk τ) (b τ (g τ))) =
        ((rename (sumComplementToProduct (σ := σ) τ₀)).toLinearMap ∘ (fun p : κ τ₀ × (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) =>
          rename Sum.inl (b τ₀ p.1) * rename Sum.inr (∏ τ : {τ // τ ≠ τ₀}, rename (Prod.mk τ) (b τ.1 (p.2 τ))))) ∘
          (Equiv.piSplitAt τ₀ κ) := by
      funext g
      rw [key g]
      rfl
    rw [hfun]
    exact h2

theorem linearIndependent_prod_rename_of_forall {ι σ : Type} [Fintype ι] [DecidableEq ι] (κ : ι → Type) (b : ∀ τ, κ τ → MvPolynomial σ K)
    (hb : ∀ τ, LinearIndependent K (b τ)) :
    LinearIndependent K (fun g : (∀ τ, κ τ) => ∏ τ, rename (Prod.mk τ) (b τ (g τ))) := by
  exact linearIndependent_prod_rename_of_card _ ι rfl κ b hb

section Len

theorem length_quot_map_of_injective {O M M' : Type*} [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
    (f : M →ₗ[O] M') (hf : Function.Injective f) (A B : Submodule O M) :
    Module.length O (A.map f ⧸ (B.map f).comap (A.map f).subtype) = Module.length O (A ⧸ B.comap A.subtype) := by
  have h : (B.comap A.subtype).map (Submodule.equivMapOfInjective f hf A : A →ₗ[O] A.map f) =
      (B.map f).comap (A.map f).subtype := by
    ext ⟨y, hy⟩
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · rintro ⟨⟨x, hxA⟩, hxB, hx⟩
      refine ⟨x, hxB, ?_⟩
      have hx' := congrArg Subtype.val hx
      exact hx'
    · rintro ⟨x, hxB, rfl⟩
      obtain ⟨x', hx'A, hx'⟩ := Submodule.mem_map.1 hy
      have hxx : x' = x := hf hx'
      subst hxx
      exact ⟨⟨x', hx'A⟩, hxB, Subtype.ext rfl⟩
  exact (Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective f hf A) h).length_eq.symm

theorem length_quot_pi_const {O M : Type*} [CommRing O] [AddCommGroup M] [Module O M] (G : Type*) [Fintype G] [DecidableEq G]
    (A B : Submodule O M) :
    Module.length O ((Submodule.pi Set.univ fun _ : G => A) ⧸
        (Submodule.pi Set.univ fun _ : G => B).comap (Submodule.pi Set.univ fun _ : G => A).subtype) =
      Fintype.card G • Module.length O (A ⧸ B.comap A.subtype) := by
  set P := Submodule.pi Set.univ fun _ : G => A with hP
  set B' := B.comap A.subtype with hB'
  let pr : G → P →ₗ[O] A := fun g =>
    LinearMap.codRestrict A ((LinearMap.proj g).comp P.subtype) (fun x => x.2 g (Set.mem_univ g))
  let φ : P →ₗ[O] (G → A ⧸ B') := LinearMap.pi fun g => B'.mkQ.comp (pr g)
  have hsurj : Function.Surjective φ := by
    intro y
    choose x hx using fun g => Submodule.Quotient.mk_surjective B' (y g)
    refine ⟨⟨fun g => (x g : M), fun g _ => (x g).2⟩, ?_⟩
    funext g
    simp only [φ, pr, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [← hx g]
    rfl
  have hker : LinearMap.ker φ = (Submodule.pi Set.univ fun _ : G => B).comap P.subtype := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_pi,
      Set.mem_univ, true_implies]
    constructor
    · intro h g
      have hg := congrFun h g
      simp only [φ, pr, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply, Pi.zero_apply,
        Submodule.Quotient.mk_eq_zero, hB', Submodule.mem_comap] at hg
      exact hg
    · intro h
      funext g
      simp only [φ, pr, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply, Pi.zero_apply,
        Submodule.Quotient.mk_eq_zero, hB', Submodule.mem_comap]
      exact h g
  have e := (Submodule.quotEquivOfEq _ _ hker.symm).trans (LinearMap.quotKerEquivOfSurjective φ hsurj)
  rw [e.length_eq, Module.length_pi, ENat.card_eq_coe_fintype_card, nsmul_eq_mul]

end Len

section Psi

variable {K : Type*} [Field K]

theorem eq_zero_of_sum_rename_mul {S₁ S₂ κ : Type*} [Fintype κ] (w : κ → MvPolynomial S₂ K) (hw : LinearIndependent K w)
    (a : κ → MvPolynomial S₁ K) (h : ∑ j, rename Sum.inl (a j) * rename Sum.inr (w j) = 0) : a = 0 := by
  funext j
  ext m
  have h' := congrArg (mvPolynomialCoeffInFirstVariables (K := K) (S₁ := S₁) (S₂ := S₂) m) h
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, leftCoeff_rename_mul, map_zero] at h'
  simpa using (Fintype.linearIndependent_iff.1 hw) (fun j => AddMonoidAlgebra.coeff (a j) m) h' j

def mvPolynomialProductExtension {ι σ : Type} [Fintype ι] [DecidableEq ι] (τ₀ : ι) (κ : ι → Type) [∀ τ, Fintype (κ τ)]
    (b : ∀ τ, κ τ → MvPolynomial σ K) :
    ((∀ τ : {τ // τ ≠ τ₀}, κ τ.1) → MvPolynomial σ K) →ₗ[K] MvPolynomial (ι × σ) K where
  toFun h := ∑ g, rename (Prod.mk τ₀) (h g) * ∏ τ : {τ // τ ≠ τ₀}, rename (Prod.mk τ.1) (b τ.1 (g τ))
  map_add' h h' := by simp only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]
  map_smul' c h := by simp only [Pi.smul_apply, map_smul, smul_mul_assoc, Finset.smul_sum, RingHom.id_apply]

theorem factorMap_injective {ι σ : Type} [Fintype ι] [DecidableEq ι] (τ₀ : ι) (κ : ι → Type) [∀ τ, Fintype (κ τ)]
    (b : ∀ τ, κ τ → MvPolynomial σ K) (hb : ∀ τ, τ ≠ τ₀ → LinearIndependent K (b τ)) :
    Function.Injective (mvPolynomialProductExtension τ₀ κ b) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro h hh
  have hW : LinearIndependent K (fun g : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) =>
      ∏ τ : {τ // τ ≠ τ₀}, rename (Prod.mk τ) (b τ.1 (g τ))) :=
    linearIndependent_prod_rename_of_forall (fun τ : {τ // τ ≠ τ₀} => κ τ.1) (fun τ => b τ.1) (fun τ => hb τ.1 τ.2)
  have key : mvPolynomialProductExtension τ₀ κ b h = rename (sumComplementToProduct (σ := σ) τ₀) (∑ g, rename Sum.inl (h g) *
      rename Sum.inr (∏ τ : {τ // τ ≠ τ₀}, rename (Prod.mk τ) (b τ.1 (g τ)))) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [mvPolynomialProductExtension, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_mul, map_prod, rename_rename]
    rfl
  rw [key] at hh
  have hh' : ∑ g, rename Sum.inl (h g) *
      rename Sum.inr (∏ τ : {τ // τ ≠ τ₀}, rename (Prod.mk τ) (b τ.1 (g τ))) = 0 :=
    rename_injective _ (splitIndex_injective τ₀) (by rw [hh, map_zero])
  exact eq_zero_of_sum_rename_mul _ hW h hh'

theorem length_quot_map_positionMap {ι σ : Type} [Fintype ι] [DecidableEq ι] (τ₀ : ι) (κ : ι → Type) [∀ τ, Fintype (κ τ)]
    [∀ τ, DecidableEq (κ τ)] (b : ∀ τ, κ τ → MvPolynomial σ K) (hb : ∀ τ, τ ≠ τ₀ → LinearIndependent K (b τ))
    (O : Subring K) (A₀ B₀ : Submodule O (MvPolynomial σ K)) :
    Module.length O (((Submodule.pi Set.univ fun _ : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) => A₀).map
          ((mvPolynomialProductExtension τ₀ κ b).restrictScalars O)) ⧸
        ((Submodule.pi Set.univ fun _ : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) => B₀).map ((mvPolynomialProductExtension τ₀ κ b).restrictScalars O)).comap
          ((Submodule.pi Set.univ fun _ : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) => A₀).map
            ((mvPolynomialProductExtension τ₀ κ b).restrictScalars O)).subtype) =
      (∏ τ : {τ // τ ≠ τ₀}, Fintype.card (κ τ.1)) • Module.length O (A₀ ⧸ B₀.comap A₀.subtype) := by
  rw [length_quot_map_of_injective _ (show Function.Injective ((mvPolynomialProductExtension τ₀ κ b).restrictScalars O) from
    factorMap_injective τ₀ κ b hb), length_quot_pi_const, Fintype.card_pi]

end Psi

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end
end

