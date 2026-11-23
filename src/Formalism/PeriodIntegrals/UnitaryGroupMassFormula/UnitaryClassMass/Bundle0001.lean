module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.CardStepOf
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0003

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.LSSkeleton
section
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

def LSLat : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) → (∃ θ : E, σ θ ≠ θ) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    h.IsSymm → h.Nondegenerate → Submodule.IsFullLattice E L0 →
    (∀ τ : E →+* ℂ, HasSignature ((gramOf h b).map τ) M 0) →
    ∀ g : HA (AF F) σ (gramOf h b), ∃ N : Submodule (𝓞 E) V,
      (N : Set V) = latSet σ (gramOf h b) b L0 g ∧ Submodule.IsFullLattice E N

def LSOne : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) → (∃ θ : E, σ θ ≠ θ) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    h.IsSymm → h.Nondegenerate → Submodule.IsFullLattice E L0 →
    (∀ τ : E →+* ℂ, HasSignature ((gramOf h b).map τ) M 0) →
    PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ (gramOf h b) (crdOf b L0) 1 = crdOf b L0

def LSLoc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) → (∃ θ : E, σ θ ≠ θ) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    h.IsSymm → h.Nondegenerate → Submodule.IsFullLattice E L0 →
    (∀ τ : E →+* ℂ, HasSignature ((gramOf h b).map τ) M 0) →
    ∀ (g : HA (AF F) σ (gramOf h b)) (p : Ideal (𝓞 E)), p.IsMaximal →
      ∃ γ : GamG σ (gramOf h b), ∀ x : Fin M → E,
        (∃ s ∈ hcompl (K := E) p, (algebraMap (𝓞 E) E s) • x ∈
            PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ (gramOf h b) (crdOf b L0) g) ↔
        (∃ s ∈ hcompl (K := E) p, (algebraMap (𝓞 E) E s) • x ∈
            PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ (gramOf h b) (crdOf b L0) (γ : HA (AF F) σ (gramOf h b)))

section Glue

variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V]

theorem equivFun_osmul {M : ℕ} (b : Module.Basis (Fin M) E V) (s : 𝓞 E) (v : V) :
    b.equivFun (s • v) = (algebraMap (𝓞 E) E s) • b.equivFun v := by
  rw [← algebraMap_smul E s v, LinearEquiv.map_smul]

theorem mem_iff_crdOf {M : ℕ} (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) (v : V) :
    v ∈ L0 ↔ b.equivFun v ∈ crdOf b L0 := by
  unfold crdOf
  show v ∈ L0 ↔ ∑ i, b.equivFun v i • b i ∈ L0
  rw [b.sum_equivFun]

end Glue

theorem latStep_of_parts (s1 : LSLat) (s2 : LSOne) (s3 : LSLoc) : LatStep := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hθ hτ hs hnd hL hsig g
  obtain ⟨N, hN, hNL⟩ := s1 F E σ V h M b L0 hσ hθ hτ hs hnd hL hsig g
  refine ⟨N, hN, hNL, fun p hp => ?_⟩
  obtain ⟨γ, hγ⟩ := s3 F E σ V h M b L0 hσ hθ hτ hs hnd hL hsig g p hp
  refine ⟨iotaG σ (gramOf h b) b γ, isomStep F E σ V h M b L0 hσ hθ hτ hs hnd hL hsig γ, ?_⟩
  set ι := iotaG σ (gramOf h b) b γ with hι
  have hE := equivStep F E σ V h M b L0 hσ hθ hτ hs hnd hL hsig 1 γ 1
  rw [mul_one, OneMemClass.coe_one, mul_one] at hE
  have h1 : latSet σ (gramOf h b) b L0 1 = (L0 : Set V) := by
    ext v
    show b.equivFun v ∈ PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ (gramOf h b) (crdOf b L0) 1 ↔ v ∈ L0
    rw [s2 F E σ V h M b L0 hσ hθ hτ hs hnd hL hsig, mem_iff_crdOf b L0]
  rw [h1] at hE
  have hcomm : ∀ (s : 𝓞 E) (w : V), ι (s • w) = s • ι w := fun s w => by
    rw [← algebraMap_smul E s w, LinearEquiv.map_smul, algebraMap_smul]
  ext v
  have key : (∃ s ∈ hcompl (K := E) p, s • v ∈ N) ↔ (∃ s ∈ hcompl (K := E) p, s • v ∈ ι '' (L0 : Set V)) := by
    rw [← hE]
    have := hγ (b.equivFun v)
    simp only [← equivFun_osmul] at this
    constructor
    · rintro ⟨s, hs, hv⟩
      have hv' : s • v ∈ (N : Set V) := hv
      rw [hN] at hv'
      obtain ⟨t, ht, htv⟩ := this.1 ⟨s, hs, hv'⟩
      exact ⟨t, ht, htv⟩
    · rintro ⟨s, hs, hv⟩
      obtain ⟨t, ht, htv⟩ := this.2 ⟨s, hs, hv⟩
      refine ⟨t, ht, ?_⟩
      show t • v ∈ (N : Set V)
      rw [hN]; exact htv
  show v ∈ ((locS (hcompl (K := E) p) L0).map ((ι : V →ₗ[E] V).restrictScalars (𝓞 E))) ↔
    v ∈ locS (hcompl (K := E) p) N
  rw [Submodule.mem_map]
  change (∃ w, (∃ s ∈ hcompl (K := E) p, s • w ∈ L0) ∧ ι w = v) ↔ ∃ s ∈ hcompl (K := E) p, s • v ∈ N
  rw [key]
  constructor
  · rintro ⟨w, ⟨s, hs, hw⟩, rfl⟩
    exact ⟨s, hs, s • w, hw, hcomm s w⟩
  · rintro ⟨s, hs, l, hl, hlv⟩
    refine ⟨ι.symm v, ⟨s, hs, ?_⟩, ι.apply_symm_apply v⟩
    have e : s • ι.symm v = l := by
      apply ι.injective
      rw [hcomm, ι.apply_symm_apply, hlv]
    rw [e]; exact hl

end PI.UnitaryGroupMassFormula.UJClassMass
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PSurjSk
section
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

def CofinStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V] (L N : Submodule (𝓞 E) V),
    Submodule.IsFullLattice E L → Submodule.IsFullLattice E N →
    ∃ D : ℤ, D ≠ 0 ∧ (∀ v ∈ L, (D : 𝓞 E) • v ∈ N) ∧ (∀ v ∈ N, (D : 𝓞 E) • v ∈ L)

def LocGmapStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (u : V ≃ₗ[E] V) (p : Ideal (𝓞 E)) (L : Submodule (𝓞 E) V),
    loc (K := E) p (gmap u L) = gmap u (loc (K := E) p L)

end PI.UnitaryGroupMassFormula.UJClassMass

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.UJClassMassOfDeep
section
open NumberField PI.UJClassFin PI.UJClassMass

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

theorem intF_smul (y : ℤ) (e : E) : (((y : 𝓞 F) : F)) • e = y • e := by
  rw [show (((y : 𝓞 F) : F)) = (y : F) by rfl, Int.cast_smul_eq_zsmul]

theorem crd_upper {M : ℕ} (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) (hfg : L0.FG) :
    ∃ y : ℤ, y ≠ 0 ∧ ∀ x ∈ crdOf b L0, ∀ i, IsIntegral ℤ (y • x i) := by
  classical
  obtain ⟨s, hs⟩ := hfg
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ
    ((s ×ˢ (Finset.univ : Finset (Fin M))).image (fun p => b.equivFun p.1 p.2))
  refine ⟨y, hy, fun x hx i => ?_⟩
  have hw : (∑ j, x j • b j) ∈ Submodule.span (𝓞 E) (s : Set V) := by rw [hs]; exact hx
  have key : ∀ w ∈ Submodule.span (𝓞 E) (s : Set V), ∀ i, IsIntegral ℤ (y • b.equivFun w i) := by
    intro w hw'
    induction hw' using Submodule.span_induction with
    | mem v hv =>
      intro i
      exact hint _ (Finset.mem_image.mpr ⟨(v, i), Finset.mem_product.mpr ⟨hv, Finset.mem_univ _⟩, rfl⟩)
    | zero => intro i; simp [isIntegral_zero]
    | add v w _ _ hv hw => intro i; rw [map_add (f := _), Pi.add_apply, smul_add]; exact (hv i).add (hw i)
    | smul a v _ hv =>
      intro i
      rw [← algebraMap_smul E a v, map_smul, Pi.smul_apply, smul_eq_mul, ← mul_smul_comm]
      exact (RingOfIntegers.isIntegral_coe a).mul (hv i)
  have := key _ hw i
  rwa [show b.equivFun (∑ j, x j • b j) = x by
    rw [← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]] at this

theorem int_smul_mem (L0 : Submodule (𝓞 E) V) {e : E} (he : IsIntegral ℤ e) {v : V} (hv : v ∈ L0) :
    e • v ∈ L0 := by
  let a : 𝓞 E := ⟨e, he⟩
  have ha : algebraMap (𝓞 E) E a = e := rfl
  rw [← ha, algebraMap_smul]
  exact L0.smul_mem a hv

theorem crd_lower {M : ℕ} (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V)
    (hspan : Submodule.span E (L0 : Set V) = ⊤) :
    ∃ y : ℤ, y ≠ 0 ∧ ∀ i, y • b i ∈ L0 := by
  classical
  have hmem : ∀ i, b i ∈ Submodule.span E (L0 : Set V) := fun i => by rw [hspan]; exact Submodule.mem_top
  choose n f g hfg using fun i => (Submodule.mem_span_set' (R := E)).mp (hmem i)
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.biUnion (fun i => Finset.univ.image (f i)))
  refine ⟨y, hy, fun i => ?_⟩
  rw [← hfg i, Finset.smul_sum]
  refine Submodule.sum_mem _ (fun k _ => ?_)
  have hk : IsIntegral ℤ (y • f i k) := hint _ (Finset.mem_biUnion.mpr
    ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩⟩)
  rw [← smul_assoc]
  exact int_smul_mem L0 hk (g i k).2

theorem intCast_ne_zero_OF (y : ℤ) (hy : y ≠ 0) : (y : 𝓞 F) ≠ 0 := by
  exact_mod_cast hy

end

theorem crdBounds : CrdBounds := by
  intro F E _ _ _ _ _ V _ _ _ _ _ M b L0 hL
  let hFull : Submodule.IsFullLattice E L0 := hL
  obtain ⟨y1, hy1, h1⟩ := crd_upper b L0 hFull.toIsLattice.fg
  obtain ⟨y2, hy2, h2⟩ := crd_lower b L0 (Submodule.IsFullLattice.span_eq_top (A := E) (M := L0))
  refine ⟨⟨(y1 : 𝓞 F), intCast_ne_zero_OF y1 hy1, fun x hx i => ?_⟩,
    ⟨(y2 : 𝓞 F), intCast_ne_zero_OF y2 hy2, fun i e he => ?_⟩⟩
  · rw [intF_smul]
    exact h1 x hx i
  · show ∑ j, (Pi.single i ((((y2 : 𝓞 F) : F)) • e) : Fin M → E) j • b j ∈ L0
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp),
      Pi.single_eq_same, intF_smul, smul_assoc, smul_comm]
    exact int_smul_mem L0 he (h2 i)

theorem uJClassMass_of_deep' (hR : PI.UnitaryGroupMassFormula.UJClassFin.RatDense) (s1 : LatStep) (s4 : SurjStep) :
    PI.UJClassMass2.UJClassMass :=
  uJClassMass_of_deep hR crdBounds s1 s4

end PI.UnitaryGroupMassFormula.UJClassMass

end
end

