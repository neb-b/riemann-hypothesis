module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.Bundle0003
public import Mathlib
public import ReciprocityTheory.GaloisValuations.ArithOfA
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ValNatCastOf

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ImAVecVMulVec
section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm PI.MassDataKppVolLemmas
open scoped TensorProduct Matrix

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

theorem imA_vecV_smul (p : TypX X) (t : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)
    (w : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.vecV X.B.I p.1 (t • w) = PI.FinKW.psiV X.B.I p.1 t • PI.FinKW.vecV X.B.I p.1 w := by
  funext i; simp [PI.FinKW.vecV, map_mul]

theorem imA_vecV_add (p : TypX X) (a b : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.vecV X.B.I p.1 (a + b) = PI.FinKW.vecV X.B.I p.1 a + PI.FinKW.vecV X.B.I p.1 b := by
  funext i; simp [PI.FinKW.vecV]

theorem imA_vecV_zero (p : TypX X) :
    PI.FinKW.vecV X.B.I p.1 (0 : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) = 0 := by
  funext i; simp [PI.FinKW.vecV]

theorem imA_OEp_mul (p : TypX X) {s t : Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E} (hs : s ∈ OEp X p)
    (ht : t ∈ OEp X p) : s * t ∈ OEp X p := by
  obtain ⟨a, ha, rfl⟩ := hs
  obtain ⟨b, hb', rfl⟩ := ht
  exact ⟨a * b, Subring.mul_mem _ ha hb', map_mul _ _ _⟩

theorem smul_mem_spanAt (p : TypX X) (S : Set (Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E))
    {t : Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E} (ht : t ∈ OEp X p)
    {w : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E}
    (hw : w ∈ Submodule.span (p.1.adicCompletionIntegers X.B.I.F) {w | ∃ t ∈ OEp X p, ∃ s ∈ S, w = t • s}) :
    t • w ∈ Submodule.span (p.1.adicCompletionIntegers X.B.I.F) {w | ∃ t ∈ OEp X p, ∃ s ∈ S, w = t • s} := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t', ht', s, hs, rfl⟩ := hx
    exact Submodule.subset_span ⟨t * t', imA_OEp_mul X p ht ht', s, hs, by rw [smul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ c hx

theorem imA_inMod_loc (p : TypX X) (m : ℕ) (S : Set (Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F))
    (w : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) (h : InMod X.B.I m S w) :
    InModP X p m (PI.FinKW.vecV X.B.I p.1 '' S) (PI.FinKW.vecV X.B.I p.1 w) := by
  obtain ⟨a, ha, b, hb', rfl⟩ := Submodule.mem_sup.mp h
  clear h
  rw [imA_vecV_add]
  refine Submodule.mem_sup.mpr ⟨_, ?_, _, ?_, rfl⟩
  · induction ha using Submodule.span_induction with
    | mem x hx =>
      exact Submodule.subset_span ⟨1, ⟨1, one_mem _, map_one _⟩, _, ⟨x, hx, rfl⟩, (one_smul _ _).symm⟩
    | zero => rw [imA_vecV_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [imA_vecV_add]; exact add_mem hx hy
    | smul c x _ hx =>
      show PI.FinKW.vecV X.B.I p.1 ((c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • x) ∈ _
      rw [imA_vecV_smul]
      exact smul_mem_spanAt X p _ ⟨c, c.2, rfl⟩ hx
  · have key : ∃ x ∈ X.B.I.Lf, b = (m : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • x := by
      induction hb' using Submodule.span_induction with
      | mem y hy => exact hy
      | zero => exact ⟨0, zero_mem _, (smul_zero _).symm⟩
      | add y z _ _ hy hz =>
        obtain ⟨y', hy', rfl⟩ := hy
        obtain ⟨z', hz', rfl⟩ := hz
        exact ⟨y' + z', add_mem hy' hz', (smul_add _ _ _).symm⟩
      | smul c y _ hy =>
        obtain ⟨y', hy', rfl⟩ := hy
        refine ⟨c • y', Submodule.smul_mem _ c hy', ?_⟩
        show (c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • _ = _ • ((c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • y')
        rw [smul_smul, smul_smul, mul_comm]
    obtain ⟨x, hx, rfl⟩ := key
    rw [imA_vecV_smul, map_natCast, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul (p.1.adicCompletionIntegers X.B.I.F)]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (PI.FinKW.LocTo.mem_local_lattice_iff X.B.I x hx p.1)

theorem imA_vecV_mulVec (p : TypX X) (x : X.B.I.Gf)
    (w : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.vecV X.B.I p.1 ((X.B.I.fmat x - 1) *ᵥ w) =
      (((HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (piV X.B.I p.1 (tf X.B.I hb x)) :
        GL (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) - 1) *ᵥ
        PI.FinKW.vecV X.B.I p.1 w := by
  rw [LocIdxLift_vecV_mulVec, Matrix.map_sub _ (map_sub _), LocIdxLift_psiV_fmat X.B.I hb,
    Matrix.map_one _ (map_zero _) (map_one _)]

theorem imA_kpp_sub (p : TypX X) : KppX X hb p ⊆ {y | y ∈ KvX X p ∧ LocCong X p y} := by
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  have hx' : x ∈ X.B.I.Kset ∧ K2cong X.B.I X.B.g X.e0 X.z0 X.bw x := hx
  obtain ⟨hxK, h1, h2, h3⟩ := hx'
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hK := (Bridge_mem_Kf_iff X.B.I hb x).mpr hxK
    rw [Kf, Subgroup.mem_iInf] at hK
    exact hK p.1
  · intro a
    have h := imA_inMod_loc X p _ _ _ (h1 a)
    rw [imA_vecV_mulVec X hb, Set.image_image] at h
    exact h
  · have h := imA_inMod_loc X p _ _ _ h2
    rw [imA_vecV_mulVec X hb, ← Set.range_comp] at h
    exact h
  · intro i
    have h := imA_inMod_loc X p _ _ _ (h3 i)
    rw [imA_vecV_mulVec X hb, Set.image_union, Set.image_image, ← Set.range_comp] at h
    exact h

end MassDataIdxSteps
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.IsOpenForallMulVec
section
noncomputable section

namespace MassDataIdxK

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain Topology
open scoped Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

theorem isOpen_forall_mulVec {Λ U : Set (Fin n → Fv F v ⊗[F] E)} (hΛ : IsCompact Λ) (hU : IsOpen U) :
    IsOpen {A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | ∀ y ∈ Λ, A *ᵥ y ∈ U} := by
  have := fdFE (F := F) (E := E)
  have := MassDataIdxSteps.tens_topRing (F := F) (E := E) v
  rw [isOpen_iff_mem_nhds]
  intro A0 hA0
  exact hΛ.eventually_forall_of_forall_eventually fun y hy =>
    (continuous_fst.matrix_mulVec continuous_snd).continuousAt.preimage_mem_nhds (hU.mem_nhds (hA0 y hy))

theorem isCompact_stab (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (hfg : L.FG) :
    IsCompact {A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | ∀ y ∈ (latLoc (E := E) v (L : Set (Fin n → E)) :
      Set (Fin n → Fv F v ⊗[F] E)), A *ᵥ y ∈ (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E))} := by
  have := fdFE (F := F) (E := E)
  have := MassDataIdxSteps.tens_topRing (F := F) (E := E) v
  set Λ : Set (Fin n → Fv F v ⊗[F] E) := (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) with hΛ
  obtain ⟨m, b, hbΛ, hsp, -⟩ := latImage v L hL hfg
  obtain ⟨hΛo, hΛc⟩ := latOpenCompact v L hL hfg
  have hΛcl : IsClosed Λ :=
    AddSubgroup.isClosed_of_isOpen (latLoc (E := E) v (L : Set (Fin n → E))).toAddSubgroup hΛo
  have hclosed : IsClosed {A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | ∀ y ∈ Λ, A *ᵥ y ∈ Λ} := by
    have : {A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | ∀ y ∈ Λ, A *ᵥ y ∈ Λ} =
        ⋂ y ∈ Λ, (fun A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) => A *ᵥ y) ⁻¹' Λ := by
      ext A; simp
    rw [this]
    exact isClosed_biInter fun y _ => hΛcl.preimage (continuous_id.matrix_mulVec continuous_const)
  let Ψ : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) →ₗ[Fv F v] (Fin m → Fin n → Fv F v ⊗[F] E) :=
    { toFun := fun A i => A *ᵥ b i
      map_add' := fun A B => by funext i; exact Matrix.add_mulVec A B (b i)
      map_smul' := fun r A => by
        funext i j
        simp [Matrix.mulVec, dotProduct, Finset.smul_sum, smul_mul_assoc] }
  have hinj : LinearMap.ker Ψ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro A hA
    let Al : (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v] (Fin n → Fv F v ⊗[F] E) :=
      { toFun := fun x => A *ᵥ x
        map_add' := Matrix.mulVec_add A
        map_smul' := fun r x => Matrix.mulVec_smul A r x }
    have hAl : Al = 0 := LinearMap.ext_on_range hsp (fun i => congrFun hA i)
    ext i j
    have := congrFun (LinearMap.congr_fun hAl (Pi.single j 1)) i
    simpa [Al, Matrix.mulVec_single_one] using this
  obtain ⟨Ψ', hΨ'⟩ := LinearMap.exists_leftInverse_of_injective Ψ hinj
  have hc : Continuous Ψ' := IsModuleTopology.continuous_of_linearMap Ψ'
  have hsub : {A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | ∀ y ∈ Λ, A *ᵥ y ∈ Λ} ⊆
      Ψ' '' Set.pi Set.univ (fun _ => Λ) := by
    intro A hA
    exact ⟨Ψ A, fun i _ => hA _ (hbΛ i), by rw [← LinearMap.comp_apply, hΨ', LinearMap.id_apply]⟩
  exact ((isCompact_univ_pi fun _ => hΛc).image hc).of_isClosed_subset hclosed hsub

theorem kloc_open_compact (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (hfg : L.FG) :
    IsOpen (Kloc (E := E) v (L : Set (Fin n → E)) : Set (GL (Fin n) (Fv F v ⊗[F] E))) ∧
      IsCompact (Kloc (E := E) v (L : Set (Fin n → E)) : Set (GL (Fin n) (Fv F v ⊗[F] E))) := by
  have := fdFE (F := F) (E := E)
  have := MassDataIdxSteps.tens_topRing (F := F) (E := E) v
  have := t2Space_scalarTensorExt (F := F) (E := E) v
  set Λ : Set (Fin n → Fv F v ⊗[F] E) := (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) with hΛ
  set S := {A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | ∀ y ∈ Λ, A *ᵥ y ∈ Λ} with hS
  obtain ⟨hΛo, hΛc⟩ := latOpenCompact v L hL hfg
  have hSo : IsOpen S := isOpen_forall_mulVec v hΛc hΛo
  have hSc : IsCompact S := isCompact_stab v L hL hfg
  have heq : (Kloc (E := E) v (L : Set (Fin n → E)) : Set (GL (Fin n) (Fv F v ⊗[F] E))) =
      Units.embedProduct _ ⁻¹' (S ×ˢ (MulOpposite.unop ⁻¹' S)) := by
    ext g
    show (∀ x, x ∈ Λ ↔ (g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ x ∈ Λ) ↔
      ((g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) ∈ S ∧
        ((g⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) ∈ S)
    constructor
    · intro hg
      refine ⟨fun y hy => (hg y).1 hy, fun y hy => ?_⟩
      have := (hg (((g⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) _) *ᵥ y)).2
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at this
      exact this hy
    · rintro ⟨h1, h2⟩ x
      refine ⟨h1 x, fun hx => ?_⟩
      have := h2 _ hx
      rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this
  rw [heq]
  refine ⟨(hSo.prod (hSo.preimage MulOpposite.continuous_unop)).preimage
    Units.isEmbedding_embedProduct.continuous, ?_⟩
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage
    (hSc.prod ((MulOpposite.opHomeomorph.symm.isCompact_preimage).2 hSc))

def sigL (σ : E →ₐ[F] E) : (Fv F v ⊗[F] E) →ₗ[Fv F v] (Fv F v ⊗[F] E) where
  toFun := sigR (Fv F v) σ
  map_add' := map_add _
  map_smul' := fun r x => by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
    rw [Algebra.TensorProduct.algebraMap_apply]
    show Algebra.TensorProduct.map (AlgHom.id F (Fv F v)) σ (algebraMap (Fv F v) (Fv F v) r ⊗ₜ 1) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl

theorem isClosed_HR (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) :
    IsClosed ((HR (Fv F v) σ J : Subgroup (GL (Fin n) (Fv F v ⊗[F] E))) : Set (GL (Fin n) (Fv F v ⊗[F] E))) := by
  have := fdFE (F := F) (E := E)
  have := MassDataIdxSteps.tens_topRing (F := F) (E := E) v
  have := t2Space_scalarTensorExt (F := F) (E := E) v
  have hσ : Continuous (sigR (F := F) (Fv F v) σ) := IsModuleTopology.continuous_of_linearMap (sigL v σ)
  have hval : Continuous (fun g : GL (Fin n) (Fv F v ⊗[F] E) => (g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) :=
    Units.continuous_val
  exact isClosed_eq (((hval.matrix_map hσ).matrix_transpose.matrix_mul continuous_const).matrix_mul hval)
    continuous_const

end MassDataIdxK
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LocDegOneBelow
section
noncomputable section

namespace MassDataIdxRes

open NumberField IsDedekindDomain Ideal

section K

variable {K : Type} [Field K] [NumberField K]

theorem locDeg_one (l : ℕ) [hl : Fact l.Prime]
    (h : {w : HeightOneSpectrum (𝓞 K) | ((l : ℕ) : 𝓞 K) ∈ w.asIdeal}.ncard = Module.finrank ℚ K)
    (w : HeightOneSpectrum (𝓞 K)) (hw : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal) :
    w.asIdeal.ramificationIdx ℤ = 1 ∧ w.asIdeal.inertiaDeg ℤ = 1 := by
  have hfin := Formalism.L2.SG.TypedSets.finite_over K l hl.out.ne_zero
  set T := hfin.toFinset with hTdef
  have hT : ∀ v, v ∈ T ↔ ((l : ℕ) : 𝓞 K) ∈ v.asIdeal := fun v => by
    rw [hTdef, Set.Finite.mem_toFinset]; rfl
  have hsum := ReciprocityTheory.Gal.sum_locDegree l T hT
  have hcard : T.card = Module.finrank ℚ K := by rw [← h, Set.ncard_eq_toFinset_card _ hfin]
  have hpos : ∀ v ∈ T, (fun _ => 1) v ≤ ReciprocityTheory.Gal.locDegree v := fun v _ =>
    Nat.mul_pos (Ideal.ramificationIdx_pos (R := ℤ) v.asIdeal) (Ideal.inertiaDeg_pos v.asIdeal ℤ)
  have hall := (Finset.sum_eq_sum_iff_of_le hpos).1 (by
    simp only [Finset.sum_const, smul_eq_mul, mul_one]; rw [hsum, hcard])
  have hm : w.asIdeal.ramificationIdx ℤ * w.asIdeal.inertiaDeg ℤ = 1 := (hall w ((hT w).2 hw)).symm
  exact ⟨Nat.eq_one_of_mul_eq_one_right hm, Nat.eq_one_of_mul_eq_one_left hm⟩

end K

section FE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem locDeg_one_below (l : ℕ) [hl : Fact l.Prime]
    (h : {w : HeightOneSpectrum (𝓞 E) | ((l : ℕ) : 𝓞 E) ∈ w.asIdeal}.ncard = Module.finrank ℚ E)
    (p : HeightOneSpectrum (𝓞 F)) (hp : ((l : ℕ) : 𝓞 F) ∈ p.asIdeal) :
    p.asIdeal.ramificationIdx ℤ = 1 ∧ p.asIdeal.inertiaDeg ℤ = 1 := by
  have := p.isMaximal
  obtain ⟨Q, hQm, hQo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) p.asIdeal
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot Q
  let w : HeightOneSpectrum (𝓞 E) := ⟨Q, hQm.isPrime, hQ0⟩
  have hw : ((l : ℕ) : 𝓞 E) ∈ w.asIdeal := by
    have := (Ideal.mem_of_liesOver Q p.asIdeal ((l : ℕ) : 𝓞 F)).1 hp
    simpa using this
  obtain ⟨he, hf⟩ := locDeg_one l h w hw
  have hQp : Q.IsPrime := hQm.isPrime
  have h1 : p.asIdeal.ramificationIdx ℤ ≤ Q.ramificationIdx ℤ :=
    Ideal.ramificationIdx_below_le (R := ℤ) (q := p.asIdeal) (r := Q)
  have h2 : p.asIdeal.inertiaDeg ℤ ≤ Q.inertiaDeg ℤ :=
    Ideal.inertiaDeg_below_le (R := ℤ) (q := p.asIdeal) (r := Q)
  have h3 := Ideal.ramificationIdx_pos (R := ℤ) p.asIdeal
  have h4 := Ideal.inertiaDeg_pos p.asIdeal ℤ
  change Q.ramificationIdx ℤ = 1 at he
  change Q.inertiaDeg ℤ = 1 at hf
  omega

end FE

section Arith

variable {F : Type} [Field F] [NumberField F]

theorem arith_of_loc (l : ℕ) [hl : Fact l.Prime] (p : HeightOneSpectrum (𝓞 F))
    (hp : ((l : ℕ) : 𝓞 F) ∈ p.asIdeal) (he : p.asIdeal.ramificationIdx ℤ = 1)
    (hf : p.asIdeal.inertiaDeg ℤ = 1) :
    Nat.card (𝓞 F ⧸ p.asIdeal) = l ∧ ((l : ℕ) : 𝓞 F) ∉ p.asIdeal ^ 2 := by
  have hlo : p.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) := (ReciprocityTheory.Gal.liesOver_span_iff l p.asIdeal).2 hp
  constructor
  · have := Ideal.pow_inertiaDeg l p.asIdeal
    rw [hf, pow_one] at this
    rw [this, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  · intro h2
    have hmap : (Ideal.span {(l : ℤ)}).map (algebraMap ℤ (𝓞 F)) = Ideal.span {((l : ℕ) : 𝓞 F)} := by
      rw [Ideal.map_span, Set.image_singleton]; simp
    have hne : (Ideal.span {(l : ℤ)}).map (algebraMap ℤ (𝓞 F)) ≠ ⊥ := by
      rw [hmap, Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast hl.out.ne_zero
    have hm := IsDedekindDomain.ramificationIdx_eq_multiplicity (Ideal.span {(l : ℤ)}) p.asIdeal hne
    rw [he, hmap] at hm
    have hdvd : p.asIdeal ^ 2 ∣ Ideal.span {((l : ℕ) : 𝓞 F)} := Ideal.dvd_span_singleton.2 h2
    have hfin : FiniteMultiplicity p.asIdeal (Ideal.span {((l : ℕ) : 𝓞 F)}) := by
      apply FiniteMultiplicity.of_not_isUnit
      · rw [Ideal.isUnit_iff]; exact p.isPrime.ne_top
      · rw [Ne, Ideal.zero_eq_bot, ← hmap]; exact hne
    have := hfin.le_multiplicity_of_pow_dvd hdvd
    omega

end Arith

end MassDataIdxRes
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MemSGIffFlagC
section
noncomputable section

namespace MassDataIdxStIm

open Matrix Formalism.FourierDecayAlt.S3

variable {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n] {m : ℕ}

def FlagC (M : Matrix n n K) (v : Fin m → n → K) : Prop :=
  ∀ b, M *ᵥ v b - v b ∈ Submodule.span K (v '' {a | a < b})

theorem span_mulVec (M : Matrix n n K) {w : n → K} {S : Set (n → K)} (h : w ∈ Submodule.span K S) :
    M *ᵥ w ∈ Submodule.span K ((fun u => M *ᵥ u) '' S) := by
  have e : (fun u => M *ᵥ u) = ⇑(Matrix.mulVecLin M) := rfl
  rw [e, Submodule.span_image]
  exact Submodule.mem_map_of_mem h

theorem flagC_conj_imp (P Pi M : Matrix n n K) (hP : Pi * P = 1) (v : Fin m → n → K) (h : FlagC M v) :
    FlagC (P * M * Pi) (fun b => P *ᵥ v b) := by
  intro b
  have h1 : (P * M * Pi) *ᵥ (P *ᵥ v b) - P *ᵥ v b = P *ᵥ (M *ᵥ v b - v b) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hP, Matrix.mul_one, Matrix.mulVec_sub,
      Matrix.mulVec_mulVec]
  rw [h1]
  have h2 := span_mulVec P (h b)
  rwa [Set.image_image] at h2

theorem flagC_conj (P Pi M : Matrix n n K) (hP : Pi * P = 1) (hP' : P * Pi = 1) (v : Fin m → n → K) :
    FlagC (P * M * Pi) (fun b => P *ᵥ v b) ↔ FlagC M v := by
  refine ⟨fun h => ?_, flagC_conj_imp P Pi M hP v⟩
  have h2 := flagC_conj_imp Pi P (P * M * Pi) hP' (fun b => P *ᵥ v b) h
  have e1 : Pi * (P * M * Pi) * P = M := by
    simp only [← Matrix.mul_assoc, hP, Matrix.one_mul]
    rw [Matrix.mul_assoc, hP, Matrix.mul_one]
  have e2 : (fun b => Pi *ᵥ (P *ᵥ v b)) = v := by
    funext b
    rw [Matrix.mulVec_mulVec, hP, Matrix.one_mulVec]
  rw [e1, e2] at h2
  exact h2

theorem span_smul_eq (c : Fin m → K) (hc : ∀ b, c b ≠ 0) (v : Fin m → n → K) (s : Set (Fin m)) :
    Submodule.span K ((fun b => c b • v b) '' s) = Submodule.span K (v '' s) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    have e : v b = (c b)⁻¹ • (c b • v b) := by rw [smul_smul, inv_mul_cancel₀ (hc b), one_smul]
    rw [SetLike.mem_coe, e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)

theorem flagC_smul (M : Matrix n n K) (c : Fin m → K) (hc : ∀ b, c b ≠ 0) (v : Fin m → n → K) :
    FlagC M (fun b => c b • v b) ↔ FlagC M v := by
  unfold FlagC
  simp only [span_smul_eq c hc v, Matrix.mulVec_smul, ← smul_sub]
  refine forall_congr' (fun b => ⟨fun h => ?_, fun h => Submodule.smul_mem _ _ h⟩)
  have h3 := Submodule.smul_mem _ (c b)⁻¹ h
  rwa [smul_smul, inv_mul_cancel₀ (hc b), one_smul] at h3

variable {r k : ℕ}

theorem colFlag_eq (M : Matrix (Idx r k) (Idx r k) K) :
    ColFlag M ↔ FlagC M (fun b => Pi.single (pe (k := k) b) (1 : K)) := Iff.rfl

theorem rowFlag_eq (M : Matrix (Idx r k) (Idx r k) K) :
    RowFlag M ↔ FlagC Mᵀ (fun b => Pi.single (pf (k := k) b) (1 : K)) := Iff.rfl

theorem mem_sG_iff_flagC (g : GL (Idx r k) K) :
    g ∈ sG K r k ↔ FlagC (g : Matrix (Idx r k) (Idx r k) K) (fun b => Pi.single (pe (k := k) b) (1 : K)) ∧
      FlagC ((g⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K)ᵀ (fun b => Pi.single (pf (k := k) b) (1 : K)) := by
  rw [mem_sG_iff_flags, ← colFlag_eq, ← rowFlag_eq, colFlag_iff, rowFlag_iff]

end MassDataIdxStIm
end
end

