module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1312
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1304
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1301
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0630
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0286
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalSubringGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodLatticeActionOfFiniteOrderAutomorphism
section
open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
open AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PeriodLattice

variable {P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp ℂ)}

theorem one_comp_of_isMonHom (f : P.A ⟶ P.A) (hf : IsMonHom f) :
    (1 : 𝟙_ (Over (Sp ℂ)) ⟶ P.A) ≫ f = 1 :=
  (IsMonHom.monoidHom f (𝟙_ (Over (Sp ℂ)))).map_one

theorem comp_mul' (x : 𝟙_ (Over (Sp ℂ)) ⟶ P.A) (f g : P.A ⟶ P.A) : x ≫ (f * g) = (x ≫ f) * (x ≫ g) := by
  rw [Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift]

theorem comp_one' (x : 𝟙_ (Over (Sp ℂ)) ⟶ P.A) : x ≫ (1 : P.A ⟶ P.A) = 1 := by
  simp [Hom.one_def]

section Lift

variable (u : HolUnif P.A P.L P.g)

theorem ex_zero : u.ex 0 = 1 := by
  have h := u.ex_add 0 0
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)

theorem ex_nsmul (k : ℕ) (z : Fin P.g → ℂ) : u.ex (k • z) = u.ex z ^ k := by
  induction k with
  | zero => rw [zero_smul, pow_zero, ex_zero]
  | succ k ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]

theorem lift_unique (f : P.A ⟶ P.A) (F F' : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ))
    (hF : ∀ z, u.ex (F z) = u.ex z ≫ f) (hF' : ∀ z, u.ex (F' z) = u.ex z ≫ f) : F = F' := by
  have hmem : ∀ z, (F - F') z ∈ u.Λ := by
    intro z
    rw [← u.ker]
    have h := u.ex_add ((F - F') z) (F' z)
    rw [LinearMap.sub_apply, sub_add_cancel, hF, hF'] at h
    exact mul_eq_right.mp h.symm
  haveI := u.discrete
  let D : (Fin P.g → ℂ) → u.Λ := fun z => ⟨(F - F') z, hmem z⟩
  have hD : Continuous D :=
    Continuous.subtype_mk (LinearMap.continuous_of_finiteDimensional _) _
  refine LinearMap.ext fun z => ?_
  have h1 : D z = D 0 := PreconnectedSpace.constant inferInstance hD
  have h2 : (F - F') z = 0 := by
    have := congrArg Subtype.val h1
    simpa [D] using this
  exact sub_eq_zero.mp (by simpa using h2)

variable (hl : ∀ f : P.A ⟶ P.A, IsMonHom f → ∃ F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ), ∀ z, u.ex (F z) = u.ex z ≫ f)

def lift (f : P.A ⟶ P.A) (hf : IsMonHom f) : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ) := Classical.choose (hl f hf)

theorem lift_spec (f : P.A ⟶ P.A) (hf : IsMonHom f) (z) : u.ex (lift u hl f hf z) = u.ex z ≫ f :=
  Classical.choose_spec (hl f hf) z

theorem lift_eq (f : P.A ⟶ P.A) (hf : IsMonHom f) (F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ))
    (hF : ∀ z, u.ex (F z) = u.ex z ≫ f) : lift u hl f hf = F :=
  lift_unique u f _ _ (lift_spec u hl f hf) hF

theorem lift_mem (f : P.A ⟶ P.A) (hf : IsMonHom f) {z} (hz : z ∈ u.Λ) : lift u hl f hf z ∈ u.Λ := by
  rw [← u.ker] at hz ⊢
  rw [lift_spec, hz, one_comp_of_isMonHom f hf]

def liftZ (f : P.A ⟶ P.A) (hf : IsMonHom f) : Module.End ℤ u.Λ where
  toFun x := ⟨lift u hl f hf x, lift_mem u hl f hf x.2⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' c x := Subtype.ext (map_zsmul (lift u hl f hf) c (x : Fin P.g → ℂ))

@[simp] theorem liftZ_val (f : P.A ⟶ P.A) (hf : IsMonHom f) (x : u.Λ) :
    ((liftZ u hl f hf x : u.Λ) : Fin P.g → ℂ) = lift u hl f hf x := rfl

end Lift

section Ring

variable (u : HolUnif P.A P.L P.g)
  (hl : ∀ f : P.A ⟶ P.A, IsMonHom f → ∃ F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ), ∀ z, u.ex (F z) = u.ex z ≫ f)
  {O : Type} [CommRing O] (act : OAct O P.A)

theorem act_zero : act.act 0 = 1 := by
  have h := act.add 0 0
  rw [add_zero] at h
  exact mul_eq_left.mp h.symm

def ringAct : O →+* Module.End ℤ u.Λ where
  toFun c := liftZ u hl (act.act c) (act.hom c)
  map_one' := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    simp only [liftZ_val, Module.End.one_apply]
    rw [lift_eq u hl _ _ LinearMap.id (fun z => by rw [act.one, Category.comp_id]; rfl)]
    rfl
  map_mul' a b := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    simp only [liftZ_val, Module.End.mul_apply]
    rw [lift_eq u hl _ _ ((lift u hl (act.act a) (act.hom a)).comp (lift u hl (act.act b) (act.hom b)))
      (fun z => by rw [LinearMap.comp_apply, lift_spec, lift_spec, Category.assoc, ← act.mul, mul_comm])]
    rfl
  map_zero' := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    simp only [liftZ_val, LinearMap.zero_apply, ZeroMemClass.coe_zero]
    rw [lift_eq u hl _ _ 0 (fun z => by rw [LinearMap.zero_apply, ex_zero, act_zero, comp_one'])]
    rfl
  map_add' a b := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    simp only [liftZ_val, LinearMap.add_apply, Submodule.coe_add]
    rw [lift_eq u hl _ _ (lift u hl (act.act a) (act.hom a) + lift u hl (act.act b) (act.hom b))
      (fun z => by rw [LinearMap.add_apply, u.ex_add, lift_spec, lift_spec, act.add, comp_mul'])]
    rfl

end Ring

section Main

variable (u : HolUnif P.A P.L P.g)
  (hl : ∀ f : P.A ⟶ P.A, IsMonHom f → ∃ F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ), ∀ z, u.ex (F z) = u.ex z ≫ f)

theorem lift_pow_spec (θ : P.A ⟶ P.A) (hθ : IsMonHom θ) (k : ℕ) (z : Fin P.g → ℂ) :
    u.ex ((lift u hl θ hθ ^ k) z) = u.ex z ≫ (fun f : P.A ⟶ P.A => f ≫ θ)^[k] (𝟙 P.A) := by
  induction k with
  | zero => rw [pow_zero, Module.End.one_apply, Function.iterate_zero, id, Category.comp_id]
  | succ k ih => rw [pow_succ', Module.End.mul_apply, lift_spec, ih, Function.iterate_succ_apply', Category.assoc]

include u hl in
theorem main_of_unif (E : Type) [Field E] [NumberField E] (act : OAct (𝓞 E) P.A) (θ : P.A ⟶ P.A) (N n : ℕ)
    (hθ : IsMonHom θ) (hN : (fun f : P.A ⟶ P.A => f ≫ θ)^[N] (𝟙 P.A) = 𝟙 P.A)
    (hc : ∀ a, act.act a ≫ θ = θ ≫ act.act a) (hn : 0 < n) :
    ∃ (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (F : Λ →ₗ[𝓞 E] Λ) (ψ : Λ → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)),
      Module.Finite (𝓞 E) Λ ∧ Module.IsTorsionFree (𝓞 E) Λ ∧ F ^ N = 1 ∧ (∀ a b, ψ (a + b) = ψ a * ψ b) ∧
      (∀ (c : 𝓞 E) a, ψ (c • a) = ψ a ≫ act.act c) ∧ (∀ a, ψ a = 1 ↔ ∃ b, a = n • b) ∧
      (∀ q : 𝟙_ (Over (Sp ℂ)) ⟶ P.A, q ^ n = 1 → ∃ a, ψ a = q) ∧ ∀ a, ψ (F a) = ψ a ≫ θ := by
  letI inst : Module (𝓞 E) u.Λ := Module.compHom u.Λ (ringAct u hl act)
  have hsmul : ∀ (c : 𝓞 E) (x : u.Λ), ((c • x : u.Λ) : Fin P.g → ℂ) = lift u hl (act.act c) (act.hom c) x :=
    fun _ _ => rfl

  have hcomm : ∀ c, (lift u hl θ hθ).comp (lift u hl (act.act c) (act.hom c)) =
      (lift u hl (act.act c) (act.hom c)).comp (lift u hl θ hθ) := fun c =>
    lift_unique u (act.act c ≫ θ) _ _
      (fun z => by rw [LinearMap.comp_apply, lift_spec, lift_spec, Category.assoc])
      (fun z => by rw [LinearMap.comp_apply, lift_spec, lift_spec, Category.assoc, hc])
  let F : u.Λ →ₗ[𝓞 E] u.Λ :=
    { toFun := liftZ u hl θ hθ
      map_add' := map_add _
      map_smul' := fun c x => Subtype.ext (by
        simp only [RingHom.id_apply, hsmul, liftZ_val]
        exact (LinearMap.congr_fun (hcomm c) x : _)) }
  have hFval : ∀ x : u.Λ, ((F x : u.Λ) : Fin P.g → ℂ) = lift u hl θ hθ x := fun _ => rfl
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  let ψ : u.Λ → (𝟙_ (Over (Sp ℂ)) ⟶ P.A) := fun a => u.ex ((n : ℂ)⁻¹ • (a : Fin P.g → ℂ))
  have hψlift : ∀ (f : P.A ⟶ P.A) (hf : IsMonHom f) (a : u.Λ),
      u.ex ((n : ℂ)⁻¹ • lift u hl f hf a) = ψ a ≫ f := fun f hf a => by
    rw [← map_smul, lift_spec]
  haveI := u.discrete
  haveI : IsZLattice ℝ u.Λ := ⟨u.full⟩
  haveI hZ : Module.Finite ℤ u.Λ := ZLattice.module_finite ℝ u.Λ
  refine ⟨u.Λ, inferInstance, inst, F, ψ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) u.Λ
  · refine Module.IsTorsionFree.of_smul_eq_zero fun c x h => ?_
    by_cases hc0 : c = 0
    · exact Or.inl hc0
    right
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {c}))
    have hm : Ideal.absNorm (Ideal.span {c}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hc0
    have h1 : (Ideal.absNorm (Ideal.span {c}) : 𝓞 E) • x = 0 := by
      rw [← hr, mul_smul, h, smul_zero]
    rw [Nat.cast_smul_eq_nsmul] at h1
    have h2 := congrArg Subtype.val h1
    rw [AddSubmonoidClass.coe_nsmul, ZeroMemClass.coe_zero, ← Nat.cast_smul_eq_nsmul ℂ] at h2
    exact Subtype.ext ((smul_eq_zero.mp h2).resolve_left (Nat.cast_ne_zero.mpr hm))
  · have hpow : lift u hl θ hθ ^ N = 1 := by
      rw [lift_unique u (𝟙 P.A) (lift u hl θ hθ ^ N) 1
        (fun z => by rw [lift_pow_spec, hN]) (fun z => by rw [Module.End.one_apply, Category.comp_id])]
    have hit : ∀ (k : ℕ) (x : u.Λ), (((F ^ k) x : u.Λ) : Fin P.g → ℂ) = (lift u hl θ hθ ^ k) x := by
      intro k
      induction k with
      | zero => intro x; rfl
      | succ k ih => intro x; rw [pow_succ', Module.End.mul_apply, hFval, ih, pow_succ', Module.End.mul_apply]
    refine LinearMap.ext fun x => Subtype.ext ?_
    rw [hit, hpow]; rfl
  · intro a b
    simp only [ψ, Submodule.coe_add, smul_add, u.ex_add]
  · intro c a
    simp only [ψ]
    rw [hsmul, hψlift]
  · intro a
    simp only [ψ]
    rw [u.ker]
    constructor
    · intro h
      refine ⟨⟨_, h⟩, Subtype.ext ?_⟩
      rw [AddSubmonoidClass.coe_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ hn']
    · rintro ⟨b, rfl⟩
      rw [AddSubmonoidClass.coe_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ hn']
      exact b.2
  · intro q hq
    obtain ⟨z, rfl⟩ := u.ex_onto q
    have hz : (n : ℂ) • z ∈ u.Λ := by
      rw [← u.ker, Nat.cast_smul_eq_nsmul, ex_nsmul, hq]
    refine ⟨⟨_, hz⟩, ?_⟩
    simp only [ψ]
    rw [inv_smul_smul₀ hn']
  · intro a
    simp only [ψ]
    rw [hFval, hψlift]

end Main

end GlobalTheory.PeriodLattice

theorem GlobalTheory.periodLattice_of_finiteOrder : ∀ (E : Type) [Field E] [NumberField E] (P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp ℂ)) (act : OAct (𝓞 E) P.A) (θ : P.A ⟶ P.A) (N n : ℕ), IsMonHom θ → 0 < N → (fun f : P.A ⟶ P.A => f ≫ θ)^[N] (𝟙 P.A) = 𝟙 P.A → (∀ a, act.act a ≫ θ = θ ≫ act.act a) → 0 < n → ∃ (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (F : Λ →ₗ[𝓞 E] Λ) (ψ : Λ → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), Module.Finite (𝓞 E) Λ ∧ Module.IsTorsionFree (𝓞 E) Λ ∧ F ^ N = 1 ∧ (∀ a b, ψ (a + b) = ψ a * ψ b) ∧ (∀ (c : 𝓞 E) a, ψ (c • a) = ψ a ≫ act.act c) ∧ (∀ a, ψ a = 1 ↔ ∃ b, a = n • b) ∧ (∀ q : 𝟙_ (Over (Sp ℂ)) ⟶ P.A, q ^ n = 1 → ∃ a, ψ a = q) ∧ ∀ a, ψ (F a) = ψ a ≫ θ := by
  intro E _ _ P act θ N n hθ _ hN hc hn
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨u, -, -, -, -, -, -, -, hl, -⟩ := GlobalTheory.thetaUnifAV_all P rig hrig
  exact GlobalTheory.PeriodLattice.main_of_unif u hl E act θ N n hθ hN hc hn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhRatOfSerCore
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PhRatCommon


set_option maxHeartbeats 1000000 in
theorem phRat_of_ser_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → ∀ (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m), OMPins T R κ v₀ O i → ∀ cc, SerOf (O i) (κ i) (v₀ i (sg0 D A)) cc 1 → (∀ x : (O i).Cl' () → VsV D i (O i).c'.F, ∃ f ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) (O i).c' (unfBC (O i).hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (Vc D i).rank, IsThClsD (T.Q.Xo ((i : ℕ) + 1)) (O i).c' ((O i).dδ ()) ((O i).w ()) ((O i).La ()) ((O i).Nc ()) ((O i).gam ()) ((O i).vol ()) ((O i).ep ()) (O i).io x f) → (O i).EquivAt (κ i) cc → (O i).PhRat (κ i) (v₀ i (sg0 D A)) cc 1 := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR t O i hpins cc hser hex hequiv
  obtain ⟨hcc, hph, hs⟩ := hser
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm ⟨1, by simp [Formalism.FrobeniusOrbits.Psi]⟩⟩
  have hn : (κ i).n = (Vc D i).rank :=
    (t.kap i τ).2.2.trans (D.sp.V_rank _ (Nat.le_add_left _ _) i.2).symm
  refine GlobalTheory.PhaseRationalDegenerate.of_before_projector (O i) (κ i) _ cc hequiv hR.grp.chiW hR.thP.thG 1 fun x₀ => ?_
  obtain ⟨h, J', hrep, hP, -, -⟩ := (hpins.2.tuple ()).reps
  obtain ⟨x, hx⟩ := hP x₀
  obtain ⟨f, hf, hcl⟩ := hex x
  have hf' : f ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) (O i).c' (unfBC (O i).hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (κ i).n := by
    rw [hn]; exact hf
  have hBC := exists_rdU_eq_sum (O i).hle (T.U ((i : ℕ) + 1)) (inC (O i).c') _ _ f hf'
  obtain ⟨m, as, fs, hbc⟩ := hBC
  have hL : ∀ a : (O i).c'.F, ∃ b : D.what₂.LL, D.what₂.embLL b = inC (O i).c' a := fun a => by
    have : (a : ℂ) ∈ D.what₂.embLL.toRatAlgHom.fieldRange := hpins.1 ▸ a.2
    exact this
  choose b hb using hL
  refine ⟨m, fun j => b (as j), fs, fun g => ?_⟩
  have := hs () h J' hrep _ x hx f hf.1 hcl g
  have e1 := hbc ((O i).dict g).1 ((O i).dict g).2
  have e2 : ∀ j, (O i).phi cc (fs j : T.R ((i : ℕ) + 1)) g = cc ((O i).dict g).1 * (O i).mu g *
      rdU (T.U ((i : ℕ) + 1) (O i).s0) (fs j : T.R ((i : ℕ) + 1)) ((O i).dict g).1 ((O i).dict g).2 := fun j => rfl
  exact this.trans (sum_shape e1 (fun j => hb (as j)) e2)

end GlobalTheory.PhRatCommon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
section
noncomputable section

namespace GlobalTheory.IndLine

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

def fockDeg (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (k : ℕ) : Submodule ℂ (SInf F (Fin n × Fin d)) :=
  Nat.rec (motive := fun _ => Submodule ℂ (SInf F (Fin n × Fin d))) (Submodule.span ℂ {f₀ | M.IsGauss ψ τ f₀})
    (fun _ N => N ⊔ Submodule.span ℂ {f₁ | ∃ u, At (evI F) u ∧ ∃ f ∈ N, ActsD (evI F) (M.heisLine ψ u) f f₁}) k

theorem fockDeg_zero (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    fockDeg M ψ τ 0 = Submodule.span ℂ {f₀ | M.IsGauss ψ τ f₀} := rfl

theorem fockDeg_succ (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (k : ℕ) :
    fockDeg M ψ τ (k + 1) = fockDeg M ψ τ k ⊔ Submodule.span ℂ {f₁ | ∃ u, At (evI F) u ∧ ∃ f ∈ fockDeg M ψ τ k,
      ActsD (evI F) (M.heisLine ψ u) f f₁} := rfl

def lowDegInf (B : Base F E) (M : Model σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) : ℕ :=
  sInf {k | ∃ f ∈ fockDeg M B.ψ B.emb k, p f ≠ 0}

def lowPartInf (B : Base F E) (M : Model σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) : Submodule ℂ P :=
  (fockDeg M B.ψ B.emb (lowDegInf B M p)).map p

theorem fockDeg_mono (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    Monotone (fockDeg M ψ τ) :=
  monotone_nat_of_le_succ fun _ => le_sup_left

theorem fockDeg_le_pol (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (k : ℕ) :
    fockDeg M ψ τ k ≤ M.Pol ψ τ := by
  induction k with
  | zero => exact Submodule.span_le.2 fun f hf => Submodule.mem_sInf.2 fun N hN => hN.1 f hf
  | succ k ih =>
    refine sup_le ih (Submodule.span_le.2 ?_)
    rintro f₁ ⟨u, hu, f, hf, hd⟩
    exact Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 (ih hf) N hN) f₁ hd

theorem pol_eq_iSup_fockDeg (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    M.Pol ψ τ = ⨆ k, fockDeg M ψ τ k := by
  refine le_antisymm (sInf_le ⟨fun f₀ hf₀ => ?_, fun u hu f hf f₁ hd => ?_⟩) (iSup_le (fockDeg_le_pol M ψ τ))
  · exact Submodule.mem_iSup_of_mem 0 (Submodule.subset_span hf₀)
  · obtain ⟨k, hk⟩ := (Submodule.mem_iSup_of_directed _ (fockDeg_mono M ψ τ).directed_le).1 hf
    exact Submodule.mem_iSup_of_mem (k + 1)
      (Submodule.mem_sup_right (Submodule.subset_span ⟨u, hu, f, hk, hd⟩))

theorem lowPartInf_ne_bot (B : Base F E) (M : Model σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (h : ∃ f ∈ M.Pol B.ψ B.emb, p f ≠ 0) : lowPartInf B M p ≠ ⊥ := by
  obtain ⟨f, hf, hp⟩ := h
  rw [pol_eq_iSup_fockDeg] at hf
  obtain ⟨k, hk⟩ := (Submodule.mem_iSup_of_directed _ (fockDeg_mono M B.ψ B.emb).directed_le).1 hf
  have hne : {k | ∃ f ∈ fockDeg M B.ψ B.emb k, p f ≠ 0}.Nonempty := ⟨k, f, hk, hp⟩
  obtain ⟨g, hg, hpg⟩ := Nat.sInf_mem hne
  intro hbot
  exact hpg ((Submodule.eq_bot_iff _).1 hbot (p g) ⟨g, hg, rfl⟩)

end GlobalTheory.IndLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDataDecomposesAtFinitePlaces
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThK.CycGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem smul_pure {κ : Type} [Fintype κ] (c : ℂ) (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) :
    c • pure f φ = pure (c • f) φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

theorem exists_decOn_some {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W)
    (Φ : (Fin n × Fin d → AF F) → ℂ) (hΦ : Φ ∈ PolData B M) :
    ∃ (T₀ : Finset (Pl (F := F))) (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d))
      (φ : Fin m → ∀ v : Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ), DecOn B M T₀ Φ m f φ := by
  classical
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, φ, hφ, hcof, rfl⟩ := hx
    have hfin : {v | ¬ φ v = M.vac v}.Finite := Filter.eventually_cofinite.1 hcof
    refine ⟨hfin.toFinset, 1, fun _ => f, fun _ => φ, fun _ => ⟨hf, hφ, fun v hv => ?_⟩, ?_⟩
    · by_contra h
      exact hv (hfin.mem_toFinset.2 h)
    · simp
  | zero =>
    exact ⟨∅, 0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨T, m, f, φ, h1, rfl⟩ := hx
    obtain ⟨T', m', f', φ', h1', rfl⟩ := hy
    refine ⟨T ∪ T', m + m', Fin.append f f', Fin.append φ φ', fun j => ?_, ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp only [Fin.append_left]
        exact ⟨(h1 i).1, (h1 i).2.1, fun v hv => (h1 i).2.2 v fun h => hv (Finset.mem_union_left _ h)⟩
      · simp only [Fin.append_right]
        exact ⟨(h1' i).1, (h1' i).2.1, fun v hv => (h1' i).2.2 v fun h => hv (Finset.mem_union_right _ h)⟩
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
  | smul c x _ hx =>
    obtain ⟨T, m, f, φ, h1, rfl⟩ := hx
    refine ⟨T, m, fun j => c • f j, φ, fun j => ⟨Submodule.smul_mem _ c (h1 j).1, (h1 j).2.1, (h1 j).2.2⟩, ?_⟩
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => smul_pure c (f j) (φ j)

end GlobalTheory.ThK.CycGen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrecedesOfSegDualPrecedes
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

namespace GlobalTheory.LocLanglands

theorem precedes_of_segDual_precedes :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    ∀ D : IrrGL (k := k) → IrrGL (k := k), (∀ x y, DualCl x y ↔ y = D x) → (∀ x, D (D x) = x) →
      (∀ (x : IrrGL (k := k)) (s : ℂ), D (x.nu s) = (D x).nu (-s)) → (∀ x, x.IsCusp → (D x).IsCusp) →
      (∀ x, (D x).1 = x.1) → ∀ Δ Γ Δ' Γ' : Segment k, SegDual Δ Δ' → SegDual Γ Γ' → Γ'.Precedes Δ' → Δ.Precedes Γ := by
  intro k _ _ _ _ D hD hDD hnu _ _ Δ Γ Δ' Γ' ⟨l1, d1⟩ ⟨l2, d2⟩ H
  obtain ⟨j, h0, h1, h2, e⟩ := Segment.precedes_iff.1 H
  rw [(hD _ _).1 d1, (hD _ _).1 d2] at e
  have e' := congrArg D e
  rw [hnu (D _), hDD, hDD, IrrGL.nu_nu] at e'
  rw [l1] at h2
  rw [l2] at h1 h2
  obtain ⟨i, hi⟩ : ∃ i : ℕ, j + Δ.len = Γ.len + i := ⟨j + Δ.len - Γ.len, by omega⟩
  refine Segment.precedes_iff.2 ⟨i, by omega, by omega, by omega, ?_⟩
  have hc : (j : ℂ) + Δ.len = Γ.len + i := by exact_mod_cast hi
  have e2 := congrArg (fun x => IrrGL.nu x (-((Γ.len : ℂ) - 1 + -(j : ℂ)))) e'
  simp only [IrrGL.nu_nu, add_neg_cancel, IrrGL.nu_zero] at e2
  rw [← e2]
  congr 1
  linear_combination hc

end GlobalTheory.LocLanglands
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDegreeEqOrderSum
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

set_option autoImplicit false

namespace GlobalTheory.RatDegZeros

theorem mem_range_fst : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (x : X), CharZero (X.residueField x) → x ∈ Set.range (ratFibre.fst p) := by
  intro k _ X p x hx
  let q : Spec (X.residueField x) ⟶ Sp ℚ := Spec.map (CommRingCat.ofHom (algebraMap ℚ (X.residueField x)))
  let y0 := (ratFibre.isPullback p).lift (X.fromSpecResidueField x) q (specZIsTerminal.hom_ext _ _)
  let z : Spec (X.residueField x) := IsLocalRing.closedPoint (X.residueField x)
  refine ⟨y0 z, ?_⟩
  have e : (y0 ≫ ratFibre.fst p) z = X.fromSpecResidueField x z := by
    rw [(ratFibre.isPullback p).lift_fst]
  rw [Scheme.Hom.comp_apply] at e
  exact e.trans (X.fromSpecResidueField_apply x z)

end GlobalTheory.RatDegZeros
end

