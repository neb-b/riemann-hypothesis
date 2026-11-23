module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0360
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0338
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0355
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0272
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0350
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0250
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0361
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0330
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0327

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParFunSiegMulStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parFun_sieg_mul' : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)), (∀ φ : Matrix α ν E → ℂ, parFun c ψ χ Q (mat c (1 : UG c (stdJ ν E))) φ = φ) ∧ ∀ p ∈ sieg c ν, ∀ q ∈ sieg c ν, ∀ φ : Matrix α ν E → ℂ, parFun c ψ χ Q (mat c (p * q)) φ = parFun c ψ χ Q (mat c p) (parFun c ψ χ Q (mat c q) φ) := by
  first | exact @GlobalTheory.KSp.parFun_sieg_mul | exact GlobalTheory.KSp.parFun_sieg_mul | (intros; apply GlobalTheory.KSp.parFun_sieg_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicFaithfullyFlatDescentUnitCocycles
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.PicCech

section
variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B]

theorem descMod_mul_le (u v : (B ⊗[A] B)ˣ) : descMod A B u * descMod A B v ≤ descMod A B (u * v) := by
  refine Submodule.mul_le.2 fun x hx y hy => ?_
  simp only [descMod, LinearMap.mem_eqLocus, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    AlgHom.toLinearMap_apply] at hx hy ⊢
  rw [map_mul, map_mul, Units.val_mul, ← hx, ← hy]; ring

theorem descMod_one_le [Module.FaithfullyFlat A B] : descMod A B 1 ≤ 1 := by
  intro b hb
  simp only [descMod, LinearMap.mem_eqLocus, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    AlgHom.toLinearMap_apply, Units.val_one, one_mul] at hb
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_algebraMap_eq_of_faithfullyFlat_includeLeft_eq_includeRight A B b hb.symm
  exact Submodule.mem_one.2 ⟨a, ha⟩

theorem uCoc_mul {u v : (B ⊗[A] B)ˣ} (hu : UCoc A B u) (hv : UCoc A B v) : UCoc A B (u * v) := by
  unfold UCoc at *
  simp only [Units.val_mul, map_mul, hu, hv]
  ring

theorem uCoc_inv {u : (B ⊗[A] B)ˣ} (hu : UCoc A B u) : UCoc A B u⁻¹ := by
  unfold UCoc at *
  set f13 := (Algebra.TensorProduct.map (AlgHom.id A B) (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B))
  set f12 := (Algebra.TensorProduct.map (AlgHom.id A B) (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B))
  set f23 := (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B))
  have key : Units.map f13.toMonoidHom u = Units.map f12.toMonoidHom u * Units.map f23.toMonoidHom u :=
    Units.ext hu
  have key' := congrArg (fun x => ((x⁻¹ : (B ⊗[A] (B ⊗[A] B))ˣ) : B ⊗[A] (B ⊗[A] B))) key
  simp only [mul_inv, ← map_inv] at key'
  simpa [mul_comm] using key'

theorem descMod_mul_inv [Module.FaithfullyFlat A B] {u : (B ⊗[A] B)ˣ} (hu : UCoc A B u) :
    descMod A B u * descMod A B u⁻¹ = 1 := by
  have hle : descMod A B u * descMod A B u⁻¹ ≤ 1 :=
    (descMod_mul_le u u⁻¹).trans (by rw [mul_inv_cancel]; exact descMod_one_le)
  refine le_antisymm hle ?_
  have htop : (⊤ : Submodule A B) * (descMod A B u * descMod A B u⁻¹) = ⊤ := by
    rw [← mul_assoc, GlobalTheory.T.top_mul_descendedSubmoduleOfUnitCocycle_eq_top A B u hu, GlobalTheory.T.top_mul_descendedSubmoduleOfUnitCocycle_eq_top A B u⁻¹ (uCoc_inv hu)]
  set J : Ideal A := (descMod A B u * descMod A B u⁻¹).comap (Algebra.linearMap A B) with hJ
  have hJtop : J • (⊤ : Submodule A B) = ⊤ := by
    rw [eq_top_iff]
    calc (⊤ : Submodule A B) = ⊤ * (descMod A B u * descMod A B u⁻¹) := htop.symm
      _ ≤ J • (⊤ : Submodule A B) := Submodule.mul_le.2 fun b _ p hp => ?_
    obtain ⟨a, rfl⟩ := Submodule.mem_one.1 (hle hp)
    have ha : a ∈ J := hp
    rw [mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  have hJ1 : J = ⊤ := ((Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top A B).1 inferInstance).2 J hJtop
  have h1 : (1 : A) ∈ J := hJ1 ▸ Submodule.mem_top
  rw [Submodule.one_le]
  simpa [hJ] using h1

theorem descMod_eq_span_iff [Module.FaithfullyFlat A B] {u : (B ⊗[A] B)ˣ} (hu : UCoc A B u) :
    (∃ x : Bˣ, Submodule.spanSingleton A (x : B) = descMod A B u) ↔
      ∃ w : Bˣ, (u : B ⊗[A] B) * (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) w =
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) w := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    have hmem : (x : B) ∈ descMod A B u := hx ▸ Submodule.mem_span_singleton_self _
    simpa [descMod, LinearMap.mem_eqLocus] using hmem
  · rintro ⟨w, hw⟩
    refine ⟨w, le_antisymm ?_ ?_⟩
    · refine (Submodule.span_le).2 ?_
      rintro _ rfl
      simpa [descMod, LinearMap.mem_eqLocus] using hw
    · intro b hb
      have hwi : ((w⁻¹ : Bˣ) : B) ∈ descMod A B u⁻¹ := by
        simp only [descMod, LinearMap.mem_eqLocus, LinearMap.comp_apply, LinearMap.mulLeft_apply,
          AlgHom.toLinearMap_apply]
        have e1 : (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) (w : B) *
            (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) ((w⁻¹ : Bˣ) : B) = 1 := by
          rw [← map_mul, Units.mul_inv, map_one]
        have e2 : (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) (w : B) *
            (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) ((w⁻¹ : Bˣ) : B) = 1 := by
          rw [← map_mul, Units.mul_inv, map_one]
        have e3 : (u : B ⊗[A] B) * ((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B) = 1 := Units.mul_inv u
        calc ((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B) * (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) ((w⁻¹ : Bˣ) : B)
            = ((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B) * (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) ((w⁻¹ : Bˣ) : B) *
              ((u : B ⊗[A] B) * (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) (w : B) *
                (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) ((w⁻¹ : Bˣ) : B)) := by
              rw [hw, e2, mul_one]
          _ = (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) ((w⁻¹ : Bˣ) : B) := by
              linear_combination (((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B) * (u : B ⊗[A] B) * (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) ((w⁻¹ : Bˣ) : B)) * e1 + ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) ((w⁻¹ : Bˣ) : B)) * e3
      have hp : b * ((w⁻¹ : Bˣ) : B) ∈ descMod A B u * descMod A B u⁻¹ := Submodule.mul_mem_mul hb hwi
      rw [descMod_mul_inv hu] at hp
      obtain ⟨a, ha⟩ := Submodule.mem_one.1 hp
      refine Submodule.mem_span_singleton.2 ⟨a, ?_⟩
      rw [Algebra.smul_def, ha, mul_assoc, Units.inv_mul, mul_one]

theorem isUnit_descMod [Module.FaithfullyFlat A B] {u : (B ⊗[A] B)ˣ} (hu : UCoc A B u) :
    IsUnit (descMod A B u) :=
  IsUnit.of_mul_eq_one _ (descMod_mul_inv hu)

theorem descMod_mul [Module.FaithfullyFlat A B] {u v : (B ⊗[A] B)ˣ} (hu : UCoc A B u)
    (hv : UCoc A B v) : descMod A B (u * v) = descMod A B u * descMod A B v := by
  refine le_antisymm ?_ (descMod_mul_le u v)
  calc descMod A B (u * v) = descMod A B (u * v) * (descMod A B u * descMod A B u⁻¹) := by
        rw [descMod_mul_inv hu, mul_one]
    _ = descMod A B u * (descMod A B (u * v) * descMod A B u⁻¹) := by ring
    _ ≤ descMod A B u * descMod A B (u * v * u⁻¹) := by
        gcongr; exact descMod_mul_le _ _
    _ = descMod A B u * descMod A B v := by
        congr 2; rw [mul_comm u v, mul_assoc, mul_inv_cancel, mul_one]

theorem exists_descMod_eq [Module.FaithfullyFlat A B] (I : (Submodule A B)ˣ) :
    ∃ u, UCoc A B u ∧ descMod A B u = I :=
  _root_.GlobalTheory.PicCech.exists_unitCocycle_descMod_eq A B descMod_one_le I

theorem uCoc_map {B' : Type} [CommRing B'] [Algebra A B'] (φ : B →ₐ[A] B') {u : (B ⊗[A] B)ˣ}
    (hu : UCoc A B u) : UCoc A B' (Units.map (Algebra.TensorProduct.map φ φ).toMonoidHom u) := by
  unfold UCoc at *
  have h13 : ∀ x, (Algebra.TensorProduct.map (AlgHom.id A B') (Algebra.TensorProduct.includeRight : B' →ₐ[A] B' ⊗[A] B'))
      (Algebra.TensorProduct.map φ φ x) = Algebra.TensorProduct.map φ (Algebra.TensorProduct.map φ φ)
        ((Algebra.TensorProduct.map (AlgHom.id A B) (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)) x) := by
    intro x; induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have h12 : ∀ x, (Algebra.TensorProduct.map (AlgHom.id A B') (Algebra.TensorProduct.includeLeft : B' →ₐ[A] B' ⊗[A] B'))
      (Algebra.TensorProduct.map φ φ x) = Algebra.TensorProduct.map φ (Algebra.TensorProduct.map φ φ)
        ((Algebra.TensorProduct.map (AlgHom.id A B) (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)) x) := by
    intro x; induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have h23 : ∀ x, (Algebra.TensorProduct.includeRight : B' ⊗[A] B' →ₐ[A] B' ⊗[A] (B' ⊗[A] B'))
      (Algebra.TensorProduct.map φ φ x) = Algebra.TensorProduct.map φ (Algebra.TensorProduct.map φ φ)
        ((Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)) x) := by
    intro x; simp
  have e : ((Units.map (Algebra.TensorProduct.map φ φ).toMonoidHom u : (B' ⊗[A] B')ˣ) : B' ⊗[A] B') =
      Algebra.TensorProduct.map φ φ (u : B ⊗[A] B) := rfl
  rw [e, h13, h12, h23, hu, map_mul]

theorem descMod_map_le {B' : Type} [CommRing B'] [Algebra A B'] (φ : B →ₐ[A] B') (u : (B ⊗[A] B)ˣ) :
    (descMod A B u).map φ.toLinearMap ≤ descMod A B' (Units.map (Algebra.TensorProduct.map φ φ).toMonoidHom u) := by
  rintro _ ⟨b, hb, rfl⟩
  simp only [descMod, LinearMap.mem_eqLocus, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    AlgHom.toLinearMap_apply, Units.coe_map, MonoidHom.coe_coe] at hb ⊢
  have := congrArg (Algebra.TensorProduct.map φ φ) hb
  simpa using this

theorem nonempty_descMod_equiv [Module.FaithfullyFlat A B] {B' : Type} [CommRing B'] [Algebra A B']
    [Module.FaithfullyFlat A B'] (φ : B →ₐ[A] B') {u : (B ⊗[A] B)ˣ} (hu : UCoc A B u) :
    Nonempty (descMod A B u ≃ₗ[A] descMod A B' (Units.map (Algebra.TensorProduct.map φ φ).toMonoidHom u)) := by
  set u' := Units.map (Algebra.TensorProduct.map φ φ).toMonoidHom u
  have hu' : UCoc A B' u' := uCoc_map φ hu
  haveI : Module.Invertible A (descMod A B u) :=
    inferInstanceAs (Module.Invertible A ((isUnit_descMod hu).unit : Submodule A B))
  haveI : Module.Invertible A (descMod A B' u') :=
    inferInstanceAs (Module.Invertible A ((isUnit_descMod hu').unit : Submodule A B'))
  have hmap := descMod_map_le φ u
  let f : descMod A B u →ₗ[A] descMod A B' u' :=
    (φ.toLinearMap.restrict (p := descMod A B u) (q := descMod A B' u')
      fun b hb => hmap (Submodule.mem_map_of_mem hb))
  have hinv : (descMod A B u⁻¹).map φ.toLinearMap ≤ descMod A B' u'⁻¹ := by
    have := descMod_map_le φ u⁻¹
    rwa [map_inv] at this
  set P := (descMod A B u).map φ.toLinearMap
  have h1 : (1 : Submodule A B') ≤ P * descMod A B' u'⁻¹ := by
    calc (1 : Submodule A B') = (1 : Submodule A B).map φ.toLinearMap := (Submodule.map_one φ).symm
      _ = P * (descMod A B u⁻¹).map φ.toLinearMap := by
          rw [← descMod_mul_inv hu, Submodule.map_mul]
      _ ≤ P * descMod A B' u'⁻¹ := by gcongr
  have hle : descMod A B' u' ≤ P := by
    calc descMod A B' u' = descMod A B' u' * 1 := (mul_one _).symm
      _ ≤ descMod A B' u' * (P * descMod A B' u'⁻¹) := by gcongr
      _ = P * (descMod A B' u' * descMod A B' u'⁻¹) := by ring
      _ = P := by rw [descMod_mul_inv hu', mul_one]
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨b, hb, rfl⟩ := hle hy
    exact ⟨⟨b, hb⟩, rfl⟩
  exact ⟨LinearEquiv.ofBijective f (Module.Invertible.bijective_of_surjective hsurj)⟩

end

def δ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (u : (B ⊗[A] B)ˣ) : CommRing.Pic A := by
  classical
  exact if h : Module.Invertible A (descMod A B u) then CommRing.Pic.mk A (descMod A B u) else 1

theorem δ_eq {A B : Type} [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    {u : (B ⊗[A] B)ˣ} (hu : UCoc A B u) :
    δ A B u = Submodule.unitsToPic A B (isUnit_descMod hu).unit := by
  have : Module.Invertible A (descMod A B u) := inferInstanceAs (Module.Invertible A ((isUnit_descMod hu).unit : Submodule A B))
  rw [δ, dite_eq_left this, Submodule.unitsToPic_apply]
  rfl

end GlobalTheory.PicCech


open GlobalTheory.PicCech in
theorem GlobalTheory.pic_cech_descent : ∀ (A : Type) [CommRing A], ∃ δ : ∀ (B : Type) [CommRing B] [Algebra A B], (B ⊗[A] B)ˣ → CommRing.Pic A, ∀ (B : Type) [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B], (∀ u v, UCoc A B u → UCoc A B v → δ B (u * v) = δ B u * δ B v) ∧ (∀ u, UCoc A B u → (δ B u = 1 ↔ ∃ w : Bˣ, (u : B ⊗[A] B) * (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) w = (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) w)) ∧ (∀ c : CommRing.Pic A, CommRing.Pic.mapAlgebra A B c = 1 → ∃ u, UCoc A B u ∧ δ B u = c) ∧ (∀ u, UCoc A B u → ∃ _ : Module.Invertible A (descMod A B u), CommRing.Pic.mk A (descMod A B u) = δ B u) ∧ ∀ (B' : Type) [CommRing B'] [Algebra A B'] [Module.FaithfullyFlat A B'] (φ : B →ₐ[A] B') (u : (B ⊗[A] B)ˣ) (u' : (B' ⊗[A] B')ˣ), UCoc A B u → (u' : B' ⊗[A] B') = Algebra.TensorProduct.map φ φ (u : B ⊗[A] B) → δ B' u' = δ B u := by
  intro A _
  refine ⟨fun B _ _ u => δ A B u, fun B _ _ _ => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro u v hu hv
    have huv : UCoc A B (u * v) := uCoc_mul hu hv
    dsimp only
    rw [δ_eq hu, δ_eq hv, δ_eq huv, ← map_mul]
    congr 1
    exact Units.ext (descMod_mul hu hv)
  · intro u hu
    dsimp only
    rw [δ_eq hu, ← MonoidHom.mem_ker, Submodule.ker_unitsToPic, ← descMod_eq_span_iff hu]
    constructor
    · rintro ⟨x, hx⟩; exact ⟨x, congrArg Units.val hx⟩
    · rintro ⟨x, hx⟩; exact ⟨x, Units.ext hx⟩
  · intro c hc
    obtain ⟨I, rfl⟩ : c ∈ (Submodule.unitsToPic A B).range := by
      rw [Submodule.range_unitsToPic]; exact hc
    obtain ⟨u, hu, hI⟩ := exists_descMod_eq I
    refine ⟨u, hu, ?_⟩
    dsimp only
    rw [δ_eq hu]; congr 1; exact Units.ext hI
  · intro u hu
    refine ⟨inferInstanceAs (Module.Invertible A ((isUnit_descMod hu).unit : Submodule A B)), ?_⟩
    dsimp only
    rw [δ_eq hu, Submodule.unitsToPic_apply]; rfl
  · intro B' _ _ _ φ u u' hu hu'
    have hu'' : u' = Units.map (Algebra.TensorProduct.map φ φ).toMonoidHom u := Units.ext hu'
    subst hu''
    dsimp only
    rw [δ_eq hu, δ_eq (uCoc_map φ hu), Submodule.unitsToPic_apply, Submodule.unitsToPic_apply,
      CommRing.Pic.mk_eq_mk_iff]
    exact (nonempty_descMod_equiv φ hu).map LinearEquiv.symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialRingIrreduciblePrimeReduction
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_ring_irreducible_prime_reduction : ∀ (k F : Type) [Field k] [Field F] [Algebra k F] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F), A = Algebra.adjoin k (Set.range u) → ∀ t : A, Irreducible t → Prime t ∧ ∃ m : ℕ, d = m + 1 ∧ ∃ y : Fin m → A, IsTranscendenceBasis k (fun j => Ideal.Quotient.mk (Ideal.span {t}) (y j)) := by
  first | (exact @GlobalTheory.TrBasisQuot.trBasis_mod_irreducible) | (exact GlobalTheory.TrBasisQuot.trBasis_mod_irreducible) | (intros; apply GlobalTheory.TrBasisQuot.trBasis_mod_irreducible  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeTensorPolynomialIsMaximalOfMemImage
section
open GlobalTheory.EtC

namespace GlobalTheory.ClosedFibre
open Polynomial
open scoped TensorProduct

theorem mem_range_of_eval₂ {K D : Type} [Field K] [IsAlgClosed K] [CommRing D] [IsDomain D]
    (ψ : K →+* D) (f : K[X]) (hf : f ≠ 0) (τ : D) (h : f.eval₂ ψ τ = 0) : ∃ r, ψ r = τ := by
  letI : Algebra K D := ψ.toAlgebra
  have hK : AIC K := fun p _ hd => IsAlgClosed.exists_root p (natDegree_pos_iff_degree_pos.mp hd).ne'
  have hm : (f * C f.leadingCoeff⁻¹).Monic := monic_mul_leadingCoeff_inv hf
  exact GlobalTheory.AICIff.root_mem_range hK _ _ hm rfl τ (by
    rw [aeval_def, eval₂_mul]
    change eval₂ ψ τ f * _ = 0
    rw [h, zero_mul])

theorem mem_range_of_etale {R K E D : Type} [CommRing R] [Field K] [IsAlgClosed K] [CommRing E]
    [CommRing D] [IsDomain D] [Algebra R K] [Algebra R E] [Algebra.Etale R E] [Algebra R D]
    (ψ : K →ₐ[R] D) (Φ : E →ₐ[R] D) (u : E) : ∃ r, ψ r = Φ u := by
  haveI : Algebra.Etale K (K ⊗[R] E) := Algebra.Etale.baseChange R E K
  haveI : Module.Finite K (K ⊗[R] E) := Algebra.FormallyUnramified.finite_of_free _ _
  haveI : Algebra.IsIntegral K (K ⊗[R] E) := Algebra.IsIntegral.of_finite _ _
  obtain ⟨f, hfm, hf⟩ := Algebra.IsIntegral.isIntegral (R := K) ((1 : K) ⊗ₜ[R] u)
  let Θ : K ⊗[R] E →ₐ[R] D := Algebra.TensorProduct.productMap ψ Φ
  have hΘ : (Θ : K ⊗[R] E →+* D).comp (algebraMap K (K ⊗[R] E)) = (ψ : K →+* D) := by
    ext k
    simp [Θ, Algebra.TensorProduct.algebraMap_apply]
  refine mem_range_of_eval₂ (ψ : K →+* D) f hfm.ne_zero (Φ u) ?_
  have h2 := congrArg (Θ : K ⊗[R] E →+* D) hf
  rw [hom_eval₂, hΘ, map_zero] at h2
  simpa [Θ] using h2

end GlobalTheory.ClosedFibre

namespace GlobalTheory.ClosedFibre
open Polynomial

theorem isMaximal_of_mem : ∀ (T : Type) [CommRing T] [IsDomain T], AIC T → ∀ (O : Type) [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[(Polynomial T)] Si i)) → ∀ P : Ideal (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))), P.IsPrime → ∀ g : Polynomial T, g ≠ 0 → algebraMap (Polynomial T) (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) g ∈ P → P.IsMaximal ∧ ∀ x : Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)), ∃ c d : T, d ≠ 0 ∧ algebraMap T (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) d * x - algebraMap T (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) c ∈ P := by
  intro T _ _ hT O _ _ _ _ hO P hP g hg hgP
  let L := Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
  let K := FractionRing T
  haveI : IsAlgClosed K := GlobalTheory.isAlgClosed_fractionRing_of_AIC T hT
  haveI := hP
  let mk : L →+* L ⧸ P := Ideal.Quotient.mk P
  have hunitL : ∀ t : T, t ≠ 0 → IsUnit (algebraMap T L t) := by
    intro t ht
    have := IsLocalization.map_units L (⟨algebraMap T O t, ⟨t, mem_nonZeroDivisors_of_ne_zero ht, rfl⟩⟩ :
      Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
    rwa [IsScalarTower.algebraMap_apply T O L]
  have hunit : ∀ y : nonZeroDivisors T, IsUnit ((mk.comp (algebraMap T L)) y) :=
    fun y => (hunitL y (nonZeroDivisors.ne_zero y.2)).map mk
  let ψ : K →+* L ⧸ P := IsLocalization.lift (M := nonZeroDivisors T) (S := K) hunit
  have hψ : ψ.comp (algebraMap T K) = mk.comp (algebraMap T L) := IsLocalization.lift_comp hunit
  let τ : L ⧸ P := mk (algebraMap (Polynomial T) L X)
  have hpoly : mk.comp (algebraMap (Polynomial T) L) = eval₂RingHom (mk.comp (algebraMap T L)) τ := by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, coe_eval₂RingHom, eval₂_C]
      rw [IsScalarTower.algebraMap_apply T (Polynomial T) L, Polynomial.algebraMap_apply]
      rfl
    · simp [τ]
  obtain ⟨a, ha⟩ : ∃ a, ψ a = τ := by
    refine mem_range_of_eval₂ ψ (g.map (algebraMap T K))
      ((Polynomial.map_ne_zero_iff (IsFractionRing.injective T K)).2 hg) τ ?_
    rw [eval₂_map, hψ, ← coe_eval₂RingHom, ← hpoly, RingHom.comp_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hgP
  letI : Algebra (Polynomial T) K := (eval₂RingHom (algebraMap T K) a).toAlgebra
  let ψA : K →ₐ[Polynomial T] L ⧸ P :=
    { ψ with
      commutes' := fun p => by
        change ψ (eval₂ (algebraMap T K) a p) = mk (algebraMap (Polynomial T) L p)
        rw [hom_eval₂, hψ, ha, ← RingHom.comp_apply mk, hpoly, coe_eval₂RingHom] }
  have key : ∀ o : O, ∃ r, ψ r = mk (algebraMap O L o) := by
    intro o
    obtain ⟨ι, _, _, _, Si, -, hcov, hE⟩ := hO
    obtain ⟨i, hi⟩ := hcov o
    obtain ⟨E, _, _, _, Q, _, ⟨e⟩⟩ := hE i
    let Φ0 : Localization.AtPrime Q →ₐ[Polynomial T] L ⧸ P :=
      (Ideal.Quotient.mkₐ (Polynomial T) P).comp
        ((IsScalarTower.toAlgHom (Polynomial T) O L).comp ((Si i).val.comp e.toAlgHom))
    let Φ : E →ₐ[Polynomial T] L ⧸ P :=
      Φ0.comp (IsScalarTower.toAlgHom (Polynomial T) E (Localization.AtPrime Q))
    obtain ⟨⟨u, s⟩, hus⟩ := IsLocalization.mk'_surjective Q.primeCompl (e.symm ⟨o, hi⟩)
    obtain ⟨r1, h1⟩ := mem_range_of_etale ψA Φ u
    obtain ⟨r2, h2⟩ := mem_range_of_etale ψA Φ s
    have hsu : IsUnit (Φ s) := (IsLocalization.map_units (Localization.AtPrime Q) s).map Φ0
    have ho : Φ0 (e.symm ⟨o, hi⟩) = mk (algebraMap O L o) := by
      change Ideal.Quotient.mk P (algebraMap O L ((e (e.symm ⟨o, hi⟩) : Si i) : O)) = mk (algebraMap O L o)
      rw [AlgEquiv.apply_symm_apply]
    have hmul : Φ0 (e.symm ⟨o, hi⟩) * Φ s = Φ u := by
      rw [← hus]
      simp only [Φ, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
      rw [← map_mul, IsLocalization.mk'_spec]
    have h1' : ψA r1 = ψ r1 := rfl
    have h2' : ψA r2 = ψ r2 := rfl
    rw [h1'] at h1
    rw [h2'] at h2
    have hr2 : r2 ≠ 0 := by
      rintro rfl
      rw [map_zero] at h2
      exact hsu.ne_zero h2.symm
    refine ⟨r1 * r2⁻¹, ?_⟩
    have hne : ψ r2 ≠ 0 := h2 ▸ hsu.ne_zero
    apply mul_right_cancel₀ hne
    rw [← map_mul, inv_mul_cancel_right₀ hr2, h1, ← ho, h2, hmul]
  have hall : ∀ x : L, ∃ r, ψ r = mk x := by
    intro x
    obtain ⟨⟨o, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)) x
    obtain ⟨t, ht, hts⟩ := s.2
    obtain ⟨r, hr⟩ := key o
    have ht0 : t ≠ 0 := nonZeroDivisors.ne_zero ht
    have hk : ψ (algebraMap T K t) = mk (algebraMap O L s) := by
      rw [← RingHom.comp_apply ψ, hψ, RingHom.comp_apply, IsScalarTower.algebraMap_apply T O L, ← hts]
    have hne : ψ (algebraMap T K t) ≠ 0 := by
      rw [hk]
      exact ((IsLocalization.map_units L s).map mk).ne_zero
    have hk0 : algebraMap T K t ≠ 0 := fun h => hne (by rw [h, map_zero])
    refine ⟨r * (algebraMap T K t)⁻¹, ?_⟩
    apply mul_right_cancel₀ hne
    rw [← map_mul, inv_mul_cancel_right₀ hk0, hr, hk, ← map_mul, IsLocalization.mk'_spec]
  have hfield : IsField (L ⧸ P) := by
    refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {y} hy => ?_⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨r, hr⟩ := hall x
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact hy (by rw [← hr, map_zero])
    exact ⟨ψ r⁻¹, by rw [← hr, ← map_mul, mul_inv_cancel₀ hr0, map_one]⟩
  refine ⟨Ideal.Quotient.maximal_of_isField P hfield, fun x => ?_⟩
  obtain ⟨r, hr⟩ := hall x
  obtain ⟨⟨c, d⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors T) r
  refine ⟨c, d, nonZeroDivisors.ne_zero d.2, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul]
  have h1 : ψ (IsLocalization.mk' K c d) * ψ (algebraMap T K d) = ψ (algebraMap T K c) := by
    rw [← map_mul, IsLocalization.mk'_spec]
  have hd : ψ (algebraMap T K d) = Ideal.Quotient.mk P (algebraMap T L d) := by
    rw [← RingHom.comp_apply ψ, hψ]; rfl
  have hc : ψ (algebraMap T K c) = Ideal.Quotient.mk P (algebraMap T L c) := by
    rw [← RingHom.comp_apply ψ, hψ]; rfl
  rw [← hd, ← hc, ← h1, ← hr, mul_comm]
  exact sub_self _

end GlobalTheory.ClosedFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFunctionCharpolyPairProdRootSum
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem psiG_rootSum_pair_prod_rootSum : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ (m k l : ℕ) (e : Fin l → ℕ), 0 < m → ∑ᶠ x, psiG (rootSum θ k) m x * star (chG (fun P => ∏ j, rootSum θ (e j) P) m x) = (Nat.card (GL (Fin m) F) : ℂ) * ((Finset.univ.filter fun a : Fin l → Fin m => k ≡ ∑ j, e j * Nat.card F ^ (a j : ℕ) [MOD Nat.card F ^ m - 1]).card : ℂ) := by
  intro F _ _ θ hθ m k l e hm
  set q := Nat.card F with hq
  have hq1 : 1 < q := Finite.one_lt_card
  have hqm : 1 < q ^ m := Nat.one_lt_pow hm.ne' hq1
  set N := q ^ m - 1 with hN
  have hN0 : 0 < N := by omega
  have hcast : ((q : ℂ) ^ m - 1) = ((N : ℕ) : ℂ) := by
    rw [hN, Nat.cast_sub hqm.le]; push_cast; ring
  have hNne : ((N : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
  have htor := GlobalTheory.T.green_function_character_sum F θ m k (fun P => ∏ j, rootSum θ (e j) P) hm
  have horth := (GlobalTheory.CuspGL.torus_orthogonality F θ hθ m hm).2
  set T := {α : AlgebraicClosure F | α ^ N = 1} with hT
  have hTfin : T.Finite := by
    apply (Polynomial.nthRoots N (1 : AlgebraicClosure F)).toFinset.finite_toSet.subset
    intro α hα
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    exact (Polynomial.mem_nthRoots hN0).2 hα
  have key : ∀ α ∈ T, θ α ^ k * star (∏ j, rootSum θ (e j) (minpoly F α ^ (m / (minpoly F α).natDegree)))
      = ∑ a : Fin l → Fin m, θ α ^ k * star (θ α ^ (∑ j, e j * q ^ (a j : ℕ))) := by
    intro α hα
    have hr : ∀ j, rootSum θ (e j) (minpoly F α ^ (m / (minpoly F α).natDegree)) = ∑ a : Fin m, θ α ^ (e j * q ^ (a : ℕ)) :=
      fun j => (GlobalTheory.T.rootSum_minpoly_pow_eq_sum_range F θ m (e j) α hm hα).trans (Finset.sum_range (fun a => θ α ^ (e j * q ^ a)))
    simp_rw [hr]
    rw [← Finset.mul_sum, ← star_sum, Finset.prod_univ_sum]
    simp only [Fintype.piFinset_univ, Finset.prod_pow_eq_pow_sum]
  have hsum : ∑ᶠ α ∈ T, θ α ^ k * star (∏ j, rootSum θ (e j) (minpoly F α ^ (m / (minpoly F α).natDegree)))
      = ∑ a : Fin l → Fin m, ∑ᶠ α ∈ T, θ α ^ k * star (θ α ^ (∑ j, e j * q ^ (a j : ℕ))) := by
    rw [finsum_mem_congr rfl key, finsum_mem_eq_finite_toFinset_sum _ hTfin, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [finsum_mem_eq_finite_toFinset_sum _ hTfin]
  rw [hsum] at htor
  simp_rw [horth] at htor
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, hcast] at htor
  apply mul_left_cancel₀ hNne
  rw [htor]
  ring

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootFreeActionFinsuppSumStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KummerSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitiveRoot_free_action_finsupp_sum : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] [Nontrivial A] (ζ : Prim q A) (ι : Type) (s : Finset ι) (c : ι → ULift.{1} (ZMod q)) (a : ι → ℕ) (v w : ι → Aˣ), (∀ i ∈ s, (w i : A) = ζ.1 ^ a i * v i) → (∑ i ∈ s, (Finsupp.single (w i) (c i) - Finsupp.single (v i) (c i))) = 0 → ∑ i ∈ s, (c i).down * (a i : ZMod q) = 0 := by
  first | (exact @GlobalTheory.EtC.FreeActSum.free_act_sum) | (exact GlobalTheory.EtC.FreeActSum.free_act_sum) | (intros; apply GlobalTheory.EtC.FreeActSum.free_act_sum  <;> assumption)
end

