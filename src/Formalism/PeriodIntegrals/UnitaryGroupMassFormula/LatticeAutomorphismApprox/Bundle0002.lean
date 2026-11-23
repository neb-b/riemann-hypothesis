module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.LocSplitChiOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.Bundle0002

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.SecondCoordinateVectorNsmul
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.ScXuExists.BrB

open NumberField IsDedekindDomain Matrix PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.ScXuExists
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists

abbrev LL (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) : Submodule (OV I v) (Fin I.n → RV I v) :=
  Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))

theorem sigV_sigV (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (r : RV I v) :
    sigV I v (sigV I v r) = r := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp only [sigV, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rw [show I.cm.sig (I.cm.sig e) = e from star_star e]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem sigV_alg (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (c : KV I v) :
    sigV I v (algebraMap (KV I v) (RV I v) c) = algebraMap (KV I v) (RV I v) c := by
  simp [sigV, Algebra.TensorProduct.algebraMap_apply]

def vecqL (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (q : RV I v →+* KV I v)
    (hq : ∀ c, q (algebraMap (KV I v) (RV I v) c) = c) :
    (Fin I.n → RV I v) →ₗ[OV I v] (Fin I.n → KV I v) where
  toFun x i := q (x i)
  map_add' x y := by funext i; simp
  map_smul' c x := by
    funext i
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [PI.FinKW.LocTo.ov_smul_eq, map_mul]
    have e : ((c : KV I v) ⊗ₜ[I.F] (1 : I.E)) = algebraMap (KV I v) (RV I v) (c : KV I v) := by
      simp [Algebra.TensorProduct.algebraMap_apply]
    rw [e, hq]
    rfl

theorem exists_of_mem_span (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (q : RV I v →+* KV I v)
    (hq : ∀ c, q (algebraMap (KV I v) (RV I v) c) = c) (y : Fin I.n → KV I v)
    (hy : y ∈ Submodule.span (OV I v)
      ((fun x : Fin I.n → RV I v => fun i => q (x i)) '' (LL I v : Set (Fin I.n → RV I v)))) :
    ∃ x ∈ LL I v, (fun i => q (x i)) = y := by
  have hy' : y ∈ Submodule.span (OV I v) (⇑(vecqL I v q hq) '' (LL I v : Set (Fin I.n → RV I v))) := hy
  rw [← Submodule.map_coe, Submodule.span_eq] at hy'
  obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hy'
  exact ⟨x, hx, hxy⟩

theorem mem_LL_iff (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (ε : RV I v) (p1 : RV I v →+* KV I v)
    (hp : IsAdaptedFirstProjection I v ε p1) (hinj : Function.Injective (piHom (sigV I v) p1))
    (hε : ∀ w ∈ LL I v, ε • w ∈ LL I v) (x : Fin I.n → RV I v) :
    x ∈ LL I v ↔ vec1 p1 x ∈ Lam1 I v p1 ∧ vec2 p1 x ∈ Lam2 I v p1 := by
  obtain ⟨hp1, hpe, hpse, -⟩ := hp
  constructor
  · intro hx
    exact ⟨Submodule.subset_span (Set.mem_image_of_mem _ hx), Submodule.subset_span (Set.mem_image_of_mem _ hx)⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨x1, hx1, e1⟩ := exists_of_mem_span I v p1 hp1 (vec1 p1 x) h1
    have hq2 : ∀ c, (p1.comp (sigV I v)) (algebraMap (KV I v) (RV I v) c) = c := by
      intro c
      rw [RingHom.comp_apply, sigV_alg, hp1]
    obtain ⟨x2, hx2, e2⟩ := exists_of_mem_span I v (p1.comp (sigV I v)) hq2 (vec2 p1 x) h2
    have hw : ε • x1 + (x2 - ε • x2) ∈ LL I v :=
      (LL I v).add_mem (hε x1 hx1) ((LL I v).sub_mem hx2 (hε x2 hx2))
    have hxw : x = ε • x1 + (x2 - ε • x2) := by
      funext i
      apply hinj
      have f1 : p1 (x1 i) = p1 (x i) := congrFun e1 i
      have f2 : p1 (sigV I v (x2 i)) = p1 (sigV I v (x i)) := congrFun e2 i
      simp only [piHom, RingHom.prod_apply, RingHom.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul, map_add, map_sub, map_mul, hpe, hpse, f1, f2]
      refine Prod.ext ?_ ?_ <;> simp
    rw [hxw]
    exact hw

theorem first_coordinate_vector_sub {I : AutInst} {v : HeightOneSpectrum (𝓞 I.F)} (p1 : RV I v →+* KV I v)
    (X X' : Fin I.n → RV I v) : vec1 p1 (X - X') = vec1 p1 X - vec1 p1 X' := by
  funext i
  simp [vec1]

theorem second_coordinate_vector_sub {I : AutInst} {v : HeightOneSpectrum (𝓞 I.F)} (p1 : RV I v →+* KV I v)
    (X X' : Fin I.n → RV I v) : vec2 p1 (X - X') = vec2 p1 X - vec2 p1 X' := by
  funext i
  simp [vec2]

theorem first_coordinate_vector_nsmul {I : AutInst} {v : HeightOneSpectrum (𝓞 I.F)} (p1 : RV I v →+* KV I v)
    (c : ℕ) (X : Fin I.n → RV I v) : vec1 p1 ((c : RV I v) • X) = (c : KV I v) • vec1 p1 X := by
  funext i
  simp [vec1]

theorem second_coordinate_vector_nsmul {I : AutInst} {v : HeightOneSpectrum (𝓞 I.F)} (p1 : RV I v →+* KV I v)
    (c : ℕ) (X : Fin I.n → RV I v) : vec2 p1 ((c : RV I v) • X) = (c : KV I v) • vec2 p1 X := by
  funext i
  simp [vec2]

end PI.UnitaryGroupMassFormula.ScXuExists.BrB
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.ValNatCastLtOne
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.ScXuExists

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists

theorem val_natCast_lt_one (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (g : ℕ)
    (hg : (g : 𝓞 F) ∈ v.asIdeal) : Valued.v ((g : v.adicCompletion F)) < 1 := by
  have h1 : ((g : v.adicCompletion F)) = (((algebraMap (𝓞 F) F (g : 𝓞 F)) : F) : v.adicCompletion F) := by
    rw [map_natCast (algebraMap (𝓞 F) F)]
    first
    | exact (map_natCast (algebraMap F (v.adicCompletion F)) g).symm
    | (rw [← map_natCast (algebraMap F (v.adicCompletion F)) g]; rfl)
  rw [h1]
  first
  | rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem v _).mpr hg
  | rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation]
    exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem v _).mpr hg
  | simpa [IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem] using hg

theorem natCast_mem_max (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (g : ℕ)
    (hg : (g : 𝓞 F) ∈ v.asIdeal) :
    (g : v.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have h1 := val_natCast_lt_one F v g hg
  have h2 : Valued.v ((w : v.adicCompletion F)) ≤ 1 := w.2
  have h3 : (g : v.adicCompletion F) * (w : v.adicCompletion F) = 1 := by
    have := congrArg Subtype.val hw
    simpa using this
  have h4 := congrArg Valued.v h3
  rw [map_mul, map_one] at h4
  have h5 : Valued.v ((g : v.adicCompletion F)) * Valued.v ((w : v.adicCompletion F)) < 1 :=
    calc Valued.v ((g : v.adicCompletion F)) * Valued.v ((w : v.adicCompletion F))
        ≤ Valued.v ((g : v.adicCompletion F)) * 1 := by gcongr
      _ = Valued.v ((g : v.adicCompletion F)) := mul_one _
      _ < 1 := h1
  exact (ne_of_lt h5) h4

theorem vecV_smul' (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (a : I.E ⊗[I.F] Af I.F)
    (x : Fin I.n → I.E ⊗[I.F] Af I.F) :
    PI.FinKW.vecV I v (a • x) = PI.FinKW.psiV I v a • PI.FinKW.vecV I v x := by
  funext i
  simp only [PI.FinKW.vecV, Pi.smul_apply, smul_eq_mul, map_mul]

theorem vecV_add' (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (x y : Fin I.n → I.E ⊗[I.F] Af I.F) :
    PI.FinKW.vecV I v (x + y) = PI.FinKW.vecV I v x + PI.FinKW.vecV I v y := by
  funext i
  simp only [PI.FinKW.vecV, Pi.add_apply, map_add (f := _)]

theorem psiV_natCast (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (m : ℕ) :
    PI.FinKW.psiV I v (m : I.E ⊗[I.F] Af I.F) = (m : RV I v) := map_natCast _ m

theorem vecV_mL (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (m : ℕ) (x : Fin I.n → I.E ⊗[I.F] Af I.F)
    (hx : x ∈ mL I m) :
    ∃ w ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)), PI.FinKW.vecV I v x = (m : RV I v) • w := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x', hx', rfl⟩ := hy
    refine ⟨PI.FinKW.vecV I v x', PI.FinKW.LocTo.mem_local_lattice_iff I x' hx' v, ?_⟩
    rw [vecV_smul', psiV_natCast]
  | zero =>
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    funext i; simp [PI.FinKW.vecV]
  | add x y _ _ hx hy =>
    obtain ⟨w1, hw1, h1⟩ := hx
    obtain ⟨w2, hw2, h2⟩ := hy
    refine ⟨w1 + w2, Submodule.add_mem _ hw1 hw2, ?_⟩
    rw [vecV_add', h1, h2, smul_add]
  | smul c x _ hx =>
    obtain ⟨w, hw, h⟩ := hx
    refine ⟨PI.FinKW.psiV I v (c : I.E ⊗[I.F] Af I.F) • w,
      PI.FinKW.LocTo.intAf_le_mulSet I v c.2 w hw, ?_⟩
    show PI.FinKW.vecV I v ((c : I.E ⊗[I.F] Af I.F) • x) = _
    rw [vecV_smul', h, smul_comm]

end PI.UnitaryGroupMassFormula.ScXuExists
end
end

