module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0866
public import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0115
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyEqOfIsZetaCont

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenFrameCongruenceUnitaryAdelic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct Topology

noncomputable section

namespace GlobalTheory.FrameCongOpen

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def congInt (N : ℕ) : Subgroup (GL (Fin n) (Formalism.L2.Herm.intAf F E)) :=
  (Matrix.GeneralLinearGroup.map (n := Fin n)
    (Ideal.Quotient.mk (Ideal.span {((N : ℕ) : Formalism.L2.Herm.intAf F E)}))).ker

theorem mem_congInt_span {N : ℕ} (z : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    z ∈ congInt N ↔ ∀ a b, z.1 a b - (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) a b ∈
      Ideal.span {((N : ℕ) : Formalism.L2.Herm.intAf F E)} := by
  rw [congInt, MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff]
  refine forall₂_congr fun a b => ?_
  rw [← Ideal.Quotient.eq]
  change Ideal.Quotient.mk _ (z.1 a b) = (1 : Matrix (Fin n) (Fin n) _) a b ↔ _
  simp only [Matrix.one_apply]
  split_ifs
  · rw [map_one]
  · rw [map_zero]

theorem mem_congInt {N : ℕ} (z : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    z ∈ congInt N ↔ ∀ a b, ∃ w ∈ Formalism.L2.Herm.intAf F E,
      ((z.1 a b : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) -
        (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) a b = (N : E ⊗[F] Formalism.L2.Herm.Af F) * w := by
  have hone : ∀ a b, (((1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) a b : Formalism.L2.Herm.intAf F E) :
      E ⊗[F] Formalism.L2.Herm.Af F) = (1 : Matrix (Fin n) (Fin n) _) a b := fun a b => by
    simp only [Matrix.one_apply]; split_ifs <;> rfl
  rw [mem_congInt_span]
  refine forall₂_congr fun a b => ?_
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, c.2, ?_⟩
    rw [← hone, ← AddSubgroupClass.coe_sub, ← hc, Subring.coe_mul, Subring.coe_natCast, mul_comm]
  · rintro ⟨w, hw, e⟩
    refine ⟨⟨w, hw⟩, Subtype.ext ?_⟩
    rw [Subring.coe_mul, Subring.coe_natCast, AddSubgroupClass.coe_sub, hone, e, mul_comm]

theorem mem_cong (β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (N : ℕ)
    (h1 : ∀ i j, (β⁻¹ * x * β).1 i j ∈ Formalism.L2.Herm.intAf F E)
    (h2 : ∀ i j, (β⁻¹ * x * β)⁻¹.1 i j ∈ Formalism.L2.Herm.intAf F E)
    (h3 : ∀ i j, ∃ z ∈ Formalism.L2.Herm.intAf F E,
      (β⁻¹ * x * β).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j = (N : E ⊗[F] Formalism.L2.Herm.Af F) * z) :
    x ∈ (congInt (F := F) (E := E) (n := n) N).map (frGL β) := by
  have hx : x = β * (β⁻¹ * x * β) * β⁻¹ := by group
  generalize β⁻¹ * x * β = m at h1 h2 h3 hx
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) =>
      A.map (Formalism.L2.Herm.intAf F E).subtype := Matrix.map_injective Subtype.val_injective
  let y : GL (Fin n) (Formalism.L2.Herm.intAf F E) :=
    ⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩,
      hi (by
        simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
        exact m.mul_inv),
      hi (by
        simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
        exact m.inv_mul)⟩
  have hy : frGL β y = x := by
    have : intGL F E n y = m := Units.ext rfl
    rw [hx, ← this]
    rfl
  exact ⟨y, (mem_congInt y).2 fun i j => h3 i j, hy⟩

theorem eventually_cong_mat (β : GL (Fin n) (E ⊗[F] Af F)) (N : ℕ) (hN : 0 < N) {X : Type} [TopologicalSpace X]
    {x₀ : X} {φ : X → GL (Fin n) (Af F ⊗[F] E)} (hf : Continuous φ) (h₀ : φ x₀ = 1) :
    ∀ᶠ κ in 𝓝 x₀, Formalism.UG.bc (GlobalTheory.Mass.swapTens F E (Af F) : _ →+* _) (φ κ) ∈
      (congInt (F := F) (E := E) (n := n) N).map (frGL β) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  have ho := (GlobalTheory.Mass.intTens_open_compact F E).1
  set s := GlobalTheory.Mass.swapTens F E (Af F)
  let β' : GL (Fin n) (Af F ⊗[F] E) := Formalism.UG.bc (s.symm : _ →+* _) β
  have hβ : Formalism.UG.bc (s : _ →+* _) β' = β := Units.ext (Matrix.ext fun i j => s.apply_symm_apply _)
  let m : X → GL (Fin n) (Af F ⊗[F] E) := fun κ => β'⁻¹ * φ κ * β'
  have hm : Continuous m := (continuous_const.mul hf).mul continuous_const
  have hm1 : m x₀ = 1 := by simp only [m, h₀, mul_one, inv_mul_cancel]
  have hs : ∀ κ, β⁻¹ * Formalism.UG.bc (s : _ →+* _) (φ κ) * β = Formalism.UG.bc (s : _ →+* _) (m κ) := fun κ => by
    simp only [m, map_mul, map_inv, hβ]
  have hone : ∀ i j, (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j ∈
      GlobalTheory.Mass.intTens F E := fun i j => by
    simp only [Matrix.one_apply]; split_ifs
    exacts [one_mem _, zero_mem _]
  have e1 : ∀ᶠ κ in 𝓝 x₀, ∀ i j, (m κ).1 i j ∈ GlobalTheory.Mass.intTens F E := by
    simp only [Filter.eventually_all]
    intro i j
    exact (ho.preimage ((Units.continuous_val.comp hm).matrix_elem i j)).mem_nhds
      (show (m x₀).1 i j ∈ _ by rw [hm1]; exact hone i j)
  have e2 : ∀ᶠ κ in 𝓝 x₀, ∀ i j, (m κ)⁻¹.1 i j ∈ GlobalTheory.Mass.intTens F E := by
    simp only [Filter.eventually_all]
    intro i j
    exact (ho.preimage ((Units.continuous_coe_inv.comp hm).matrix_elem i j)).mem_nhds
      (show (m x₀)⁻¹.1 i j ∈ _ by rw [hm1, inv_one]; exact hone i j)
  have e3 : ∀ᶠ κ in 𝓝 x₀, ∀ i j,
      algebraMap F _ ((N : ℕ) : F)⁻¹ *
        ((m κ).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j) ∈ GlobalTheory.Mass.intTens F E := by
    simp only [Filter.eventually_all]
    intro i j
    have hc : Continuous fun κ => algebraMap F (Af F ⊗[F] E) ((N : ℕ) : F)⁻¹ *
        ((m κ).1 i j - (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j) :=
      continuous_const.mul (((Units.continuous_val.comp hm).matrix_elem i j).sub continuous_const)
    refine (ho.preimage hc).mem_nhds ?_
    rw [Set.mem_preimage, hm1, Units.val_one, sub_self, mul_zero]
    exact (GlobalTheory.Mass.intTens F E).zero_mem
  filter_upwards [e1, e2, e3] with κ h1 h2 h3
  refine mem_cong β _ N ?_ ?_ ?_
  · rw [hs]; exact h1
  · rw [hs, ← map_inv]; exact h2
  · intro i j
    refine ⟨_, h3 i j, ?_⟩
    have hN' : ((N : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    have e : (m κ).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j =
        (N : ℕ) * (algebraMap F _ ((N : ℕ) : F)⁻¹ *
        ((m κ).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j)) := by
      rw [← mul_assoc, ← map_natCast (algebraMap F (Af F ⊗[F] E)), ← map_mul,
        mul_inv_cancel₀ hN', map_one, one_mul]
    have := congrArg s e
    rw [map_mul, map_natCast, map_sub] at this
    rw [hs]
    refine Eq.trans ?_ this
    congr 1
    simp only [Matrix.one_apply]; split_ifs <;> simp

def congFr (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (N : ℕ) : Subgroup (GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :=
  (congInt (F := F) (E := E) (n := n) N).map (frGL β)

theorem mem_congFr {β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {N : ℕ} (hx : x ∈ congFr β N) :
    ∃ z : GL (Fin n) (Formalism.L2.Herm.intAf F E), frGL β z = x ∧ ∀ a b, ∃ w ∈ Formalism.L2.Herm.intAf F E,
      ((z.1 a b : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) -
        (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) a b = (N : E ⊗[F] Formalism.L2.Herm.Af F) * w := by
  obtain ⟨z, hz, e⟩ := Subgroup.mem_map.1 hx
  exact ⟨z, e, (mem_congInt z).1 hz⟩

end General

theorem exists_open_cong : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (N : ℕ), 0 < N → ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ κ ∈ U, ∃ z : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E), Formalism.L2.DIV.frGL β z = Lev.finE V κ ∧ ∀ a b, ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ((z.1 a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) - (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) a b = (N : Lev.EAf D) * w := by
  intro D V β N hN
  refine ⟨(congFr β N).comap (Formalism.IndefR.Lev.finE V),
    ?_, fun κ hκ => ?_⟩
  · haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
    haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
    haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram
    have hf : Continuous (finHom V) :=
      (continuous_subtype_val.comp hπ.continuous).congr fun κ => hπ κ
    exact eventually_cong_mat β N hN hf (map_one _)
  · exact mem_congFr (Subgroup.mem_comap.1 hκ)

end GlobalTheory.FrameCongOpen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
section
noncomputable section

namespace GlobalTheory.SphTheta

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil

def antiG (L : Type) [Field L] (n : ℕ) : GL (Fin n) L :=
  ⟨antiJ L n, antiJ L n, P.fIwasawa_antiJ_mul_antiJ, P.fIwasawa_antiJ_mul_antiJ⟩

def hi (n : ℕ) (k : Fin (n / 2)) : Fin n := ⟨n - n / 2 + k, by omega⟩

def lo (n : ℕ) (k : Fin (n / 2)) : Fin n := ⟨k, by omega⟩

def liftPar (q : ℂˣ) (n n' : ℕ) (α : Fin (n / 2) → ℂˣ) (k : Fin (n' / 2)) : ℂˣ :=
  if h : k.1 < n' / 2 - n / 2 then (-1) ^ n * q ^ ((n' : ℤ) - n - 1 - 2 * (k.1 : ℤ))
  else (-1) ^ (n + n') * (α ⟨n' / 2 - 1 - k.1, by omega⟩)⁻¹

section

variable {L : Type} [Field L]

def embLow (n' n : ℕ) (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L) : Matrix (Fin n') (Fin n) L := fun r c =>
  if h : n' - n' / 2 ≤ r.1 ∧ n - n / 2 ≤ c.1 then z ⟨r.1 - (n' - n' / 2), by omega⟩ ⟨c.1 - (n - n / 2), by omega⟩ else 0

def lowBlock {n : ℕ} (g : Matrix (Fin n) (Fin n) L) : Matrix (Fin (n / 2)) (Fin (n / 2)) L := g.submatrix (hi n) (hi n)

def pairing (σ : L →+* L) (δ : L) (ψ : AddChar L ℂ) {n n' : ℕ} (x y : Matrix (Fin n') (Fin n) L) : ℂ :=
  ψ (δ * (∑ i, ∑ j, x i j * σ (y i.rev j.rev)) + σ (δ * (∑ i, ∑ j, x i j * σ (y i.rev j.rev))))

variable [Valued L (WithZero (Multiplicative ℤ))]


variable (L) in
def intMat (α β : Type) : Submodule (intL L) (Matrix α β L) where
  carrier := {x | ∀ i j, x i j ∈ intL L}
  add_mem' h h' i j := add_mem (h i j) (h' i j)
  zero_mem' _ _ := zero_mem _
  smul_mem' r _ h i j := mul_mem r.2 (h i j)


variable (L) in
def mixLat (n' n : ℕ) : Submodule (intL L) (Matrix (Fin n') (Fin n) L) where
  carrier := {x | ∀ r c, (n' - n' / 2 ≤ r.1 ∨ n' / 2 ≤ r.1 ∧ c.1 < n / 2 → x r c = 0) ∧
    (n' / 2 ≤ r.1 → c.1 < n - n / 2 → x r c ∈ intL L)}
  add_mem' h h' r c := ⟨fun e => by rw [Matrix.add_apply, (h r c).1 e, (h' r c).1 e, add_zero],
    fun e e' => add_mem ((h r c).2 e e') ((h' r c).2 e e')⟩
  zero_mem' _ _ := ⟨fun _ => rfl, fun _ _ => zero_mem _⟩
  smul_mem' a x h r c := ⟨fun e => by rw [Matrix.smul_apply, (h r c).1 e, smul_zero],
    fun e e' => mul_mem a.2 ((h r c).2 e e')⟩

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def CayleyRule {σ : L →+* L} {n : ℕ} (q N : ℕ) {α β : Type} (ρ : Matrix α β L → Module.End ℂ M)
    (π : GU σ n →* Module.End ℂ M) (s : M) : Prop :=
  ∀ e : M →ₗ[ℂ] ℂ, (∀ u ∈ intMat L α β, ∀ v, e (ρ u v) = e v) → ∀ g : GU σ n, (1 + g.1.1).det ≠ 0 →
    (1 + g.1.1)⁻¹ ∈ intMat L (Fin n) (Fin n) → e (π g⁻¹ s) = ((-1) ^ N * (q : ℂ) ^ N) ^ ordL (1 + g.1.1).det * e s

def IsStd (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) {n n' : ℕ}
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M) : Prop :=
  LocPair ϖ σ q δ (antiG L n) (antiG L n') ψ ρ ω ∧ s ≠ 0 ∧ LocVac ρ s ∧ Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem antiJ_mul_apply {n : ℕ} {β : Type} (A : Matrix (Fin n) β L) (i : Fin n) (j : β) : (antiJ L n * A) i j = A i.rev j := by
  simp [Matrix.mul_apply, P.fIwasawa_antiJ]

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem mul_antiJ_apply {n : ℕ} {β : Type} (A : Matrix β (Fin n) L) (i : β) (j : Fin n) : (A * antiJ L n) i j = A i j.rev := by
  simp only [Matrix.mul_apply, P.fIwasawa_antiJ, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single j.rev] <;> simp +contextual [eq_comm (a := j), Fin.rev_eq_iff]

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem locH_antiG (σ : L →+* L) (δ : L) {n n' : ℕ} (x y : Matrix (Fin n') (Fin n) L) :
    locH σ δ (antiG L n) (antiG L n') x y = δ * ∑ i, ∑ j, x i j * σ (y i.rev j.rev) := by
  show δ * Matrix.trace (antiJ L n * (y.map σ)ᵀ * antiJ L n' * x) = _
  congr 1
  rw [Matrix.trace, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_antiJ_apply, antiJ_mul_apply, mul_comm]
  rfl

theorem mem_intL {x : L} : x ∈ intL L ↔ Valued.v x ≤ 1 := Iff.rfl

def intConj {σ : L →+* L} (hv : ∀ x, Valued.v (σ x) = Valued.v x) : intL L →+* intL L :=
  (σ.comp (intL L).subtype).codRestrict _ fun x => mem_intL.2 ((hv x).trans_le x.2)

def half (h2 : Valued.v (2 : L) = 1) : intL L := ⟨2⁻¹, mem_intL.2 (by rw [map_inv₀, h2, inv_one])⟩

variable {ϖ : L} {σ : L →+* L} {q : ℕ} {δ : L} {ψ : AddChar L ℂ} {n n' : ℕ}

theorem two_ne_zero_of (h2 : Valued.v (2 : L) = 1) : (2 : L) ≠ 0 := fun h => by simp [h] at h2

theorem isHeis_of (hσ : ∀ x, σ (σ x) = x) (hv : ∀ x, Valued.v (σ x) = Valued.v x) (h2 : Valued.v (2 : L) = 1)
    (hδ : σ δ = -δ) {ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M} (h0 : ρ 0 = 1)
    (hm : ∀ x y, ρ x * ρ y = ψ ((locH σ δ (antiG L n) (antiG L n') x y +
      σ (locH σ δ (antiG L n) (antiG L n') x y)) / 2) • ρ (x + y)) :
    IsHeis (intConj hv) (half h2) (pairing σ δ ψ) ρ := by
  refine { sg_sg := fun r => Subtype.ext (hσ r)
           w_add := ?_, add_left := ?_, add_right := ?_, alt := ?_
           adj := ?_, zero := ?_, comp := ?_ }
  · apply Subtype.ext
    have := two_ne_zero_of h2
    show (2⁻¹ : L) + σ 2⁻¹ = 1
    rw [map_inv₀, map_ofNat]; field_simp; norm_num
  · intro x y z
    simp only [pairing, ← AddChar.map_add_eq_mul, Matrix.add_apply, add_mul, Finset.sum_add_distrib, mul_add, map_add (f := _)]
    congr 1; ring
  · intro x y z
    simp only [pairing, ← AddChar.map_add_eq_mul, Matrix.add_apply, add_mul, Finset.sum_add_distrib, mul_add, map_add (f := _)]
    congr 1; ring
  · intro x
    have : σ (∑ i, ∑ j, x i j * σ (x i.rev j.rev)) = ∑ i, ∑ j, x i j * σ (x i.rev j.rev) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, hσ]
      rw [← Equiv.sum_comp Fin.revPerm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Equiv.sum_comp Fin.revPerm]
      simp [mul_comm]
    rw [pairing, map_mul, this, hδ, neg_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  · intro r x y
    have : ∀ i j, (r • x) i j * σ (y i.rev j.rev) = x i j * σ ((intConj hv r • y) i.rev j.rev) := fun i j => by
      show (r : L) * x i j * _ = x i j * σ (σ r * y i.rev j.rev)
      rw [map_mul, hσ]; ring
    simp only [pairing, this]
  · intro v
    rw [h0]; rfl
  · intro x y v
    have e : ∀ i j, (half h2 • x) i j * σ (y i.rev j.rev) = 2⁻¹ * (x i j * σ (y i.rev j.rev)) := fun i j =>
      mul_assoc _ _ _
    rw [← Module.End.mul_apply, hm, locH_antiG, pairing]
    simp only [e, ← Finset.mul_sum, map_mul, map_inv₀, map_ofNat, LinearMap.smul_apply]
    congr 2; ring

theorem pairing_single (x : Matrix (Fin n') (Fin n) L) (i : Fin n') (j : Fin n) (u : L) :
    pairing σ δ ψ x (Matrix.single i.rev j.rev u) = ψ (δ * (x i j * σ u) + σ (δ * (x i j * σ u))) := by
  have : ∑ i', ∑ j', x i' j' * σ (Matrix.single i.rev j.rev u i'.rev j'.rev) = x i j * σ u := by
    rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      rw [Matrix.single_apply_of_col_ne _ _ (fun h => hb (Fin.rev_injective h).symm), map_zero, mul_zero]
    · simp
    · intro b _ hb
      exact Finset.sum_eq_zero fun c _ => by
        rw [Matrix.single_apply_of_row_ne (fun h => hb (Fin.rev_injective h).symm), map_zero, mul_zero]
    · simp
  rw [pairing, this]

theorem exists_pairing_single_ne (hU : IsUnramInv ϖ σ q) (h2 : Valued.v (2 : L) = 1) (hδ : Valued.v δ = 1)
    (hψ : ∃ a ∈ intL L, σ a = a ∧ ψ (ϖ⁻¹ * a) ≠ 1) (x : Matrix (Fin n') (Fin n) L) {i : Fin n'} {j : Fin n}
    (hx : x i j ∉ intL L) : ∃ u ∈ intL L, pairing σ δ ψ x (Matrix.single i.rev j.rev u) ≠ 1 := by
  obtain ⟨a, ha, ha', hne⟩ := hψ
  have h0 : x i j ≠ 0 := fun h => hx (h ▸ zero_mem _)
  have hd : δ ≠ 0 := fun h => by simp [h] at hδ
  have h20 := two_ne_zero_of h2
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  refine ⟨σ (ϖ⁻¹ * a / (2 * δ * x i j)), mem_intL.2 ?_, ?_⟩
  · have hv0 : Valued.v (x i j) ≠ 0 := (Valuation.ne_zero_iff _).2 h0
    have h1 : WithZero.exp (1 : ℤ) ≤ Valued.v (x i j) := by
      rw [mem_intL, not_le, ← WithZero.exp_log hv0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
      rw [← WithZero.exp_log hv0, WithZero.exp_le_exp]; omega
    rw [hU.2.1, map_div₀, map_mul, map_mul, map_mul, h2, hδ, one_mul, one_mul, map_inv₀, hϖ, ← WithZero.exp_neg, neg_neg,
      div_le_one₀ (zero_lt_iff.2 hv0)]
    exact (mul_le_of_le_one_right' ha).trans h1
  · have : δ * (x i j * (ϖ⁻¹ * a / (2 * δ * x i j))) = ϖ⁻¹ * a / 2 := by field_simp
    rw [pairing_single, hU.1, this, map_div₀, map_mul, map_inv₀, hU.2.2.1, ha', map_ofNat, show ϖ⁻¹ * a / 2 + ϖ⁻¹ * a / 2 = ϖ⁻¹ * a by field_simp; norm_num]
    exact hne

theorem selfDual_intMat (hU : IsUnramInv ϖ σ q) (h2 : Valued.v (2 : L) = 1) (hδ : Valued.v δ = 1)
    (hψ0 : ∀ a ∈ intL L, σ a = a → ψ a = 1) (hψ : ∃ a ∈ intL L, σ a = a ∧ ψ (ϖ⁻¹ * a) ≠ 1) :
    SelfDual (pairing σ δ ψ) (intMat L (Fin n') (Fin n)) := by
  have hs : ∀ a ∈ intL L, σ a ∈ intL L := fun a ha => mem_intL.2 ((hU.2.1 a).trans_le ha)
  refine fun x => ⟨fun hx y hy => ?_, fun h i j => ?_⟩
  · have : δ * ∑ i, ∑ j, x i j * σ (y i.rev j.rev) ∈ intL L :=
      mul_mem (mem_intL.2 hδ.le) (sum_mem fun i _ => sum_mem fun j _ => mul_mem (hx i j) (hs _ (hy _ _)))
    exact hψ0 _ (add_mem this (hs _ this)) (by rw [map_add (f := _), hU.1, add_comm])
  · by_contra hx
    obtain ⟨u, hu, hne⟩ := exists_pairing_single_ne hU h2 hδ hψ x hx
    refine hne (h _ fun i' j' => ?_)
    rw [Matrix.single_apply]
    split_ifs
    exacts [hu, zero_mem _]

variable {ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M} {ω : GU σ n × GU σ n' →* Module.End ℂ M} {s : M}

theorem IsStd.v_two (h : IsStd ϖ σ q δ ψ ρ ω s) : Valued.v (2 : L) = 1 := LatModel.v_two h.1.unr h.1.odd

theorem IsStd.isHeis (h : IsStd ϖ σ q δ ψ ρ ω s) : IsHeis (intConj h.1.unr.2.1) (half h.v_two) (pairing σ δ ψ) ρ :=
  isHeis_of h.1.unr.1 h.1.unr.2.1 h.v_two h.1.delta.2 h.1.rho_zero h.1.rho_mul

theorem IsStd.selfDual (h : IsStd ϖ σ q δ ψ ρ ω s) : SelfDual (pairing σ δ ψ) (intMat L (Fin n') (Fin n)) :=
  selfDual_intMat h.1.unr h.v_two h.1.delta.1 h.1.psi_int h.1.psi_ne

theorem IsStd.fixes (h : IsStd ϖ σ q δ ψ ρ ω s) : Fixes ρ (intMat L (Fin n') (Fin n)) s := h.2.2.1

theorem mem_KU_iff {g : GU σ n} : g ∈ KU σ n ↔ (g : GL (Fin n) L) ∈ GLint (Fin n) (intL L) :=
  ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩

end

end GlobalTheory.SphTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenEmbeddingFiniteAdeleOfSPartAndIntegralPartStatement
section
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpenEmbedding_finiteAdeleOfSPartAndIntegralPart : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))), IsOpenEmbedding (jS F S) := by
  first | exact @GlobalTheory.ModuLR.isOpenEmbedding_jS | exact GlobalTheory.ModuLR.isOpenEmbedding_jS | (intros; apply GlobalTheory.ModuLR.isOpenEmbedding_jS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelDatumValueEqProdLocalResidueValues
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StepVec

theorem level_character_congr {E : Type} [Field E] [NumberField E] {Pg : Finset (Formalism.L2.DIV.Pl E)} {r : ℕ}
    {P Q : Formalism.L2.DIV.LevelP Pg r ℂ} (h : P = Q) (x : Formalism.L2.DIV.G0 Pg r) (hx : x ∈ P.H) (hx' : x ∈ Q.H) :
    P.chi ⟨x, hx⟩ = Q.chi ⟨x, hx'⟩ := by
  subst h; rfl

theorem omegaG_eq_prod_gLoc : ∀ (D : D7) (a b : ℕ) (L : Formalism.L2.DIV.LevDat D.host.E ℂ a)
    (χ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (Hl : ∀ PP : ↥L.Pg, Subgroup (GL (Fin L.r) (Formalism.L2.DIV.kP PP.1))) (cl : ∀ PP : ↥L.Pg, Hl PP →* ℂˣ),
    L.P = Formalism.L2.DIV.LevelP.ofLocal Hl cl →
    ∀ y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP),
      omegaG L χ y = ∏ PP : ↥L.Pg, gLoc L PP.1 (Hl PP) (cl PP) (χ PP.1) (y PP.1) := by
  intro D a b L χ Hl cl hP y
  classical
  have hmem : ∀ x, x ∈ L.P.H ↔ ∀ PP, x PP ∈ Hl PP := by
    intro x; rw [hP]; simp [Formalism.L2.DIV.LevelP.ofLocal, Subgroup.mem_pi]
  by_cases hall : ∀ PP : ↥L.Pg, LowZero a (y PP.1) ∧ ∃ g : GL (Fin a) (Formalism.L2.DIV.kP PP.1),
      ((g : GL (Fin a) _) : Matrix (Fin a) (Fin a) _) = topL a (y PP.1) ∧
      g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf L.r L.t) ∧ Formalism.L2.DIV.upperLeftBlock L.hr g ∈ Hl PP
  · have hG : (∀ PP ∈ L.Pg, LowZero a (y PP)) ∧
        ∃ g : ∀ PP : ↥L.Pg, GL (Fin a) (Formalism.L2.DIV.kP PP.1),
          (∀ PP : ↥L.Pg, ((g PP : GL (Fin a) _) : Matrix (Fin a) (Fin a) _) = topL a (y PP.1)) ∧
          (∀ PP : ↥L.Pg, g PP ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf L.r L.t)) ∧
          (fun PP => Formalism.L2.DIV.upperLeftBlock L.hr (g PP)) ∈ L.P.H :=
      ⟨fun PP hPP => (hall ⟨PP, hPP⟩).1, fun PP => (hall PP).2.choose, fun PP => (hall PP).2.choose_spec.1,
        fun PP => (hall PP).2.choose_spec.2.1, (hmem _).2 fun PP => (hall PP).2.choose_spec.2.2⟩
    have key : ∀ PP, hG.2.choose PP = (hall PP).2.choose := fun PP =>
      Units.ext ((hG.2.choose_spec.1 PP).trans ((hall PP).2.choose_spec.1).symm)
    rw [omegaG, dite_eq_left hG]
    have hloc : ∀ PP : ↥L.Pg, gLoc L PP.1 (Hl PP) (cl PP) (χ PP.1) (y PP.1) =
        ((cl PP ⟨Formalism.L2.DIV.upperLeftBlock L.hr (hall PP).2.choose, (hall PP).2.choose_spec.2.2⟩ : ℂˣ) : ℂ) *
          (∏ i ∈ Finset.range L.s,
            ((L.cg (i + 1) PP.1 (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf L.r L.t) (i + 1) (hall PP).2.choose) : ℂˣ) : ℂ)) *
          (((χ PP.1 (Matrix.GeneralLinearGroup.det (hall PP).2.choose)) : ℂˣ) : ℂ)⁻¹ := fun PP => by
      rw [gLoc, dite_eq_left (hall PP)]
    rw [Finset.prod_congr rfl fun PP _ => hloc PP]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    have hx' : (fun PP => Formalism.L2.DIV.upperLeftBlock L.hr (hG.2.choose PP)) ∈ (Formalism.L2.DIV.LevelP.ofLocal Hl cl).H := by
      rw [← hP]; exact hG.2.choose_spec.2.2
    congr 1
    congr 1
    · rw [level_character_congr hP _ _ hx', ← Units.coe_prod]
      refine congrArg Units.val ((MonoidHom.finsetProd_apply _ _ _).trans (Finset.prod_congr rfl fun PP _ => ?_))
      refine congrArg (cl PP) (Subtype.ext ?_)
      exact congrArg (Formalism.L2.DIV.upperLeftBlock L.hr) (key PP)
    · refine Finset.prod_congr rfl fun PP _ => ?_
      rw [key PP]
    · refine Finset.prod_congr rfl fun PP _ => ?_
      rw [key PP]
  · have hG : ¬ ((∀ PP ∈ L.Pg, LowZero a (y PP)) ∧
        ∃ g : ∀ PP : ↥L.Pg, GL (Fin a) (Formalism.L2.DIV.kP PP.1),
          (∀ PP : ↥L.Pg, ((g PP : GL (Fin a) _) : Matrix (Fin a) (Fin a) _) = topL a (y PP.1)) ∧
          (∀ PP : ↥L.Pg, g PP ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf L.r L.t)) ∧
          (fun PP => Formalism.L2.DIV.upperLeftBlock L.hr (g PP)) ∈ L.P.H) := by
      rintro ⟨h1, g, hg1, hg2, hg3⟩
      exact hall fun PP => ⟨h1 PP.1 PP.2, g PP, hg1 PP, hg2 PP, (hmem _).1 hg3 PP⟩
    push_neg at hall
    obtain ⟨PP, hPP⟩ := hall
    rw [omegaG, dite_eq_right hG]
    refine (Finset.prod_eq_zero (Finset.mem_univ PP) ?_).symm
    rw [gLoc, dite_eq_right]
    rintro ⟨h1, g, hg1, hg2, hg3⟩
    exact hPP h1 g hg1 hg2 hg3

end GlobalTheory.StepVec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimplePoleOfHecke
section
namespace GlobalTheory.LiftPoleObj

theorem simplePole_of_hecke (hH : GlobalTheory.Published.HeckeLPartialContinuation) : GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.SimplePole :=
  GlobalTheory.LiftPole.simplePole_of_hecke hH

end GlobalTheory.LiftPoleObj
end

