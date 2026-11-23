module

public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictDef
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0003
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.KdMulRight
section
set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.KCo

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Sgl

variable {F : Type} [Field F] [NumberField F] {v : Pl F}

theorem ev_sgl (x : Fv F v) : evFin F v (sgl v x) = x := evalV_singleFin_self v x

theorem mul_sgl (a : AF F) (x : Fv F v) : a * sgl v x = sgl v (evFin F v a * x) := by
  refine Prod.ext (mul_zero _) ?_
  change a.2 * singleFin v x = singleFin v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v a.2 * x)
  refine af_ext fun u => ?_
  rw [map_mul]
  by_cases h : u = v
  · subst h; rw [evalV_singleFin_self, evalV_singleFin_self]
  · rw [evalV_singleFin_ne h, evalV_singleFin_ne h, mul_zero]

theorem kd_at_iff {M : Type} [AddCommGroup M] [Module (AF F) M] {z : M} : At (evFin F v) z ↔ sgl v 1 • z = z := by
  refine ⟨fun h => ?_, fun h u hu => ?_⟩
  · have := h (1 - sgl v 1) (by rw [map_sub, map_one, ev_sgl, sub_self])
    rw [sub_smul, one_smul, sub_eq_zero] at this
    exact this.symm
  · rw [← h, smul_smul, mul_sgl, hu, zero_mul, map_zero, zero_smul]

theorem at_sgl_smul {M : Type} [AddCommGroup M] [Module (AF F) M] (x : Fv F v) (z : M) : At (evFin F v) (sgl v x • z) :=
  fun u hu => by rw [smul_smul, mul_sgl, hu, zero_mul, map_zero, zero_smul]

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At.kd_map {M N : Type} [AddCommGroup M] [Module (AF F) M] [AddCommGroup N] [Module (AF F) N] (f : M →ₗ[AF F] N) {z : M}
    (h : At (evFin F v) z) : At (evFin F v) (f z) := fun u hu => by rw [← map_smul, h u hu, map_zero]

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At.kd_add {M : Type} [AddCommGroup M] [Module (AF F) M] {z z' : M} (h : At (evFin F v) z) (h' : At (evFin F v) z') :
    At (evFin F v) (z + z') := fun u hu => by rw [smul_add, h u hu, h' u hu, add_zero]

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At.kd_sub {M : Type} [AddCommGroup M] [Module (AF F) M] {z z' : M} (h : At (evFin F v) z) (h' : At (evFin F v) z') :
    At (evFin F v) (z - z') := fun u hu => by rw [smul_sub, h u hu, h' u hu, sub_zero]

end Sgl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {t : E →ₐ[F] Fv F v} {sec : Fv F v × Fv F v → AE F E} {α β γ : Type}

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At.kd_mul_right [Fintype β] {z : Matrix α β (AE F E)} (h : At (evFin F v) z) (m : Matrix β γ (AE F E)) :
    At (evFin F v) (z * m) := fun u hu => by rw [← Matrix.smul_mul, h u hu, Matrix.zero_mul]

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At.kd_mul_left [Fintype β] {z : Matrix β γ (AE F E)} (h : At (evFin F v) z) (m : Matrix α β (AE F E)) :
    At (evFin F v) (m * z) := fun u hu => by rw [← Matrix.mul_smul, h u hu, Matrix.mul_zero]

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At.kd_transpose {z : Matrix α β (AE F E)} (h : At (evFin F v) z) : At (evFin F v) zᵀ :=
  fun u hu => by rw [← Matrix.transpose_smul, h u hu, Matrix.transpose_zero]

theorem kd_at_matrix {z : Matrix α β (AE F E)} : At (evFin F v) z ↔ ∀ i j, At (evFin F v) (z i j) :=
  ⟨fun h i j u hu => congrFun (congrFun (h u hu) i) j, fun h u hu => Matrix.ext fun i j => h i j u hu⟩

def secM (sec : Fv F v × Fv F v → AE F E) (P Q : Matrix α β (Fv F v)) : Matrix α β (AE F E) := Matrix.of fun i j => sec (P i j, Q i j)

namespace IsSec

variable (h : IsSec σ t sec)
include h

theorem atM (P Q : Matrix α β (Fv F v)) : At (evFin F v) (secM sec P Q) := kd_at_matrix.2 fun _ _ => h.at' _

theorem fstM (P Q : Matrix α β (Fv F v)) : (secM sec P Q).map (piW t) = P := Matrix.ext fun _ _ => h.fst _

theorem sndM (P Q : Matrix α β (Fv F v)) : (secM sec P Q).map (piW (t.comp σ)) = Q := Matrix.ext fun _ _ => h.snd _

theorem extM {z z' : Matrix α β (AE F E)} (ha : At (evFin F v) (z - z')) (h1 : z.map (piW t) = z'.map (piW t))
    (h2 : z.map (piW (t.comp σ)) = z'.map (piW (t.comp σ))) : z = z' := Matrix.ext fun i j =>
  sub_eq_zero.1 (h.ext _ (kd_at_matrix.1 ha i j) (by rw [map_sub, sub_eq_zero]; exact congrFun (congrFun h1 i) j)
    (by rw [map_sub, sub_eq_zero]; exact congrFun (congrFun h2 i) j))

theorem conj1 (z : Matrix α β (AE F E)) : (z.map (cA σ)).map (piW t) = z.map (piW (t.comp σ)) := Matrix.ext fun _ _ => (h.conj _).1

theorem conj2 (z : Matrix α β (AE F E)) : (z.map (cA σ)).map (piW (t.comp σ)) = z.map (piW t) := Matrix.ext fun _ _ => (h.conj _).2

theorem smul1 (a : AF F) (z : Matrix α β (AE F E)) : (a • z).map (piW t) = evFin F v a • z.map (piW t) :=
  Matrix.ext fun _ _ => (h.smul _ _).1

theorem smul2 (a : AF F) (z : Matrix α β (AE F E)) : (a • z).map (piW (t.comp σ)) = evFin F v a • z.map (piW (t.comp σ)) :=
  Matrix.ext fun _ _ => (h.smul _ _).2

variable [Fintype β] [DecidableEq β]

theorem exists_gl (g₁ g₂ : GL β (Fv F v)) : ∃ g : GL β (AE F E), At (evFin F v) ((g : Matrix β β (AE F E)) - 1) ∧
    (g : Matrix β β (AE F E)).map (piW t) = g₁ ∧ (g : Matrix β β (AE F E)).map (piW (t.comp σ)) = g₂ := by
  have k1 : ∀ a b : Matrix β β (Fv F v), (1 + secM sec (a - 1) (b - 1)).map (piW t) = a := fun a b => by
    rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), h.fstM]; abel
  have k2 : ∀ a b : Matrix β β (Fv F v), (1 + secM sec (a - 1) (b - 1)).map (piW (t.comp σ)) = b := fun a b => by
    rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), h.sndM]; abel
  have k3 : ∀ a b a' b' : Matrix β β (Fv F v), a * a' = 1 → b * b' = 1 →
      (1 + secM sec (a - 1) (b - 1)) * (1 + secM sec (a' - 1) (b' - 1)) = 1 := fun a b a' b' e1 e2 => by
    refine h.extM ?_ ?_ ?_
    · have : (1 + secM sec (a - 1) (b - 1)) * (1 + secM sec (a' - 1) (b' - 1)) - 1 =
          secM sec (a - 1) (b - 1) * (1 + secM sec (a' - 1) (b' - 1)) + secM sec (a' - 1) (b' - 1) := by noncomm_ring
      rw [this]
      exact ((h.atM _ _).kd_mul_right _).kd_add (h.atM _ _)
    · rw [Matrix.map_mul, k1, k1, e1, Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [Matrix.map_mul, k2, k2, e2, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨⟨1 + secM sec (g₁.1 - 1) (g₂.1 - 1), 1 + secM sec ((g₁⁻¹).1 - 1) ((g₂⁻¹).1 - 1), k3 _ _ _ _ g₁.mul_inv g₂.mul_inv,
    k3 _ _ _ _ g₁.inv_mul g₂.inv_mul⟩, ?_, k1 _ _, k2 _ _⟩
  rw [Units.val_mk, add_sub_cancel_left]
  exact h.atM _ _

theorem unit_rel {J : Matrix β β (AE F E)} (g : UG (cA σ) J) :
    (((g : GL β (AE F E)) : Matrix β β (AE F E)).map (piW t))ᵀ * J.map (piW t) *
      ((g : GL β (AE F E)) : Matrix β β (AE F E)).map (piW (t.comp σ)) = J.map (piW t) := by
  have := congrArg (fun m : Matrix β β (AE F E) => m.map (piW t))
    (show ((g : GL β (AE F E)) : Matrix β β (AE F E))ᵀ * J * ((g : GL β (AE F E)) : Matrix β β (AE F E)).map (cA σ) = J from g.2)
  rwa [Matrix.map_mul, Matrix.map_mul, h.conj1, Matrix.transpose_map] at this

theorem exists_ug {J : Matrix β β (AE F E)} {ε : Fv F v} (hJ : J.map (piW (t.comp σ)) = ε • (J.map (piW t))ᵀ)
    (hu : IsUnit (J.map (piW t))) (g₀ : GL β (Fv F v)) : ∃ g : UG (cA σ) J,
      At (evFin F v) (((g : GL β (AE F E)) : Matrix β β (AE F E)) - 1) ∧
      ((g : GL β (AE F E)) : Matrix β β (AE F E)).map (piW t) = g₀ := by
  obtain ⟨B, hB⟩ := hu
  let gT : GL β (Fv F v) := ⟨(g₀.1)ᵀ, ((g₀⁻¹).1)ᵀ, by rw [← transpose_mul, Units.inv_mul, transpose_one],
    by rw [← transpose_mul, Units.mul_inv, transpose_one]⟩
  obtain ⟨g, ha, h1, h2⟩ := h.exists_gl g₀ (B⁻¹ * gT⁻¹ * B)
  have key : (g₀.1)ᵀ * B.1 * (B⁻¹ * gT⁻¹ * B).1 = B.1 := by
    have : gT * B * (B⁻¹ * gT⁻¹ * B) = B := by group
    exact congrArg Units.val this
  refine ⟨⟨g, ?_⟩, ha, h1⟩
  change (g : Matrix β β (AE F E))ᵀ * J * (g : Matrix β β (AE F E)).map (cA σ) = J
  refine h.extM ?_ ?_ ?_
  · have e : (g : Matrix β β (AE F E))ᵀ * J * (g : Matrix β β (AE F E)).map (cA σ) - J =
        ((g : Matrix β β (AE F E)) - 1)ᵀ * (J * (g : Matrix β β (AE F E)).map (cA σ)) +
          J * ((g : Matrix β β (AE F E)) - 1).map (cA σ) := by
      rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), transpose_sub, transpose_one]
      noncomm_ring
    rw [e]
    exact (ha.kd_transpose.kd_mul_right _).kd_add (At.kd_mul_left (kd_at_matrix.2 fun i j => h.atConj _ (kd_at_matrix.1 ha i j)) _)
  · rw [Matrix.map_mul, Matrix.map_mul, h.conj1, Matrix.transpose_map, h1, h2, ← hB, key]
  · rw [Matrix.map_mul, Matrix.map_mul, h.conj2, Matrix.transpose_map, h1, h2, hJ, ← hB, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    have := congrArg Matrix.transpose key
    rwa [transpose_mul, transpose_mul, transpose_transpose, ← Matrix.mul_assoc] at this

theorem ug_ext {J : Matrix β β (AE F E)} (hu : IsUnit (J.map (piW t))) {g g' : UG (cA σ) J}
    (ha : At (evFin F v) (((g : GL β (AE F E)) : Matrix β β (AE F E)) - 1))
    (ha' : At (evFin F v) (((g' : GL β (AE F E)) : Matrix β β (AE F E)) - 1))
    (e : ((g : GL β (AE F E)) : Matrix β β (AE F E)).map (piW t) = ((g' : GL β (AE F E)) : Matrix β β (AE F E)).map (piW t)) :
    g = g' := by
  refine Subtype.ext (Units.ext (h.extM (by simpa using ha.kd_sub ha') e ?_))
  have h1 := h.unit_rel g
  have h2 := h.unit_rel g'
  rw [← e] at h2
  have hg : IsUnit (((g : GL β (AE F E)) : Matrix β β (AE F E)).map (piW t))ᵀ :=
    (Matrix.isUnit_transpose _).2 ((g : GL β (AE F E)).isUnit.map (piW t).mapMatrix)
  exact (hg.mul hu).mul_left_cancel (h1.trans h2.symm)

end IsSec

end PositivityTheory.KCo
end
end

-- bundled from Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictMod
section
noncomputable section

open Matrix GlobalTheory.WeilM MeasureTheory Filter Topology ValuativeRel

namespace PositivityTheory.KCo

namespace Mod

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)]
  {κ μ : Type} [Fintype κ] [Fintype μ] {ψ : AddChar k ℂ}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem schr_schr (w w' : (κ → k) × (κ → k)) (φ : (κ → k) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (⅟(2 : k) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') φ := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add,
    ← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc, add_dotProduct, dotProduct_add]
  congr 2
  have h2 : ⅟(2 : k) * 2 = 1 := invOf_mul_self _
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * h2

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem schr_zero (φ : (κ → k) → ℂ) : schr ψ 0 φ = φ := by
  funext x
  simp [schr]

theorem schr_mem (hc : Continuous ψ) (w : (κ → k) × (κ → k)) {φ : (κ → k) → ℂ} (hφ : φ ∈ SB (κ → k)) :
    schr ψ w φ ∈ SB (κ → k) := by
  have := nonarch_field k
  have hlc := isLocallyConstant_addChar ψ hc
  have h1 : IsLocallyConstant fun x : κ → k => ψ (x ⬝ᵥ w.2 + ⅟(2 : k) * (w.1 ⬝ᵥ w.2)) :=
    hlc.comp_continuous ((continuous_id.dotProduct continuous_const).add continuous_const)
  exact ⟨h1.mul (hφ.1.comp_continuous (continuous_id.add continuous_const)),
    (hφ.2.comp_homeomorph (Homeomorph.addRight w.1)).mul_left⟩

omit [Invertible (2 : k)] in
theorem norm_le_one (hc : Continuous ψ) (x : k) : ‖ψ x‖ ≤ 1 := by
  obtain ⟨ψ₀, h₀⟩ := (GlobalTheory.CompanionTheory.VacLoc.GoodInh.exists_goodChar k).1
  obtain ⟨M, hM⟩ := h₀.compact.exists_bound_of_continuousOn (f := fun y : k => ψ (x * y))
    (hc.comp (continuous_const.mul continuous_id)).continuousOn
  by_contra h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M (not_le.1 h)
  have := hM (n : k) (natCast_mem _ n)
  rw [mul_comm, ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow, norm_pow] at this
  exact absurd hn (not_lt.2 this)

omit [Invertible (2 : k)] in
theorem norm_one (hc : Continuous ψ) (x : k) : ‖ψ x‖ = 1 := by
  have h1 := norm_le_one hc x
  have h2 := norm_le_one hc (-x)
  have h3 : ‖ψ x‖ * ‖ψ (-x)‖ = 1 := by rw [← norm_mul, ← AddChar.map_add_eq_mul, add_neg_cancel]; simp
  nlinarith [norm_nonneg (ψ x), norm_nonneg (ψ (-x))]

theorem cyc (hc : Continuous ψ) (h1 : ψ ≠ 1) {φ₀ : (κ → k) → ℂ} (h₀ : φ₀ ∈ SB (κ → k)) (hne : φ₀ ≠ 0)
    (l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ) (hl : ∀ w, l (schr ψ w φ₀) = 0) : ∀ φ ∈ SB (κ → k), l φ = 0 := by
  have := GlobalTheory.SplitWeil.t2Space k
  obtain ⟨u, hu⟩ := (GlobalTheory.CompanionTheory.VacLoc.GoodInh.exists_goodChar k).2 ψ hc (norm_one hc) h1
  let d : Darboux (R := k) (W := (κ → k) × (κ → k)) (fun w w' => w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) κ :=
    ⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩
  let : MeasurableSpace (κ → k) := borel _
  have : BorelSpace (κ → k) := ⟨rfl⟩
  obtain ⟨S, hS⟩ := GlobalTheory.CompanionTheory.SchrSys.exists_isModel ψ _ u d Measure.addHaar hu inferInstance
  have hcyc := (GlobalTheory.CompanionTheory.VacLoc.ModelLine.cyclic_and_line ψ _ u d _ S ⊥ (fun _ => 1) ⟨φ₀, h₀⟩ ⟨φ₀, h₀⟩ hu hS).1
    (fun h => hne (congrArg Subtype.val h))
  intro φ hφ
  have hle : Submodule.span ℂ (Set.range fun x => S.rho x ⟨φ₀, h₀⟩) ≤ LinearMap.ker (l ∘ₗ (SB (κ → k)).subtype) := by
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    show l _ = 0
    rw [Submodule.subtype_apply, hS.1]
    exact hl w
  have hm : (⟨φ, hφ⟩ : SB (κ → k)) ∈ Submodule.span ℂ (Set.range fun x => S.rho x ⟨φ₀, h₀⟩) := by
    rw [show Submodule.span ℂ (Set.range fun x => S.rho x ⟨φ₀, h₀⟩) = ⊤ from hcyc]
    trivial
  exact hle hm

theorem small (hc : Continuous ψ) {φ : (κ → k) → ℂ} (hφ : φ ∈ SB (κ → k)) :
    ∀ᶠ w in 𝓝 (0 : (κ → k) × (κ → k)), schr ψ w φ = φ := by
  have := nonarch_field k
  have hlc := isLocallyConstant_addChar ψ hc
  have h1 := eventually_comp_eq (p₀ := (0 : (κ → k) × (κ → k))) (fun p v => v + p.1) (fun p v => v - p.1)
    (by fun_prop) (by fun_prop) (by simp) (by simp) (by simp) hφ
  have hq : Continuous fun q : ((κ → k) × (κ → k)) × (κ → k) => q.2 ⬝ᵥ q.1.2 + ⅟(2 : k) * (q.1.1 ⬝ᵥ q.1.2) :=
    (continuous_snd.dotProduct continuous_fst.snd).add
      (continuous_const.mul (continuous_fst.fst.dotProduct continuous_fst.snd))
  have h2 : ∀ᶠ w in 𝓝 (0 : (κ → k) × (κ → k)), ∀ v ∈ tsupport φ, ψ (v ⬝ᵥ w.2 + ⅟(2 : k) * (w.1 ⬝ᵥ w.2)) = 1 := by
    refine IsCompact.eventually_forall_of_forall_eventually hφ.2 fun v _ => ?_
    filter_upwards [(hlc.comp_continuous hq).eventually_eq (0, v)] with q h
    simpa using h
  filter_upwards [h1, h2] with w a b
  funext v
  rw [schr, a v]
  by_cases hv : v ∈ tsupport φ
  · rw [b v hv, one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hv, mul_zero]

theorem model (hc : Continuous ψ) (h1 : ψ ≠ 1) (e : ((μ → k) × (μ → k)) ≃ₗ[k] ((κ → k) × (κ → k)))
    (he : ∀ w w', (e w).1 ⬝ᵥ (e w').2 - (e w').1 ⬝ᵥ (e w).2 = w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) :
    ∃ ι : ((κ → k) → ℂ) →ₗ[ℂ] ((μ → k) → ℂ), Set.BijOn ι (SB (κ → k) : Set _) (SB (μ → k) : Set _) ∧
      ∀ w, ∀ φ ∈ SB (κ → k), ι (schr ψ (e w) φ) = schr ψ w (ι φ) := by
  classical
  obtain ⟨l, ⟨φ₀, hφ₀, hl₀⟩, hl⟩ := GlobalTheory.CompanionTheory.LagFun.exists_invariant_form k κ ψ hc h1
    (LinearMap.range (e.toLinearMap ∘ₗ LinearMap.inr k _ _)) (by
      rintro _ ⟨z, rfl⟩ _ ⟨z', rfl⟩
      have := he (0, z) (0, z')
      simpa [sub_eq_zero] using this)
  have hl' : ∀ z, ∀ φ ∈ SB (κ → k), l (schr ψ (e (0, z)) φ) = l φ := fun z => hl _ ⟨z, rfl⟩
  let ι : ((κ → k) → ℂ) →ₗ[ℂ] ((μ → k) → ℂ) :=
    { toFun := fun φ y => l (schr ψ (e (y, 0)) φ)
      map_add' := fun φ φ' => funext fun y => by
        rw [Pi.add_apply, ← map_add (f := _)]
        congr 1
        funext x
        simp [schr, mul_add]
      map_smul' := fun c φ => funext fun y => by
        rw [RingHom.id_apply, Pi.smul_apply, ← map_smul]
        congr 1
        funext x
        simp [schr, mul_left_comm] }
  have hι : ∀ φ y, ι φ y = l (schr ψ (e (y, 0)) φ) := fun _ _ => rfl
  have h0 : ∀ φ, ι φ 0 = l φ := fun φ => by rw [hι, show ((0 : μ → k), (0 : μ → k)) = 0 from rfl, map_zero, schr_zero]
  have hint : ∀ w, ∀ φ ∈ SB (κ → k), ι (schr ψ (e w) φ) = schr ψ w (ι φ) := fun w φ hφ => funext fun y => by
    have a := hl' w.2 _ (schr_mem hc (e (y + w.1, 0)) hφ)
    rw [schr_schr, he, ← map_add (f := _), map_smul] at a
    rw [hι, schr_schr, he, ← map_add (f := _), map_smul, schr, hι, ← a,
      show ((y, 0) + w : (μ → k) × (μ → k)) = (0, w.2) + (y + w.1, 0) from Prod.ext (by simp) (by simp),
      smul_eq_mul, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    have h2 : ⅟(2 : k) * 2 = 1 := invOf_mul_self _
    simp only [dotProduct_zero, add_dotProduct]
    linear_combination (y ⬝ᵥ w.2) * h2
  have c1 : Continuous fun y : μ → k => e (y, 0) := (e.toLinearMap ∘ₗ LinearMap.inl k _ _).continuous_on_pi
  have c2 : Continuous fun y : μ → k => e (0, y) := (e.toLinearMap ∘ₗ LinearMap.inr k _ _).continuous_on_pi
  have hmaps : ∀ φ ∈ SB (κ → k), ι φ ∈ SB (μ → k) := fun φ hφ => by
    have s1 : ∀ᶠ y in 𝓝 (0 : μ → k), schr ψ (e (y, 0)) φ = φ :=
      (c1.tendsto' 0 0 (map_zero e)).eventually (small hc hφ)
    have s2 : ∀ᶠ y in 𝓝 (0 : μ → k), schr ψ (e (0, y)) φ = φ :=
      (c2.tendsto' 0 0 (map_zero e)).eventually (small hc hφ)
    refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun y₀ => ?_, ?_⟩
    · have : Tendsto (fun y => y - y₀) (𝓝 y₀) (𝓝 0) := Continuous.tendsto' (by fun_prop) _ _ (sub_self _)
      filter_upwards [this.eventually s1] with y hy
      have := congrFun (hint (y - y₀, 0) φ hφ) y₀
      rw [hy] at this
      simpa [schr] using this.symm
    · obtain ⟨u, hu⟩ := (GlobalTheory.CompanionTheory.VacLoc.GoodInh.exists_goodChar k).2 ψ hc (norm_one hc) h1
      have s3 : ∀ i : μ, ∃ v : kˣ, ∀ o ∈ 𝒪[k], schr ψ (e (0, Pi.single i ((v : k) * o))) φ = φ := fun i =>
        hu.basis _ (((continuous_single (A := fun _ : μ => k) i).tendsto' 0 0 (Pi.single_zero i)).eventually s2)
      choose v hv using s3
      refine HasCompactSupport.intro (K := Set.pi Set.univ fun i => (fun o => (u : k) * ((v i)⁻¹ : kˣ) * o) '' (𝒪[k] : Set k))
        (isCompact_univ_pi fun i => hu.compact.image (by fun_prop)) fun y hy => by_contra fun hne => hy fun i _ => ?_
      refine ⟨_, (hu.ann (y i * v i)).1 fun o ho => ?_, ?_⟩
      · have := congrFun (hint (0, Pi.single i ((v i : k) * o)) φ hφ) y
        rw [hv i o ho] at this
        simp only [schr, Pi.zero_apply, zero_mul, mul_zero, add_zero, dotProduct_single] at this
        rw [mul_assoc]
        exact mul_right_cancel₀ hne (this.symm.trans (one_mul _).symm)
      · simp only [Units.val_inv_eq_inv_val]
        field_simp
  refine ⟨ι, ⟨hmaps, fun φ hφ φ' hφ' h => ?_, fun Φ hΦ => ?_⟩, hint⟩
  · by_contra hne
    have hd := (SB (κ → k)).sub_mem hφ hφ'
    refine hl₀ (cyc hc h1 hd (sub_ne_zero.2 hne) l (fun w => ?_) _ hφ₀)
    obtain ⟨w, rfl⟩ := e.surjective w
    rw [← h0, hint w _ hd, map_sub, h, sub_self]
    simp [schr]
  · by_contra hn
    have hn' : Φ ∉ (SB (κ → k)).map ι := hn
    obtain ⟨m, hm, hb⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn' inferInstance
    refine hm (cyc hc h1 (hmaps _ hφ₀) (fun h => hl₀ (by rw [← h0, h]; rfl)) m (fun w => ?_) _ hΦ)
    rw [← hint w _ hφ₀, ← Submodule.mem_bot ℂ, ← hb]
    exact ⟨_, ⟨_, schr_mem hc _ hφ₀, rfl⟩, rfl⟩

end Mod

theorem cyclicity : Cyc := fun _ _ _ _ _ _ _ _ _ hc h1 _ h₀ hne l hl => Mod.cyc hc h1 h₀ hne l hl

theorem model_existence : ModelEx := fun _ _ _ _ _ _ _ _ _ _ _ hc h1 e he => Mod.model hc h1 e he

end PositivityTheory.KCo
end
end

-- bundled from Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfSplit
section
namespace PositivityTheory.KCo

theorem good_split_of_cm : GoodSplit := by
  intro F E _ _ _ _ _ σ B hB v hs
  have hcm := hB.cm
  haveI hgal : IsGalois ℚ E := hB.galois
  haveI : IsGalois F E := IsGalois.tower_top_of_isGalois ℚ F E
  set p : Ideal ℤ := Ideal.under ℤ v.asIdeal with hp
  have hs' : (p.primesOver (NumberField.RingOfIntegers E)).ncard = Module.finrank ℚ E := hs
  have hfin : (p.primesOver (NumberField.RingOfIntegers E)).Finite :=
    Set.finite_of_ncard_ne_zero (by rw [hs']; exact Module.finrank_pos.ne')
  haveI : Fintype (p.primesOver (NumberField.RingOfIntegers E)) := hfin.fintype
  have hA : ∀ q ∈ p.primesOver (NumberField.RingOfIntegers E),
      q.ramificationIdx ℤ * q.inertiaDeg ℤ = 1 := by
    have hsum := Ideal.sum_ramification_inertia_eq_finrank p (NumberField.RingOfIntegers E)
    rw [NumberField.RingOfIntegers.rank] at hsum
    have hcard : Fintype.card (p.primesOver (NumberField.RingOfIntegers E)) = Module.finrank ℚ E := by
      rw [Fintype.card_eq_nat_card, Nat.card_coe_set_eq, hs']
    have hpos : ∀ x : p.primesOver (NumberField.RingOfIntegers E),
        1 ≤ x.1.ramificationIdx ℤ * x.1.inertiaDeg ℤ := by
      intro x
      haveI : x.1.IsPrime := x.2.1
      exact Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)
    intro q hq
    by_contra hne
    have hlt : ∑ _x : p.primesOver (NumberField.RingOfIntegers E), (1 : ℕ) <
        ∑ x : p.primesOver (NumberField.RingOfIntegers E), x.1.ramificationIdx ℤ * x.1.inertiaDeg ℤ :=
      Finset.sum_lt_sum (fun x _ => hpos x)
        ⟨⟨q, hq⟩, Finset.mem_univ _, lt_of_le_of_ne (hpos ⟨q, hq⟩) (Ne.symm hne)⟩
    rw [hsum] at hlt
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, hcard] at hlt
    exact lt_irrefl _ hlt
  have hB1 : ∀ Q ∈ v.asIdeal.primesOver (NumberField.RingOfIntegers E),
      Q.ramificationIdx (NumberField.RingOfIntegers F) = 1 ∧
        Q.inertiaDeg (NumberField.RingOfIntegers F) = 1 := by
    intro Q hQ
    haveI : Q.IsPrime := hQ.1
    haveI : Q.LiesOver v.asIdeal := hQ.2
    haveI : v.asIdeal.LiesOver p := ⟨rfl⟩
    haveI : Q.LiesOver p := Ideal.LiesOver.trans Q v.asIdeal p
    have h1 := hA Q ⟨inferInstance, inferInstance⟩
    rw [Ideal.ramificationIdx_tower (R := ℤ) (q := v.asIdeal) (r := Q),
      Ideal.inertiaDeg_tower (R := ℤ) (q := v.asIdeal) (r := Q)] at h1
    have h2 := mul_eq_one.mp h1
    exact ⟨(mul_eq_one.mp h2.1).2, (mul_eq_one.mp h2.2).2⟩
  have hC := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn v.asIdeal
    (NumberField.RingOfIntegers E) (E ≃ₐ[F] E)
  have hG : Nat.card (E ≃ₐ[F] E) = 2 := by
    rw [IsGalois.card_aut_eq_finrank]
    exact hcm.2.2.1
  rw [hG] at hC
  have hne : (v.asIdeal.primesOver (NumberField.RingOfIntegers E)).ncard ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hC
    exact absurd hC (by norm_num)
  obtain ⟨Q, hQ⟩ := Set.nonempty_of_ncard_ne_zero hne
  haveI : Q.IsPrime := hQ.1
  haveI : Q.LiesOver v.asIdeal := hQ.2
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal Q (E ≃ₐ[F] E),
    Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal Q (E ≃ₐ[F] E), (hB1 Q hQ).1, (hB1 Q hQ).2,
    mul_one, mul_one] at hC
  exact (GlobalTheory.AdelicU.nonempty_split_iff hcm).mpr hC

end PositivityTheory.KCo
end

