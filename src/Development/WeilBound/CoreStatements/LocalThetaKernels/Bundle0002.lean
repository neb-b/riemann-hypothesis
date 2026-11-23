module

public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InertDef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.LocalThetaKernels.EvlBridge
section
noncomputable section

namespace PositivityTheory.ThKH.Evl

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.LatVac (liftV psiAt locCo evFin_liftV at_liftV)
open PositivityTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

open Classical in
theorem exists_bump {κ : Type} [Fintype κ] : ∃ f : SInf F κ, f 0 = 1 := by
  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport fun x => (b x : ℂ) := b.hasCompactSupport.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
  refine ⟨h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff), ?_⟩
  show (b 0 : ℂ) = 1
  rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one), Complex.ofReal_one]

theorem exists_rest {κ : Type} [Fintype κ] (v : Pl F) {φ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB _) :
    ∃ r, Rest (evFin F v) φ r ∧ r 0 = 1 := by
  classical
  obtain ⟨f, hf⟩ := exists_bump (F := F) (κ := κ)
  let s : ∀ u : Pl F, (κ → Fv F u) → ℂ := fun u => Set.indicator {x | ∀ i, x i ∈ u.adicCompletionIntegers F} 1
  obtain ⟨r, hr, ht⟩ := GlobalTheory.PureFactor.exists_rest_factor v f s (Filter.Eventually.of_forall fun _ => rfl)
  have hS : ∀ u, Function.update s v φ u ∈ SB _ := fun u => by
    rcases eq_or_ne u v with rfl | hu
    · rwa [Function.update_self]
    · rw [Function.update_of_ne hu]
      exact GlobalTheory.StdVacuum.indicator_mem_SB u
  have hc : ∀ᶠ u in Filter.cofinite, Function.update s v φ u =
      Set.indicator {x | ∀ i, x i ∈ u.adicCompletionIntegers F} 1 := by
    filter_upwards [(Set.finite_singleton v).compl_mem_cofinite] with u hu
    rw [Function.update_of_ne hu]
  refine ⟨r, ⟨hr, ?_⟩, ?_⟩
  · rw [ht]
    exact Submodule.subset_span ⟨f, _, ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV _ hS hc,
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod _ hS hc⟩, rfl⟩
  · have h := congrFun (ht 1) 0
    simp only [tens, Pi.one_apply, one_mul] at h
    rw [h]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
    rw [finprod_eq_one_of_forall_eq_one, mul_one, ← hf]
    · congr 1
      funext i
      exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    · intro u
      by_cases h : u = v
      · subst h; simp
      · rw [Function.update_of_ne h]
        simp only [s]
        rw [Set.indicator_of_mem (fun i => by simp)]; rfl

theorem acts_unique {κ : Type} [Fintype κ] {v : Pl F} {T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ}
    {φ φ₁ φ₂ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB _) (h₁ : Acts (evFin F v) T φ φ₁) (h₂ : Acts (evFin F v) T φ φ₂) :
    φ₁ = φ₂ := by
  obtain ⟨r, hr, h0⟩ := exists_rest v hφ
  have h := (h₁ r hr).symm.trans (h₂ r hr)
  funext t
  have h' := congrFun h fun i => liftV v (t i)
  have e : r (fun i => liftV v (t i)) = 1 := by
    rw [← h0, ← hr.1 0 _ (fun u hu => funext fun i => at_liftV v (t i) u hu), zero_add]
  simpa only [tens, evFin_liftV, e, mul_one] using h'

section Co

variable {V : Type} [AddCommGroup V] [Module (AF F) V] {Bf : V → V → AF F} {κ : Type} [Fintype κ] (co : Darboux Bf κ)
  {v : Pl F}

theorem acts_iff (ψ : AddChar (AF F) ℂ) {u : V} (hu : At (evFin F v) u) {φ φ₁ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB _) :
    Acts (evFin F v) (co.rho ψ u) φ φ₁ ↔ φ₁ = schr (psiAt ψ v) (locCo co v u) φ :=
  ⟨fun h => acts_unique hφ h (GlobalTheory.VacBridge.rho_acts_locCo co ψ v u hu φ),
    fun h => h ▸ GlobalTheory.VacBridge.rho_acts_locCo co ψ v u hu φ⟩

theorem ev_form (u u' : V) : evFin F v (Bf u u') =
    (locCo co v u).1 ⬝ᵥ (locCo co v u').2 - (locCo co v u').1 ⬝ᵥ (locCo co v u).2 := by
  rw [co.form]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, map_sub, map_sum, map_mul]
  rfl

theorem psi_form (ψ : AddChar (AF F) ℂ) {u : V} (hu : At (evFin F v) u) (u' : V) : ψ (Bf u u') =
    psiAt ψ v ((locCo co v u).1 ⬝ᵥ (locCo co v u').2 - (locCo co v u').1 ⬝ᵥ (locCo co v u).2) := by
  rw [← ev_form, GlobalTheory.LatVac.psiAt_apply, ← GlobalTheory.StdVacuum.psi_eq_psiLoc]
  intro t ht
  have h : co.e (t • u) = 0 := by rw [hu t ht, map_zero]
  rw [map_smul] at h
  have h1 : t • (co.e u).1 = 0 := congrArg Prod.fst h
  have h2 : t • (co.e u).2 = 0 := congrArg Prod.snd h
  rw [co.form, smul_sub, ← smul_dotProduct, ← dotProduct_smul, h1, h2]
  simp

theorem exists_locCo (w : (κ → Fv F v) × (κ → Fv F v)) : ∃ u : V, locCo co v (liftV v 1 • u) = w := by
  refine ⟨co.e.symm (fun k => liftV v (w.1 k), fun k => liftV v (w.2 k)), ?_⟩
  rw [GlobalTheory.LatOpenCpt.locCo_smul, evFin_liftV, one_smul]
  ext k <;> simp [locCo, evFin_liftV]

end Co

section Lag

variable {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) {v : Pl F} {m : ℕ}

theorem at_mul {Cy : Matrix (Fin d) (Fin m) (AE F E)} (h : At (evFin F v) Cy) (z : Matrix (Fin n) (Fin m) (AE F E)) :
    At (evFin F v) (z * Cyᵀ) := fun t ht => by
  rw [← Matrix.mul_smul, ← Matrix.transpose_smul, h t ht, Matrix.transpose_zero, Matrix.mul_zero]

theorem symp_lag {Cy : Matrix (Fin d) (Fin m) (AE F E)} (h : IsLagAt σ W v Cy) (ξ : AE F E)
    (z z' : Matrix (Fin n) (Fin m) (AE F E)) :
    symp (R := AF F) (cA σ) ξ (incM F X.J) (incM F W.J) (z * Cyᵀ) (z' * Cyᵀ) = 0 := by
  rw [symp, GlobalTheory.CompanionTheory.SplitUnique.hTens_eq_zero (cA σ) _ h.iso, mul_zero, map_zero]


variable (v) in
def lagr (Cy : Matrix (Fin d) (Fin m) (AE F E)) :
    Submodule (Fv F v) ((Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) where
  carrier := {w | ∃ z : Matrix (Fin n) (Fin m) (AE F E), locCo M.co v (z * Cyᵀ) = w}
  zero_mem' := ⟨0, by rw [Matrix.zero_mul, map_zero]⟩
  add_mem' := by
    rintro _ _ ⟨z, rfl⟩ ⟨z', rfl⟩
    exact ⟨z + z', by rw [Matrix.add_mul, map_add (f := _)]⟩
  smul_mem' := by
    rintro a _ ⟨z, rfl⟩
    exact ⟨liftV v a • z, by rw [Matrix.smul_mul, GlobalTheory.LatOpenCpt.locCo_smul, evFin_liftV]⟩

theorem lagr_iso {Cy : Matrix (Fin d) (Fin m) (AE F E)} (h : IsLagAt σ W v Cy) :
    ∀ w ∈ lagr M v Cy, ∀ w' ∈ lagr M v Cy, w.1 ⬝ᵥ w'.2 = w'.1 ⬝ᵥ w.2 := by
  rintro _ ⟨z, rfl⟩ _ ⟨z', rfl⟩
  rw [← sub_eq_zero, ← ev_form, symp_lag h, map_zero]

theorem isEvAt_iff {Cy : Matrix (Fin d) (Fin m) (AE F E)} (h : IsLagAt σ W v Cy) (ψ : AddChar (AF F) ℂ)
    (l : Fn F n d v →ₗ[ℂ] ℂ) :
    IsEvAt M ψ v Cy l ↔ ∀ w ∈ lagr M v Cy, ∀ φ ∈ SB _, l (schr (psiAt ψ v) w φ) = l φ := by
  constructor
  · rintro hl _ ⟨z, rfl⟩ φ hφ
    exact hl z φ hφ _ ((acts_iff M.co ψ (at_mul h.supp z) hφ).2 rfl)
  · intro hl z φ hφ φ₁ h₁
    rw [(acts_iff M.co ψ (at_mul h.supp z) hφ).1 h₁]
    exact hl _ ⟨z, rfl⟩ φ hφ

theorem vecMulVec_mem {x : Fin n → E} (hx : x ∈ X.L) {y : Fin d → AE F E} (hy : y ∈ latW W v) :
    Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) y ∈ latAtV X W v := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hav, y, hy, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, hav, x, hx, y, hy, ?_⟩
    ext i j
    simp [incM, Matrix.vecMulVec_apply]
  | zero =>
    have e : Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (0 : Fin d → AE F E) = 0 := by
      ext i j
      exact mul_zero _
    rw [e]; exact zero_mem _
  | add a b _ _ ha hb => rw [Matrix.vecMulVec_add]; exact add_mem ha hb
  | neg a _ ha => rw [Matrix.vecMulVec_neg]; exact neg_mem ha

theorem vecMulVec_mulVec {R : Type} [CommRing R] (x : Fin n → R) (C : Matrix (Fin d) (Fin m) R) (s : Fin m → R) :
    Matrix.vecMulVec x (C *ᵥ s) = Matrix.vecMulVec x s * Cᵀ := by
  ext i j
  simp [Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]

theorem lat_split {Cy Cx : Matrix (Fin d) (Fin m) (AE F E)}
    (h : ∀ y ∈ latW W v, ∃ s t : Fin m → AE F E, Cy *ᵥ s ∈ latW W v ∧ Cx *ᵥ t ∈ latW W v ∧ y = Cy *ᵥ s + Cx *ᵥ t)
    {γ : Matrix (Fin n) (Fin d) (AE F E)} (hγ : γ ∈ latAtV X W v) :
    ∃ z z' : Matrix (Fin n) (Fin m) (AE F E), z * Cyᵀ ∈ latAtV X W v ∧ γ = z * Cyᵀ + z' * Cxᵀ := by
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hav, x, hx, y, hy, rfl⟩ := hz
    obtain ⟨s, t, hs, -, e⟩ := h _ (AddSubgroup.subset_closure ⟨a, ha, hav, y, hy, rfl⟩)
    refine ⟨Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) s,
      Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) t, ?_, ?_⟩
    · rw [← vecMulVec_mulVec]; exact vecMulVec_mem hx hs
    · rw [← vecMulVec_mulVec, ← vecMulVec_mulVec, ← Matrix.vecMulVec_add, ← e]
      ext i j
      simp [incM, Matrix.vecMulVec_apply]
  | zero => exact ⟨0, 0, by rw [Matrix.zero_mul]; exact zero_mem _, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨z₁, z₁', h₁, rfl⟩ := ha
    obtain ⟨z₂, z₂', h₂, rfl⟩ := hb
    exact ⟨z₁ + z₂, z₁' + z₂', by rw [Matrix.add_mul]; exact add_mem h₁ h₂, by simp only [Matrix.add_mul]; abel⟩
  | neg a _ ha =>
    obtain ⟨z₁, z₁', h₁, rfl⟩ := ha
    exact ⟨-z₁, -z₁', by rw [Matrix.neg_mul]; exact neg_mem h₁, by simp only [Matrix.neg_mul]; abel⟩

theorem space_split (hX : X.L.IsFullLattice E) (hW : W.L.IsFullLattice E) {Cy Cx : Matrix (Fin d) (Fin m) (AE F E)}
    (h : ∀ y ∈ latW W v, ∃ s t : Fin m → AE F E, Cy *ᵥ s ∈ latW W v ∧ Cx *ᵥ t ∈ latW W v ∧ y = Cy *ᵥ s + Cx *ᵥ t)
    (u : Matrix (Fin n) (Fin d) (AE F E)) :
    ∃ z z' : Matrix (Fin n) (Fin m) (AE F E), liftV v 1 • u = z * Cyᵀ + z' * Cxᵀ := by
  have hu := GlobalTheory.LatOpenCpt.span_top (F := F) hX hW (fun p : X.L × W.L => Matrix.vecMulVec p.1.1 p.2.1)
    (fun x hx y hy => Submodule.subset_span ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩) u
  induction hu using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨p, rfl⟩ := hz
    obtain ⟨z, z', -, e⟩ := lat_split (X := X) h (AddSubgroup.subset_closure
      ⟨liftV v 1, at_liftV v 1, by rw [evFin_liftV]; exact one_mem _, p.1.1, p.1.2, p.2.1, p.2.2, rfl⟩)
    exact ⟨z, z', e⟩
  | zero => exact ⟨0, 0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨z₁, z₁', h₁⟩ := ha
    obtain ⟨z₂, z₂', h₂⟩ := hb
    exact ⟨z₁ + z₂, z₁' + z₂', by rw [smul_add, h₁, h₂]; simp only [Matrix.add_mul]; abel⟩
  | smul a x _ hx =>
    obtain ⟨z₁, z₁', h₁⟩ := hx
    exact ⟨a • z₁, a • z₁', by rw [smul_comm, h₁, smul_add, Matrix.smul_mul, Matrix.smul_mul]⟩

end Lag

end PositivityTheory.ThKH.Evl
end
end

-- bundled from Development.WeilBound.CoreStatements.LocalThetaKernels.EvlDual
section
noncomputable section

namespace PositivityTheory.ThKH.Evl

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}


open scoped nonZeroDivisors in
theorem exists_dual_frame {R K V : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] (L : Submodule R V) [Module.Finite R L]
    (hden : ∀ z : V, ∃ a : R, a ≠ 0 ∧ a • z ∈ L) :
    ∃ (N : ℕ) (e : Fin N → V) (g : Fin N → V →ₗ[K] K), (∀ i, e i ∈ L) ∧
      (∀ i, ∀ x ∈ L, ∃ a : R, g i x = algebraMap R K a) ∧ ∀ x, ∑ i, g i x • e i = x := by
  classical
  have inj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have canc : ∀ a : R, a ≠ 0 → ∀ x y : V, a • x = a • y → x = y := fun a ha x y h => by
    rw [← algebraMap_smul K, ← algebraMap_smul K a y] at h
    exact smul_right_injective V ((map_ne_zero_iff _ inj).2 ha) h
  have : Module.IsTorsionFree R L := by
    refine ⟨fun a ha x y h => Subtype.ext (canc a ha.ne_zero _ _ (congrArg Subtype.val h))⟩
  have : Module.FinitePresentation R L := Module.finitePresentation_of_finite R L
  have : Module.Projective R L := Module.Flat.projective_of_finitePresentation
  obtain ⟨N, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R L
  have : IsLocalizedModule R⁰ L.subtype :=
    { map_units := fun a => by
        rw [← (Algebra.lsmul R (A := K) R V).commutes]
        exact (IsLocalization.map_units K a).map _
      surj := fun y => by
        obtain ⟨a, ha, h⟩ := hden y
        exact ⟨(⟨_, h⟩, ⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩), rfl⟩
      exists_of_eq := fun h => ⟨1, by rw [Subtype.ext h]⟩ }
  have hb := IsLocalizedModule.isBaseChange R⁰ K L.subtype
  let G : Fin N → V →ₗ[K] K := fun i => hb.lift (Algebra.linearMap R K ∘ₗ LinearMap.proj i ∘ₗ g)
  have hG : ∀ i (x : L), G i x = algebraMap R K (g x i) := fun i x => hb.lift_eq _ x
  refine ⟨N, fun i => f (Pi.single i 1), G, fun i => (f _).2, fun i x hx => ⟨_, hG i ⟨x, hx⟩⟩, fun x => ?_⟩
  obtain ⟨a, ha, h⟩ := hden x
  refine canc a ha _ _ ?_
  have h1 : f (g ⟨_, h⟩) = ⟨_, h⟩ := LinearMap.congr_fun hfg _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Finset.univ_sum_single (g ⟨_, h⟩), map_sum] at h1
  have h2 := congrArg Subtype.val h1
  rw [Submodule.coe_sum] at h2
  rw [Finset.smul_sum]
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h2
  have e1 : (Pi.single i (g ⟨_, h⟩ i) : Fin N → R) = g ⟨_, h⟩ i • (Pi.single i 1 : Fin N → R) := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [e1, map_smul, Submodule.coe_smul, ← algebraMap_smul K (g ⟨_, h⟩ i), ← hG, ← smul_assoc, LinearMap.map_smul_of_tower]

omit [NumberField F] [NumberField E] in
theorem exists_form {J : Matrix (Fin n) (Fin n) E} (hJ : J.det ≠ 0) (c : Fin n → E) :
    ∃ x', ∀ x, form σ J x' x = ∑ i, c i * σ (x i) := by
  refine ⟨c ᵥ* J⁻¹, fun x => ?_⟩
  rw [form, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hJ.isUnit, Matrix.vecMul_one]
  rfl

omit [NumberField F] [NumberField E] in
theorem form_smul (J : Matrix (Fin n) (Fin n) E) (a : E) (x y : Fin n → E) : form σ J x (a • y) = σ a * form σ J x y := by
  simp [form, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_left_comm]

omit [NumberField F] [NumberField E] in
theorem rep_E {J : Matrix (Fin n) (Fin n) E} (hJ : J.det ≠ 0) (g : (Fin n → E) →ₗ[E] E) :
    ∃ x', ∀ x, form σ J x' x = σ (g x) := by
  obtain ⟨x', h⟩ := exists_form (σ := σ) hJ fun i => σ (g fun j => if i = j then 1 else 0)
  refine ⟨x', fun x => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, g.pi_apply_eq_sum_univ x, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, map_mul, mul_comm]

theorem rep_F (hσ : ∀ z, σ (σ z) = z) {J : Matrix (Fin n) (Fin n) E} (hJ : J.det ≠ 0) (g : (Fin n → E) →ₗ[F] F) :
    ∃ x', ∀ x, Algebra.trace F E (form σ J x' x) = g x := by
  have hn := traceForm_nondegenerate F E
  obtain ⟨x', h⟩ := exists_form (σ := σ) hJ fun i =>
    ((Algebra.traceForm F E).toDual hn).symm (g ∘ₗ LinearMap.single F (fun _ => E) i ∘ₗ σ.toLinearMap)
  refine ⟨x', fun x => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [← Finset.univ_sum_single x, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Algebra.traceForm_apply, LinearMap.BilinForm.apply_toDual_symm_apply]
  simp [hσ]

theorem invol (h : IsCMExt F E σ) (z : E) : σ (σ z) = z := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem isIntegral_map {z : E} (h : IsIntegral ℤ z) : IsIntegral ℤ (σ z) := h.map (σ.toRingHom.toIntAlgHom)

theorem frame_X {B : Base F E} {X : Spc F E n} {r s : ℕ} (hX : X.IsHerm σ B r s) :
    ∃ (N : ℕ) (x x' : Fin N → Fin n → E), (∀ i, x i ∈ X.L) ∧ (∀ i, x' i ∈ X.L) ∧
      ∃ g : Fin N → (Fin n → E) → E, (∀ i z, form σ X.J (x' i) z = σ (g i z)) ∧ ∀ z, ∑ i, g i z • x i = z := by
  have hJ : X.J.det ≠ 0 := fun h0 => by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    refine GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hX.sig w) ?_
    rw [show (X.J.map (B.emb w).1).det = (B.emb w).1 X.J.det from (RingHom.map_det _ _).symm, h0, map_zero]
  have : Module.Finite (𝓞 E) X.L := Module.Finite.iff_fg.mpr hX.lat.fg
  obtain ⟨N, e, g, he, hg, hs⟩ := exists_dual_frame (K := E) X.L fun z => by
    obtain ⟨m, hm, h⟩ := GlobalTheory.LatOpenCpt.exists_zsmul_mem X.L hX.lat z
    exact ⟨m, Int.cast_ne_zero.2 hm, by rwa [Int.cast_smul_eq_zsmul]⟩
  choose x' hx' using fun i => rep_E (σ := σ) hJ (g i)
  refine ⟨N, e, x', he, fun i => (hX.dual _).2 fun x hx => ?_, fun i z => g i z, hx', hs⟩
  obtain ⟨a, ha⟩ := hg i x hx
  rw [hx', ha]
  exact isIntegral_map a.isIntegral_coe

theorem frame_alt_alt {B : Base F E} {W : Spc F E d} {r s : ℕ} (hB : B.IsGood σ) (hW : W.IsSkew σ B r s) :
    ∃ (N : ℕ) (y y' : Fin N → Fin d → E), (∀ i, y i ∈ W.L) ∧ (∀ i, y' i ∈ W.L) ∧
      ∀ z, ∑ i, Algebra.trace F E (form σ W.J (y' i) z) • y i = z := by
  have hσ := invol hB.cm
  have hJ : W.J.det ≠ 0 := fun h0 => by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    refine GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hW.sig w) ?_
    rw [Matrix.det_smul, show (W.J.map (B.emb w).1).det = (B.emb w).1 W.J.det from (RingHom.map_det _ _).symm, h0,
      map_zero, mul_zero]
  have : Module.Finite (𝓞 E) W.L := Module.Finite.iff_fg.mpr hW.lat.fg
  have : Module.Finite (𝓞 F) W.L := Module.Finite.trans (𝓞 E) W.L
  have : Module.Finite (𝓞 F) (W.L.restrictScalars (𝓞 F)) := this
  obtain ⟨N, e, g, he, hg, hs⟩ := exists_dual_frame (K := F) (W.L.restrictScalars (𝓞 F)) fun z => by
    obtain ⟨m, hm, h⟩ := GlobalTheory.LatOpenCpt.exists_zsmul_mem W.L hW.lat z
    exact ⟨m, Int.cast_ne_zero.2 hm, by rwa [Int.cast_smul_eq_zsmul]⟩
  choose y' hy' using fun i => rep_F hσ hJ (g i)
  refine ⟨N, e, y', he, fun i => (hW.dual _).2 fun x hx o => ?_, fun z => by simpa only [hy'] using hs z⟩
  let o' : 𝓞 E := ⟨σ o, isIntegral_map o.isIntegral_coe⟩
  obtain ⟨a, ha⟩ := hg i (o' • x) (W.L.smul_mem o' hx)
  have e1 : (o : E) * form σ W.J (y' i) x = form σ W.J (y' i) (o' • x) := by
    rw [show o' • x = σ (o : E) • x from rfl, form_smul, hσ]
  rw [e1, ← Algebra.trace_trace (S := F), hy', ha]
  exact Algebra.isIntegral_trace a.isIntegral_coe

theorem exists_frames {B : Base F E} {X : Spc F E n} {W : Spc F E d} {r s r' s' : ℕ} (hB : B.IsGood σ)
    (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') :
    ∃ (ι : Type) (_ : Fintype ι) (x x' : ι → Fin n → E) (y y' : ι → Fin d → E),
      (∀ i, x i ∈ X.L ∧ x' i ∈ X.L ∧ y i ∈ W.L ∧ y' i ∈ W.L) ∧ ∀ u : Matrix (Fin n) (Fin d) (AE F E),
        u = ∑ i, symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) (incM F (Matrix.vecMulVec (x' i) (y' i))) u •
          incM F (Matrix.vecMulVec (x i) (y i)) := by
  obtain ⟨N, x, x', hx, hx', g, hg, hgs⟩ := frame_X hX
  obtain ⟨N', y, y', hy, hy', hs⟩ := frame_alt_alt hB hW
  refine ⟨Fin N × Fin N', inferInstance, fun p => x p.1, fun p => -x' p.1, fun p => y p.2, fun p => y' p.2,
    fun p => ⟨hx _, neg_mem (hx' _), hy _, hy' _⟩, fun u => ?_⟩
  have hu := GlobalTheory.LatOpenCpt.span_top (F := F) hX.lat hW.lat (fun p : X.L × W.L => Matrix.vecMulVec p.1.1 p.2.1)
    (fun x hx y hy => Submodule.subset_span ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩) u
  induction hu using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, rfl⟩ := hz
    have key : Matrix.vecMulVec a b = ∑ p : Fin N × Fin N',
        Algebra.trace F E (form σ W.J (y' p.2) (g p.1 a • b)) • Matrix.vecMulVec (x p.1) (y p.2) := by
      rw [Fintype.sum_prod_type]
      conv_lhs => rw [← hgs a]
      ext i j
      simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Finset.sum_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      have h := congrFun (hs (g k a • b)) j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h ⊢
      rw [mul_comm (g k a), mul_assoc, ← h, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [mul_smul_comm]
    have hs' : ∀ p : Fin N × Fin N', symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)
        (incM F (Matrix.vecMulVec (-x' p.1) (y' p.2))) (incM F (Matrix.vecMulVec a b)) =
        algebraMap F (AF F) (Algebra.trace F E (form σ W.J (y' p.2) (g p.1 a • b))) := fun p => by
      have h := GlobalTheory.LatVacArith.symp_incM σ X.J W.J (-1) (-x' p.1) a (y' p.2) b
      rw [map_neg, map_one] at h
      rw [h, form_smul, ← hg]
      simp [form]
    simp only [hs']
    conv_lhs => rw [key]
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [incM, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, map_sum, algebraMap_smul]
    refine Finset.sum_congr rfl fun p _ => ?_
    exact map_smul (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E) _ _
  | zero => simp [GlobalTheory.LatVacArith.symp_zero_right]
  | add a b _ _ ha hb =>
    simp only [GlobalTheory.LatVacArith.symp_add_right, add_smul, Finset.sum_add_distrib]
    rw [← ha, ← hb]
  | smul a z _ hz =>
    conv_lhs => rw [hz, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    have h := GlobalTheory.LatVac.symp_smul_smul σ (incM F X.J) (incM F W.J) (-1) 1 a
      (incM F (Matrix.vecMulVec (-x' p.1) (y' p.2))) z
    rw [one_smul, one_mul] at h
    rw [h, smul_smul]

theorem mem_latAtV_of_dual {B : Base F E} {X : Spc F E n} {W : Spc F E d} {r s r' s' : ℕ} (hB : B.IsGood σ)
    (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') {v : Pl F} (hv : PsiUnr B.ψ v)
    {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evFin F v) u)
    (h : ∀ γ ∈ latAtV X W v, B.ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) γ u) = 1) :
    u ∈ latAtV X W v := by
  obtain ⟨ι, _, x, x', y, y', hm, he⟩ := exists_frames hB hX hW
  rw [he u]
  refine AddSubgroup.sum_mem _ fun i _ => ?_
  have hat : At (evFin F v) (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)
      (incM F (Matrix.vecMulVec (x' i) (y' i))) u) := fun t ht => by
    have h := GlobalTheory.LatVac.symp_smul_smul σ (incM F X.J) (incM F W.J) (-1) 1 t (incM F (Matrix.vecMulVec (x' i) (y' i))) u
    rw [hu t ht, GlobalTheory.LatVacArith.symp_zero_right, one_mul] at h
    exact h.symm
  refine AddSubgroup.subset_closure ⟨_, hat, (hv _).1 fun a ha => ?_, _, (hm i).1, _, (hm i).2.2.1, rfl⟩
  have h1 := h _ (AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v a, GlobalTheory.LatVac.at_liftV v a,
    by rw [GlobalTheory.LatVac.evFin_liftV]; exact ha, _, (hm i).2.1, _, (hm i).2.2.2, rfl⟩)
  have h2 := GlobalTheory.LatVac.symp_smul_smul σ (incM F X.J) (incM F W.J) (-1) (GlobalTheory.LatVac.liftV v a) 1
    (incM F (Matrix.vecMulVec (x' i) (y' i))) u
  rw [one_smul, mul_one] at h2
  have hat' : At (evFin F v) (GlobalTheory.LatVac.liftV v a *
      symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)
        (incM F (Matrix.vecMulVec (x' i) (y' i))) u) := fun t ht => by
    rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul t _, hat t ht, mul_zero]
  rw [h2, GlobalTheory.StdVacuum.psi_eq_psiLoc _ v _ hat', map_mul, GlobalTheory.LatVac.evFin_liftV, mul_comm] at h1
  exact h1

end PositivityTheory.ThKH.Evl
end
end

