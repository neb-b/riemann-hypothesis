module

public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.IndicatorMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1588
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0007
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.ActsFormula
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0032

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.CompFinLiftE
section
noncomputable section

namespace PositivityTheory.KCo

open Filter Topology NumberField IsDedekindDomain Matrix GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  GlobalTheory.CompanionTheory.Ar.RT.Move GlobalTheory.LatVac
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}

theorem at_iff {M : Type} [AddCommGroup M] [Module (AF F) M] {z : M} : At (evFin F v) z ↔ liftV v 1 • z = z := by
  refine ⟨fun h => ?_, fun h u hu => ?_⟩
  · have := h (1 - liftV v 1) (by rw [map_sub, map_one, evFin_liftV, sub_self])
    rw [sub_smul, one_smul, sub_eq_zero] at this
    exact this.symm
  · rw [← h, smul_smul, show u * liftV v 1 = 0 from at_liftV v 1 u hu, zero_smul]

theorem at_eq {a : AF F} (h : At (evFin F v) a) : a = liftV v (evFin F v a) := by
  rw [← GlobalTheory.LatVacArith.liftV_one_mul]; exact (at_iff.1 h).symm

theorem mul_liftV (a : AF F) (s : Fv F v) : a * liftV v s = liftV v (evFin F v a * s) := by
  have h : At (evFin F v) (a * liftV v s) := fun u hu => by
    rw [smul_eq_mul, mul_left_comm, show u * liftV v s = 0 from at_liftV v s u hu, mul_zero]
  rw [at_eq h, map_mul, evFin_liftV]

def liftE (v : Pl F) : Fv F v ⊗[F] E →ₗ[F] AE F E := TensorProduct.map (liftV v) LinearMap.id

theorem compFin_liftE (p : Fv F v ⊗[F] E) : compFin F E v (liftE v p) = p := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a e =>
    change evFin F v (liftV v a) ⊗ₜ e = _
    rw [evFin_liftV]

theorem smul_eq_liftE (z : AE F E) : liftV v 1 • z = liftE v (compFin F E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy]
  | tmul a e =>
    change (liftV v 1 * a) ⊗ₜ e = liftV v (evFin F v a) ⊗ₜ e
    rw [GlobalTheory.LatVacArith.liftV_one_mul]

theorem at_liftE (p : Fv F v ⊗[F] E) : At (evFin F v) (liftE v p) := at_iff.2 (by rw [smul_eq_liftE, compFin_liftE])

theorem eq_zero_of_at (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) {z : AE F E} (hz : At (evFin F v) z) (h0 : piW t z = 0)
    (h1 : piW (t.comp σ) z = 0) : z = 0 := by
  rw [← at_iff.1 hz, smul_eq_liftE, split_ext h t (z := 0) (h0.trans (map_zero _).symm) (h1.trans (map_zero _).symm), map_zero]

theorem piW_cA (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (z : AE F E) : piW (t.comp σ) (cA σ z) = piW t z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a e =>
    change evFin F v a * t (σ (σ e)) = evFin F v a * t e
    rw [cm_conj_conj h]

theorem exists_pair (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (a b : Fv F v) :
    ∃ z : AE F E, At (evFin F v) z ∧ piW t z = a ∧ piW (t.comp σ) z = b := by
  obtain ⟨p, hp⟩ := (splitPair_bijective h t).2 (a, b)
  refine ⟨liftE v p, at_liftE p, ?_, ?_⟩
  · change splitProj t (compFin F E v _) = a
    rw [compFin_liftE]; exact congrArg Prod.fst hp
  · change splitProj (t.comp σ) (compFin F E v _) = b
    rw [compFin_liftE]; exact congrArg Prod.snd hp

variable {n d : ℕ}

theorem at_matrix {x : Matrix (Fin n) (Fin d) (AE F E)} : At (evFin F v) x ↔ ∀ i j, At (evFin F v) (x i j) :=
  ⟨fun h i j u hu => congrFun (congrFun (h u hu) i) j, fun h u hu => Matrix.ext fun i j => h i j u hu⟩

theorem at_mul_mul {x : Matrix (Fin n) (Fin d) (AE F E)} (h : At (evFin F v) x) (g : Matrix (Fin n) (Fin n) (AE F E))
    (k : Matrix (Fin d) (Fin d) (AE F E)) : At (evFin F v) (g * x * k) := fun u hu => by
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, h u hu, Matrix.mul_zero, Matrix.zero_mul]

theorem symp_iso (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (ξ : AE F E) (JA : Matrix (Fin n) (Fin n) (AE F E))
    (JB : Matrix (Fin d) (Fin d) (AE F E)) {x w : Matrix (Fin n) (Fin d) (AE F E)} (hx : At (evFin F v) x)
    (h0 : x.map (piW t) = 0) (h1 : w.map (piW t) = 0) : symp (R := AF F) (cA σ) ξ JA JB x w = 0 := by
  have : hTens (cA σ) JA JB x w = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_
    refine eq_zero_of_at h t (fun u hu => ?_) ?_ ?_
    · rw [← smul_mul_assoc, ← smul_mul_assoc, ← smul_mul_assoc, at_matrix.1 hx i j u hu]; simp
    · have : piW t (x i j) = 0 := congrFun (congrFun h0 i) j
      simp [this]
    · have : piW t (w k l) = 0 := congrFun (congrFun h1 k) l
      rw [map_mul, piW_cA h, this, mul_zero]
  rw [symp, this, mul_zero, map_zero]

theorem hTens_eq {R K : Type} [CommRing R] [CommRing K] [Algebra R K] (c : K →ₐ[R] K) (JA : Matrix (Fin n) (Fin n) K)
    (JB : Matrix (Fin d) (Fin d) K) (x y : Matrix (Fin n) (Fin d) K) :
    hTens c JA JB x y = (xᵀ * JA * y.map c * JBᵀ).trace := by
  simp only [hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring

theorem symp_act {R K : Type} [CommRing R] [CommRing K] [Algebra R K] (c : K →ₐ[R] K) (ξ : K) (JA : Matrix (Fin n) (Fin n) K)
    (JB : Matrix (Fin d) (Fin d) K) (p : UG c JA × UG c JB) (x y : Matrix (Fin n) (Fin d) K) :
    symp (R := R) c ξ JA JB (actAB c p x) (actAB c p y) = symp (R := R) c ξ JA JB x y := by
  have h1 : (p.1.1 : Matrix _ _ K)ᵀ * JA * (p.1.1 : Matrix _ _ K).map c = JA := p.1.2
  have h2 : (p.2.1 : Matrix _ _ K)ᵀ * JB * (p.2.1 : Matrix _ _ K).map c = JB := p.2.2
  have h3 : ((p.2.1 : Matrix _ _ K).map c)ᵀ * JBᵀ * (p.2.1 : Matrix _ _ K) = JBᵀ := by
    conv_rhs => rw [← h2]
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  have m : ∀ {a b e : ℕ} (A : Matrix (Fin a) (Fin b) K) (B : Matrix (Fin b) (Fin e) K), (A * B).map c = A.map c * B.map c :=
    fun A B => Matrix.map_mul (f := c.toRingHom)
  unfold symp
  congr 2
  rw [hTens_eq, hTens_eq, actAB, actAB, m, m, Matrix.transpose_map]
  generalize ((p.1.1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = g at h1 ⊢
  generalize ((p.2.1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = k at h3 ⊢
  calc ((g * x * kᵀ)ᵀ * JA * (g.map c * y.map c * (k.map c)ᵀ) * JBᵀ).trace
      = (k * (xᵀ * (gᵀ * JA * g.map c) * y.map c * ((k.map c)ᵀ * JBᵀ))).trace := by
        simp [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h1, Matrix.trace_mul_comm, Matrix.mul_assoc _ _ k, h3]

variable {X : Spc F E n} {W : Spc F E d} (M : Model σ X W)

theorem at_co {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evFin F v) u) (i : Fin n × Fin d) :
    At (evFin F v) ((M.co.e u).1 i) ∧ At (evFin F v) ((M.co.e u).2 i) := by
  have h : ∀ a, evFin F v a = 0 → a • M.co.e u = 0 := fun a ha => by rw [← map_smul, hu a ha, map_zero]
  exact ⟨fun a ha => congrFun (congrArg Prod.fst (h a ha)) i, fun a ha => congrFun (congrArg Prod.snd (h a ha)) i⟩

include M in
theorem exists_sep (h : IsCMExt F E σ) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (t : E →ₐ[F] Fv F v)
    {z : Matrix (Fin n) (Fin d) (AE F E)} (hz : At (evFin F v) z) (h0 : z.map (piW t) = 0) (hne : z ≠ 0) :
    ∃ u, At (evFin F v) u ∧ u.map (piW (t.comp σ)) = 0 ∧ ψ (symp (cA σ) (-1) (incM F X.J) (incM F W.J) z u) ≠ 1 := by
  classical
  obtain ⟨s, hs⟩ : ∃ s, ψ (liftV v s) ≠ 1 := by
    by_contra e
    push Not at e
    exact GlobalTheory.PsiNontriv.psiV_ne_one ψ hψ v (AddChar.ext _ _ e)
  obtain ⟨w, hw, e⟩ : ∃ w, At (evFin F v) w ∧ symp (cA σ) (-1) (incM F X.J) (incM F W.J) z w = liftV v s := by
    have hat : ∀ p : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F), At (evFin F v) p → At (evFin F v) (M.co.e.symm p) :=
      fun p hp a ha => by rw [← map_smul, hp a ha, map_zero]
    have hsg : ∀ (i : Fin n × Fin d) (r : Fv F v) a, evFin F v a = 0 → a • (Pi.single i (liftV v r) : Fin n × Fin d → AF F) = 0 :=
      fun i r a ha => by rw [← Pi.single_smul, at_liftV v r a ha, Pi.single_zero]
    have hz' : M.co.e z ≠ 0 := fun e => hne (M.co.e.injective (e.trans (map_zero _).symm))
    by_cases ha : (M.co.e z).1 = 0
    · obtain ⟨i, hi⟩ : ∃ i, (M.co.e z).2 i ≠ 0 := Function.ne_iff.1 fun e => hz' (Prod.ext ha e)
      have hi' : evFin F v ((M.co.e z).2 i) ≠ 0 := fun e => hi (by rw [at_eq (at_co M hz i).2, e, map_zero])
      refine ⟨M.co.e.symm (Pi.single i (liftV v (-(s / evFin F v ((M.co.e z).2 i)))), 0),
        hat _ fun a ha => Prod.ext (hsg _ _ a ha) (smul_zero a), ?_⟩
      rw [M.co.form, LinearEquiv.apply_symm_apply]
      simp only [dotProduct_zero, single_dotProduct, zero_sub]
      rw [mul_comm, mul_liftV, ← map_neg]
      congr 1
      field_simp
    · obtain ⟨i, hi⟩ : ∃ i, (M.co.e z).1 i ≠ 0 := Function.ne_iff.1 ha
      have hi' : evFin F v ((M.co.e z).1 i) ≠ 0 := fun e => hi (by rw [at_eq (at_co M hz i).1, e, map_zero])
      refine ⟨M.co.e.symm (0, Pi.single i (liftV v (s / evFin F v ((M.co.e z).1 i)))),
        hat _ fun a ha => Prod.ext (smul_zero a) (hsg _ _ a ha), ?_⟩
      rw [M.co.form, LinearEquiv.apply_symm_apply]
      simp only [zero_dotProduct, dotProduct_single, sub_zero]
      rw [mul_liftV]
      congr 1
      field_simp
  obtain ⟨ε, -, e0, e1⟩ := exists_pair h t 1 0
  refine ⟨ε • w, fun a ha => by rw [smul_comm, hw a ha, smul_zero], Matrix.ext fun i j => by simp [e1], ?_⟩
  have h2 := symp_iso h t (-1) (incM F X.J) (incM F W.J) (w := w - ε • w) hz h0 (Matrix.ext fun i j => by simp [e0])
  have h3 := GlobalTheory.LatVacArith.symp_add_right σ (-1) (incM F X.J) (incM F W.J) z (ε • w) (w - ε • w)
  rw [add_sub_cancel, h2, add_zero, e] at h3
  rwa [← h3]

def locRho (ψ : AddChar (AF F) ℂ) (v : Pl F) (u : Matrix (Fin n) (Fin d) (AE F E)) (φ : (Fin n × Fin d → Fv F v) → ℂ) :
    (Fin n × Fin d → Fv F v) → ℂ :=
  fun y => ψ (⅟(2 : AF F) * ((M.co.e u).1 ⬝ᵥ (M.co.e u).2)) *
    (ψ (liftV v (y ⬝ᵥ fun i => evFin F v ((M.co.e u).2 i))) * φ (y + fun i => evFin F v ((M.co.e u).1 i)))

theorem locRho_mem {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (u : Matrix (Fin n) (Fin d) (AE F E)) {φ}
    (hφ : φ ∈ SB (Fin n × Fin d → Fv F v)) : locRho M ψ v u φ ∈ SB (Fin n × Fin d → Fv F v) := by
  have h1 : IsLocallyConstant fun s : Fv F v => ψ (liftV v s) :=
    (GlobalTheory.CompanionTheory.AdelicHeis.isLocallyConstant_fin (ψ.compAddMonoidHom (AddMonoidHom.inr (Ainf F) (Af F)))
      (hψ.1.comp (continuous_const.prodMk continuous_id)) fun x => GlobalTheory.StdCharFromIsStd.norm_psi hψ _).comp_continuous
      (continuous_singleFin v)
  exact Submodule.smul_mem _ _ (GlobalTheory.CompanionTheory.AdelicHeis.mul_mem_SB h1 _ _ hφ)

theorem rho_apply (ψ : AddChar (AF F) ℂ) {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evFin F v) u)
    (Ψ : (Fin n × Fin d → AF F) → ℂ) (x : Fin n × Fin d → AF F) :
    M.co.rho ψ u Ψ x = ψ (⅟(2 : AF F) * ((M.co.e u).1 ⬝ᵥ (M.co.e u).2)) *
      (ψ (liftV v ((fun i => evFin F v (x i)) ⬝ᵥ fun i => evFin F v ((M.co.e u).2 i))) * Ψ (x + (M.co.e u).1)) := by
  have e : x ⬝ᵥ (M.co.e u).2 = liftV v ((fun i => evFin F v (x i)) ⬝ᵥ fun i => evFin F v ((M.co.e u).2 i)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [← mul_liftV, ← at_eq (at_co M hu i).2]
  simp only [Darboux.rho, schr, AddChar.map_add_eq_mul, e]
  ring

theorem rho_tens (ψ : AddChar (AF F) ℂ) {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evFin F v) u) (φ)
    {r : (Fin n × Fin d → AF F) → ℂ} (hr : ∀ x z, At (evFin F v) z → r (x + z) = r x) :
    M.co.rho ψ u (tens (evFin F v) φ r) = tens (evFin F v) (locRho M ψ v u φ) r := by
  funext x
  rw [rho_apply M ψ hu]
  simp only [tens, locRho, hr x _ (fun a ha => funext fun i => (at_co M hu i).1 a ha), Pi.add_apply, map_add (f := _)]
  rw [show (fun i => evFin F v (x i) + evFin F v ((M.co.e u).1 i)) =
    (fun i => evFin F v (x i)) + fun i => evFin F v ((M.co.e u).1 i) from rfl]
  ring

theorem repl_add {κ : Type} [Fintype κ] (z : κ → AF F) (y s : κ → Fv F v) :
    repl v z y + (fun i => liftV v (s i)) = repl v z (y + s) := by
  funext i
  refine Prod.ext (add_zero _) ?_
  change (finPart z - epsK v (piK v (finPart z)) + epsK v y) i + epsK v s i =
    (finPart z - epsK v (piK v (finPart z)) + epsK v (y + s)) i
  rw [map_add (f := _), ← add_assoc]
  rfl

theorem slice_rho (ψ : AddChar (AF F) ℂ) {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evFin F v) u)
    (Ψ : (Fin n × Fin d → AF F) → ℂ) (z : Fin n × Fin d → AF F) :
    (fun y => M.co.rho ψ u Ψ (repl v z y)) = locRho M ψ v u fun y => Ψ (repl v z y) := by
  funext y
  rw [rho_apply M ψ hu, piK_repl, locRho]
  have e : repl v z y + (M.co.e u).1 = repl v z (y + fun i => evFin F v ((M.co.e u).1 i)) := by
    rw [← repl_add]
    exact congrArg (repl v z y + ·) (funext fun i => at_eq (at_co M hu i).1)
  rw [e]

theorem slice_mem' {κ : Type} [Fintype κ] {Ψ : (κ → AF F) → ℂ} (h : Ψ ∈ schA F κ) (z : κ → AF F) :
    (fun y => Ψ (repl v z y)) ∈ SB (κ → Fv F v) := by
  induction h using Submodule.span_induction with
  | mem Ψ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    haveI : T2Space (Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
    exact Submodule.smul_mem _ (f fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1)
      (slice_mem (epsK v) (piK v) (continuous_epsK v) (continuous_piK v) (piK_epsK v) hg _)
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul c a _ ha => exact Submodule.smul_mem _ c ha

end PositivityTheory.KCo
end
end

-- bundled from Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.LmOfLinBar
section
set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.KCo

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {t : E →ₐ[F] Fv F v} {sec : Fv F v × Fv F v → AE F E} {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype κ] {JA : Matrix α α (AE F E)} {JB : Matrix β β (AE F E)} {ψ : AddChar (AF F) ℂ}

theorem Grams.swap (hG : Grams σ t JA JB) : Grams σ t JB JA := by
  obtain ⟨ε, h1, h2, h3⟩ := hG.sym
  exact ⟨hG.uB, hG.uA, -ε, by rw [neg_mul_neg, h1], h3, by rw [neg_neg, h2]⟩

theorem bij_comp {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {ι : (X → ℂ) →ₗ[ℂ] (Y → ℂ)}
    (hb : Set.BijOn ι (SB X : Set _) (SB Y : Set _)) (e : Z ≃ₜ Y) :
    Set.BijOn (LinearMap.funLeft ℂ ℂ e ∘ₗ ι) (SB X : Set _) (SB Z : Set _) := by
  have hb' : Set.BijOn (LinearMap.funLeft ℂ ℂ e) (SB Y : Set _) (SB Z : Set _) := by
    refine ⟨fun Φ h => ?_, fun a _ b _ h => funext fun y => ?_, fun Φ h => ⟨Φ ∘ e.symm, ?_, funext fun z => by simp⟩⟩
    · exact And.intro (h.1.comp_continuous e.continuous) (h.2.comp_homeomorph e)
    · simpa using congrFun h (e.symm y)
    · exact And.intro (h.1.comp_continuous e.symm.continuous) (h.2.comp_homeomorph e.symm)
  exact hb'.comp hb

def swH (k α β : Type) [TopologicalSpace k] : (β × α → k) ≃ₜ (α × β → k) := Homeomorph.piCongrLeft (Y := fun _ => k) (Equiv.prodComm β α)

theorem swH_apply {k α β : Type} [TopologicalSpace k] (y : β × α → k) : swH k α β y = fun p => y p.swap := by
  funext p
  simp [swH, Homeomorph.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft']

def ofH (k α β : Type) [TopologicalSpace k] : Matrix α β k ≃ₜ (α × β → k) where
  toFun := ofM
  invFun := toM
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_pi fun p => (continuous_apply p.2).comp (continuous_apply p.1)
  continuous_invFun := continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j)

theorem LM.swap {d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ} {ι} (hι : LM t ψ d ι)
    {d' : Darboux (symp (R := AF F) (cA σ) (-1) JB JA) κ} (hd : ∀ x : Matrix α β (AE F E), d'.e xᵀ = d.e x) :
    LM t ψ d' (LinearMap.funLeft ℂ ℂ (swH (Fv F v) α β) ∘ₗ ι) := by
  refine ⟨bij_comp hι.bij _, fun u φ hφ => funext fun y => ?_⟩
  have e1 : (coord σ t JA JB uᵀ).1 = fun p => (coord σ t JB JA u).1 p.swap := by
    have : JA.map (piW t) * uᵀ.map (piW (t.comp σ)) * (JB.map (piW t))ᵀ =
        (JB.map (piW t) * u.map (piW (t.comp σ)) * (JA.map (piW t))ᵀ)ᵀ := by
      rw [transpose_mul, transpose_mul, transpose_transpose, transpose_map, Matrix.mul_assoc]
    rw [coord, this]; rfl
  have e2 : (coord σ t JA JB uᵀ).2 = fun p => (coord σ t JB JA u).2 p.swap := rfl
  have dt : ∀ a b : β × α → Fv F v, (fun p : α × β => a p.swap) ⬝ᵥ (fun p => b p.swap) = a ⬝ᵥ b := fun a b =>
    (Equiv.prodComm α β).sum_comp fun p => a p * b p
  rw [← transpose_transpose u, hd, transpose_transpose]
  simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, hι.Heisenberg₂ _ φ hφ, schr, swH_apply, e1, e2, dt]
  rfl

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}

theorem incM_map (h : IsSec σ t sec) {a b : Type} (J : Matrix a b E) : (incM F J).map (piW t) = J.map t :=
  Matrix.ext fun i j => by rw [incM, map_apply, map_apply, map_apply]; exact (h.inc (J i j)).1

theorem incM_map' (h : IsSec σ t sec) {a b : Type} (J : Matrix a b E) (i j) :
    (incM F J).map (piW (t.comp σ)) i j = t (σ (J i j)) := by rw [incM, map_apply, map_apply]; exact (h.inc (J i j)).2

theorem co_eq (h : IsSec σ t sec) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    -((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * u.map (piW (t.comp σ)) * (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1) =
      toM (coord σ t (incM F X.J) (incM F W.J) u).1 := by
  rw [coord, incM_map h, incM_map h, toM_ofM, Units.val_one, Units.val_one, transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem coord_snd {u : Matrix α β (AE F E)} : (coord σ t JA JB u).2 = 0 ↔ u.map (piW t) = 0 :=
  ⟨fun h => neg_eq_zero.1 (congrArg toM h), fun h => by rw [coord, h, neg_zero]; rfl⟩

theorem coord_fst {u : Matrix α β (AE F E)} (h : u.map (piW (t.comp σ)) = 0) : (coord σ t JA JB u).1 = 0 := by
  rw [coord, h, Matrix.mul_zero, Matrix.zero_mul, neg_zero]; rfl

theorem linBar_of_lm (hA : AdSt) (hU : ActsUniq) (h : IsSec σ t sec) (hG : Grams σ t (incM F X.J) (incM F W.J)) {ι}
    (hι : LM t ψ M.co ι) : M.IsLinBar ψ t 1 1 (LinearMap.funLeft ℂ ℂ (ofH (Fv F v) (Fin n) (Fin d)) ∘ₗ ι) := by
  have k : ∀ u, At (evFin F v) u → ∀ φ ∈ SB _, ∀ φ₁, Acts (evFin F v) (M.co.rho ψ u) φ φ₁ →
      ι φ₁ = schr (psiV ψ v) (coord σ t (incM F X.J) (incM F W.J) u) (ι φ) := fun u hu φ hφ φ₁ ha => by
    rw [hU F _ v _ φ hφ _ _ ha (hA.Heisenberg₂ F _ ψ v _ (hu.kd_map M.co.e.toLinearMap) φ)]
    exact hι.Heisenberg₂ u φ hφ
  refine ⟨bij_comp hι.bij _, fun u hu h0 φ hφ φ₁ _ ha Y => ?_, fun u hu h0 φ hφ φ₁ _ ha x hx hx0 => ?_⟩
  · simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, k u hu φ hφ φ₁ ha, schr, coord_snd.2 h0, dotProduct_zero, mul_zero,
      add_zero, AddChar.map_zero_eq_one, one_mul, co_eq h]
    rfl
  · simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, k u hu φ hφ φ₁ ha, schr, coord_fst h0, zero_dotProduct, mul_zero,
      add_zero, co_eq h, symp_eq h hG hx, sub_zero]
    rfl

theorem lm_of_linBar (hA : AdSt) (hψ : IsStd ψ) (h : IsSec σ t sec) (hG : Grams σ t (incM F X.J) (incM F W.J)) {ι}
    (hι : M.IsLinBar ψ t 1 1 ι) : LM t ψ M.co (LinearMap.funLeft ℂ ℂ (ofH (Fv F v) (Fin n) (Fin d)).symm ∘ₗ ι) := by
  have hc := ((hA.psi F ψ hψ).2 v).1
  obtain ⟨e, he1, he⟩ := exists_e h hG M.co
  set ι' := LinearMap.funLeft ℂ ℂ (ofH (Fv F v) (Fin n) (Fin d)).symm ∘ₗ ι
  have a1 : ∀ y, ∀ φ ∈ SB _, ι' (schr (psiV ψ v) (e (y, 0)) φ) = schr (psiV ψ v) (y, 0) (ι' φ) := fun y φ hφ => funext fun z => by
    obtain ⟨u, hu, hco, -⟩ := exists_coord h hG (y, 0)
    have := hι.trans u hu (coord_snd.1 (congrArg Prod.snd hco)) φ hφ _ (schr_mem hc _ hφ)
      (hA.Heisenberg₂ F _ ψ v _ (hu.kd_map M.co.e.toLinearMap) φ) (toM z)
    rw [co_eq h, hco] at this
    rw [← hco, he, hco]
    simp only [schr, dotProduct_zero, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul]
    exact this
  have a2 : ∀ y, ∀ φ ∈ SB _, ι' (schr (psiV ψ v) (e (0, y)) φ) = schr (psiV ψ v) (0, y) (ι' φ) := fun y φ hφ => funext fun z => by
    obtain ⟨u, hu, hco, h0⟩ := exists_coord h hG (0, y)
    obtain ⟨x, hx, hcx, -⟩ := exists_coord h hG (z, 0)
    have := hι.mult u hu (h0 rfl) φ hφ _ (schr_mem hc _ hφ) (hA.Heisenberg₂ F _ ψ v _ (hu.kd_map M.co.e.toLinearMap) φ) x hx
      (coord_snd.1 (congrArg Prod.snd hcx))
    rw [co_eq h, symp_eq h hG hx, hco, hcx] at this
    rw [← hco, he, hco]
    simp only [schr, zero_dotProduct, mul_zero, add_zero, sub_zero] at this ⊢
    exact this
  refine ⟨bij_comp hι.bij _, fun u φ hφ => ?_⟩
  rw [← he]
  obtain ⟨y, z⟩ := coord σ t (incM F X.J) (incM F W.J) u
  have b := a1 y _ (schr_mem hc (e (0, z)) hφ)
  rw [a2 z φ hφ, schr_schr, schr_schr, he1, ← map_add (f := _), map_smul] at b
  simp only [Prod.mk_add_mk, add_zero, zero_add] at b
  exact smul_right_injective _ (AddChar.val_isUnit _ _).ne_zero b

def DictX : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (B : Base F E)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (om : Rep σ X W) (χX χW : Chr F E), B.IsGood σ → (∃ r s, X.IsHerm σ B r s) →
    (∃ r s, W.IsSkew σ B r s) → M.IsWeil B.ψ χX χW om → ∀ (v : Pl F) (t : E →ₐ[F] Fv F v), (∃ ι, M.IsLinBar B.ψ t 1 1 ι) ∧
      (∀ g₀ : GL (Fin n) (Fv F v), ∃ g ∈ UAt σ X (evFin F v), (mat g).map (piW t) = g₀) ∧
      (∀ h₀ : GL (Fin d) (Fv F v), ∃ h ∈ UAt σ W (evFin F v), (mat h).map (piW t) = h₀) ∧
      ∀ ι, M.IsLinBar B.ψ t 1 1 ι →
        (∀ g ∈ UAt σ X (evFin F v), ∀ g₀ : GL (Fin n) (Fv F v), (mat g).map (piW t) = g₀ →
          Reads v ι (om (g, 1)) (omB (chrW χW t) (chrW χX t) g₀ 1)) ∧
        ∀ h ∈ UAt σ W (evFin F v), ∀ h₀ : GL (Fin d) (Fv F v), (mat h).map (piW t) = h₀ →
          Reads v ι (om (1, h)) (omB (chrW χW t) (chrW χX t) 1 h₀)

theorem dictX_of (hM : ModelEx) (hC : Cyc) (hA : AdSt) (hS : SecSt) (hU : ActsUniq) : DictX := by
  intro F E _ _ _ _ _ σ n d B X W M om χX χW hB ⟨_, _, hX⟩ ⟨_, _, hW⟩ hom v t
  obtain ⟨⟨sec, h⟩, -⟩ := hS F E σ hB.cm v t
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have uu : ∀ {m : ℕ} {J : Matrix (Fin m) (Fin m) E}, IsUnit J.det → IsUnit ((incM F J).map (piW t)) := fun {m J} hJ => by
    rw [incM_map h]
    exact ((Matrix.isUnit_iff_isUnit_det J).2 hJ).map (t : E →+* Fv F v).mapMatrix
  have hG : Grams σ t (incM F X.J) (incM F W.J) := by
    refine ⟨uu (GlobalTheory.CompanionTheory.Ar.RT.isUnit_det_of_cartan (F := F) X.J (B.emb w).1 1 (X.θ w) (by rw [one_smul]; exact hX.cartan w)),
      uu (GlobalTheory.CompanionTheory.Ar.RT.isUnit_det_of_cartan (F := F) W.J (B.emb w).1 Complex.I (W.θ w) (hW.cartan w)), 1, one_mul _,
      Matrix.ext fun i j => ?_, Matrix.ext fun i j => ?_⟩
    · rw [incM_map' h, incM_map h, one_smul, hX.herm]; rfl
    · rw [incM_map' h, incM_map h, neg_smul, one_smul, hW.skew, map_neg]; rfl
  obtain ⟨ι₀, hι₀⟩ := exists_lm hM hA hB.std h hG M.co
  obtain ⟨hR, ⟨d', hd', hL⟩, -⟩ := hom
  obtain ⟨ε, -, hε, hε'⟩ := hG.sym
  refine ⟨⟨_, linBar_of_lm hA hU h hG hι₀⟩, fun g₀ => h.exists_ug hε hG.uA g₀, fun g₀ => h.exists_ug hε' hG.uB g₀, fun ι hι => ?_⟩
  have lm := lm_of_linBar hA hB.std h hG hι
  refine ⟨fun g hg g₀ e φ hφ => ?_, fun g hg g₀ e φ hφ => ?_⟩
  · obtain ⟨φ₁, h1, h2, h3⟩ := acts_formula hM hC hA hB.std h hG.swap (lm.swap hd') hL.isWeilB g hg g₀ e φ hφ
    refine ⟨φ₁, h1, h2, funext fun Y => ?_⟩
    have := congrFun h3 (ofM Yᵀ)
    simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, Pi.smul_apply, rmL_apply, swH_apply, toM_ofM, smul_eq_mul] at this
    simp only [omB, gdet, map_one, Units.val_one, mul_one, apow_one, Matrix.mul_one]
    refine this.trans (congrArg _ (congrArg _ ?_))
    rw [← transpose_transpose (g₀.1ᵀ * Y), transpose_mul, transpose_transpose]
    rfl
  · obtain ⟨φ₁, h1, h2, h3⟩ := acts_formula hM hC hA hB.std h hG lm hR.isWeilB g hg g₀ e φ hφ
    refine ⟨φ₁, h1, h2, funext fun Y => ?_⟩
    have := congrFun h3 (ofM Y)
    simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, Pi.smul_apply, rmL_apply, toM_ofM, smul_eq_mul] at this
    simp only [omB, gdet, map_one, Units.val_one, mul_one, one_mul, apow_one, transpose_one, Matrix.one_mul]
    exact this

theorem dictSt_of (hX : DictX) (hS : SecSt) : DictSt := by
  intro F E _ _ _ _ _ σ n d B X W M om χX χW hB h1 h2 _ hom hχX hχW v t
  obtain ⟨e, s1, s2, k⟩ := hX F E σ n d B X W M om χX χW hB h1 h2 hom v t
  have hu := (hS F E σ hB.cm v t).2
  refine ⟨e, _, _, hu χW hχW, hu χX hχX, fun _ _ h => Or.inl h, fun ι hι => ⟨fun g hg => ⟨_, (k ι hι).1 g hg
    (GeneralLinearGroup.map (piW t) g.1) rfl⟩, fun g₀ => ?_, fun g hg => ⟨_, (k ι hι).2 g hg (GeneralLinearGroup.map (piW t) g.1) rfl⟩,
      fun g₀ => ?_⟩⟩
  · obtain ⟨g, hg, e⟩ := s1 g₀
    exact ⟨g, hg, (k ι hι).1 g hg g₀ e⟩
  · obtain ⟨g, hg, e⟩ := s2 g₀
    exact ⟨g, hg, (k ι hι).2 g hg g₀ e⟩

end PositivityTheory.KCo
end
end

