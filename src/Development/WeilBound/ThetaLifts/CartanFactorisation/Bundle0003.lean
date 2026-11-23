module

public import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle0002
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle0002
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.Bundle0009
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLFrame
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0125

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.CartanFactorisation.ExistsMaximalCompactInfinite
section
noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.EmbChart (atPlace atPlace_mul_right evFin_atPlace)
open PositivityTheory.ThK (kc_ring adele_t2Space kc_smul kc_cont_atPlace kc_at_atPlace kc_idem kc_closedU kc_cont_mat isCompact_of_units)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

attribute [local instance] kc_ring adele_t2Space kc_smul

theorem mat_mul' {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one' {J : Matrix (Fin n) (Fin n) E} : mat (1 : UA σ J) = 1 := rfl

def atGrp (σ : E →ₐ[F] E) (X : Spc F E n) {R : Type} [Zero R] (ev : AF F → R) : Subgroup (UA σ X.J) where
  carrier := UAt σ X ev
  one_mem' := fun u _ => by rw [mat_one', sub_self, smul_zero]
  mul_mem' := fun {g h} hg hh u hu => by
    have e : mat (g * h) - 1 = (mat g - 1) * mat h + (mat h - 1) := by rw [mat_mul', sub_mul, one_mul, sub_add_sub_cancel]
    rw [e, smul_add, ← Matrix.smul_mul, hg u hu, hh u hu, Matrix.zero_mul, add_zero]
  inv_mem' := fun {k} hk u hu => by
    have e0 : mat k⁻¹ * mat k = 1 := by rw [← mat_mul', inv_mul_cancel, mat_one']
    have e : mat k⁻¹ - 1 = -(mat k⁻¹ * (mat k - 1)) := by rw [mul_sub, e0, mul_one, neg_sub]
    rw [e, smul_neg, ← Matrix.mul_smul, hk u hu, Matrix.mul_zero, neg_zero]

theorem exists_maximal_compact_infinite :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (X : Spc F E n)
    (τ : ∀ w : InfinitePlace F, EmbOver E w), ∃ K : Subgroup (UA σ X.J), (K : Set (UA σ X.J)) = KInf σ X τ := by
  intro F E _ _ _ _ _ σ n X τ
  refine ⟨{ carrier := KInf σ X τ
            one_mem' := ⟨(atGrp σ X (evI F)).one_mem, fun w => by
              rw [mat_one', Matrix.map_one _ (map_zero _) (map_one _)]; exact Commute.one_left _⟩
            mul_mem' := fun {g h} hg hh => ⟨(atGrp σ X (evI F)).mul_mem hg.1 hh.1, fun w => by
              rw [mat_mul', Matrix.map_mul]; exact (hg.2 w).mul_left (hh.2 w)⟩
            inv_mem' := fun {k} hk => ⟨(atGrp σ X (evI F)).inv_mem hk.1, fun w => by
              have e0 : (mat k⁻¹).map (piInf (τ w)) * (mat k).map (piInf (τ w)) = 1 := by
                rw [← Matrix.map_mul, ← mat_mul', inv_mul_cancel, mat_one', Matrix.map_one _ (map_zero _) (map_one _)]
              have e1 : (mat k).map (piInf (τ w)) * (mat k⁻¹).map (piInf (τ w)) = 1 := mul_eq_one_comm.1 e0
              have h := (hk.2 w).eq
              calc _ = (mat k⁻¹).map (piInf (τ w)) * X.θ w * ((mat k).map (piInf (τ w)) * (mat k⁻¹).map (piInf (τ w))) := by
                    rw [e1, mul_one]
                _ = (mat k⁻¹).map (piInf (τ w)) * (X.θ w * (mat k).map (piInf (τ w))) * (mat k⁻¹).map (piInf (τ w)) := by
                    simp only [mul_assoc]
                _ = _ := by rw [← h, ← mul_assoc, e0, one_mul]⟩ }, rfl⟩


variable (E) in
abbrev Ix : Type := Module.Free.ChooseBasisIndex ℤ (𝓞 E)


variable (F) in
def bA (i : Ix E) : AE F E := inclR (F := F) (AF F) (integralBasis E i)

theorem bA_mul (i j : Ix E) : ∃ c : Ix E → ℤ, bA F i * bA F j = ∑ k, c k • bA F k := by
  refine ⟨fun k => (RingOfIntegers.basis E).repr (RingOfIntegers.basis E i * RingOfIntegers.basis E j) k, ?_⟩
  have h := congrArg (fun x : 𝓞 E => inclR (F := F) (AF F) (algebraMap (𝓞 E) E x))
    ((RingOfIntegers.basis E).sum_repr (RingOfIntegers.basis E i * RingOfIntegers.basis E j))
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_zsmul, map_mul] at h
  simp only [bA, integralBasis_apply]
  exact h.symm

theorem exists_sectionC : ∃ S : AE F E →ₗ[AF F] (Ix E → AF F), ∀ a, ∑ i, S a i • bA F i = a := by
  let Φ : (Ix E → AF F) →ₗ[AF F] AE F E := Fintype.linearCombination (AF F) (bA F)
  have hs : Function.Surjective Φ := by
    intro a
    change a ∈ LinearMap.range Φ
    induction a using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | add x y hx hy => exact add_mem hx hy
    | tmul a x =>
      refine ⟨fun i => (algebraMap ℚ F ((integralBasis E).repr x i)) • a, ?_⟩
      conv_rhs => rw [← (integralBasis E).sum_repr x, TensorProduct.tmul_sum]
      rw [Fintype.linearCombination_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← algebraMap_smul F ((integralBasis E).repr x i) (integralBasis E i), TensorProduct.tmul_smul,
        smul_assoc]
      congr 1
      change a • ((1 : AF F) ⊗ₜ[F] _) = _
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  obtain ⟨S, hS⟩ := Module.projective_lifting_property Φ LinearMap.id hs
  exact ⟨S, fun a => by simpa [Φ, Fintype.linearCombination_apply] using LinearMap.congr_fun hS a⟩

def phi (v : Pl F) (x : Ix E → Fv F v) : AE F E := ∑ i, atPlace v (x i) • bA F i

theorem phi_cont (v : Pl F) : Continuous (phi (E := E) v) :=
  continuous_finsetSum _ fun i _ => Continuous.fun_smul (f := fun a : Ix E → Fv F v => atPlace v (a i)) ((kc_cont_atPlace v).comp (continuous_apply i)) continuous_const

def lam (v : Pl F) (ε : ℝ) (hε : 0 ≤ ε) : AddSubgroup (AE F E) where
  carrier := phi v '' {x | ∀ i, ‖x i‖ ≤ ε}
  zero_mem' := ⟨0, fun i => by simpa using hε, by simp [phi]⟩
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, fun i => (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx i) (hy i)), by
      simp [phi, add_smul, Finset.sum_add_distrib]⟩
  neg_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨-x, fun i => by simpa using hx i, by simp [phi]⟩

theorem single_mem (v : Pl F) {ε : ℝ} (hε : 0 ≤ ε) (k : Ix E) {t : Fv F v} (ht : ‖t‖ ≤ ε) :
    atPlace v t • bA F k ∈ lam (E := E) v ε hε := by
  classical
  refine ⟨Pi.single k t, fun i => ?_, ?_⟩
  · by_cases h : i = k
    · subst h; simpa using ht
    · simpa [h] using hε
  · rw [phi, Finset.sum_eq_single k (fun i _ h => by simp [h]) (by simp)]; simp

theorem lam_mul (v : Pl F) {ε : ℝ} (hε : 0 ≤ ε) (h1 : ε ≤ 1) {a b : AE F E} (ha : a ∈ lam v ε hε) (hb : b ∈ lam v ε hε) :
    a * b ∈ lam v ε hε := by
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  rw [phi, phi, Finset.sum_mul_sum]
  refine sum_mem fun i _ => sum_mem fun j _ => ?_
  obtain ⟨c, hc⟩ := bA_mul (F := F) i j
  rw [smul_mul_smul_comm, hc, Finset.smul_sum, atPlace_mul_right, evFin_atPlace]
  refine sum_mem fun k _ => ?_
  rw [smul_comm]
  refine zsmul_mem (single_mem v hε k ?_) _
  rw [norm_mul]
  exact (mul_le_mul (hx i) ((hy j).trans h1) (norm_nonneg _) hε).trans_eq (mul_one _)

theorem lam_cpt (v : Pl F) {ε : ℝ} (hε : 0 ≤ ε) : IsCompact (lam (E := E) v ε hε : Set (AE F E)) := by
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  refine IsCompact.image ?_ (phi_cont v)
  have : {x : Ix E → Fv F v | ∀ i, ‖x i‖ ≤ ε} = Set.univ.pi fun _ => Metric.closedBall 0 ε := by ext; simp
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_closedBall _ _

def kEps (σ : E →ₐ[F] E) (X : Spc F E n) (v : Pl F) (ε : ℝ) (hε : 0 ≤ ε) (h1 : ε ≤ 1) : Subgroup (UA σ X.J) where
  carrier := {g | g ∈ UAt σ X (evFin F v) ∧ ∀ i j, (mat g - 1) i j ∈ lam v ε hε ∧ (mat g⁻¹ - 1) i j ∈ lam v ε hε}
  one_mem' := ⟨(atGrp σ X _).one_mem, fun i j => by simp [mat_one']⟩
  mul_mem' := fun {g h} hg hh => by
    have key : ∀ A B : Matrix (Fin n) (Fin n) (AE F E), (∀ i j, (A - 1) i j ∈ lam v ε hε) → (∀ i j, (B - 1) i j ∈ lam v ε hε) →
        ∀ i j, (A * B - 1) i j ∈ lam v ε hε := fun A B hA hB i j => by
      have e : A * B - 1 = (A - 1) * (B - 1) + (A - 1) + (B - 1) := by noncomm_ring
      rw [e, Matrix.add_apply, Matrix.add_apply, Matrix.mul_apply]
      exact add_mem (add_mem (sum_mem fun k _ => lam_mul v hε h1 (hA i k) (hB k j)) (hA i j)) (hB i j)
    refine ⟨(atGrp σ X _).mul_mem hg.1 hh.1, fun i j => ⟨key _ _ (fun i j => (hg.2 i j).1) (fun i j => (hh.2 i j).1) i j, ?_⟩⟩
    rw [mul_inv_rev]
    exact key _ _ (fun i j => (hh.2 i j).2) (fun i j => (hg.2 i j).2) i j
  inv_mem' := fun {g} hg => ⟨(atGrp σ X _).inv_mem hg.1, fun i j => ⟨(hg.2 i j).2, by rw [inv_inv]; exact (hg.2 i j).1⟩⟩

theorem kEps_cpt (X : Spc F E n) (v : Pl F) {ε : ℝ} (hε : 0 ≤ ε) (h1 : ε ≤ 1) :
    IsCompact (kEps σ X v ε hε h1 : Set (UA σ X.J)) := by
  have hm := kc_cont_mat (σ := σ) X.J
  have hi : Continuous fun k : UA σ X.J => mat k⁻¹ := hm.comp continuous_inv
  have hL := lam_cpt (E := E) v hε
  let S₀ : Set (Matrix (Fin n) (Fin n) (AE F E)) := Set.univ.pi fun _ => Set.univ.pi fun _ => (lam (E := E) v ε hε : Set (AE F E))
  have hS₀ : IsCompact S₀ := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hL
  refine isCompact_of_units _ (kc_closedU X.J) _ ?_ ((fun A => A + 1) '' S₀) (hS₀.image (continuous_id.add continuous_const))
    fun k hk => ⟨⟨mat k - 1, fun i _ j _ => (hk.2 i j).1, sub_add_cancel _ _⟩,
      ⟨mat k⁻¹ - 1, fun i _ j _ => (hk.2 i j).2, sub_add_cancel _ _⟩⟩
  have e : (kEps σ X v ε hε h1 : Set (UA σ X.J)) = (⋂ u, ⋂ _ : evFin F v u = 0, {k : UA σ X.J | u • (mat k - 1) = 0}) ∩
      ⋂ i, ⋂ j, ((fun k : UA σ X.J => (mat k - 1) i j) ⁻¹' (lam (E := E) v ε hε : Set (AE F E)) ∩
        (fun k : UA σ X.J => (mat k⁻¹ - 1) i j) ⁻¹' (lam (E := E) v ε hε : Set (AE F E))) := by
    ext k
    simp only [Set.mem_inter_iff, Set.mem_iInter]
    rfl
  rw [e]
  exact IsClosed.inter (isClosed_iInter fun u => isClosed_iInter fun _ =>
    isClosed_eq ((hm.sub continuous_const).const_smul u) continuous_const)
    (isClosed_iInter fun i => isClosed_iInter fun j => IsClosed.inter
      (hL.isClosed.preimage ((hm.sub continuous_const).matrix_elem i j))
      (hL.isClosed.preimage ((hi.sub continuous_const).matrix_elem i j)))

theorem kEps_nhds (X : Spc F E n) (v : Pl F) {ε : ℝ} (hε : 0 < ε) (h1 : ε ≤ 1) :
    ∃ U' ∈ 𝓝 (1 : UA σ X.J), U' ∩ UAt σ X (evFin F v) ⊆ kEps σ X v ε hε.le h1 := by
  obtain ⟨S, hS⟩ := exists_sectionC (F := F) (E := E)
  have hSc : Continuous S := IsModuleTopology.continuous_of_linearMap S
  have hev : Continuous (evFin F v) := ((RestrictedProduct.continuous_eval v).comp continuous_snd)
  have hm := kc_cont_mat (σ := σ) X.J
  have hi : Continuous fun k : UA σ X.J => mat k⁻¹ := hm.comp continuous_inv
  have hin : ∀ A : Matrix (Fin n) (Fin n) (AE F E), At (evFin F v) A → ∀ i j, (∀ k, ‖evFin F v (S (A i j) k)‖ < ε) →
      A i j ∈ lam v ε hε.le := fun A hA i j h => by
    refine ⟨fun k => evFin F v (S (A i j) k), fun k => (h k).le, ?_⟩
    have h2 : atPlace v 1 • A i j = A i j := congrFun (congrFun (kc_idem hA) i) j
    rw [← h2]
    conv_rhs => rw [← hS (A i j), Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul, atPlace_mul_right, one_mul, h2]
  have op : ∀ f : UA σ X.J → Matrix (Fin n) (Fin n) (AE F E), Continuous f → f 1 = 0 →
      ∀ᶠ g in 𝓝 (1 : UA σ X.J), ∀ i j k, ‖evFin F v (S (f g i j) k)‖ < ε := fun f hf h0 => by
    simp only [eventually_all]
    intro i j k
    have c : Continuous fun g => ‖evFin F v (S (f g i j) k)‖ :=
      (hev.comp ((continuous_apply k).comp (hSc.comp (hf.matrix_elem i j)))).norm
    exact c.continuousAt.eventually_lt continuousAt_const (by simpa [h0] using hε)
  refine ⟨_, (op _ (hm.sub continuous_const) (sub_self _)).and (op _ (hi.sub continuous_const) (by simp [mat_one'])),
    fun g hg => ⟨hg.2, fun i j => ⟨hin _ hg.2 i j (hg.1.1 i j), hin _ ((atGrp σ X _).inv_mem hg.2) i j (hg.1.2 i j)⟩⟩⟩

theorem local_compact_open_subgroups :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (X : Spc F E n)
    (v : Pl F), (∀ g ∈ UAt σ X (evFin F v), g⁻¹ ∈ UAt σ X (evFin F v)) ∧
      (∀ g ∈ UAt σ X (evFin F v), ∀ g' ∈ UAt σ X (evFin F v), g * g' ∈ UAt σ X (evFin F v)) ∧ ∀ U ∈ 𝓝 (1 : UA σ X.J),
      ∃ K : Subgroup (UA σ X.J), IsCompact (K : Set (UA σ X.J)) ∧ (K : Set (UA σ X.J)) ⊆ U ∩ UAt σ X (evFin F v) ∧
        ∃ U' ∈ 𝓝 (1 : UA σ X.J), U' ∩ UAt σ X (evFin F v) ⊆ K := by
  intro F E _ _ _ _ _ σ n X v
  refine ⟨fun g hg => (atGrp σ X _).inv_mem hg, fun g hg g' hg' => (atGrp σ X _).mul_mem hg hg', fun U hU => ?_⟩
  let e : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
  have e0 : ∀ m, 0 < e m := fun m => by positivity
  have e1 : ∀ m, e m ≤ 1 := fun m => (div_le_one (by positivity)).2 (by linarith [Nat.cast_nonneg (α := ℝ) m])
  let K : ℕ → Set (UA σ X.J) := fun m => kEps σ X v (e m) (e0 m).le (e1 m)
  have anti : Antitone K := fun a b hab g hg => ⟨hg.1, fun i j => by
    have hle : e b ≤ e a := Nat.one_div_le_one_div hab
    exact ⟨Set.image_mono (fun x hx => fun k => (hx k).trans hle) (hg.2 i j).1,
      Set.image_mono (fun x hx => fun k => (hx k).trans hle) (hg.2 i j).2⟩⟩
  haveI : T2Space (UA σ X.J) := (Units.isEmbedding_embedProduct.comp Topology.IsEmbedding.subtypeVal).t2Space
  have hint : ∀ g ∈ ⋂ m, K m, g = 1 := fun g hg => by
    refine Subtype.ext (Units.ext ?_)
    change mat g = 1
    rw [← sub_eq_zero]
    ext i j
    choose x hx hxe using fun m => ((Set.mem_iInter.1 hg m).2 i j).1
    have t0 : Tendsto x atTop (𝓝 0) := tendsto_pi_nhds.2 fun k =>
      squeeze_zero_norm (fun m => hx m k) tendsto_one_div_add_atTop_nhds_zero_nat
    have t1 := ((phi_cont (E := E) v).tendsto 0).comp t0
    have : (phi v ∘ x) = fun _ => (mat g - 1) i j := funext hxe
    rw [this] at t1
    have := tendsto_nhds_unique tendsto_const_nhds t1
    simpa [phi] using this
  obtain ⟨m, hm⟩ := exists_subset_nhds_of_isCompact' (V := K) anti.directed_ge (fun m => kEps_cpt X v _ _)
    (fun m => (kEps_cpt X v _ _).isClosed) (U := U) (mem_nhdsSet_iff_forall.2 (fun g hg => by rw [hint g hg]; exact hU))
  exact ⟨kEps σ X v (e m) (e0 m).le (e1 m), kEps_cpt X v _ _, fun g hg => ⟨hm hg, hg.1⟩, kEps_nhds X v (e0 m) (e1 m)⟩

end PositivityTheory.ThKF

end
end

-- bundled from Development.WeilBound.ThetaLifts.CartanFactorisation.PolCount
section
noncomputable section

namespace PositivityTheory.ThKF.PC

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem incM_map {n m : Type} (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

theorem pol_le (hV : VacLine) {n d P Q R S : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) {ψ : AddChar (AF F) ℂ}
    {τ : ∀ w : InfinitePlace F, EmbOver E w} {A : InfinitePlace F → Matrix (Fin n) (Ix P Q) ℂ}
    {C : InfinitePlace F → Matrix (Fin d) (Ix R S) ℂ} {Φ : Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)}
    (hcm : IsCMExt F E σ) (hψ : IsStd ψ) (hfr : Framed τ (incM F X.J) (incM F W.J) 1 Complex.I A C)
    (hθX : ∀ w, X.θ w * A w = A w * Jm P Q) (hθW : ∀ w, W.θ w * C w = C w * Jm R S) (hΦ : IsFockMap ψ τ M.co A C Φ) :
    M.Pol ψ τ ≤ LinearMap.range Φ := by
  have hL := PositivityTheory.RL.actsLaws
  have hz : ∀ (u : Matrix (Fin n) (Fin d) (AE F E)) (t : ℝ), M.co.rho ψ (realAd F t • u) 0 = 0 := by
    intro u t; funext x; simp [Darboux.rho, schr]
  have toD : ∀ u (f f₁ : SInf F (Fin n × Fin d)), SD (fun t => M.co.rho ψ (realAd F t • u)) f f₁ →
      ActsD (evI F) (M.heisLine ψ u) f f₁ := fun u f f₁ h => (hL F (Fin n × Fin d) f f₁ f₁).1 _ (hz u) h
  choose A' hA' using fun w => (hfr.2.1 w).2
  choose C' hC' using fun w => (hfr.2.2 w).2
  have decomp : ∀ (u : Matrix (Fin n) (Fin d) (AE F E)) w,
      u.map (piInf (τ w)) = A w * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * (C w)ᵀ := by
    intro u w
    rw [show A w * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * (C w)ᵀ =
        (A w * A' w) * u.map (piInf (τ w)) * ((C w) * (C' w))ᵀ by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc], hA', hC']
    simp
  have tw : ∀ w (c : Matrix (Ix P Q) (Ix R S) ℂ) (e : ℂ),
      A w * (e • (Jm P Q * c * Jm R S)) * (C w)ᵀ = e • (X.θ w * (A w * c * (C w)ᵀ) * (W.θ w)ᵀ) := by
    intro w c e
    have h2 : (C w)ᵀ * (W.θ w)ᵀ = Jm R S * (C w)ᵀ := by
      rw [← Matrix.transpose_mul, hθW w, Matrix.transpose_mul,
        show (Jm R S)ᵀ = Jm R S by simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_transpose]]
    calc A w * (e • (Jm P Q * c * Jm R S)) * (C w)ᵀ = e • ((A w * Jm P Q) * c * (Jm R S * (C w)ᵀ)) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = _ := by rw [← hθX w, ← h2]; simp only [Matrix.mul_assoc]
  unfold Model.Pol
  refine sInf_le ⟨fun f₀ hf₀ => ?_, fun u hu f hf f₁ h1 => ?_⟩
  · obtain ⟨ε, hε⟩ := hf₀
    obtain ⟨z, hz⟩ := hV F E σ (Fin n) (Fin d) (Fin n × Fin d) P Q R S ψ τ (incM F X.J) (incM F W.J) M.co 1
      Complex.I A C Φ hcm hψ hfr hΦ f₀ ε (fun u u' hu hu' c hc hc' f f' hf hf' =>
        hε u u' hu hu' (fun w => by rw [hc' w, tw, ← hc w]) f f' (toD _ _ _ hf) (toD _ _ _ hf'))
    exact ⟨z • PiTensorProduct.tprod ℂ (fun _ => (1 : Formalism.BasicNotions.TH.Pol P Q R S)), by rw [map_smul, hz]⟩
  · obtain ⟨T, rfl⟩ := hf
    exact ⟨_, (hL F _ _ _ _).2.2.1 _ (toD _ _ _ (hΦ.2 u hu _ (decomp u) T)) h1⟩

theorem exists_fock (hF : FockEx) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ X W} {χX χW : Chr F E}
    {om : Rep σ X W} {r s r' s' : ℕ} (hp : IsPair B M χX χW om r s r' s') :
    ∃ (A : InfinitePlace F → Matrix (Fin n) (Ix r s) ℂ) (C : InfinitePlace F → Matrix (Fin d) (Ix r' s') ℂ)
      (Φ : Tens F r s r' s' →ₗ[ℂ] SInf F (Fin n × Fin d)), Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C ∧
      (∀ w, X.θ w * A w = A w * Jm r s) ∧ (∀ w, W.θ w * C w = C w * Jm r' s') ∧ IsFockMap B.ψ B.emb M.co A C Φ := by
  choose A hA using fun w => PositivityTheory.RL.frameEx n r s _ _ (hp.herm.sig w) (hp.herm.cartan w)
  choose C hC using fun w => PositivityTheory.RL.frameEx d r' s' _ _ (hp.skew.sig w) (hp.skew.cartan w)
  have hfr : Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C :=
    ⟨one_mul _, fun w => by rw [one_smul, incM_map]; exact (hA w).1, fun w => by rw [incM_map]; exact (hC w).1⟩
  obtain ⟨Φ, hΦ⟩ := hF F E σ _ _ _ r s r' s' B.ψ B.emb _ _ M.co 1 Complex.I A C hp.base.cm hp.base.std hfr
  exact ⟨A, C, Φ, hfr, fun w => (hA w).2, fun w => (hC w).2, hΦ⟩

theorem rank_tens {ι L : Type} [Fintype ι] [Finite L] : Module.rank ℂ (⨂[ℂ] _ : ι, MvPolynomial L ℂ) ≤ Cardinal.aleph0 := by
  have b := Basis.piTensorProduct fun _ : ι => MvPolynomial.basisMonomials L ℂ
  rw [← b.mk_eq_rank'']
  exact Cardinal.mk_le_aleph0

theorem polCount_of (hF : FockEx) (hV : VacLine) : PolCount := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp
  obtain ⟨A, C, Φ, h1, h2, h3, h4⟩ := exists_fock hF hp
  exact (Submodule.rank_mono (pol_le hV M hp.base.cm hp.base.std h1 h2 h3 h4)).trans
    ((rank_range_le Φ).trans rank_tens)

end PositivityTheory.ThKF.PC

end
end

-- bundled from Development.WeilBound.ThetaLifts.CartanFactorisation.Unimod
section
noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_scale (h : IsCMExt F E σ) (ε : ℤˣ) : ∃ c : E, c ≠ 0 ∧ σ c = ((ε : ℤ) : E) * c := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · exact ⟨1, one_ne_zero, by simp⟩
  · by_contra hn
    push Not at hn
    have hid : ∀ x, σ x = x := fun x => by
      by_contra hx
      refine hn (x - σ x) (sub_ne_zero.2 (Ne.symm hx)) ?_
      simp [GlobalTheory.SiegelSet.sigma_sigma h]
    haveI := h.2.1
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    have hc : w.IsComplex := IsTotallyComplex.isComplex w
    refine (InfinitePlace.not_isReal_iff_isComplex.2 hc) ?_
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    ext x
    have := h.2.2.2 w.embedding x
    rw [hid] at this
    simpa using this.symm

theorem exists_hr (h : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {ε : ℤˣ}
    (hJ : ∀ i j, σ (J j i) = ((ε : ℤ) : E) * J i j) (hd : J.det ≠ 0) :
    ∃ J', IsHermND σ J' ∧ UG (cA σ) (incM F J) = HR (AF F) σ J' := by
  obtain ⟨c, hc, hσc⟩ := exists_scale h ε
  have hσ := GlobalTheory.SiegelSet.sigma_sigma h
  refine ⟨c • J.map σ, ⟨fun i j => ?_, ?_⟩, GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := J) hσ hc⟩
  · simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, hσ, hσc]
    rw [hJ j i]; ring
  · rw [Matrix.det_smul, show J.map σ = (σ : E →+* E).mapMatrix J from rfl, ← RingHom.map_det]
    exact mul_ne_zero (pow_ne_zero _ hc) ((map_ne_zero _).2 hd)

theorem unimodLC (h : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {ε : ℤˣ}
    (hJ : ∀ i j, σ (J j i) = ((ε : ℤ) : E) * J i j) (hd : J.det ≠ 0) : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure.IsUnimodularLC (UA σ J) := by
  obtain ⟨J', hJ', e⟩ := exists_hr h hJ hd
  have key : ∀ S : Subgroup (GL (Fin n) (AE F E)), S = HR (AF F) σ J' →
      @GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure.IsUnimodularLC S _ _ (borel S) := by
    rintro S rfl
    exact (GlobalTheory.AdelicStabUnimod.unimodularOver_adele F E σ h n J' hJ').1
  exact key _ e

theorem countable_ratU (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Countable (ratU σ J) := by
  haveI : Countable E := Function.Injective.countable (Module.finBasis ℚ E).equivFun.injective
  haveI : Countable (GL (Fin n) E) :=
    Function.Injective.countable (f := fun (g : GL (Fin n) E) (i j : Fin n) => (g : Matrix (Fin n) (Fin n) E) i j)
      fun _ _ h => Units.ext (Matrix.ext fun i j => congrFun (congrFun h i) j)
  haveI := (Set.countable_range (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F)))).to_subtype
  exact Function.Injective.countable
    (f := fun γ : ratU σ J => (⟨γ.1.1, Subgroup.mem_subgroupOf.1 γ.2⟩ :
      Set.range (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F)))))
    fun γ γ' h => Subtype.val_injective (Subtype.val_injective (congrArg Subtype.val h :))

theorem inclR_inj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  haveI : Nontrivial (AF F ⊗[F] E) := by
    haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
    infer_instance
  (inclR (F := F) (E := E) (AF F)).injective

theorem discrete_ratU (h : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {ε : ℤˣ}
    (hJ : ∀ i j, σ (J j i) = ((ε : ℤ) : E) * J i j) (hd : J.det ≠ 0) : DiscreteTopology (ratU σ J) := by
  obtain ⟨J', -, e⟩ := exists_hr h hJ hd
  haveI : DiscreteTopology (HFinIn (AF F) σ J') := GlobalTheory.RationalDiscrete.discreteTopology_HFinIn σ J'
  have mem : ∀ γ : ratU σ J, γ.1.1 ∈ HFin (AF F) σ J' := fun γ => by
    obtain ⟨u, hu⟩ := Subgroup.mem_subgroupOf.1 γ.2
    have h1 : γ.1.1 ∈ HR (AF F) σ J' := e ▸ γ.1.2
    refine Subgroup.mem_map.2 ⟨u, ?_, hu⟩
    rw [← show _ = γ.1.1 from hu] at h1
    change Formalism.UG.cT (sigR (AF F) σ) (u.1.map (inclR (AF F))) * J'.map (inclR (AF F)) * u.1.map (inclR (AF F)) =
      J'.map (inclR (AF F)) at h1
    change Formalism.UG.cT (σ : E →+* E) u.1 * J' * u.1 = J'
    apply Matrix.map_injective (inclR_inj (F := F))
    simp only [Matrix.map_mul]
    exact h1
  let f : ratU σ J → HFinIn (AF F) σ J' := fun γ => ⟨⟨γ.1.1, e ▸ γ.1.2⟩, Subgroup.mem_subgroupOf.2 (mem γ)⟩
  have hc : Continuous f := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  exact DiscreteTopology.of_continuous_injective hc fun a b hab =>
    Subtype.ext (Subtype.ext (congrArg (fun z : HFinIn (AF F) σ J' => z.1.1) hab))

theorem sigmaFinite_of_lc {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    (h : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure.IsUnimodularLC G) (μ : Measure G) [μ.IsHaarMeasure] : SigmaFinite μ := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := h
  infer_instance

theorem sFinite_haar (h : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {ε : ℤˣ}
    (hJ : ∀ i j, σ (J j i) = ((ε : ℤ) : E) * J i j) (hd : J.det ≠ 0) (μ : Measure (UA σ J)) [μ.IsHaarMeasure] :
    SigmaFinite μ :=
  sigmaFinite_of_lc (unimodLC h hJ hd) μ

theorem unimodularity_holds : Unimod := by
  intro F E _ _ _ _ _ σ h n J ε hJ hd
  obtain ⟨h1, h2, h3, h4, h5, ⟨μ, hμ⟩, h7⟩ := unimodLC h hJ hd
  haveI := countable_ratU σ J
  haveI := discrete_ratU h hJ hd
  obtain ⟨𝓕, -, h𝓕⟩ := (GlobalTheory.RationalUnitaryDomains.isDiscreteWithDomains_of_discrete (ratU σ J)).2.2 μ hμ
  exact ⟨inferInstance, ⟨μ, 𝓕, hμ, h𝓕⟩, h7⟩

end PositivityTheory.ThKF

end
end

