module

public import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
public import Development.WeilBound.ThetaLifts.SmallCones.SliceArch
public import Development.WeilBound.ThetaLifts.LatticeBasics.IsCompactIntV
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import GroundTheory.GlobalFields.TateThesis.Bundle0008
public import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
public import GroundTheory.GlobalFields.TateThesis.SchwartzBruhatFinite
public import Development.WeilBound.ThetaLifts.SmallCones.Bundle0001
public import Development.WeilBound.ThetaLifts.SmallCones.Bundle0011

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.SliceAd
section
noncomputable section

namespace PositivityTheory.ThKCT.Ad

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField.mixedEmbedding
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.HeisSchA PositivityTheory.ThKCT.Arch

variable {F : Type} [Field F] [NumberField F] {κ κ₁ : Type} [Fintype κ] [Fintype κ₁]


variable (F) in
def qI : AF F →+* mixedSpace F := (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp p1

theorem continuous_qI : Continuous (qI F) := by
  have : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
    change Continuous fun x : InfiniteAdeleRing F =>
      ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
       (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
    refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
    · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
    · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)
  exact this.comp continuous_fst

def pt (x : mixedSpace F) (y : Af F) : AF F := mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x) y

theorem qI_pt (x : mixedSpace F) (y : Af F) : qI F (pt x y) = x :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply x

theorem finite_projection_mixed_point (x : mixedSpace F) (y : Af F) : p2 (pt x y) = y := rfl

theorem pureA_pt (f : (κ → mixedSpace F) → ℂ) (g : (κ → Af F) → ℂ) (x : κ → mixedSpace F) (y : κ → Af F) :
    pureA F f g (fun i => pt (x i) (y i)) = f x * g y := by
  change f (fun i => qI F (pt (x i) (y i))) * g y = _
  simp only [qI_pt]

theorem pureA_cancel {f f' : SInf F κ} {g : (κ → Af F) → ℂ} (hg : g ≠ 0) (h : pureA F f g = pureA F f' g) : f = f' := by
  obtain ⟨y, hy⟩ := Function.ne_iff.1 hg
  ext x
  have := congrFun h fun i => pt (x i) (y i)
  rw [pureA_pt, pureA_pt] at this
  exact mul_right_cancel₀ hy this

theorem pureA_smul_left (c : ℂ) (f : SInf F κ) (g : (κ → Af F) → ℂ) : pureA F (c • f : SInf F κ) g = c • pureA F f g :=
  funext fun _ => mul_assoc _ _ _

theorem pureA_mem (f : SInf F κ) {g : (κ → Af F) → ℂ} (hg : g ∈ SB _) : pureA F f g ∈ schA F κ :=
  Submodule.subset_span ⟨f, g, hg, rfl⟩

theorem psi_eq {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (a : AF F) : ψ a =
    Complex.exp (Complex.I * ((-(2 * Real.pi) * Algebra.trace ℝ (mixedSpace F) (qI F a) : ℝ) : ℂ)) * finChar ψ (p2 a) := by
  rw [map_eq_mul ψ, hψ.2.2 _ (at_mk _)]
  congr 2
  change _ * ((Algebra.trace ℝ (mixedSpace F) (qI F a) : ℝ) : ℂ) = _
  push_cast
  ring


variable (F κ) in
def aw0 : ((κ → mixedSpace F) × (κ → mixedSpace F)) →ₗ[ℝ] (κ → mixedSpace F) × ((κ → mixedSpace F) →L[ℝ] ℝ) :=
  LinearMap.prodMap LinearMap.id
    { toFun := fun c => -(2 * Real.pi) • trL c
      map_add' := fun c c' => by ext y; simp [trL_apply, mul_add]; ring
      map_smul' := fun r c => by ext y; simp [trL_apply]; ring }

def ev2 (w : (κ → AF F) × (κ → AF F)) : (κ → mixedSpace F) × (κ → mixedSpace F) := (fun i => qI F (w.1 i), fun i => qI F (w.2 i))

def fn2 (w : (κ → AF F) × (κ → AF F)) : (κ → Af F) × (κ → Af F) := (fun i => p2 (w.1 i), fun i => p2 (w.2 i))

theorem pairEvaluation_linear_combination {m : ℕ} (y : Fin m → AF F) (c : Fin m → (κ → AF F) × (κ → AF F)) :
    ev2 (∑ j, y j • c j) = ∑ j, qI F (y j) • ev2 (c j) := by
  ext i <;> simp [ev2, Prod.fst_sum, Prod.snd_sum]

theorem pairFunctional_linear_combination {m : ℕ} (y : Fin m → AF F) (c : Fin m → (κ → AF F) × (κ → AF F)) :
    fn2 (∑ j, y j • c j) = ∑ j, p2 (y j) • fn2 (c j) := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [fn2, Prod.fst_sum, Prod.snd_sum]

theorem pairEvaluation_smul (y : AF F) (c : (κ → AF F) × (κ → AF F)) : ev2 (y • c) = qI F y • ev2 c := by
  ext i <;> simp [ev2]

theorem pairFunctional_smul (y : AF F) (c : (κ → AF F) × (κ → AF F)) : fn2 (y • c) = p2 y • fn2 c := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [fn2]

def fw (ψ : AddChar (AF F) ℂ) (b : (κ → Af F) × (κ → Af F)) (g : (κ → Af F) → ℂ) : (κ → Af F) → ℂ :=
  finS ψ g b.2 b.1 (p2 (⅟(2 : AF F)) * (b.1 ⬝ᵥ b.2))

theorem fw_mem {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (b : (κ → Af F) × (κ → Af F)) {g : (κ → Af F) → ℂ} (hg : g ∈ SB _) :
    fw ψ b g ∈ SB _ := finS_mem ψ hψ.1 hg _ _ _

theorem fw_zero (ψ : AddChar (AF F) ℂ) (g : (κ → Af F) → ℂ) : fw ψ 0 g = g := by
  funext x
  simp [fw, finS]

theorem schr_pure {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (w : (κ → AF F) × (κ → AF F)) (f : SInf F κ) (g : (κ → Af F) → ℂ) :
    schr ψ w (pureA F f g) = pureA F (S (aw0 F κ (ev2 w)) f) (fw ψ (fn2 w) g) := by
  funext x
  have h2 : qI F (⅟(2 : AF F)) = algebraMap ℝ _ (1 / 2 : ℝ) := by
    have e : qI F (⅟(2 : AF F)) * 2 = 1 := by rw [← map_ofNat (qI F) 2, ← map_mul, invOf_mul_self, map_one]
    have e' : algebraMap ℝ (mixedSpace F) (1 / 2 : ℝ) * 2 = 1 := by
      rw [← map_ofNat (algebraMap ℝ (mixedSpace F)) 2, ← map_mul, ← map_one (algebraMap ℝ (mixedSpace F))]; norm_num
    linear_combination (algebraMap ℝ (mixedSpace F) (1 / 2 : ℝ)) * e - qI F (⅟(2 : AF F)) * e'
  change ψ _ * (f (fun i => qI F ((x + w.1) i)) * g (fun i => p2 ((x + w.1) i))) =
    S (aw0 F κ (ev2 w)) f (fun i => qI F (x i)) * (finChar ψ ((fun i => p2 (x i)) ⬝ᵥ (fn2 w).2 + _) * g ((fun i => p2 (x i)) + (fn2 w).1))
  rw [S_apply, psi_eq hψ, ph]
  have e1 : (fun i => qI F ((x + w.1) i)) = (fun i => qI F (x i)) + (aw0 F κ (ev2 w)).1 := funext fun i => map_add _ _ _
  have e2 : (fun i => p2 ((x + w.1) i)) = (fun i => p2 (x i)) + (fn2 w).1 := funext fun i => map_add _ _ _
  have e3 : p2 (x ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) =
      (fun i => p2 (x i)) ⬝ᵥ (fn2 w).2 + p2 (⅟(2 : AF F)) * ((fn2 w).1 ⬝ᵥ (fn2 w).2) := by
    rw [map_add (f := _), map_mul, RingHom.map_dotProduct, RingHom.map_dotProduct]; rfl
  have e4 : -(2 * Real.pi) * Algebra.trace ℝ (mixedSpace F) (qI F (x ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2))) =
      (aw0 F κ (ev2 w)).2 (fun i => qI F (x i)) + (aw0 F κ (ev2 w)).2 (aw0 F κ (ev2 w)).1 / 2 := by
    rw [map_add (f := _), map_mul, RingHom.map_dotProduct, RingHom.map_dotProduct, h2, ← Algebra.smul_def, map_add (f := _), map_smul]
    change _ = -(2 * Real.pi) * Algebra.trace ℝ (mixedSpace F) ((qI F ∘ x) ⬝ᵥ (qI F ∘ w.2)) +
      -(2 * Real.pi) * Algebra.trace ℝ (mixedSpace F) ((qI F ∘ w.1) ⬝ᵥ (qI F ∘ w.2)) / 2
    rw [smul_eq_mul]; ring
  rw [e1, e2, e3, e4]
  ring

theorem schr_comm {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (w w' : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) • schr ψ w' (schr ψ w φ) := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, add_dotProduct]
  rw [add_right_comm x w.1]
  congr 2
  ring

theorem fw_lc {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {g : (κ → Af F) → ℂ} (hg : g ∈ SB _) :
    IsLocallyConstant fun b => fw ψ b g := by
  haveI := nonarch_finiteAdeleRing (F := F)
  haveI := nonarch_pi (G := fun _ : κ => Af F)
  obtain ⟨U, hU⟩ := GlobalTheory.WeilM.HaarUniq.exists_invariant hg
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun b₀ => ?_
  have hc : IsLocallyConstant fun z : ((κ → Af F) × (κ → Af F)) × (κ → Af F) =>
      finChar ψ (z.2 ⬝ᵥ z.1.2 + p2 (⅟(2 : AF F)) * (z.1.1 ⬝ᵥ z.1.2)) :=
    (finChar_isLocallyConstant ψ hψ.1).comp_continuous ((continuous_snd.dotProduct continuous_fst.snd).add
      (continuous_const.mul (continuous_fst.fst.dotProduct continuous_fst.snd)))
  have hK : IsCompact (tsupport fun x => g (x + b₀.1)) := hg.2.comp_homeomorph (Homeomorph.addRight b₀.1)
  have h1 := hK.eventually_forall_of_forall_eventually (x₀ := b₀)
    (P := fun b x => finChar ψ (x ⬝ᵥ b.2 + p2 (⅟(2 : AF F)) * (b.1 ⬝ᵥ b.2)) =
      finChar ψ (x ⬝ᵥ b₀.2 + p2 (⅟(2 : AF F)) * (b₀.1 ⬝ᵥ b₀.2))) fun x _ => by
      filter_upwards [hc.eventually_eq (b₀, x),
        (hc.comp_continuous (continuous_const.prodMk continuous_snd :
          Continuous fun z : ((κ → Af F) × (κ → Af F)) × (κ → Af F) => (b₀, z.2))).eventually_eq (b₀, x)] with z h h'
      exact h.trans h'.symm
  have h2 : ∀ᶠ b : (κ → Af F) × (κ → Af F) in 𝓝 b₀, b.1 - b₀.1 ∈ U :=
    (continuous_fst.sub continuous_const).continuousAt.eventually_mem (by simpa using U.mem_nhds_zero)
  filter_upwards [h1, h2] with b hb hb'
  funext x
  have e : g (x + b.1) = g (x + b₀.1) := by rw [← hU _ hb' (x + b₀.1)]; congr 1; abel
  simp only [fw, finS, e]
  by_cases hx : x ∈ tsupport fun x => g (x + b₀.1)
  · rw [hb x hx]
  · rw [show g (x + b₀.1) = 0 from image_eq_zero_of_notMem_tsupport (f := fun x => g (x + b₀.1)) hx, mul_zero, mul_zero]


open GroundTheory.Global in
theorem annih {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {U : Set (Af F)} (hU : U ∈ 𝓝 0) :
    ∃ C : Set (Af F), IsCompact C ∧ ∀ b, (∀ a ∈ U, finChar ψ (a * b) = 1) → b ∈ C := by
  let χ : AddChar (AF F) Circle :=
    { toFun := fun x => ⟨ψ x, by simpa [Submonoid.unitSphere] using GlobalTheory.StdCharFromIsStd.norm_psi hψ x⟩
      map_zero_eq_one' := Subtype.ext ψ.map_zero_eq_one
      map_add_eq_mul' := fun a b => Subtype.ext (ψ.map_add_eq_mul a b) }
  obtain ⟨ξ, hξ, -⟩ := existsUnique_eq_adelicChar_mul χ (hψ.1.subtype_mk _) fun k => Subtype.ext (hψ.2.1 k)
  have h0 : ξ ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := GlobalTheory.StdCharFromIsStd.exists_ne_one hψ
    have := hξ x
    rw [map_zero, zero_mul, AddChar.map_zero_eq_one] at this
    exact hx (congrArg Subtype.val this)
  obtain ⟨d, hd, hd'⟩ := exists_forall_mul_mem_of_mem_nhds hU
  have hd0 : algebraMap (𝓞 F) F d ≠ 0 := fun h => hd (RingOfIntegers.coe_injective (h.trans (map_zero _).symm))
  refine ⟨_, (isCompact_idealFiniteAdeles (traceDualIdeal F 1)).image
    (continuous_const_mul (algebraMap F (Af F) (ξ * algebraMap (𝓞 F) F d)⁻¹)), fun b hb =>
    ⟨algebraMap F (Af F) (ξ * algebraMap (𝓞 F) F d) * b, ?_, ?_⟩⟩
  · refine (forall_finiteAdelicChar_mul_eq_one_iff 1 _).1 fun x hx => ?_
    have h1 := hb _ (hd' x (by rw [← SetLike.mem_coe, ← idealFiniteAdeles_one]; exact hx))
    have h2 := hξ (finiteAdeleInr (algebraMap F (Af F) (algebraMap (𝓞 F) F d) * x * b))
    rw [algebraMap_mul_finiteAdeleInr, ← finiteAdelicChar_apply] at h2
    rw [show x * (algebraMap F (Af F) (ξ * algebraMap (𝓞 F) F d) * b) =
      algebraMap F (Af F) ξ * (algebraMap F (Af F) (algebraMap (𝓞 F) F d) * x * b) by rw [map_mul]; ring, ← h2]
    exact Subtype.ext h1
  · beta_reduce
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (mul_ne_zero h0 hd0), map_one, one_mul]

theorem trace_nondeg (b : mixedSpace F) (h : ∀ y, Algebra.trace ℝ (mixedSpace F) (b * y) = 0) : b = 0 := by
  refine (latticeBasis F).ext_elem fun j => ?_
  have := h (mixedEmbedding F ((integralBasis F).traceDual j))
  rw [← (latticeBasis F).sum_repr b] at this
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, latticeBasis_apply, ← map_mul,
    GlobalTheory.ThK.Dbl.Dense.trace_emb, Module.Basis.trace_mul_traceDual] at this
  simpa [apply_ite] using this

theorem exists_half_trace : ∃ K : ℝ, 0 ≤ K ∧ ∀ x : mixedSpace F, x ≠ 0 → ∃ a, ‖a‖ * ‖x‖ ≤ K ∧
    Algebra.trace ℝ (mixedSpace F) (x * a) = 1 / 2 :=
  exists_half ((LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := mixedSpace F) (F' := ℝ)).toLinearMap ∘ₗ
    Algebra.traceForm ℝ (mixedSpace F)) fun x hx => trace_nondeg x fun y => DFunLike.congr_fun hx y

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d}
  {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}

theorem ev_pure {B : Base F E} {M : Model σ X W} {M₁ : Model σ X₁ W₁} (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ) {ι ι' I e}
    (he : IsEv B M M₁ ι ι' I e) : ∃ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁))
      (ef : ((Fin n × Fin d → Af F) → ℂ) → (Fin n₁ × Fin d₁ → Af F) → ℂ), ei ≠ 0 ∧
      ∀ φ ∈ SB (Fin n × Fin d → Af F), ef φ ∈ SB _ ∧ ∀ f : SInf F _, e (pureA F f φ) = pureA F (ei f) (ef φ) := by
  obtain ⟨ei, ev, h0, h1, h2⟩ := he.loc
  have : ∀ φ, φ ∈ SB (Fin n × Fin d → Af F) → ∃ φ₁ ∈ SB (Fin n₁ × Fin d₁ → Af F),
      ∀ f : SInf F _, e (pureA F f φ) = pureA F (ei f) φ₁ := fun g hg => by
    have := GlobalTheory.ThK.Dbl.Dense.mem_span_pf hg
    clear hg
    induction this using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨φ, hφ, rfl⟩ := hx
      have hv : ∀ᶠ v in cofinite, φ v = M.vac v := by
        filter_upwards [hφ.2, hM.std] with v a b using a.trans b.symm
      refine ⟨GlobalTheory.ThK.Dbl.Dense.pf fun v => ev v (φ v), GlobalTheory.ThK.Dbl.Dense.pf_mem ⟨fun v => (h1 v).2 ▸ ⟨_, hφ.1 v, rfl⟩, ?_⟩,
        fun f => h2 f φ hφ.1 hv⟩
      filter_upwards [hv, hM₁.std] with v a b
      rw [a, (h1 v).1, b]; rfl
    | zero => exact ⟨0, zero_mem _, fun f => by simp only [GlobalTheory.ThK.Dbl.Dense.pureA_zero, map_zero]⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, ha'⟩ := hx
      obtain ⟨b, hb, hb'⟩ := hy
      exact ⟨a + b, add_mem ha hb, fun f => by simp only [GlobalTheory.ThK.Dbl.Dense.pureA_add, map_add (f := _), ha', hb']⟩
    | smul c x _ hx =>
      obtain ⟨a, ha, ha'⟩ := hx
      exact ⟨c • a, Submodule.smul_mem _ _ ha, fun f => by simp only [GlobalTheory.ThK.Dbl.Dense.pureA_smul, map_smul, ha']⟩
  choose! ef h using this
  exact ⟨ei, ef, h0, h⟩

end PositivityTheory.ThKCT.Ad

end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.SoKill
section
noncomputable section

namespace PositivityTheory.ThKCT.So

open Filter Topology NumberField IsDedekindDomain Matrix GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  GlobalTheory.CompanionTheory.Ar.RT.Move GlobalTheory.LatVac PositivityTheory.KCo GlobalTheory.ThK
open scoped TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField Classical.propDecidable

theorem kill_set {X : Type} [TopologicalSpace X] (N : Submodule ℂ (X → ℂ)) (Z : Set X)
    (h : ∀ Y ∉ Z, ∃ (m : X → ℂ) (c : ℂ), IsLocallyConstant m ∧ m Y ≠ c ∧ ∀ Φ ∈ SB X, (fun y => (m y - c) * Φ y) ∈ N) :
    ∀ Φ ∈ SB X, (∀ Y ∈ Z, Φ Y = 0) → Φ ∈ N := by
  classical
  choose! m c hm hne hN using h
  have key : ∀ s : Finset X, (∀ Y ∈ s, Y ∉ Z) → ∀ Φ ∈ SB X, (∀ y, Φ y ≠ 0 → ∃ Y ∈ s, m Y y = m Y Y) → Φ ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _ Φ _ h0
      have : Φ = 0 := funext fun y => by by_contra e; simpa using h0 y e
      rw [this]; exact zero_mem _
    | insert Y s hY ih =>
      intro hs Φ hΦ h0
      have hY1 := hs Y (Finset.mem_insert_self _ _)
      have hU : IsClopen {y | m Y y = m Y Y} := (hm Y hY1).isClopen_fiber _
      have h1 := hN Y hY1 _ (Submodule.smul_mem _ (m Y Y - c Y)⁻¹ (indicator_mem hU hΦ))
      have h2 := ih (fun Z hZ => hs Z (Finset.mem_insert_of_mem hZ)) _ (indicator_mem hU.compl hΦ) fun y hy => by
        have hy1 : y ∈ {y | m Y y = m Y Y}ᶜ := Set.mem_of_indicator_ne_zero hy
        rw [Set.indicator_of_mem hy1] at hy
        obtain ⟨Z, hZ, e⟩ := h0 y hy
        rcases Finset.mem_insert.1 hZ with rfl | hZ
        · exact (hy1 e).elim
        · exact ⟨Z, hZ, e⟩
      convert add_mem h1 h2 using 1
      funext y
      by_cases hy : y ∈ {y | m Y y = m Y Y}
      · have e : m Y y = m Y Y := hy
        have : y ∉ {y | m Y y = m Y Y}ᶜ := fun h => h hy
        simp only [Pi.add_apply, Pi.smul_apply, Set.indicator_of_mem hy, Set.indicator_of_notMem this, e, smul_eq_mul]
        rw [mul_inv_cancel_left₀ (sub_ne_zero.2 (hne Y hY1)), add_zero]
      · simp [Set.indicator_of_notMem hy, Set.indicator_of_mem (show y ∈ {y | m Y y = m Y Y}ᶜ from hy)]
  intro Φ hΦ h1
  have hK : IsCompact {y | Φ y ≠ 0} :=
    hΦ.2.isCompact.of_isClosed_subset (hΦ.1.isClopen_fiber 0).compl.1 subset_closure
  obtain ⟨s, hs, hc⟩ := hK.elim_nhds_subcover (fun Y => {y | m Y y = m Y Y}) fun Y hY =>
    ((hm Y fun e => hY (h1 Y e)).isOpen_fiber _).mem_nhds rfl
  refine key s (fun Y hY e => hs Y hY (h1 Y e)) Φ hΦ fun y hy => ?_
  simpa using hc hy

theorem rank_ne_iff {k : Type} [Field k] {n d : ℕ} (C : Matrix (Fin n) (Fin d) k) : C.rank ≠ n ↔ ∃ p, p ≠ 0 ∧ p ᵥ* C = 0 := by
  have h := LinearMap.finrank_range_add_finrank_ker Cᵀ.mulVecLin
  rw [Module.finrank_fin_fun, ← Matrix.rank, Matrix.rank_transpose] at h
  have : C.rank ≠ n ↔ LinearMap.ker Cᵀ.mulVecLin ≠ ⊥ := by
    rw [Ne, Ne, ← Submodule.finrank_eq_zero]
    omega
  rw [this, Submodule.ne_bot_iff]
  refine exists_congr fun p => ?_
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose, and_comm]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) {ψ : AddChar (AF F) ℂ}

theorem eigen_kill_set (h : IsCMExt F E σ) (hψ : IsStd ψ) (hX : X.J.det ≠ 0) (hW : W.J.det ≠ 0) {t : E →ₐ[F] Fv F v} {ι}
    (hι : M.IsLinBar ψ t 1 1 ι) (l : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ)
    (A : Set (Matrix (Fin n) (Fin d) (AE F E) × ℂ)) (hA : ∀ a ∈ A, At (evFin F v) a.1 ∧ a.1.map (piW (t.comp σ)) = 0)
    (hl : ∀ a ∈ A, ∀ φ ∈ SB _, l (locRho M ψ v a.1 φ) = a.2 * l φ) {φ} (hφ : φ ∈ SB (Fin n × Fin d → Fv F v))
    (hz : ∀ x, At (evFin F v) x → x.map (piW t) = 0 → (∀ a ∈ A, ψ (sy σ X W x a.1) = a.2) → ι φ (coB σ X W t x) = 0) :
    l φ = 0 := by
  choose xo a1 a2 a3 using exists_coB h t hX hW
  have hb := hι.bij
  have key := kill_set ((SB _ ⊓ LinearMap.ker l).map ι) {Y | ∀ a ∈ A, ψ (sy σ X W (xo Y) a.1) = a.2} (fun Y hY => ?_) _ (hb.1 hφ)
    fun Y hY => by rw [← a3 Y]; exact hz _ (a1 Y) (a2 Y) hY
  · obtain ⟨φ', h', e⟩ := key
    rw [← hb.2.1 h'.1 hφ e]
    exact h'.2
  simp only [Set.mem_setOf_eq, not_forall] at hY
  obtain ⟨⟨u, c⟩, ha, hne⟩ := hY
  obtain ⟨hu, h1⟩ := hA _ ha
  let m : Matrix (Fin n) (Fin d) (Fv F v) → ℂ := fun y => ψ (sy σ X W (xo y) u)
  have hm : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ι (locRho M ψ v u φ) = fun y => m y * ι φ y := fun φ hφ => funext fun y => by
    have := mult' M hψ hι hu h1 (a1 y) (a2 y) hφ
    rwa [a3] at this
  haveI : T2Space (Matrix (Fin n) (Fin d) (Fv F v)) := inferInstanceAs (T2Space (Fin n → Fin d → Fv F v))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin d) (Fv F v)) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin d → Fv F v))
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin d) (Fv F v)) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin d → Fv F v))
  refine ⟨m, c, lc_of_mul m fun Φ hΦ => ?_, hne, fun Φ hΦ => ?_⟩
  · obtain ⟨φ', h', rfl⟩ := hb.2.2 hΦ
    rw [← hm φ' h']
    exact hb.1 (locRho_mem M hψ u h')
  · obtain ⟨φ', h', rfl⟩ := hb.2.2 hΦ
    refine ⟨locRho M ψ v u φ' - c • φ', ⟨sub_mem (locRho_mem M hψ u h') (Submodule.smul_mem _ _ h'), ?_⟩, ?_⟩
    · change l _ = 0
      rw [map_sub, map_smul, hl _ ha φ' h', smul_eq_mul, sub_self]
    · rw [map_sub, map_smul, hm φ' h']
      funext y
      simp [sub_mul]

include M in
theorem sy_smul (x u : Matrix (Fin n) (Fin d) (AE F E)) (a : AF F) : sy σ X W x (a • u) = a * sy σ X W x u := by
  simp only [sy, M.co.form, map_smul, Prod.smul_fst, Prod.smul_snd, dotProduct_smul, smul_dotProduct, smul_eq_mul, mul_sub]

theorem map_vec (π : AE F E →+* Fv F v) (t : E → Fv F v) (ht : ∀ x, π (inclR (F := F) (AF F) x) = t x) (ε : AE F E) (p : Fin n → E)
    (q : Fin d → E) : (ε • incM F (vecMulVec p q)).map π = π ε • vecMulVec (fun i => t (p i)) fun j => t (q j) := by
  ext i j
  simp [incM, vecMulVec_apply, ht]

theorem trace_vec {k : Type} [Field k] (C : Matrix (Fin n) (Fin d) k) (p : Fin n → k) (q : Fin d → k) :
    (Cᵀ * vecMulVec p q).trace = p ⬝ᵥ C *ᵥ q := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem piW_inc (t : E →ₐ[F] Fv F v) (x : E) : piW t (inclR (F := F) (AF F) x) = t x := by
  show splitProj t (compFin F E v ((1 : AF F) ⊗ₜ[F] x)) = t x
  have : compFin F E v ((1 : AF F) ⊗ₜ[F] x) = 1 ⊗ₜ[F] x :=
    congrArg (· ⊗ₜ[F] x) (map_one (evFin F v))
  rw [this, splitProj_tmul, one_mul]

theorem at_lift (c : Fv F v) (u : Matrix (Fin n) (Fin d) (AE F E)) : At (evFin F v) (liftV v c • u) := fun a ha => by
  rw [smul_smul, ← smul_eq_mul, at_liftV v c a ha, zero_smul]

theorem so_le (hM : M.IsGood ψ) (t : E →ₐ[F] Fv F v) {Ψ} (h : Ψ ∈ M.So ψ t) : Ψ ∈ schA F (Fin n × Fin d) := by
  refine (Submodule.span_le.2 ?_ : M.So ψ t ≤ _) h
  rintro _ ⟨f, φ, h1, h2, -, rfl⟩
  obtain ⟨g, hg, e⟩ := GlobalTheory.CompanionTheory.Ar.RT.Inj.pure_eq_pureA M ψ hM φ h1 h2
  rw [e f]
  exact Submodule.subset_span ⟨f, g, hg, rfl⟩

theorem so_kill (hL : LinEx) {B : Base F E} {r s r' s' : ℕ} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s')
    (hM : M.IsGood B.ψ) (t : E →ₐ[F] Fv F v) (L : Fn F n d →ₗ[ℂ] ℂ) (S : Set ((Fin n → E) × (Fin d → E) × Fv F v))
    (hS : ∀ a ∈ S, ∀ ε : AE F E, At (evFin F v) ε → piW t ε = 1 → piW (t.comp σ) ε = 0 → ∀ c : Fv F v, ∀ Φ ∈ schA F _,
      L (M.co.rho B.ψ (liftV v c • ε • incM F (vecMulVec a.1 a.2.1)) Φ) = B.ψ (liftV v (a.2.2 * c)) * L Φ)
    (hz : ∀ C : Matrix (Fin n) (Fin d) (Fv F v), (∀ a ∈ S, (fun i => t (a.1 i)) ⬝ᵥ C *ᵥ (fun j => t (a.2.1 j)) = a.2.2) →
      ∃ p, p ≠ 0 ∧ p ᵥ* C = 0) : ∀ Φ ∈ M.So B.ψ t, L Φ = 0 := by
  refine fun Φ hΦ => (Submodule.span_le (p := LinearMap.ker L)).2 ?_ hΦ
  rintro _ ⟨f, φ, h1, h2, ⟨hv, ι, hι, h3⟩, rfl⟩
  obtain ⟨r, hr, er⟩ := GlobalTheory.CompanionTheory.Ar.RT.Inj.pure_at M B.ψ hM φ h2 f v
  have hsch : ∀ φ' ∈ SB (Fin n × Fin d → Fv F v), tens (evFin F v) φ' r ∈ schA F (Fin n × Fin d) := fun φ' h' => by
    have e := er (Function.update φ v φ') fun w hw => Function.update_of_ne hw _ _
    rw [Function.update_self] at e
    obtain ⟨g, hg, e'⟩ := GlobalTheory.CompanionTheory.Ar.RT.Inj.pure_eq_pureA M B.ψ hM (Function.update φ v φ') (fun w => by
      by_cases hw : w = v
      · subst hw
        simpa using h'
      · rw [Function.update_of_ne hw]
        exact h1 w) (by
      filter_upwards [h2, Filter.eventually_cofinite_ne v] with w h h'
      rw [Function.update_of_ne h', h])
    rw [← e, e' f]
    exact Submodule.subset_span ⟨f, g, hg, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, er φ fun _ _ => rfl]
  let l : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun φ' => L (tens (evFin F v) φ' r)
      map_add' := fun a b => by
        have e : tens (evFin F v) (a + b) r = tens (evFin F v) a r + tens (evFin F v) b r := funext fun _ => add_mul _ _ _
        rw [e, map_add (f := _)]
      map_smul' := fun c a => by
        have e : tens (evFin F v) (c • a) r = c • tens (evFin F v) a r := funext fun _ => mul_assoc _ _ _
        rw [e, map_smul]
        rfl }
  obtain ⟨ε, e0, e1, e2⟩ := exists_pair hB.cm t 1 0
  have hat : ∀ (c : Fv F v) (u : Matrix (Fin n) (Fin d) (AE F E)), At (evFin F v) (liftV v c • u) := at_lift
  refine eigen_kill_set M hB.cm hB.std (det_herm hX) (det_skew hW) hι l
    {b | ∃ a ∈ S, ∃ c : Fv F v, b = (liftV v c • ε • incM F (vecMulVec a.1 a.2.1), B.ψ (liftV v (a.2.2 * c)))} ?_ ?_ hv
    fun x hx h0 hc => h3 _ ?_
  · rintro _ ⟨a, -, c, rfl⟩
    refine ⟨hat _ _, ?_⟩
    rw [← smul_assoc, map_vec _ _ (piW_inc _), Algebra.smul_def, map_mul, e2, mul_zero, zero_smul]
  · rintro _ ⟨a, ha, c, rfl⟩ φ' h'
    change L (tens _ (locRho M B.ψ v _ φ') r) = _ * L _
    rw [← rho_tens M B.ψ (hat _ _) φ' hr, hS a ha ε e0 e1 e2 c _ (hsch φ' h')]
  obtain ⟨s₀, hs₀⟩ : ∃ s₀, B.ψ (liftV v s₀) ≠ 1 := by
    by_contra e
    push Not at e
    exact GlobalTheory.PsiNontriv.psiV_ne_one B.ψ hB.std v (AddChar.ext _ _ e)
  obtain ⟨p, hp, e⟩ := hz (X.J.map t * x.map (piW (t.comp σ)) * (W.J.map t)ᵀ) fun a ha => by
    have k1 := (hL F E σ B n d X W M _ _ _ _ hB hX hW v t).2 x (ε • incM F (vecMulVec a.1 a.2.1)) hx h0
    rw [map_vec _ _ (piW_inc _), e1, one_smul, trace_vec] at k1
    rw [← k1]
    by_contra hne
    set b := evFin F v (sy σ X W x (ε • incM F (vecMulVec a.1 a.2.1)))
    have k2 := hc _ ⟨a, ha, s₀ / (b - a.2.2), rfl⟩
    simp only at k2
    rw [sy_smul M, mul_comm, mul_liftV] at k2
    have k3 : b * (s₀ / (b - a.2.2)) = s₀ + a.2.2 * (s₀ / (b - a.2.2)) := by
      have := sub_ne_zero.2 hne
      field_simp
      ring
    rw [k3, map_add (f := _), AddChar.map_add_eq_mul] at k2
    refine hs₀ ((mul_eq_right₀ fun e0 => ?_).1 k2)
    have := GlobalTheory.StdCharFromIsStd.norm_psi hB.std (liftV v (a.2.2 * (s₀ / (b - a.2.2))))
    rw [e0, norm_zero] at this
    exact zero_ne_one this
  refine (rank_ne_iff _).2 ⟨p, hp, ?_⟩
  rw [coB_eq, Matrix.neg_mul, Matrix.neg_mul, Matrix.vecMul_neg, e, neg_zero]

end PositivityTheory.ThKCT.So

end
end

