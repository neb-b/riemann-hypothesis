module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0359
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0414
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0365
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0374
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0409
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0425
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0428
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0395

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitCentreDerivativeLieAction
section
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.CuspFinDeriv

variable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)

def cExp (t : ℝ) : GL (Fin a) (Cinf E) :=
  Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => (t : ℂ))

theorem splitCentre_eq_infGL (t : ℝ) : GlobalTheory.UnitaryBC.splitCentre E a t = infGL E a (cExp E a t) := rfl

theorem cExp_zero : cExp E a 0 = 1 := by
  have h1 : (GlobalTheory.CuspRep.expU fun _ : InfinitePlace E => ((0 : ℝ) : ℂ)) = 1 := by
    apply Units.ext
    funext v
    simp [GlobalTheory.CuspRep.expU]
  unfold cExp
  rw [h1, map_one]

theorem hasDerivAt_cExp : HasDerivAt (fun t => toL (cExp E a t).val) (oneL E a) 0 := by
  unfold cExp GlobalTheory.CuspRep.toL GlobalTheory.CuspRep.oneL
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  rw [hasDerivAt_pi]
  intro v
  simp [GlobalTheory.CuspRep.expU, Matrix.scalar_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    have h := (Complex.hasDerivAt_exp ((0 : ℝ) : ℂ)).comp_ofReal
    simp only [Complex.ofReal_zero, Complex.exp_zero] at h
    simpa using h
  · simpa [hij] using hasDerivAt_const (0 : ℝ) (0 : ℂ)

theorem hasDerivAt_splitCentre : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (g : GA E a) (s : ℝ),
    HasDerivAt (fun s : ℝ => φ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a s))
      ((lie E a (oneL E a) φ).1 (g * GlobalTheory.UnitaryBC.splitCentre E a s)) s := by
  intro E _ _ _ a φ g s
  have hφ := φ.2
  unfold GlobalTheory.CuspRep.Sm at hφ
  have hc := hφ (g * GlobalTheory.UnitaryBC.splitCentre E a s)
  have hopen : IsOpen (GlobalTheory.CuspRep.invSet E a) := by
    unfold GlobalTheory.CuspRep.invSet
    have hdet : Continuous fun x : GlobalTheory.CuspRep.Lie E a => (Matrix.of x).det :=
      (continuous_id.comp continuous_id).matrix_det
    have h3 := Units.isOpen.preimage hdet
    simpa [Matrix.isUnit_iff_isUnit_det] using h3
  have hmem : GlobalTheory.CuspRep.oneL E a ∈ GlobalTheory.CuspRep.invSet E a := by
    unfold GlobalTheory.CuspRep.invSet GlobalTheory.CuspRep.oneL GlobalTheory.CuspRep.toL
    change IsUnit (1 : Matrix (Fin a) (Fin a) (Cinf E))
    exact isUnit_one
  have hdiff : DifferentiableAt ℝ (GlobalTheory.CuspRep.chart (↑φ) (g * GlobalTheory.UnitaryBC.splitCentre E a s))
      (GlobalTheory.CuspRep.oneL E a) :=
    (hc.differentiableOn (by simp)).differentiableAt (hopen.mem_nhds hmem)
  have hγ0 : GlobalTheory.CuspRep.toL (cExp E a 0).val = GlobalTheory.CuspRep.oneL E a := by
    rw [cExp_zero]
    rfl
  have hl : HasFDerivAt (GlobalTheory.CuspRep.chart (↑φ) (g * GlobalTheory.UnitaryBC.splitCentre E a s))
      (fderiv ℝ (GlobalTheory.CuspRep.chart (↑φ) (g * GlobalTheory.UnitaryBC.splitCentre E a s)) (GlobalTheory.CuspRep.oneL E a))
      (GlobalTheory.CuspRep.toL (cExp E a 0).val) := by
    rw [hγ0]
    exact hdiff.hasFDerivAt
  have hcomp := hl.comp_hasDerivAt (0 : ℝ) (hasDerivAt_cExp E a)
  have hadd : ∀ s t : ℝ, GlobalTheory.UnitaryBC.splitCentre E a (s + t) =
      GlobalTheory.UnitaryBC.splitCentre E a s * GlobalTheory.UnitaryBC.splitCentre E a t := by
    intro s t
    rw [splitCentre_eq_infGL, splitCentre_eq_infGL, splitCentre_eq_infGL, ← map_mul]
    congr 1
    unfold cExp
    rw [← map_mul]
    congr 1
    apply Units.ext
    funext v
    simp [GlobalTheory.CuspRep.expU, Complex.exp_add]
  have hval : ∀ t : ℝ, GlobalTheory.CuspRep.chart (↑φ) (g * GlobalTheory.UnitaryBC.splitCentre E a s)
      (GlobalTheory.CuspRep.toL (cExp E a t).val) = (φ : GlobalTheory.CuspRep.GA E a → ℂ) (g * GlobalTheory.UnitaryBC.splitCentre E a (s + t)) := by
    intro t
    unfold GlobalTheory.CuspRep.chart GlobalTheory.CuspRep.toL
    have hu : IsUnit (Matrix.of (Matrix.of.symm (cExp E a t).val)) := by
      change IsUnit (cExp E a t).val
      exact (cExp E a t).isUnit
    rw [dite_eq_left hu]
    have hunit : hu.unit = cExp E a t := Units.ext (by rfl)
    rw [hunit, ← splitCentre_eq_infGL, hadd, mul_assoc]
  have hF : HasDerivAt (fun t : ℝ => (φ : GlobalTheory.CuspRep.GA E a → ℂ) (g * GlobalTheory.UnitaryBC.splitCentre E a (s + t)))
      (fderiv ℝ (GlobalTheory.CuspRep.chart (↑φ) (g * GlobalTheory.UnitaryBC.splitCentre E a s)) (GlobalTheory.CuspRep.oneL E a)
        (GlobalTheory.CuspRep.oneL E a)) (s - s) := by
    rw [sub_self]
    have h5 : (GlobalTheory.CuspRep.chart (↑φ) (g * GlobalTheory.UnitaryBC.splitCentre E a s) ∘ fun t => GlobalTheory.CuspRep.toL (cExp E a t).val) =
        fun t : ℝ => (φ : GlobalTheory.CuspRep.GA E a → ℂ) (g * GlobalTheory.UnitaryBC.splitCentre E a (s + t)) := funext hval
    rw [← h5]
    exact hcomp
  have hF2 := HasDerivAt.comp_sub_const s s hF
  have h6 : (fun x : ℝ => (φ : GlobalTheory.CuspRep.GA E a → ℂ) (g * GlobalTheory.UnitaryBC.splitCentre E a (s + (x - s)))) =
      fun x : ℝ => (φ : GlobalTheory.CuspRep.GA E a → ℂ) (g * GlobalTheory.UnitaryBC.splitCentre E a x) := by
    funext x
    rw [show s + (x - s) = x by ring]
  rw [h6] at hF2
  exact hF2

end GlobalTheory.CompanionTheory.CuspFinDeriv

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitCentreTranslatePreservesCuspSpace
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.CuspFinGL.Transl

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem rt_comm_of_central {h : GA E a} (hc : ∀ g : GA E a, h * g = g * h) (x : GA E a) (φ : Sm E a) :
    rt E a x (rt E a h φ) = rt E a h (rt E a x φ) := by
  refine Subtype.ext (funext fun g => ?_)
  change φ.1 (g * x * h) = φ.1 (g * h * x)
  rw [mul_assoc g x h, mul_assoc g h x, hc x]

theorem rt_injective (h : GA E a) : Function.Injective (rt E a h) := fun φ ψ e => by
  refine Subtype.ext (funext fun g => ?_)
  have := congrArg (fun f : Sm E a => f.1 (g * h⁻¹)) e
  simpa using this

theorem isAutForm_rt_of_central {h : GA E a} (hc : ∀ g : GA E a, h * g = g * h) {φ : Sm E a}
    (hφ : IsAutForm φ) : IsAutForm (rt E a h φ) := by
  refine { left := ?_, level := ?_, kfin := ?_, zfin := ?_, growth := ?_ }
  · intro γ g
    change φ.1 (ratGL E a γ * g * h) = φ.1 (g * h)
    rw [mul_assoc, hφ.left]
  · have e : {k | finRep E a k (rt E a h φ) = rt E a h φ} = {k | finRep E a k φ = φ} := by
      ext k
      change rt E a (finGL E a k) (rt E a h φ) = rt E a h φ ↔ rt E a (finGL E a k) φ = φ
      rw [rt_comm_of_central hc]
      exact (rt_injective h).eq_iff
    rw [e]
    exact hφ.level
  · have := hφ.kfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)).map (rt E a h))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨cptRep E a k φ, Submodule.subset_span ⟨k, rfl⟩, (rt_comm_of_central hc _ φ).symm⟩
  · have := hφ.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a)).map (rt E a h))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨z φ, Submodule.subset_span ⟨z, hz, rfl⟩, ?_⟩
    exact (LinearMap.congr_fun (GlobalTheory.CompanionTheory.CTFin.Slice1.commute_rt_of_mem_Zalg hz h).eq φ).symm
  · intro g
    obtain ⟨C, N, hb⟩ := hφ.growth (g * h)
    refine ⟨C, N, fun y => ?_⟩
    have e : (rt E a h φ).1 (g * infGL E a y) = φ.1 (g * h * infGL E a y) := by
      change φ.1 (g * infGL E a y * h) = _
      rw [mul_assoc g _ h, mul_assoc g h, hc]
    rw [e]
    exact hb y

theorem rt_splitCentre_mem : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (L : Subgroup (GL (Fin a) (Af E))) (W : Type) [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Kinf E a) W) (J : Set (Module.End ℂ (Sm E a))), J ⊆ Zalg E a →
    ∀ φ : Sm E a, φ ∈ genSpace L ρ J → IsCuspidal φ.1 → ∀ t : ℝ,
      rt E a (GlobalTheory.UnitaryBC.splitCentre E a t) φ ∈ genSpace L ρ J ∧
        IsCuspidal (rt E a (GlobalTheory.UnitaryBC.splitCentre E a t) φ).1 := by
  intro E _ _ _ a L W _ _ ρ J hJ φ hφ hcusp t
  set h := GlobalTheory.UnitaryBC.splitCentre E a t with hh
  have hc : ∀ g : GA E a, h * g = g * h := GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm t
  obtain ⟨hA, hL, hK, hZ⟩ := hφ
  refine ⟨⟨isAutForm_rt_of_central hc hA, fun k hk => ?_, fun g => ?_, fun z hz => ?_⟩, ?_⟩
  · change rt E a (finGL E a k) (rt E a h φ) = rt E a h φ
    rw [rt_comm_of_central hc]
    exact congrArg (rt E a h) (hL k hk)
  · have e : (fun k : Kinf E a => (cptRep E a k (rt E a h φ)).1 g) =
        fun k : Kinf E a => (cptRep E a k φ).1 (g * h) := by
      funext k
      exact congrArg (fun f : Sm E a => f.1 g) (rt_comm_of_central hc _ φ)
    rw [e]
    exact hK (g * h)
  · have e := LinearMap.congr_fun (GlobalTheory.CompanionTheory.CTFin.Slice1.commute_rt_of_mem_Zalg (hJ hz) h).eq φ
    rw [mul_apply_eq_comp, mul_apply_eq_comp] at e
    rw [e, hZ z hz, map_zero]
  · intro r hr hr' inst1 inst2 μ 𝓕 hμ hF g
    have e : ∀ x : BlockIx a r → Ad E, (rt E a h φ).1 (unip x * g) = φ.1 (unip x * (g * h)) :=
      fun x => congrArg φ.1 (mul_assoc _ _ _)
    simp only [e]
    exact hcusp r hr hr' μ 𝓕 hμ hF (g * h)

end GlobalTheory.CompanionTheory.CuspFinGL.Transl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StrictlyDominantHeckeKernel
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Lbc

theorem heckeOp_nilpotent_on_ker :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ t : Levi k (Bl d), IsStrictlyDominant k N J d hd t → ∀ T : Module.End ℂ (fixed π J), IsHeckeOp π J (leviEmb k (stdBlocks d hd) t) T → ∀ v : fixed π J, (Submodule.Quotient.mk (v : V) : Jacquet π (unipRad k (stdBlocks d hd))) = 0 → ∃ r : ℕ, (T ^ r) v = 0 := by
  intro k _ _ _ _ N h d hd J hJo hJc hJf hpos V _ _ π hπ t ht T hT v hv
  set e := leviEmb k (stdBlocks d hd) with he

  have hdom : ∀ r : ℕ, IsDominant k N J d hd (t ^ r) := by
    intro r
    induction r with
    | zero => simpa using (isDominant_one_and_mul k N J h d hd).1
    | succ r ih =>
      rw [pow_succ]
      exact (isDominant_one_and_mul k N J h d hd).2 _ _ ih ht.1

  have hecke : ∀ r : ℕ, IsHeckeOp π J (e (t ^ r)) (T ^ r) := by
    intro r
    induction r with
    | zero =>
      intro w l _
      simp
    | succ r ih =>
      rw [pow_succ, pow_succ T]
      exact _root_.GlobalTheory.CompanionTheory.Lbc.hecke_dominant_mul k N h d hd J hJo hJc hJf hpos V π hπ _ _ (hdom r) ht.1 _ _ ih hT

  have key : ∀ u ∈ twKer π (unipRad k (stdBlocks d hd)) 1, ∃ R : ℕ, ∀ r ≥ R,
      ∀ l : Module.Dual ℂ V, (∀ x ∈ J, l ∘ₗ π x = l) → l (π (e t ^ r) u) = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨n, w, rfl⟩ := hu
      obtain ⟨R, hR⟩ := _root_.GlobalTheory.CompanionTheory.ExpandN.exists_pow_conj_mem_KN k N h d hd J hJo hJc hJf hpos t ht (n : GL (Fin N) k) n.2
      refine ⟨R, fun r hr l hl => ?_⟩
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hr
      have hmem : e t ^ (R + j) * (n : GL (Fin N) k) * (e t ^ (R + j))⁻¹ ∈ KN k N J d hd := by
        have := (hdom j).1 _ hR
        rw [map_pow] at this
        convert this using 1
        rw [add_comm R j, pow_add]
        group
        rfl
      have hx := hl _ hmem.1
      have hy := LinearMap.congr_fun hx (π (e t ^ (R + j)) w)
      simp only [LinearMap.comp_apply] at hy
      have hz : π (e t ^ (R + j) * (n : GL (Fin N) k) * (e t ^ (R + j))⁻¹) (π (e t ^ (R + j)) w)
          = π (e t ^ (R + j)) (π (n : GL (Fin N) k) w) := by
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 2
        group
      rw [hz] at hy
      simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub, hy, sub_self]
    | zero => exact ⟨0, fun r _ l _ => by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨A, hA⟩ := ha
      obtain ⟨B, hB⟩ := hb
      refine ⟨max A B, fun r hr l hl => ?_⟩
      rw [map_add (f := _), map_add (f := _), hA r (le_trans (le_max_left _ _) hr) l hl,
        hB r (le_trans (le_max_right _ _) hr) l hl, add_zero]
    | smul c a _ ha =>
      obtain ⟨A, hA⟩ := ha
      refine ⟨A, fun r hr l hl => ?_⟩
      rw [map_smul, map_smul, hA r hr l hl, smul_zero]
  obtain ⟨R, hR⟩ := key _ ((Submodule.Quotient.mk_eq_zero _).1 hv)
  refine ⟨R, ?_⟩
  have h0 : (((T ^ R) v : fixed π J) : V) = 0 := by
    refine _root_.GlobalTheory.CompanionTheory.CompactAvg.invariant_forms_separate_fixed _ J hJc V π hπ _ ((T ^ R) v).2 fun l hl => ?_
    rw [← hecke R v l hl, map_pow]
    exact hR R le_rfl l hl
  exact Subtype.ext h0

end GlobalTheory.CompanionTheory.Lbc
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumFrameIdem
section
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.RapidDecay

abbrev FrameIx (r : ℕ) : Type := Option (Fin r ⊕ Fin r)

variable {E : Type} [Field E] {n r : ℕ}

def frameIdem (S : E →+* E) (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E) :
    FrameIx r → Matrix (Fin n) (Fin n) E
  | some (Sum.inl i) => X * single i i (1 : E) * (cT S Y * J)
  | some (Sum.inr i) => Y * single i i (1 : E) * (cT S X * J)
  | none => 1 - X * (cT S Y * J) - Y * (cT S X * J)

def frameWt (t : Fin r → ℝ) : FrameIx r → ℝ
  | some (Sum.inl i) => t i
  | some (Sum.inr i) => (t i)⁻¹
  | none => 1

def frameLev (s : Fin r) : FrameIx r → ℕ
  | some (Sum.inl i) => if i ≤ s then 2 else 1
  | some (Sum.inr i) => if i ≤ s then 0 else 1
  | none => 1

theorem sum_frameIdem (S : E →+* E) (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E) :
    ∑ α, frameIdem S J X Y α = 1 := by
  have key : ∀ (A : Matrix (Fin n) (Fin r) E) (B : Matrix (Fin r) (Fin n) E),
      ∑ i : Fin r, (A * (Matrix.single i i (1 : E) : Matrix (Fin r) (Fin r) E) * B : Matrix (Fin n) (Fin n) E) = A * B := fun A B => by
    rw [← Matrix.sum_mul, ← Matrix.mul_sum, Matrix.sum_single_one, Matrix.mul_one]
  rw [Fintype.sum_option, Fintype.sum_sum_type]
  simp only [frameIdem]
  rw [key, key]
  abel

theorem frameWt_pos {t : Fin r → ℝ} (ht : ∀ i, 0 < t i) (α : FrameIx r) : 0 < frameWt t α := by
  rcases α with _ | i | i
  · exact one_pos
  · exact ht i
  · exact inv_pos.2 (ht i)

end GlobalTheory.CompanionTheory.RapidDecay

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistTwistAdd
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibOrd

theorem dpow_add_apply {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (s s' : ℝ) (x : GL (Fin n) k) : dpow n (s + s') x = dpow n s x * dpow n s' x := by
  simp only [dpow, detChar_apply, Complex.ofReal_add, absPow_add, MonoidHom.mul_apply]

theorem giso_tw_tw : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (A : GRep k n) (s s' : ℝ), GIso ((A.tw s).tw s') (A.tw (s + s')) := by
  intro k _ _ _ _ n A s s'
  refine ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ A.V) fun x => ?_⟩
  ext v
  show ((dpow n s' x : ℂˣ) : ℂ) • ((dpow n s x : ℂˣ) : ℂ) • A.ρ x v = ((dpow n (s + s') x : ℂˣ) : ℂ) • A.ρ x v
  rw [dpow_add_apply, smul_smul, Units.val_mul, mul_comm]

end GlobalTheory.CompanionTheory.LeibOrd

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedBoxIntegralIdentity
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology

namespace GlobalTheory.CompanionTheory.MirPair

theorem setIntegral_inter_box_of_twists {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
    (ψ : AddChar k Circle) (c : kˣ) (hψ : Continuous ψ) (hc : HasConductor ψ c) (m : ℕ) (t : kˣ)
    (M : Set (Fin m → k)) (f : (Fin m → k) → ℂ) (A : ℂ) (hM : IsCompact M) (hMm : MeasurableSet M)
    (hf : Continuous f)
    (h : ∀ b ∈ box m (c * t⁻¹), ∫ x in M, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * f x ∂(piHaar ν m) = A) :
    ∫ x in M ∩ (box m t : Set (Fin m → k)), f x ∂(piHaar ν m) = A := by
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  haveI : (GlobalTheory.CompanionTheory.MirPair.piHaar ν m).IsAddHaarMeasure := by
    unfold GlobalTheory.CompanionTheory.MirPair.piHaar
    infer_instance
  haveI : SigmaFinite (GlobalTheory.CompanionTheory.MirPair.piHaar ν m) := by
    unfold GlobalTheory.CompanionTheory.MirPair.piHaar
    infer_instance
  haveI : (GlobalTheory.CompanionTheory.MirPair.piHaar ν m).IsAddRightInvariant := inferInstance
  set μ := GlobalTheory.CompanionTheory.MirPair.piHaar ν m with hμ
  have hbox : ∀ s : kˣ, GlobalTheory.SplitWeil.FourierPi.box (Fin m) s = (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box m s : Set (Fin m → k)) := by
    intro s
    rw [GlobalTheory.CompanionTheory.BZOnto.PerpSmall.coe_box]
    rfl
  set B' : Set (Fin m → k) := (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box m (c * t⁻¹) : Set (Fin m → k)) with hB'
  set Bt : Set (Fin m → k) := (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box m t : Set (Fin m → k)) with hBt
  have hB'c : IsCompact B' := GlobalTheory.CompanionTheory.BZOnto.PerpSmall.isCompact_box m _
  have hB'm : MeasurableSet B' := hB'c.isClosed.measurableSet
  have hBtm : MeasurableSet Bt := (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.isCompact_box m t).isClosed.measurableSet
  have hpos : 0 < μ.real B' := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (μ.measure_pos_of_mem_nhds (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box_mem_nhds m _)).ne'
      hB'c.measure_lt_top.ne
  have hfour : ∀ x, ∫ b, B'.indicator (fun _ => (1 : ℂ)) b * ((ψ (b ⬝ᵥ x) : Circle) : ℂ) ∂μ =
      Bt.indicator (fun _ => ((μ.real B' : ℝ) : ℂ)) x := by
    intro x
    have e := GlobalTheory.SplitWeil.FourierPi.fourier_indicator_pi μ hc t x
    rw [hbox, hbox] at e
    exact e
  have hcc : Continuous (fun z : Circle => (z : ℂ)) := continuous_induced_dom
  have hdot : Continuous fun q : (Fin m → k) × (Fin m → k) => q.1 ⬝ᵥ q.2 :=
    GlobalTheory.SplitWeil.FourierPi.continuous_dot
  have hψc : Continuous fun q : (Fin m → k) × (Fin m → k) => ((ψ (-(q.1 ⬝ᵥ q.2)) : Circle) : ℂ) :=
    hcc.comp (hψ.comp hdot.neg)
  have hg1 : Integrable (B'.indicator fun _ => (1 : ℂ)) μ :=
    (integrable_indicator_iff hB'm).2 (continuousOn_const.integrableOn_compact' hB'c hB'm)
  have hg2 : Integrable (M.indicator f) μ :=
    (integrable_indicator_iff hMm).2 (hf.continuousOn.integrableOn_compact' hM hMm)
  have hint : Integrable (fun z : (Fin m → k) × (Fin m → k) => ((ψ (-(z.1 ⬝ᵥ z.2)) : Circle) : ℂ) *
      (B'.indicator (fun _ => (1 : ℂ)) z.1 * M.indicator f z.2)) (μ.prod μ) := by
    refine (hg1.mul_prod hg2).bdd_mul (c := 1) hψc.aestronglyMeasurable (ae_of_all _ fun z => ?_)
    simp [Circle.norm_coe]
  have hswap : ∫ b, (∫ x, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) *
        (B'.indicator (fun _ => (1 : ℂ)) b * M.indicator f x) ∂μ) ∂μ =
      ∫ x, (∫ b, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) *
        (B'.indicator (fun _ => (1 : ℂ)) b * M.indicator f x) ∂μ) ∂μ :=
    integral_integral_swap hint
  have hD : (fun b => ∫ x, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) *
      (B'.indicator (fun _ => (1 : ℂ)) b * M.indicator f x) ∂μ) = B'.indicator (fun _ => A) := by
    funext b
    by_cases hb : b ∈ B'
    · simp only [Set.indicator_of_mem hb, one_mul]
      have hx : (fun x => ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * M.indicator f x) =
          M.indicator (fun x => ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * f x) := by
        funext x
        by_cases hxM : x ∈ M
        · simp only [Set.indicator_of_mem hxM]
        · simp only [Set.indicator_of_notMem hxM, mul_zero]
      rw [hx, integral_indicator hMm]
      exact h b hb
    · simp [Set.indicator_of_notMem hb]
  have hE : (fun x => ∫ b, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) *
      (B'.indicator (fun _ => (1 : ℂ)) b * M.indicator f x) ∂μ) =
      fun x => ((μ.real B' : ℝ) : ℂ) * (M ∩ Bt).indicator f x := by
    funext x
    have e : ∀ b, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * (B'.indicator (fun _ => (1 : ℂ)) b * M.indicator f x) =
        B'.indicator (fun _ => (1 : ℂ)) b * ((ψ (b ⬝ᵥ -x) : Circle) : ℂ) * M.indicator f x := by
      intro b
      rw [dotProduct_neg]
      ring
    simp only [e]
    rw [integral_mul_const, hfour (-x)]
    have hneg : -x ∈ Bt ↔ x ∈ Bt := by
      simp only [hBt, SetLike.mem_coe, neg_mem_iff]
    by_cases hxB : x ∈ Bt
    · by_cases hxM : x ∈ M
      · simp only [Set.indicator_of_mem (hneg.2 hxB), Set.indicator_of_mem hxM,
          Set.indicator_of_mem (Set.mem_inter hxM hxB)]
      · simp only [Set.indicator_of_mem (hneg.2 hxB), Set.indicator_of_notMem hxM,
          Set.indicator_of_notMem (fun hx : x ∈ M ∩ Bt => hxM hx.1), mul_zero]
    · simp only [Set.indicator_of_notMem (fun hx : -x ∈ Bt => hxB (hneg.1 hx)),
        Set.indicator_of_notMem (fun hx : x ∈ M ∩ Bt => hxB hx.2), zero_mul, mul_zero]
  rw [hD, hE, integral_indicator_const _ hB'm, integral_const_mul,
    integral_indicator (hMm.inter hBtm), Complex.real_smul] at hswap
  exact (mul_left_cancel₀ (Complex.ofReal_ne_zero.2 hpos.ne') hswap).symm

end GlobalTheory.CompanionTheory.MirPair
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRankProductLeOneStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_rank_product_le_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Leib.WhitHeredity k → GlobalTheory.BZSeg.WhitRankIrr k → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (h N : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), Module.rank ℂ (TwJacquet (prodIrr x hd) (unipB k (Fin N)) (whitChar ψ N)) ≤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.RgGu.rank_twJacquet_prodIrr_le_one | exact GlobalTheory.CompanionTheory.RgGu.rank_twJacquet_prodIrr_le_one | (intros; apply GlobalTheory.CompanionTheory.RgGu.rank_twJacquet_prodIrr_le_one <;> assumption)
end

